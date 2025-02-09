// Copyright (c) 2022, Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0
//
// Most of the code below is based on code from https://github.com/celo-org/celo-threshold-bls-rs,
// modified for our needs.
//

use crate::types::{IndexedValue, ShareIndex};
use fastcrypto::error::{FastCryptoError, FastCryptoResult};
use fastcrypto::groups::{GroupElement, MultiScalarMul, Scalar};
use fastcrypto::traits::AllowedRng;
use itertools::Either;
use serde::{Deserialize, Serialize};
use std::borrow::Borrow;
use std::collections::HashSet;

/// Types

pub type Eval<A> = IndexedValue<A>;

/// A polynomial that is using a scalar for the variable x and a generic
/// element for the coefficients.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Poly<C>(Vec<C>);

pub type PrivatePoly<C> = Poly<<C as GroupElement>::ScalarType>;
pub type PublicPoly<C> = Poly<C>;

/// Vector related operations.

impl<C> Poly<C> {
    /// Returns the degree of the polynomial
    pub fn degree(&self) -> u32 {
        // e.g. c_0 + c_1 * x + c_2 * x^2 + c_3 * x^3
        // ^ 4 coefficients correspond to a 3rd degree poly
        (self.0.len() - 1) as u32
    }
}

impl<C> From<Vec<C>> for Poly<C> {
    fn from(c: Vec<C>) -> Self {
        Self(c)
    }
}

/// GroupElement operations.

impl<C: GroupElement> Poly<C> {
    /// Returns a polynomial with the zero element.
    pub fn zero() -> Self {
        Self::from(vec![C::zero()])
    }

    /// Performs polynomial addition in place.
    pub fn add(&mut self, other: &Self) {
        // if we have a smaller degree we should pad with zeros
        if self.0.len() < other.0.len() {
            self.0.resize(other.0.len(), C::zero())
        }
        self.0.iter_mut().zip(&other.0).for_each(|(a, b)| *a += *b)
    }

    // TODO: Some of the functions/steps below may be executed many times in practice thus cache can be
    // used to improve efficiency (e.g., eval(i) may be called with the same index every time a partial
    // signature from party i is verified).

    /// Evaluates the polynomial at the specified value.
    pub fn eval(&self, i: ShareIndex) -> Eval<C> {
        // Use Horner's Method to evaluate the polynomial.
        let xi = C::ScalarType::from(i.get().into());
        let res = self
            .0
            .iter()
            .rev()
            .fold(C::zero(), |sum, coeff| sum * xi + coeff);

        Eval {
            index: i,
            value: res,
        }
    }

    // Multiply using u128 if possible, otherwise just convert one element to the group element and return the other.
    pub fn fast_mult(x: u128, y: u128) -> Either<(C::ScalarType, u128), u128> {
        if x.leading_zeros() >= (128 - y.leading_zeros()) {
            Either::Right(x * y)
        } else {
            Either::Left((C::ScalarType::from(x), y))
        }
    }

    // Expects exactly t unique shares.
    fn get_lagrange_coefficients_for_c0(
        t: u32,
        mut shares: impl Iterator<Item = impl Borrow<Eval<C>>>,
    ) -> FastCryptoResult<Vec<C::ScalarType>> {
        let mut ids_set = HashSet::new();
        let (shares_size_lower, shares_size_upper) = shares.size_hint();
        let indices = shares.try_fold(
            Vec::with_capacity(shares_size_upper.unwrap_or(shares_size_lower)),
            |mut vec, s| {
                // Check for duplicates.
                if !ids_set.insert(s.borrow().index) {
                    return Err(FastCryptoError::InvalidInput); // expected unique ids
                }
                vec.push(s.borrow().index.get() as u128);
                Ok(vec)
            },
        )?;
        if indices.len() != t as usize {
            return Err(FastCryptoError::InvalidInput);
        }

        let full_numerator = indices.iter().fold(C::ScalarType::generator(), |acc, i| {
            acc * C::ScalarType::from(*i)
        });

        let mut coeffs = Vec::new();
        for i in &indices {
            let mut negative = false;
            let (mut denominator, remaining) = indices.iter().filter(|j| *j != i).fold(
                (C::ScalarType::from(*i), 1u128),
                |(prev_acc, remaining), j| {
                    let diff = if i > j {
                        negative = !negative;
                        i - j
                    } else {
                        j - i
                    };
                    debug_assert_ne!(diff, 0);
                    let either = Self::fast_mult(remaining, diff);
                    match either {
                        Either::Left((remaining, diff)) => (prev_acc * remaining, diff),
                        Either::Right(diff) => (prev_acc, diff),
                    }
                },
            );

            denominator = denominator * C::ScalarType::from(remaining); // remaining != 0
            if negative {
                denominator = -denominator;
            }
            let coeff = full_numerator / denominator;
            coeffs.push(coeff.expect("safe since i != j"));
        }
        Ok(coeffs)
    }

    /// Given exactly `t` polynomial evaluations, it will recover the polynomial's constant term.
    pub fn recover_c0(
        t: u32,
        shares: impl Iterator<Item = impl Borrow<Eval<C>>> + Clone,
    ) -> Result<C, FastCryptoError> {
        let coeffs = Self::get_lagrange_coefficients_for_c0(t, shares.clone())?;
        let plain_shares = shares.map(|s| s.borrow().value);
        let res = coeffs
            .iter()
            .zip(plain_shares)
            .fold(C::zero(), |acc, (c, s)| acc + (s * *c));
        Ok(res)
    }

    /// Checks if a given share is valid.
    pub fn verify_share(&self, idx: ShareIndex, share: &C::ScalarType) -> FastCryptoResult<()> {
        let e = C::generator() * share;
        let pub_eval = self.eval(idx);
        if pub_eval.value == e {
            Ok(())
        } else {
            Err(FastCryptoError::InvalidInput)
        }
    }

    /// Return the constant term of the polynomial.
    pub fn c0(&self) -> &C {
        &self.0[0]
    }

    /// Returns the coefficients of the polynomial.
    pub fn as_vec(&self) -> &Vec<C> {
        &self.0
    }
}

/// Scalar operations.

impl<C: Scalar> Poly<C> {
    /// Returns a new polynomial of the given degree where each coefficients is
    /// sampled at random from the given RNG.
    /// In the context of secret sharing, the threshold is the degree + 1.
    pub fn rand<R: AllowedRng>(degree: u32, rng: &mut R) -> Self {
        let coeffs: Vec<C> = (0..=degree).map(|_| C::rand(rng)).collect();
        Self::from(coeffs)
    }

    /// Commits the scalar polynomial to the group and returns a polynomial over
    /// the group.
    pub fn commit<P: GroupElement<ScalarType = C>>(&self) -> Poly<P> {
        let commits = self
            .0
            .iter()
            .map(|c| P::generator() * c)
            .collect::<Vec<P>>();

        Poly::<P>::from(commits)
    }
}

impl<C: GroupElement + MultiScalarMul> Poly<C> {
    /// Given exactly `t` polynomial evaluations, it will recover the polynomial's
    /// constant term.
    pub fn recover_c0_msm(
        t: u32,
        shares: impl Iterator<Item = impl Borrow<Eval<C>>> + Clone,
    ) -> Result<C, FastCryptoError> {
        let coeffs = Self::get_lagrange_coefficients_for_c0(t, shares.clone())?;
        let plain_shares = shares.map(|s| s.borrow().value).collect::<Vec<_>>();
        let res = C::multi_scalar_mul(&coeffs, &plain_shares).expect("sizes match");
        Ok(res)
    }
}
