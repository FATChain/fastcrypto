use crate::polynomial::PrivatePoly;
use fastcrypto::error::{FastCryptoError, FastCryptoResult};
use fastcrypto::groups::{GroupElement, MultiScalarMul};
use fastcrypto::traits::AllowedRng;
use std::num::NonZeroU32;

/// Helper functions for checking relations between scalars and group elements.

/// Check that a pair (k, H) satisfies H = k*G using a random combination of the pairs and
/// multi scalar multiplication.
pub fn verify_pairs<G: GroupElement + MultiScalarMul, R: AllowedRng>(
    pairs: &[(G::ScalarType, G)],
    rng: &mut R,
) -> FastCryptoResult<()> {
    if pairs.is_empty() {
        return Ok(());
    }
    // Denote the inputs by (k1, H1), (k2, H2), ..., (kn, Hn)
    // Generate random r1, r2, ..., rn
    let rs = get_random_scalars::<G, R>(pairs.len() as u32, rng);
    // Compute (r1*k1 + r2*k2 + ... + rn*kn)*G
    let lhs = G::generator()
        * rs.iter()
            .zip(pairs.iter())
            .fold(G::ScalarType::zero(), |acc, (r, (k, _))| acc + *r * *k);
    // Compute r1*H1 + r2*H2 + ... + rn*Hn
    let rhs = G::multi_scalar_mul(
        &rs[..],
        &pairs.iter().map(|(_, g)| g.clone()).collect::<Vec<_>>()[..],
    )
    .expect("valid sizes");

    if lhs == rhs {
        Ok(())
    } else {
        Err(FastCryptoError::InvalidProof)
    }
}

/// Check that a triplet (k, G, H) satisfies H = k*G using a random combination of the
/// triplets and multi scalar multiplication.
pub fn verify_triplets<G: GroupElement + MultiScalarMul, R: AllowedRng>(
    triplets: &[(G::ScalarType, G, G)],
    rng: &mut R,
) -> FastCryptoResult<()> {
    if triplets.is_empty() {
        return Ok(());
    }
    // Denote the inputs by (k1, G1, H1), (k2, G2, H2), ..., (kn, Gn, Hn)
    // Generate random r1, r2, ..., rn
    let rs = get_random_scalars::<G, R>(triplets.len() as u32, rng);
    // Compute r1*k1, r2*k2, ..., rn*kn
    let lhs_coeffs = rs
        .iter()
        .zip(triplets.iter())
        .map(|(r, (k, _, _))| *r * *k)
        .collect::<Vec<_>>();
    // Compute r1*k1*G1 + r2*k2*G2 + ... + rn*kn*Gn
    let lhs = G::multi_scalar_mul(
        &lhs_coeffs[..],
        &triplets
            .iter()
            .map(|(_, b, _)| b.clone())
            .collect::<Vec<_>>()[..],
    )
    .expect("valid sizes");
    // Compute r1*H1 + r2*H2 + ... + rn*Hn
    let rhs = G::multi_scalar_mul(
        &rs[..],
        &triplets
            .iter()
            .map(|(_, _, k_b)| k_b.clone())
            .collect::<Vec<_>>()[..],
    )
    .expect("valid sizes");

    if lhs == rhs {
        Ok(())
    } else {
        Err(FastCryptoError::InvalidProof)
    }
}

/// Check that partial public keys form a polynomial of the right degree using the protocol of
/// https://eprint.iacr.org/2017/216.pdf. deg_f should be n-k-2 if the polynomial is of degree k.
pub fn verify_deg_t_poly<G: GroupElement + MultiScalarMul, R: AllowedRng>(
    deg_f: u32,
    values: &[G],
    precomputed_dual_code_coefficients: &Vec<G::ScalarType>,
    rng: &mut R,
) -> FastCryptoResult<()> {
    let poly_f = PrivatePoly::<G>::rand(deg_f, rng);
    let coefficients = precomputed_dual_code_coefficients
        .iter()
        .enumerate()
        .map(|(i, c)| *c * poly_f.eval(NonZeroU32::new((i + 1) as u32).unwrap()).value)
        .collect::<Vec<_>>();
    let lhs = G::multi_scalar_mul(&coefficients[..], values).expect("sizes match");
    if lhs != G::zero() {
        return Err(FastCryptoError::InvalidProof);
    }
    Ok(())
}

pub fn get_random_scalars<G: GroupElement, R: AllowedRng>(
    n: u32,
    rng: &mut R,
) -> Vec<<G as GroupElement>::ScalarType> {
    // TODO: can use 40 bits instead of 64 (& 0x000F_FFFF_FFFF_FFFF below)
    (0..n)
        .into_iter()
        .map(|_| G::ScalarType::from(rng.next_u64()))
        .collect::<Vec<_>>()
}
