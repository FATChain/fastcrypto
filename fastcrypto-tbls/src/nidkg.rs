// Copyright (c) 2022, Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0
//

use crate::ecies;
use crate::polynomial::{Poly, PrivatePoly, PublicPoly};
use crate::random_oracle::RandomOracle;
use crate::tbls::Share;
use crate::types::ShareIndex;
use fastcrypto::error::{FastCryptoError, FastCryptoResult};
use fastcrypto::groups::{GroupElement, HashToGroupElement, MultiScalarMul, Scalar};
use fastcrypto::hmac::{hmac_sha3_256, HmacKey};
use fastcrypto::traits::{AllowedRng, ToFromBytes};
use itertools::izip;
use serde::{de::DeserializeOwned, Deserialize, Serialize};
use std::collections::HashMap;
use std::num::NonZeroU32;

// TODO: add outputs -> fraud claims -> weights

/// PKI node, with a unique id and its encryption public key.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PkiNode<G: GroupElement> {
    pub id: ShareIndex,
    pub pk: ecies::PublicKey<G>,
}

// Assumptions:
// - All parties have the same list.
// - Their IDs are some permutation of the range(1, n) where n is the number of parties.
pub type Nodes<G> = Vec<PkiNode<G>>;

/// Party in the DKG protocol.
#[derive(Clone, PartialEq, Eq)]
pub struct Party<G: GroupElement>
where
    G::ScalarType: Serialize + DeserializeOwned,
{
    id: ShareIndex,
    nodes: Nodes<G>,
    threshold: u32,
    random_oracle: RandomOracle,
    ecies_sk: ecies::PrivateKey<G>,
    vss_sk: PrivatePoly<G>,
    message: Message<G>,
    // Precomputed values to be used when verifying messages.
    precomputed_dual_code_coefficients: Vec<G::ScalarType>,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct PairOfEncryptions<G: GroupElement> {
    pub enc0: ecies::Encryption<G>,
    pub enc1: ecies::Encryption<G>,
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
enum EncryptionInfo<G: GroupElement> {
    ForVerification { k: G::ScalarType, k_x_g: G }, // k_x_g is added to reduce verification time.
    ForEvaluation { diff: G::ScalarType },
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
struct ProcessedPair<G: GroupElement>
where
    G::ScalarType: Serialize + DeserializeOwned,
{
    pub enc0: EncryptionInfo<G>,
    pub enc1: EncryptionInfo<G>,
}

#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
pub struct Message<G: GroupElement>
where
    G::ScalarType: Serialize + DeserializeOwned,
{
    sender: ShareIndex,
    // TODO: need a proof of possession/knowledge?
    partial_pks: Vec<G>,
    /// The encrypted shares created by the sender.
    pairs: Vec<PairOfEncryptions<G>>,
    processed_pairs: Vec<ProcessedPair<G>>,
}

// #[derive(Clone, Debug)]
// pub struct PartyPostDkg<G: GroupElement> {
//     id: ShareIndex,
//     nodes: Nodes<G>,
//     threshold: u32,
//     random_oracle: RandomOracle,
//     // ecies_sk: ecies::PrivateKey<G>,
//     // vss_sk: PrivatePoly<G>,
//     vss_pk: PublicPoly<G>,
//
//     // Precomputed values to be used when verifying messages.
//     precomputed_dual_code_coefficients: Vec<G::ScalarType>,
// }

/// A dealer in the DKG protocol.
impl<G> Party<G>
where
    <G as GroupElement>::ScalarType: Serialize + DeserializeOwned + HashToGroupElement,
    G: GroupElement + MultiScalarMul + Serialize,
{
    /// 1. Create a new private key and send the public key to all parties.
    /// 2. After all parties have sent their public keys, create the set of nodes. We assume here
    ///    that the set of nodes is the same for all parties.
    /// 3. Create a new Party instance with the private key and the set of nodes.
    pub fn new<R: AllowedRng>(
        ecies_sk: ecies::PrivateKey<G>,
        nodes: Nodes<G>,
        threshold: u32, // The number of parties that are needed to reconstruct the full signature.
        random_oracle: RandomOracle,
        rng: &mut R,
    ) -> Result<Self, FastCryptoError> {
        // Check all ids are consecutive and start from 1.
        let mut nodes = nodes;
        nodes.sort_by_key(|n| n.id);
        let max_id = nodes.len();
        if (1..=max_id).any(|i| nodes[i - 1].id != NonZeroU32::new(i as u32).unwrap()) {
            return Err(FastCryptoError::InvalidInput);
        }
        // Check if my public key is in one of the nodes.
        let ecies_pk = ecies::PublicKey::<G>::from_private_key(&ecies_sk);
        let curr_node = nodes
            .iter()
            .find(|n| n.pk == ecies_pk)
            .ok_or(FastCryptoError::InvalidInput)?;
        // Generate a secret polynomial.
        if threshold >= nodes.len() as u32 {
            return Err(FastCryptoError::InvalidInput);
        }
        let vss_sk = PrivatePoly::<G>::rand(threshold - 1, rng);
        // Precompute the dual code coefficients.
        let ids_as_scalars = (1..=max_id)
            .into_iter()
            .map(|i| (i, G::ScalarType::from(i as u64)))
            .collect::<HashMap<_, _>>();
        let precomputed_dual_code_coefficients = (1..=max_id)
            .into_iter()
            .map(|i| {
                (1..=max_id)
                    .into_iter()
                    .filter(|j| i != *j)
                    .map(|j| ids_as_scalars[&i] - ids_as_scalars[&j])
                    .fold(G::ScalarType::generator(), |acc, x| acc * x)
                    .inverse()
                    .expect("non zero")
            })
            .collect();
        // Create the message to be broadcasted.
        let message = Self::create_message(
            rng,
            curr_node.id,
            &nodes,
            threshold,
            &random_oracle,
            &vss_sk,
        );

        Ok(Self {
            id: curr_node.id,
            nodes,
            threshold,
            random_oracle,
            ecies_sk,
            vss_sk,
            message,
            precomputed_dual_code_coefficients,
        })
    }

    pub fn threshold(&self) -> u32 {
        self.threshold
    }

    pub fn n(&self) -> u32 {
        self.nodes.len() as u32
    }

    pub fn msg(&self) -> &Message<G> {
        &self.message
    }

    fn create_message<R: AllowedRng>(
        rng: &mut R,
        id: ShareIndex,
        nodes: &Nodes<G>,
        threshold: u32,
        random_oracle: &RandomOracle,
        vss_sk: &PrivatePoly<G>,
    ) -> Message<G> {
        // TODO: Can this be done faster?
        let partial_pks = nodes
            .iter()
            .map(|n| G::generator() * vss_sk.eval(n.id).value)
            .collect();
        let mut rs = Vec::new();
        let pairs = nodes
            .iter()
            .map(|n| {
                let (r0, r1) = (G::ScalarType::rand(rng), G::ScalarType::rand(rng));
                let (msg0, msg1) = (
                    bcs::to_bytes(&r0).expect("serialization should work"),
                    bcs::to_bytes(&r1).expect("serialization should work"),
                );
                let (r0_g, r1_g) = (G::generator() * r0, G::generator() * r1);
                let (r0_x_g, r1_x_g) = (*n.pk.as_element() * r0, *n.pk.as_element() * r1);
                let (enc0, enc1) = (
                    n.pk.deterministic_encrypt(&msg0, &r0_g, &r0_x_g),
                    n.pk.deterministic_encrypt(&msg1, &r1_g, &r1_x_g),
                );
                // Save also the points instead of recomputing them later.
                rs.push(((r0, r0_x_g), (r1, r1_x_g)));
                PairOfEncryptions { enc0, enc1 }
            })
            .collect();
        let msg_before_fiat_shamir = Message {
            sender: id,
            pairs,
            partial_pks,
            processed_pairs: Vec::new(), // pre fiat-shamir
        };
        // Compute the cut-and-choose challenge bits.
        let ro = random_oracle.extend(format!("-{}-cut-and-choose", id).as_str());
        let seed = ro.evaluate(&msg_before_fiat_shamir);
        let challenge = Self::challenge(seed.as_slice(), nodes.len() as u32);

        // Reveal the scalars corresponding to the challenge bits.
        let processed_pairs = izip!(nodes.iter(), challenge.iter(), rs.iter())
            .map(
                |(node, (to_verify0, to_verify1), ((r0, r0_x_g), (r1, r1_x_g)))| {
                    let share = vss_sk.eval(node.id).value;
                    let enc0 = if *to_verify0 {
                        EncryptionInfo::ForVerification {
                            k: *r0,
                            k_x_g: *r0_x_g,
                        }
                    } else {
                        EncryptionInfo::ForEvaluation { diff: share - r0 }
                    };
                    let enc1 = if *to_verify1 {
                        EncryptionInfo::ForVerification {
                            k: *r1,
                            k_x_g: *r1_x_g,
                        }
                    } else {
                        EncryptionInfo::ForEvaluation { diff: share - r1 }
                    };
                    ProcessedPair { enc0, enc1 }
                },
            )
            .collect();

        let msg_after = Message {
            processed_pairs,
            ..msg_before_fiat_shamir
        };
        msg_after
    }

    /// 4. Verify messages (and store the valid ones elsewhere).
    pub fn verify_message<R: AllowedRng>(
        &self,
        msg: &Message<G>,
        rng: &mut R,
    ) -> FastCryptoResult<()> {
        let n = self.n();
        // Check the degree of the sender's polynomial..
        self.verify_deg_t_poly(n - self.threshold - 1, &msg.partial_pks[..], rng)?;

        // Check the cut-and-choose encryptions.
        let msg_before_fiat_shamir = Message {
            processed_pairs: Vec::new(),
            ..msg.clone()
        };
        let ro = self
            .random_oracle
            .extend(format!("-{}-cut-and-choose", msg.sender).as_str());
        let seed = ro.evaluate(&msg_before_fiat_shamir);
        let challenge = Self::challenge(seed.as_slice(), n);

        let mut pairs_to_check = Vec::new();
        let mut tuples_to_check = Vec::new();
        let all_ok = izip!(
            self.nodes.iter(),
            msg.pairs.iter(),
            challenge.iter(),
            msg.processed_pairs.iter(),
            msg.partial_pks.iter()
        )
        .all(|(node, pair, chal_bits, proc_pair, partial_pk)| {
            for (to_verify, enc, oenc) in vec![
                (&chal_bits.0, &pair.enc0, &proc_pair.enc0),
                (&chal_bits.1, &pair.enc1, &proc_pair.enc1),
            ] {
                // Some of the checks are verified as a batch below, using MSM.
                match (to_verify, oenc) {
                    (true, EncryptionInfo::ForVerification { k, k_x_g }) => {
                        let msg = bcs::to_bytes(&k).expect("serialization should work");
                        let k_g = enc.ephemeral_key();
                        if node.pk.deterministic_encrypt(&msg, &k_g, &k_x_g) != *enc {
                            return false;
                        }
                        pairs_to_check.push((*k, *k_g));
                        tuples_to_check.push((*k, *node.pk.as_element(), *k_x_g))
                    }
                    (false, EncryptionInfo::ForEvaluation { diff }) => {
                        pairs_to_check.push((*diff, *partial_pk - enc.ephemeral_key()))
                    }
                    _ => {
                        return false;
                    }
                }
            }
            return true;
        });

        if all_ok {
            // if true {
            Self::verify_pairs(rng, &pairs_to_check[..])?;
            Self::verify_triplets(rng, &tuples_to_check[..])?;
            Ok(())
        } else {
            Err(FastCryptoError::InvalidProof)
        }
    }

    fn get_random_scalars<R: AllowedRng>(
        n: u32,
        rng: &mut R,
    ) -> Vec<<G as GroupElement>::ScalarType> {
        // TODO: can use 40 bits instead of 64 (& 0x000F_FFFF_FFFF_FFFF below)
        (0..n)
            .into_iter()
            .map(|_| G::ScalarType::from(rng.next_u64()))
            .collect::<Vec<_>>()
    }

    // Check that a given pair (k, H) is indeed H = k*G using a random combination of the pairs and
    // multi scalar multiplication.
    pub fn verify_pairs<R: AllowedRng>(
        rng: &mut R,
        pairs: &[(G::ScalarType, G)],
    ) -> FastCryptoResult<()> {
        if pairs.is_empty() {
            return Ok(());
        }

        let random_coeffs = Self::get_random_scalars(pairs.len() as u32, rng);
        let lhs = G::generator()
            * random_coeffs
                .iter()
                .zip(pairs.iter())
                .fold(G::ScalarType::zero(), |acc, (r, (k, _))| acc + *r * *k);
        let rhs = G::multi_scalar_mul(
            &random_coeffs[..],
            &pairs.iter().map(|(_, g)| g.clone()).collect::<Vec<_>>()[..],
        )
        .expect("valid sizes");
        if lhs == rhs {
            Ok(())
        } else {
            Err(FastCryptoError::InvalidProof)
        }
    }

    // Check that a given tripled (k, G, H) is indeed H = k*G using a random combination of the
    // triplets and multi scalar multiplication.
    fn verify_triplets<R: AllowedRng>(
        rng: &mut R,
        triplets: &[(G::ScalarType, G, G)],
    ) -> FastCryptoResult<()> {
        if triplets.is_empty() {
            return Ok(());
        }

        let random_coeffs = Self::get_random_scalars(triplets.len() as u32, rng);
        let lhs_coeffs = random_coeffs
            .iter()
            .zip(triplets.iter())
            .map(|(r, (k, _, _))| *r * *k)
            .collect::<Vec<_>>();
        let lhs = G::multi_scalar_mul(
            &lhs_coeffs[..],
            &triplets
                .iter()
                .map(|(_, b, _)| b.clone())
                .collect::<Vec<_>>()[..],
        )
        .expect("valid sizes");

        let rhs = G::multi_scalar_mul(
            &random_coeffs[..],
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

    // Returns deterministic n pairs of challenge bits 00/01/11.
    fn challenge(seed: &[u8], n: u32) -> Vec<(bool, bool)> {
        let hmac_key = HmacKey::from_bytes(seed).expect("HMAC key should be valid");
        let mut res = Vec::new();
        let mut i: u32 = 0;
        let mut random_bits = Vec::new();
        while res.len() < n as usize {
            if random_bits.is_empty() {
                let random_bytes = hmac_sha3_256(&hmac_key, i.to_le_bytes().as_slice()).to_vec();
                random_bits = random_bytes
                    .iter()
                    .flat_map(|&byte| (0..8).map(move |i| (byte >> i) & 1 == 1))
                    .collect();
                i += 1;
            }
            // random_bits.len() is always even.
            let b0 = random_bits.pop().expect("non empty");
            let b1 = random_bits.pop().expect("non empty");
            // skip 11
            if !b0 | !b1 {
                res.push((b0, b1));
            }
        }
        res
    }

    // Verify that partial public keys form a polynomial of degree threshold-1 using the
    // protocol of https://eprint.iacr.org/2017/216.pdf.
    fn verify_deg_t_poly<R: AllowedRng>(
        &self,
        deg_f: u32,
        values: &[G],
        rng: &mut R,
    ) -> FastCryptoResult<()> {
        let poly_f = PrivatePoly::<G>::rand(deg_f, rng);
        let coefficients = self
            .precomputed_dual_code_coefficients
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
}
