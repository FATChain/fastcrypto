// Copyright (c) 2022, Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0
//

use crate::dl_verification::{verify_deg_t_poly, verify_pairs, verify_triplets};
use crate::ecies;
use crate::ecies::Encryption;
use crate::polynomial::{Eval, Poly, PrivatePoly, PublicPoly};
use crate::random_oracle::RandomOracle;
use crate::types::ShareIndex;
use fastcrypto::error::{FastCryptoError, FastCryptoResult};
use fastcrypto::groups::{GroupElement, HashToGroupElement, MultiScalarMul, Scalar};
use fastcrypto::hmac::{hmac_sha3_256, HmacKey};
use fastcrypto::traits::{AllowedRng, ToFromBytes};
use itertools::izip;
use serde::{de::DeserializeOwned, Deserialize, Serialize};
use std::collections::HashMap;
use std::iter::Map;
use std::num::NonZeroU32;
use std::ops::RangeInclusive;

// TODOs:
//  process_message(...) -> (shares, fraud_claims (sender, receiver, claim)) - called after verify_message() in parallel; if there is a fraud, send it
//  process_fraud_claim(...) -> Ok(sender, shares_to_reveal) - called per claim (but not twice per sender)
//  process_revealed_shares(after t) -> update shares
//
// sign, etc
//
// work in G1

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Node<G: GroupElement> {
    pub id: u16,
    pub pk: ecies::PublicKey<G>,
    pub weight: u16,
}

/// Assumptions: All parties have the same set of Nodes. Their ids are 0..n-1.
pub type Nodes<G> = Vec<Node<G>>;

/// Party in the DKG protocol.
#[derive(Clone, PartialEq, Eq)]
pub struct Party<G: GroupElement>
where
    G::ScalarType: Serialize + DeserializeOwned,
{
    id: u16,
    nodes: Nodes<G>,
    t: u32,
    n: u32,
    random_oracle: RandomOracle,
    ecies_sk: ecies::PrivateKey<G>,
    vss_sk: PrivatePoly<G>,
    // Precomputed values to be used when verifying messages.
    precomputed_dual_code_coefficients: Vec<G::ScalarType>,
}

const NUM_OF_ENCRYPTIONS_PER_SHARE: usize = 2;

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct Encryptions<G: GroupElement> {
    pub values: [ecies::Encryption<G>; NUM_OF_ENCRYPTIONS_PER_SHARE],
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
enum EncryptionInfo<G: GroupElement> {
    // Let the encryption be (k*G, AES_{hkdf(k*xG)}(k)).
    ForVerification { k: G::ScalarType, k_x_g: G }, // k_x_g is added to reduce verification time.
    ForEvaluation { diff: G::ScalarType },          // share - k
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
struct ProcessedEncryptions<G: GroupElement>
where
    G::ScalarType: Serialize + DeserializeOwned,
{
    pub infos: [EncryptionInfo<G>; NUM_OF_ENCRYPTIONS_PER_SHARE],
}

#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
pub struct Message<G: GroupElement>
where
    G::ScalarType: Serialize + DeserializeOwned,
{
    sender: u16,
    // TODO: need a proof of possession/knowledge?
    partial_pks: Vec<G>, // One per share.
    /// The encrypted shares created by the sender.
    encrypted_random_shares: Vec<Encryptions<G>>, // One per share.
    processed_encryptions: Vec<ProcessedEncryptions<G>>, // One per share.
}

// struct PartialShares<G: GroupElement> {
//     // (sender, receiver) -> share
//     shares: HashMap<(ShareIndex, ShareIndex), G::ScalarType>,
// }

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
        t: u32, // The number of shares that are needed to reconstruct the full signature.
        random_oracle: RandomOracle,
        rng: &mut R,
    ) -> Result<Self, FastCryptoError> {
        // Check all ids are consecutive and start from 0.
        let mut nodes = nodes;
        nodes.sort_by_key(|n| n.id);
        if (0..nodes.len()).any(|i| (nodes[i].id as usize) != i) {
            return Err(FastCryptoError::InvalidInput);
        }
        // Check if my public key is in one of the nodes.
        let ecies_pk = ecies::PublicKey::<G>::from_private_key(&ecies_sk);
        let curr_node = nodes
            .iter()
            .find(|n| n.pk == ecies_pk)
            .ok_or(FastCryptoError::InvalidInput)?;
        // Get the total weight of the nodes.
        let n = nodes.iter().map(|n| n.weight as u32).sum::<u32>();
        // Generate a secret polynomial.
        if t >= n {
            return Err(FastCryptoError::InvalidInput);
        }
        let vss_sk = PrivatePoly::<G>::rand(t - 1, rng);
        // Precompute the dual code coefficients.
        let ids_as_scalars = (1..=n)
            .into_iter()
            .map(|i| (i, G::ScalarType::from(i as u64)))
            .collect::<HashMap<_, _>>();
        let precomputed_dual_code_coefficients = (1..=n)
            .into_iter()
            .map(|i| {
                (1..=n)
                    .into_iter()
                    .filter(|j| i != *j)
                    .map(|j| ids_as_scalars[&i] - ids_as_scalars[&j])
                    .fold(G::ScalarType::generator(), |acc, x| acc * x)
                    .inverse()
                    .expect("non zero")
            })
            .collect();

        Ok(Self {
            id: curr_node.id,
            nodes,
            t,
            n,
            random_oracle,
            ecies_sk,
            vss_sk,
            precomputed_dual_code_coefficients,
        })
    }

    fn share_ids_iter(&self) -> Map<RangeInclusive<u32>, fn(u32) -> NonZeroU32> {
        (1..=self.n)
            .into_iter()
            .map(|i| ShareIndex::new(i).expect("nonzero"))
    }

    fn share_id_to_node(&self, share_id: ShareIndex) -> &Node<G> {
        // TODO: Cache this
        let mut curr_share_id = 1;
        for n in &self.nodes {
            if curr_share_id <= share_id.get() && share_id.get() < curr_share_id + (n.weight as u32)
            {
                return n;
            }
            curr_share_id += n.weight as u32;
        }
        panic!("share id not found");
    }

    pub fn create_message<R: AllowedRng>(&self, rng: &mut R) -> Message<G> {
        // TODO: Can this be done faster?
        let partial_pks = self
            .share_ids_iter()
            .map(|i| G::generator() * self.vss_sk.eval(i).value)
            .collect();
        let mut interim_values: Vec<[(G::ScalarType, G); NUM_OF_ENCRYPTIONS_PER_SHARE]> =
            Vec::new();
        let pairs = self
            .share_ids_iter()
            .map(|i| {
                let mut values = Vec::new();
                let node = self.share_id_to_node(i);
                let encryptions = (0..NUM_OF_ENCRYPTIONS_PER_SHARE)
                    .into_iter()
                    .map(|i| {
                        let r = G::ScalarType::rand(rng);
                        let msg = bcs::to_bytes(&r).expect("serialization should work");
                        let r_g = G::generator() * r;
                        let r_x_g = *node.pk.as_element() * r;
                        // Save also the points instead of recomputing them later.
                        values.push((r, r_x_g));
                        node.pk.deterministic_encrypt(&msg, &r_g, &r_x_g)
                    })
                    .collect::<Vec<_>>()
                    .try_into()
                    .expect("should work");
                interim_values.push(values.try_into().expect("should work"));
                Encryptions {
                    values: encryptions,
                }
            })
            .collect();
        let msg_before_fiat_shamir = Message {
            sender: self.id,
            encrypted_random_shares: pairs,
            partial_pks,
            processed_encryptions: Vec::new(), // pre fiat-shamir
        };
        // Compute the cut-and-choose challenge bits.
        let ro = self
            .random_oracle
            .extend(format!("-{}-cut-and-choose", self.id).as_str());
        let seed = ro.evaluate(&msg_before_fiat_shamir);
        let challenge = Self::challenge(seed.as_slice(), self.n);

        // Reveal the scalars corresponding to the challenge bits.
        let processed_pairs = izip!(
            self.share_ids_iter(),
            challenge.iter(),
            interim_values.iter()
        )
        .map(|(share_id, chal, &values)| {
            let share = self.vss_sk.eval(share_id).value;
            let infos = (0..NUM_OF_ENCRYPTIONS_PER_SHARE)
                .into_iter()
                .map(|i| {
                    if chal[i] {
                        EncryptionInfo::ForVerification {
                            k: values[i].0.clone(),
                            k_x_g: values[i].1.clone(),
                        }
                    } else {
                        EncryptionInfo::ForEvaluation {
                            diff: share - values[i].0,
                        }
                    }
                })
                .collect::<Vec<_>>()
                .try_into()
                .expect("should work");
            ProcessedEncryptions { infos }
        })
        .collect();

        let msg_after = Message {
            processed_encryptions: processed_pairs,
            ..msg_before_fiat_shamir
        };
        msg_after
    }

    /// 5. Verify messages (and store the valid ones elsewhere).
    pub fn verify_message<R: AllowedRng>(
        &self,
        msg: &Message<G>,
        rng: &mut R,
    ) -> FastCryptoResult<()> {
        // Check the degree of the sender's polynomial..
        verify_deg_t_poly(
            self.n - self.t - 1,
            &msg.partial_pks,
            &self.precomputed_dual_code_coefficients,
            rng,
        )?;

        // Check the cut-and-choose encryptions.
        let msg_before_fiat_shamir = Message {
            processed_encryptions: Vec::new(),
            ..msg.clone()
        };
        let ro = self
            .random_oracle
            .extend(format!("-{}-cut-and-choose", msg.sender).as_str());
        let seed = ro.evaluate(&msg_before_fiat_shamir);
        let challenge = Self::challenge(seed.as_slice(), self.n);

        let mut pairs_to_check = Vec::new();
        let mut tuples_to_check = Vec::new();
        let all_ok = izip!(
            self.share_ids_iter(),
            msg.encrypted_random_shares.iter(),
            challenge.iter(),
            msg.processed_encryptions.iter(),
            msg.partial_pks.iter()
        )
        .all(
            |(share_id, encryptions, chal, proc_encryptions, partial_pk)| {
                let node = self.share_id_to_node(share_id);
                for i in (0..NUM_OF_ENCRYPTIONS_PER_SHARE) {
                    let enc = &encryptions.values[i];
                    // Some of the checks are verified as a batch below, using MSM.
                    match (chal[i], &proc_encryptions.infos[i]) {
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
            },
        );

        if all_ok {
            // if true {
            verify_pairs(&pairs_to_check, rng)?;
            verify_triplets(&tuples_to_check, rng)?;
            Ok(())
        } else {
            Err(FastCryptoError::InvalidProof)
        }
    }

    /// 6. Given enough verified messages, compute the final public keys.
    // TODO: Should fail if not enough messages?
    pub fn compute_final_pks(&self, messages: &[Message<G>]) -> (G, Vec<G>) {
        let mut res = Vec::<G>::with_capacity(messages.len());
        for msg in messages {
            for (i, pk) in msg.partial_pks.iter().enumerate() {
                res[i] = res[i] + pk;
            }
        }
        // Compute the BLS pk
        let evals = res
            .iter()
            .take(self.t as usize)
            .enumerate()
            .map(|(i, pk)| Eval {
                index: NonZeroU32::new((i + 1) as u32).expect("non zero"),
                value: *pk,
            })
            .collect::<Vec<Eval<G>>>();
        let pk = Poly::<G>::recover_c0(self.t, &evals).expect("enough shares");

        (pk, res)
    }
    //
    // pub fn process_message(&self, msg: &Message<G>) -> (PartialShares<G>, FraudProof<G>) {
    //     let partial_pk = msg.partial_pks[self.id - 1];
    //     let encryptions = msg.encrypted_random_shares[self.id - 1];
    //     let processed_encs = msg.processed_encryptions[self.id - 1];
    //     let mut res = G::ScalarType::zero();
    //     for i in (0..NUM_OF_ENCRYPTIONS_PER_SHARE) {
    //         if let EncryptionInfo::ForEvaluation { diff } = processed_encs.infos[i] {
    //             let msg = self.ecies_sk.decrypt(&encryptions.values[i]);
    //             let k: G::ScalarType = bcs::from_bytes(&msg).expect("deserialization should work");
    //             if G::generator() * (k + diff) == partial_pk {
    //                 res = res + k;
    //             } else {
    //                 //fruad proof
    //             }
    //         }
    //     }
    //
    //     (res, proofs)
    // }

    // Returns deterministic n pairs of challenge bits 00/01/11.
    fn challenge(seed: &[u8], n: u32) -> Vec<[bool; NUM_OF_ENCRYPTIONS_PER_SHARE]> {
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
                res.push([b0, b1]);
            }
        }
        res
    }
}
