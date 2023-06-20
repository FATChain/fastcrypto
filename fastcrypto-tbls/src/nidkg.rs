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
use std::num::NonZeroU32;

// TODOs:
//  process_message(...) -> (shares, fraud_claims (sender, receiver, claim)) - called after verify_message() in parallel; if there is a fraud, send it
//  process_fraud_claim(...) -> Ok(sender, shares_to_reveal) - called per claim (but not twice per sender)
//  process_revealed_shares(after t) -> update shares
//
// sign, etc
//
// weights
// work in G1

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
    sender: ShareIndex,
    // TODO: need a proof of possession/knowledge?
    partial_pks: Vec<G>, // One per share.
    /// The encrypted shares created by the sender.
    encrypted_random_shares: Vec<Encryptions<G>>, // One per share.
    processed_encryptions: Vec<ProcessedEncryptions<G>>, // One per share.
}

struct PartialShares<G: GroupElement> {
    // (sender, receiver) -> share
    shares: HashMap<(ShareIndex, ShareIndex), G::ScalarType>,
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

    /// 4. Send the message to all parties.
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
        let mut interim_values: Vec<[(G::ScalarType, G); NUM_OF_ENCRYPTIONS_PER_SHARE]> =
            Vec::new();
        let pairs = nodes
            .iter()
            .map(|n| {
                let mut values = Vec::new();
                let encryptions = (0..NUM_OF_ENCRYPTIONS_PER_SHARE)
                    .into_iter()
                    .map(|i| {
                        let r = G::ScalarType::rand(rng);
                        let msg = bcs::to_bytes(&r).expect("serialization should work");
                        let r_g = G::generator() * r;
                        let r_x_g = *n.pk.as_element() * r;
                        // Save also the points instead of recomputing them later.
                        values.push((r, r_x_g));
                        n.pk.deterministic_encrypt(&msg, &r_g, &r_x_g)
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
            sender: id,
            encrypted_random_shares: pairs,
            partial_pks,
            processed_encryptions: Vec::new(), // pre fiat-shamir
        };
        // Compute the cut-and-choose challenge bits.
        let ro = random_oracle.extend(format!("-{}-cut-and-choose", id).as_str());
        let seed = ro.evaluate(&msg_before_fiat_shamir);
        let challenge = Self::challenge(seed.as_slice(), nodes.len() as u32);

        // Reveal the scalars corresponding to the challenge bits.
        let processed_pairs = izip!(nodes.iter(), challenge.iter(), interim_values.iter())
            .map(|(node, chal, &values)| {
                let share = vss_sk.eval(node.id).value;
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
        let n = self.n();
        // Check the degree of the sender's polynomial..
        verify_deg_t_poly(
            n - self.threshold - 1,
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
        let challenge = Self::challenge(seed.as_slice(), n);

        let mut pairs_to_check = Vec::new();
        let mut tuples_to_check = Vec::new();
        let all_ok = izip!(
            self.nodes.iter(),
            msg.encrypted_random_shares.iter(),
            challenge.iter(),
            msg.processed_encryptions.iter(),
            msg.partial_pks.iter()
        )
        .all(|(node, encryptions, chal, proc_encryptions, partial_pk)| {
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
        });

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
    pub fn compute_final_pks(&self, messages: &[Message<G>], t: u32) -> (G, Vec<G>) {
        let mut res = Vec::<G>::with_capacity(messages.len());
        for msg in messages {
            for (i, pk) in msg.partial_pks.iter().enumerate() {
                res[i] = res[i] + pk;
            }
        }

        let evals = res
            .iter()
            .take(t as usize)
            .enumerate()
            .map(|(i, pk)| Eval {
                index: NonZeroU32::new((i + 1) as u32).expect("non zero"),
                value: *pk,
            })
            .collect::<Vec<Eval<G>>>();
        let pk = Poly::<G>::recover_c0(t, &evals).expect("enough shares");

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
