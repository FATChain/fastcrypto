// Copyright (c) 2022, Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use crate::ecies;
use crate::nidkg::{Node, Party};
use crate::random_oracle::RandomOracle;
use crate::tbls::ThresholdBls;
use crate::types::{ShareIndex, ThresholdBls12381MinSig};
use fastcrypto::groups::bls12381::G2Element;
use fastcrypto::groups::ristretto255::RistrettoPoint;
use fastcrypto::groups::GroupElement;
use rand::thread_rng;

const MSG: [u8; 4] = [1, 2, 3, 4];

type G = G2Element;

pub fn gen_ecies_keys(n: u16) -> Vec<(u16, ecies::PrivateKey<G>, ecies::PublicKey<G>)> {
    (0..n)
        .into_iter()
        .map(|id| {
            let sk = ecies::PrivateKey::<G>::new(&mut thread_rng());
            let pk = ecies::PublicKey::<G>::from_private_key(&sk);
            (id, sk, pk)
        })
        .collect()
}

pub fn setup_party(
    id: usize,
    threshold: u32,
    keys: &[(u16, ecies::PrivateKey<G>, ecies::PublicKey<G>)],
) -> Party<G> {
    let nodes = keys
        .iter()
        .map(|(id, _sk, pk)| Node::<G> {
            id: *id,
            pk: pk.clone(),
            weight: 1,
        })
        .collect();
    Party::<G>::new(
        keys.get(id).unwrap().1.clone(),
        nodes,
        threshold,
        RandomOracle::new("dkg"),
        &mut thread_rng(),
    )
    .unwrap()
}

#[test]
fn test_dkg_e2e_4_parties_threshold_2() {
    let keys = gen_ecies_keys(4);

    let d0 = setup_party(0, 2, &keys);
    let mut d1 = setup_party(1, 2, &keys);
    let d2 = setup_party(2, 2, &keys);
    // The third party is ignored (emulating a byzantine party).
    let _d3 = setup_party(3, 2, &keys);

    let m0 = d0.create_message(&mut thread_rng());
    let m1 = d1.create_message(&mut thread_rng());
    let mut m2 = d2.create_message(&mut thread_rng());

    assert!(d0.verify_message(&m1, &mut thread_rng()).is_ok());
    assert!(d2.verify_message(&m1, &mut thread_rng()).is_ok());
    assert!(d1.verify_message(&m2, &mut thread_rng()).is_ok());
    // TODO: test failure of verify_message

    //
    // let (shares1, r2m1) = d1
    //     .create_second_message(&r1_all[..], &mut thread_rng())
    //     .unwrap();
    // let (shares2, r2m2) = d2
    //     .create_second_message(&r1_all[..], &mut thread_rng())
    //     .unwrap();
    // // Note that d4's first round message is not included but it should still be able to receive
    // // shares and post complaints.
    // let (shares4, r2m4) = d4
    //     .create_second_message(&r1_all[..], &mut thread_rng())
    //     .unwrap();
    //
    // // There should be some complaints on the first messages of d2.
    // assert!(
    //     !r2m1.complaints.is_empty() || !r2m2.complaints.is_empty() || !r2m4.complaints.is_empty()
    // );
    // // But also no complaints from one of the parties.
    // assert!(r2m1.complaints.is_empty() || r2m2.complaints.is_empty() || r2m4.complaints.is_empty());
    //
    // let r2_all = vec![r2m1, r2m2, r2m4];
    // let shares1 = d1.process_responses(&r1_all, &r2_all, shares1, 3).unwrap();
    // let shares2 = d2.process_responses(&r1_all, &r2_all, shares2, 3).unwrap();
    // let shares4 = d4.process_responses(&r1_all, &r2_all, shares4, 3).unwrap();
    //
    // // Only the first message of d1 passed all tests -> only one vss is used.
    // assert_eq!(shares1.len(), 1);
    // assert_eq!(shares2.len(), 1);
    // assert_eq!(shares4.len(), 1);
    //
    // let o1 = d1.aggregate(&r1_all, shares1);
    // let _o2 = d2.aggregate(&r1_all, shares2);
    // let o4 = d4.aggregate(&r1_all, shares4);
    //
    // // Use the shares from 01 and o4 to sign a message.
    // type S = ThresholdBls12381MinSig;
    // let sig1 = S::partial_sign(&o1.share, &MSG);
    // let sig4 = S::partial_sign(&o4.share, &MSG);
    //
    // S::partial_verify(&o1.vss_pk, &MSG, &sig1).unwrap();
    // S::partial_verify(&o4.vss_pk, &MSG, &sig4).unwrap();
    //
    // let sigs = vec![sig1, sig4];
    // let sig = S::aggregate(d1.threshold(), &sigs).unwrap();
    // S::verify(o1.vss_pk.c0(), &MSG, &sig).unwrap();
}
