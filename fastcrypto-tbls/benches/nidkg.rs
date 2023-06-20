// Copyright (c) 2022, Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use criterion::{criterion_group, criterion_main, BenchmarkGroup, Criterion};
use fastcrypto::groups::bls12381;
use fastcrypto_tbls::ecies;
use fastcrypto_tbls::nidkg::{Node, Party};
use fastcrypto_tbls::random_oracle::RandomOracle;
use fastcrypto_tbls::types::ShareIndex;
use rand::thread_rng;

type G = bls12381::G1Element;

fn gen_ecies_keys(n: u16) -> Vec<(u16, ecies::PrivateKey<G>, ecies::PublicKey<G>)> {
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

mod nidkg_benches {
    use super::*;

    fn nidkg(c: &mut Criterion) {
        const SIZES: [u16; 1] = [512];

        {
            let mut create: BenchmarkGroup<_> = c.benchmark_group("NI-DKG create");
            for n in SIZES {
                let t = (n / 2) as u32;
                let keys = gen_ecies_keys(n);
                let d0 = setup_party(0, t, &keys);
                let d1 = setup_party(1, t, &keys);

                create.bench_function(format!("n={}, t={}", n, t).as_str(), |b| {
                    b.iter(|| d0.create_message(&mut thread_rng()))
                });
            }
        }

        {
            let mut verify: BenchmarkGroup<_> = c.benchmark_group("NI-DKG message verification");
            for n in SIZES {
                let t = (n / 2) as u32;
                let keys = gen_ecies_keys(n);
                let d0 = setup_party(0, t, &keys);
                let d1 = setup_party(1, t, &keys);
                let m = d0.create_message(&mut thread_rng());

                verify.bench_function(format!("n={}, t={}", n, t).as_str(), |b| {
                    b.iter(|| d1.verify_message(&m, &mut thread_rng()))
                });
            }
        }

        {
            let mut verify: BenchmarkGroup<_> =
                c.benchmark_group("NI-DKG message processing for one share");
            for n in SIZES {
                let t = (n / 2) as u32;
                let keys = gen_ecies_keys(n);
                let d0 = setup_party(0, t, &keys);
                let d1 = setup_party(1, t, &keys);
                let m = d0.create_message(&mut thread_rng());

                verify.bench_function(format!("n={}, t={}", n, t).as_str(), |b| {
                    b.iter(|| d1.process_message(&m, &mut thread_rng()))
                });
            }
        }
    }

    criterion_group! {
        name = nidkg_benches;
        config = Criterion::default();
        targets = nidkg,
    }
}

criterion_main!(nidkg_benches::nidkg_benches);
