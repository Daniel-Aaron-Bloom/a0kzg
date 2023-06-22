use std::{time::Duration};

use bls12_381::{G2Projective, G2Affine, G1ProjectiveA};
use ff::Field;
use a0kzg::{TrustedTau, Scalar, TrustedVerifier, TrustedProver, Prover, Verifier, UntrustedVerifier, UntrustedProver, kzg::{PowTauG1Projective, PowTauG2Projective, PowTauG1Affine, PowTauG2Affine, PowTauG1AffineBatch}, Poly};
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use once_cell::sync::Lazy;
use rand::Rng;

type G1Projective = bls12_381::G1Projective<true>;
type G1Affine = bls12_381::G1Affine<true>;

mod perf {
    use pprof::ProfilerGuard;
    use criterion::{profiler::Profiler};

    use std::{path::Path, fs::File, ffi::c_int};

    pub struct FlamegraphProfiler<'a> {
        frequency: c_int,
        active_profiler: Option<ProfilerGuard<'a>>,
    }

    impl<'a> FlamegraphProfiler<'a> {
        #[allow(dead_code)]
        pub fn new(frequency: c_int) -> Self {
            FlamegraphProfiler {
                frequency,
                active_profiler: None,
            }
        }
    }

    impl<'a> Profiler for FlamegraphProfiler<'a> {
        fn start_profiling(&mut self, _benchmark_id: &str, _benchmark_dir: &Path) {
            self.active_profiler = Some(ProfilerGuard::new(self.frequency).unwrap());
        }

        fn stop_profiling(&mut self, _benchmark_id: &str, benchmark_dir: &Path) {
            std::fs::create_dir_all(benchmark_dir).unwrap();
            let flamegraph_path = benchmark_dir.join("flamegraph.svg");
            let flamegraph_file = File::create(&flamegraph_path)
                .expect("File system error while creating flamegraph.svg");
            if let Some(profiler) = self.active_profiler.take() {
                profiler
                    .report()
                    .build()
                    .unwrap()
                    .flamegraph(flamegraph_file)
                    .expect("Error writing flamegraph");
            }
        }
    }

}

static TAU: Lazy<TrustedTau> = Lazy::new(|| TrustedTau(Scalar::random(rand::thread_rng())));
static TRUSTED_PROVER: Lazy<TrustedProver> = Lazy::new(|| TrustedProver::new(*TAU));
static TRUSTED_VERIFIER: Lazy<TrustedVerifier> = Lazy::new(|| TrustedVerifier::new(*TAU));

static SIZES: &[(usize, &[usize])] = &[
    (16, &[1, 2, 8]),
    (32, &[1, 2, 16]),
    (64, &[1, 2, 16, 32]),
    (128, &[1, 2, 16, 32, 64]),
    (256, &[1, 2, 16, 32, 64, 128]),
];

static POINTS: Lazy<Vec<(Scalar, Scalar)>> = Lazy::new(|| {
    (0..1025)
        .map(|_| (Scalar::random(rand::thread_rng()), Scalar::random(rand::thread_rng())))
        .collect::<Vec<_>>()
});


static G1_PROJECTIVE: Lazy<Vec<G1Projective>> = Lazy::new(|| TAU.g1_projective_iter().take(POINTS.len()-1).collect() );
static G2_PROJECTIVE: Lazy<Vec<G2Projective>> = Lazy::new(|| TAU.g2_projective_iter().take(POINTS.len()-1).collect() );
static G1_AFFINE: Lazy<Vec<G1Affine>> = Lazy::new(|| TAU.g1_affine_iter().take(POINTS.len()-1).collect() );
static G2_AFFINE: Lazy<Vec<G2Affine>> = Lazy::new(|| TAU.g2_affine_iter().take(POINTS.len()-1).collect() );
static G1_BATCH: Lazy<Vec<G1ProjectiveA>> = Lazy::new(|| TAU.g1_projective_a_iter().take(POINTS.len()-1).collect() );

fn zkg(c: &mut Criterion) {
    let projective = (
        PowTauG1Projective(|| G1_PROJECTIVE.iter()),
        PowTauG2Projective(|| G2_PROJECTIVE.iter()),
    );
    let affine = (
        PowTauG1Affine(|| G1_AFFINE.iter()),
        PowTauG2Affine(|| G2_AFFINE.iter()),
    );
    let batch = PowTauG1AffineBatch::new(G1_BATCH.iter());

    let prvr_a = UntrustedProver::new(affine.clone());
    let vrfr_a = UntrustedVerifier::new(affine.clone());
    let prvr_p = UntrustedProver::new(projective.clone());
    let vrfr_p = UntrustedVerifier::new(projective.clone());

    let mut group = c.benchmark_group("zkg");
    for &(set_size, proof_sizes) in SIZES.iter() {
        let id = BenchmarkId::from_parameter(format!("trusted commit {set_size}"));
        group.throughput(Throughput::Elements(set_size as u64));
        group.bench_with_input(id, &POINTS[0..set_size], |b, points| {
            b.iter(|| TRUSTED_PROVER.poly_commitment_from_set(points))
        });
        let id = BenchmarkId::from_parameter(format!("affine untrusted commit {set_size}"));
        group.throughput(Throughput::Elements(set_size as u64));
        group.bench_with_input(id, &POINTS[0..set_size], |b, points| {
            b.iter(|| prvr_a.poly_commitment_from_set(points))
        });
        let id = BenchmarkId::from_parameter(format!("projective untrusted commit {set_size}"));
        group.throughput(Throughput::Elements(set_size as u64));
        group.bench_with_input(id, &POINTS[0..set_size], |b, points| {
            b.iter(|| prvr_p.poly_commitment_from_set(points))
        });
        let id = BenchmarkId::from_parameter(format!("batch untrusted commit {set_size}"));
        group.throughput(Throughput::Elements(set_size as u64));
        group.bench_with_input(id, &POINTS[0..set_size], |b, points| {
            b.iter(|| batch.poly_commitment_from_set(points))
        });

        let v = TRUSTED_PROVER.poly_commitment_from_set(&POINTS[0..set_size]);
        // assert_eq!(v, prvr_a.poly_commitment_from_set(&POINTS[0..set_size]));
        // assert_eq!(v, prvr_p.poly_commitment_from_set(&POINTS[0..set_size]));
        let (p, c) = v;
        let c = c.into();

        for &proof_size in proof_sizes {
            let id = BenchmarkId::from_parameter(format!("trusted prove {set_size}:{proof_size}"));
            group.throughput(Throughput::Elements(proof_size as u64));
            group.bench_with_input(id, &(&p, &POINTS[0..proof_size]), |b, &(poly, points)| {
                b.iter(|| TRUSTED_PROVER.prove(poly.clone(), points))
            });
            let id = BenchmarkId::from_parameter(format!("affine untrusted prove {set_size}:{proof_size}"));
            group.throughput(Throughput::Elements(proof_size as u64));
            group.bench_with_input(id, &(&p, &POINTS[0..proof_size]), |b, &(poly, points)| {
                b.iter(|| prvr_a.prove(poly.clone(), points))
            });
            let id = BenchmarkId::from_parameter(format!("projective untrusted prove {set_size}:{proof_size}"));
            group.throughput(Throughput::Elements(proof_size as u64));
            group.bench_with_input(id, &(&p, &POINTS[0..proof_size]), |b, &(poly, points)| {
                b.iter(|| prvr_p.prove(poly.clone(), points))
            });

            let i = Poly::lagrange(&POINTS[0..proof_size]);

            let id = BenchmarkId::from_parameter(format!("affine untrusted prove_with_poly {set_size}:{proof_size}"));
            group.throughput(Throughput::Elements(proof_size as u64));
            group.bench_with_input(id, &(&p, &i, &POINTS[0..proof_size]), |b, &(poly, i, points)| {
                b.iter(|| prvr_a.prove_with_poly(poly.clone(), i, points))
            });

            let pi = TRUSTED_PROVER.prove(p.clone(), &POINTS[0..proof_size]);
            // assert_eq!(prvr_a.prove(p.clone(), &POINTS[0..proof_size]), pi);
            // assert_eq!(prvr_p.prove(p.clone(), &POINTS[0..proof_size]), pi);
            let pi = pi.into();

            let id = BenchmarkId::from_parameter(format!("trusted verify {set_size}:{proof_size}"));
            group.throughput(Throughput::Elements(proof_size as u64));
            group.bench_with_input(id, &(&c, &POINTS[0..proof_size]), |b, &(commitment, points)| {
                b.iter(|| TRUSTED_VERIFIER.verify(commitment, points, &pi))
            });
            assert!(TRUSTED_VERIFIER.verify(&c, &POINTS[0..proof_size], &pi));

            let id = BenchmarkId::from_parameter(format!("affine untrusted verify {set_size}:{proof_size}"));
            group.throughput(Throughput::Elements(proof_size as u64));
            group.bench_with_input(id, &(&c, &POINTS[0..proof_size]), |b, &(commitment, points)| {
                b.iter(|| vrfr_a.verify(commitment, points, &pi))
            });
            let id = BenchmarkId::from_parameter(format!("projective untrusted verify {set_size}:{proof_size}"));
            group.throughput(Throughput::Elements(proof_size as u64));
            group.bench_with_input(id, &(&c, &POINTS[0..proof_size]), |b, &(commitment, points)| {
                b.iter(|| vrfr_p.verify(commitment, points, &pi))
            });
            assert!(vrfr_a.verify(&c, &POINTS[0..proof_size], &pi));
            assert!(vrfr_p.verify(&c, &POINTS[0..proof_size], &pi));
        }
    }
    group.finish();
}

fn micro(_c: &mut Criterion) {
    let mut _group = _c.benchmark_group("micro");
/*
    let g: G2Prepared = G2Prepared::from(G2Affine::generator());
    let p = (G1Affine::generator() * Scalar::random(rand::thread_rng())).into();

    let id = BenchmarkId::from_parameter(format!("pairing"));
    group.bench_with_input(id, &p, |b, p| {
        b.iter(|| pairing(p, &G2Affine::generator()))
    });

    let id = BenchmarkId::from_parameter(format!("multi_miller_loop"));
    group.bench_with_input(id, &p, |b, p| {
        b.iter(|| multi_miller_loop(&[(&p, &g)]).final_exponentiation())
    });
    let id = BenchmarkId::from_parameter(format!("z_poly_of"));
    group.bench_with_input(id, &POINTS[..128], |b, p| {
        b.iter(|| Poly::z_poly_of(p))
    });
    let id = BenchmarkId::from_parameter(format!("lagrange"));
    _group.bench_with_input(id, &POINTS[..128], |b, p| {
        b.iter(|| a0kzg::Poly::lagrange(p))
    });
    let id = BenchmarkId::from_parameter(format!("lagrange2"));
    _group.bench_with_input(id, &POINTS[..128], |b, p| {
        b.iter(|| a0kzg::Poly::lagrange2(p))
    });
*/

    let nm: ([u64; 10], [u64; 10]) = rand::thread_rng().gen();
    let id = BenchmarkId::from_parameter(format!("sbb"));
    _group.bench_with_input(id, &nm, |b, &(n, m)| {
        b.iter(|| {
            let (v0, borrow) = sbb(n[0], m[0], 0);
            let (v1, borrow) = sbb(n[1], m[1], borrow);
            let (v2, borrow) = sbb(n[2], m[2], borrow);
            let (v3, borrow) = sbb(n[3], m[3], borrow);
            let (v4, borrow) = sbb(n[4], m[4], borrow);
            let (v5, borrow) = sbb(n[5], m[5], borrow);
            let (v6, borrow) = sbb(n[6], m[6], borrow);
            let (v7, borrow) = sbb(n[7], m[7], borrow);
            let (v8, borrow) = sbb(n[8], m[8], borrow);
            let (v9, _borrow) = sbb(n[9], m[9], borrow);
            [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9]
        })
    });
    let id = BenchmarkId::from_parameter(format!("borrowing_sub"));
    _group.bench_with_input(id, &nm, |b, &(n, m)| {
        b.iter(|| {
            let (v0, borrow) = borrowing_sub(n[0], m[0], false);
            let (v1, borrow) = borrowing_sub(n[1], m[1], borrow);
            let (v2, borrow) = borrowing_sub(n[2], m[2], borrow);
            let (v3, borrow) = borrowing_sub(n[3], m[3], borrow);
            let (v4, borrow) = borrowing_sub(n[4], m[4], borrow);
            let (v5, borrow) = borrowing_sub(n[5], m[5], borrow);
            let (v6, borrow) = borrowing_sub(n[6], m[6], borrow);
            let (v7, borrow) = borrowing_sub(n[7], m[7], borrow);
            let (v8, borrow) = borrowing_sub(n[8], m[8], borrow);
            let (v9, _borrow) = borrowing_sub(n[9], m[9], borrow);
            [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9]
        })
    });
    

}

#[inline(always)]
pub const fn sbb(a: u64, b: u64, borrow: u64) -> (u64, u64) {
    let ret = (a as u128).wrapping_sub((b as u128) + ((borrow >> 63) as u128));
    (ret as u64, (ret >> 64) as u64)
}

#[inline(always)]
pub const fn borrowing_sub(a: u64, b: u64, borrow: bool) -> (u64, bool) {
    let (a, b) = a.overflowing_sub(b);
    let (c, d) = a.overflowing_sub(borrow as u64);
    (c, b != d)
}


criterion_group!{
    name=benches;
    config = Criterion::default().measurement_time(Duration::from_secs(15)).with_profiler(perf::FlamegraphProfiler::new(5000));
    targets = zkg, micro
}
criterion_main!(benches);
