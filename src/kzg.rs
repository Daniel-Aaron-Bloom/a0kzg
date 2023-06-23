//! this module contains an implementation of Kate-Zaverucha-Goldberg polynomial commitments

use std::{borrow::Borrow, iter::from_fn};

use super::poly::Poly;
 use bls12_381::{G2Affine, G2Projective, G2Prepared, pairing, G1AffineA, multi_miller_loop, G1ProjectiveA, G1Precompute, G1PrecomputeAffine, util::VarTime};
use itertools::Itertools;
use once_cell::sync::Lazy;


type G1Projective = bls12_381::G1Projective<true>;
type G1Affine = bls12_381::G1Affine<true>;

use crate::Scalar;

/// A KZG prover which can generate polynomial commitment and proofs
pub trait Prover {
    /// Generate a polynomial and its commitment from a `set` of points
    fn poly_commitment_from_set(&self, set: &[(Scalar, Scalar)]) -> (Poly, Commitment) {
        let poly = Poly::lagrange(set);
        let commitment = self.eval_g1(poly.iter());
        (poly, commitment)
    }

    /// Generates a proof that `points` exists in `set`
    #[allow(non_snake_case)]
    fn prove<'a, 'b: 'a>(&self, poly: Poly<'a>, points: &[(Scalar, Scalar)]) -> Proof {
        // compute a lagrange polynomial I that have all the points to proof that are in the set
        // compute the polynomial Z that has roots (y=0) in all x's of I,
        // so this is I=(x-x0)(x-x1)...(x-xn)
        let I = Poly::lagrange(points);
        Self::prove_with_poly(&self, poly, &I, points)
    }

    /// Generates a proof that `points` exists in `set` with a pre-calculated lagrange polynomial
    #[allow(non_snake_case)]
    fn prove_with_poly<'a, 'b: 'a>(&self, mut poly: Poly<'a>, I: &Poly<'b>, points: &[(Scalar, Scalar)]) -> Proof {
        //let Z = Poly::z_poly_of(points);

        // now compute that Q = ( P - I(x) ) / Z(x)
        // also check that the division does not have remainder
        poly -= I;
        // let (Q, remainder) = poly / Z;
        // assert!(remainder.is_zero());
        let Q = poly.div_by_z_poly_of(points);

        // the proof is evaluating the Q at tau in G1
        self.eval_g1(Q.iter())
    }

    /// Generates a proof given the Q polynomial
    #[doc(hidden)]
    fn eval_g1<'a, 'b: 'a>(&self, poly: impl Iterator<Item = &'a Scalar>) -> Proof;
}

#[derive(Clone, Copy)]
pub struct TrustedTau(pub Scalar);

impl TrustedTau {
    pub fn eval_g1<'a>(&self, mut poly: impl Iterator<Item = &'a Scalar>) -> G1Projective {
        match poly.next().map(|k| G1Affine::generator() * k) {
            None => G1Projective::identity(),
            Some(v) => {
                poly.fold((v, self.0), |(acc, pow_tau), k| {
                    (
                        acc + G1Affine::generator() * (pow_tau * k),
                        pow_tau * self.0,
                    )
                })
                .0
            }
        }
    }
    pub fn eval_g2<'a>(&self, mut poly: impl Iterator<Item = &'a Scalar>) -> G2Projective {
        match poly.next().map(|k| G2Affine::generator() * k.vartime()) {
            None => G2Projective::identity(),
            Some(v) => {
                poly.fold((v, self.0), |(acc, pow_tau), k| {
                    (
                        acc + G2Affine::generator() * (pow_tau * k).vartime(),
                        pow_tau * self.0,
                    )
                })
                .0
            }
        }
    }

    pub fn g1_projective_iter(self) -> impl Iterator<Item = G1Projective> {
        let tau = self.0;
        let mut v = tau;
        from_fn(move || {
            let ret = G1Affine::generator() * v;
            v *= tau;
            Some(ret)
        })
    }

    pub fn g1_affine_iter(self) -> impl Iterator<Item = G1Affine> {
        let tau = self.0;
        let mut v = tau;
        from_fn(move || {
            let ret = G1Affine::generator() * v;
            v *= tau;
            Some(ret.into())
        })
    }

    pub fn g1_projective_a_iter(self) -> impl Iterator<Item = G1ProjectiveA> {
        let tau = self.0;
        let mut v = tau;
        from_fn(move || {
            let ret = G1ProjectiveA::generator().mul(&v.vartime());
            v *= tau;
            Some(ret)
        })
    }

    pub fn g2_projective_iter(self) -> impl Iterator<Item = G2Projective> {
        let tau = self.0;
        let mut v = tau;
        from_fn(move || {
            let ret = G2Affine::generator() * v.vartime();
            v *= tau;
            Some(ret)
        })
    }
    pub fn g2_affine_iter(self) -> impl Iterator<Item = G2Affine> {
        let tau = self.0;
        let mut v = tau;
        from_fn(move || {
            let ret = G2Affine::generator() * v.vartime();
            v *= tau;
            Some(ret.into())
        })
    }
}

/// A trusted KZG prover that can forge arbitrary proofs. This should only be used in a trusted environment.
#[derive(Clone, Copy)]
pub struct TrustedProver {
    tau: TrustedTau,
}

impl TrustedProver {
    /// Setup the trusted prover from `tau`. Having `tau` allows forging of arbitrary proofs,
    /// so ensure this is only used in a trusted environment.
    pub const fn new(tau: TrustedTau) -> Self {
        Self { tau }
    }
}

impl Prover for TrustedProver {
    fn eval_g1<'a, 'b: 'a>(&self, poly: impl Iterator<Item = &'a Scalar>) -> Proof {
        self.tau.eval_g1(poly)
    }
}

pub trait PowTauG1 {
    fn eval_g1<'a>(&self, poly: impl Iterator<Item = &'a Scalar>) -> G1Projective;
}

impl<G1: PowTauG1, T> PowTauG1 for (G1, T) {
    fn eval_g1<'a>(&self, poly: impl Iterator<Item = &'a Scalar>) -> G1Projective {
        self.0.eval_g1(poly)
    }
}

#[derive(Clone)]
pub struct PowTauG1Affine<F>(pub F);

impl<I: Iterator, F: Fn() -> I> PowTauG1 for PowTauG1Affine<F>
where
    <I as Iterator>::Item: Borrow<G1Affine>,
{
    fn eval_g1<'a>(&self, mut poly: impl Iterator<Item = &'a Scalar>) -> G1Projective {
        match poly.next().map(|k| G1Affine::generator().mul(k)) {
            None => G1Projective::identity(),
            Some(v) => poly
                .zip(self.0())
                .fold(v, |acc, (k, tau)| acc + tau.borrow().mul(k)),
        }
    }
}

#[derive(Clone, Copy)]
pub struct PowTauG1Projective<F>(pub F);
impl<I: Iterator, F: Fn() -> I> PowTauG1 for PowTauG1Projective<F>
where
    <I as Iterator>::Item: Borrow<G1Projective>,
{
    fn eval_g1<'a>(&self, mut poly: impl Iterator<Item = &'a Scalar>) -> G1Projective {
        match poly.next().map(|k| G1Affine::generator().mul(k)) {
            None => G1Projective::identity(),
            Some(v) => poly
                .zip(self.0())
                .fold(v, |acc, (k, tau)| acc + tau.borrow().mul(k)),
        }
    }
}

pub trait PowTauG2 {
    fn eval_g2<'a>(&self, poly: impl Iterator<Item = &'a Scalar>) -> G2Projective;
}
impl<T, G2: PowTauG2> PowTauG2 for (T, G2) {
    fn eval_g2<'a>(&self, poly: impl Iterator<Item = &'a Scalar>) -> G2Projective {
        self.1.eval_g2(poly)
    }
}

#[derive(Clone, Copy)]
pub struct PowTauG2Affine<F>(pub F);
impl<I: Iterator, F: Fn() -> I> PowTauG2 for PowTauG2Affine<F>
where
    <I as Iterator>::Item: Borrow<G2Affine>,
{
    fn eval_g2<'a>(&self, mut poly: impl Iterator<Item = &'a Scalar>) -> G2Projective {
        match poly.next().map(|k| G2Affine::generator().mul::<true>(k)) {
            None => G2Projective::identity(),
            Some(v) => poly
                .zip(self.0())
                .fold(v, |acc, (k, tau)| acc + tau.borrow().mul::<true>(k)),
        }
    }
}

#[derive(Clone, Copy)]
pub struct PowTauG2Projective<F>(pub F);
impl<I: Iterator, F: Fn() -> I> PowTauG2 for PowTauG2Projective<F>
where
    <I as Iterator>::Item: Borrow<G2Projective>,
{
    fn eval_g2<'a>(&self, mut poly: impl Iterator<Item = &'a Scalar>) -> G2Projective {
        match poly.next().map(|k| G2Affine::generator().mul::<true>(k)) {
            None => G2Projective::identity(),
            Some(v) => poly
                .zip(self.0())
                .fold(v, |acc, (k, tau)| acc + tau.borrow().mul::<true>(k)),
        }
    }
}

/// An KZG prover that can be run in untrusted environments.
#[derive(Clone, Copy)]
pub struct UntrustedProver<G1> {
    pow_tau_g1: G1,
}

impl<G1: PowTauG1> UntrustedProver<G1> {
    /// Setup the untrusted prover from the powers of tau; `tau` is masked behind the discrete logarithm problem.
    pub fn new(pow_tau_g1: G1) -> Self {
        Self { pow_tau_g1 }
    }
}

impl<G1: PowTauG1> Prover for UntrustedProver<G1> {
    fn eval_g1<'a, 'b: 'a>(&self, poly: impl Iterator<Item = &'a Scalar>) -> Proof {
        self.pow_tau_g1.eval_g1(poly)
    }
}

pub trait Verifier {
    fn verify(&self, commitment: &G1Affine, points: &[(Scalar, Scalar)], proof: &G1Affine) -> bool;
}

static G2_PREPARED: Lazy<G2Prepared> = Lazy::new(|| G2Prepared::from(G2Affine::generator()));

/// A trusted KZG verifier that can forge arbitrary proofs. This should only be used in a trusted environment.

#[derive(Clone, Copy)]
pub struct TrustedVerifier {
    tau: TrustedTau,
}

impl TrustedVerifier {
    /// Generate the trusted setup. Is expected that this function is called
    /// in a safe evironment what will be destroyed after its execution
    pub const fn new(tau: TrustedTau) -> Self {
        Self { tau }
    }
}

impl Verifier for TrustedVerifier {
    /// Verifies that `points` exists in `proof`
    /// # Example
    /// ```
    /// use a0kzg::{Scalar, TrustedTau, TrustedVerifier, TrustedProver, Prover, Verifier};
    /// use ff::Field;
    ///
    /// // Create a trusted setup
    /// let tau = TrustedTau(Scalar::random(rand::thread_rng()));
    /// let prvr = TrustedProver::new(tau);
    /// let vrfr = TrustedVerifier::new(tau);
    ///
    /// // define the set of points (the "population")
    /// let set = vec![
    ///    (Scalar::from(1), Scalar::from(2)),
    ///    (Scalar::from(2), Scalar::from(3)),
    ///    (Scalar::from(3), Scalar::from(4)),
    ///    (Scalar::from(4), Scalar::from(57)),
    /// ];
    ///
    /// // create a polynomial for them, plus the polynomial commitment
    /// // see the polynomial commitment like the "hash" of the polynomial
    /// let (p, c) = prvr.poly_commitment_from_set(&set);
    /// let c = c.into();
    ///
    /// // generate a proof that (1,2) and (2,3) are in the set
    /// let proof01 = prvr.prove(p.clone(), &vec![set[0].clone(), set[1].clone()]).into();
    ///  
    /// // prove that the whole set exists in the whole set
    /// let proof0123 = prvr.prove(p, &set).into();
    ///
    /// // prove that (1,2) and (2,3) are in the set
    /// assert!(vrfr.verify(&c, &vec![set[0].clone(), set[1].clone()], &proof01));
    /// assert!(vrfr.verify(&c, &vec![set[1].clone(), set[0].clone()], &proof01));
    /// // other proofs will fail since the proof only works for exactly (1,2) AND (2,3)
    /// assert!(!vrfr.verify(&c, &vec![set[0].clone()], &proof01));
    /// assert!(!vrfr.verify(&c, &vec![set[0].clone(), set[2].clone()], &proof01));
    ///
    /// // verify that the whole set exists in the whole set
    /// assert!(vrfr.verify(&c, &set, &proof0123));
    /// ```
    #[allow(non_snake_case)]
    fn verify(&self, commitment: &G1Affine, points: &[(Scalar, Scalar)], proof: &G1Affine) -> bool {
        let z = G2Affine::generator() * Poly::evaluate_z_poly(points, &self.tau.0).vartime();
        let i = G1Affine::generator() * Poly::evaluate_lagrange(points, &self.tau.0).vartime();

        let e1 = pairing::<true>(&proof.vartime(), &z.into());
        let p = G1Affine::from(commitment - i).vartime();
        let e2 = multi_miller_loop(&[(&p, &G2_PREPARED)]).final_exponentiation::<true>();

        e1 == e2
    }
}

/// An KZG prover that can be run in untrusted environments.
#[derive(Clone, Copy)]
pub struct UntrustedVerifier<G12> {
    pow_tau: G12,
}

impl<G12: PowTauG1 + PowTauG2> UntrustedVerifier<G12> {
    /// Setup the untrusted prover from the powers of tau; `tau` is masked behind the discrete logarithm problem.
    pub fn new(pow_tau: G12) -> Self {
        Self { pow_tau }
    }
}

impl<G12: PowTauG1 + PowTauG2> Verifier for UntrustedVerifier<G12> {
    /// Verifies that `points` exists in `proof`
    /// # Example
    /// ```
    /// use a0kzg::{Scalar, TrustedTau, UntrustedVerifier, TrustedProver, Prover, Verifier, kzg::{PowTauG1Projective, PowTauG2Projective}};
    /// use ff::Field;
    ///
    /// // Create a trusted setup
    /// let tau = TrustedTau(Scalar::random(rand::thread_rng()));
    /// let prvr = TrustedProver::new(tau);
    ///
    /// // define the set of points (the "population")
    /// let set = vec![
    ///    (Scalar::from(1), Scalar::from(2)),
    ///    (Scalar::from(2), Scalar::from(3)),
    ///    (Scalar::from(3), Scalar::from(4)),
    ///    (Scalar::from(4), Scalar::from(57)),
    /// ];
    ///
    /// // create a polynomial for them, plus the polynomial commitment
    /// // see the polynomial commitment like the "hash" of the polynomial
    /// let (p, c) = prvr.poly_commitment_from_set(&set);
    /// let c = c.into();
    ///
    /// // generate a proof that (1,2) and (2,3) are in the set
    /// let proof01 = prvr.prove(p.clone(), &vec![set[0].clone(), set[1].clone()]).into();
    ///  
    /// // prove that the whole set exists in the whole set
    /// let proof0123 = prvr.prove(p, &set).into();
    ///
    /// // Create the untrusted setup
    /// let g1: Vec<_> = tau.g1_projective_iter().take(3).collect();
    /// let g2: Vec<_> = tau.g2_projective_iter().take(3).collect();
    /// let vrfr = UntrustedVerifier::new((PowTauG1Projective(|| g1.iter()), PowTauG2Projective(|| g2.iter())));
    /// // prove that (1,2) and (2,3) are in the set
    /// assert!(vrfr.verify(&c, &vec![set[0].clone(), set[1].clone()], &proof01));
    /// assert!(vrfr.verify(&c, &vec![set[1].clone(), set[0].clone()], &proof01));
    /// // other proofs will fail since the proof only works for exactly (1,2) AND (2,3)
    /// assert!(!vrfr.verify(&c, &vec![set[0].clone()], &proof01));
    /// assert!(!vrfr.verify(&c, &vec![set[0].clone(), set[2].clone()], &proof01));
    ///
    /// // verify that the whole set exists in the whole set
    /// assert!(vrfr.verify(&c, &set, &proof0123));
    /// ```
    #[allow(non_snake_case)]
    fn verify(&self, commitment: &G1Affine, points: &[(Scalar, Scalar)], proof: &G1Affine) -> bool {
        let I = Poly::lagrange(points);
        let Z = Poly::z_poly_of(points);

        let e1 = pairing::<true>(&proof.vartime(), &self.pow_tau.eval_g2(Z.iter()).into());
        let p = G1Affine::from(commitment - &self.pow_tau.eval_g1(I.iter())).vartime();
        let e2 = multi_miller_loop(&[(&p, &G2_PREPARED)]).final_exponentiation::<true>();

        e1 == e2
    }
}

#[derive(Clone)]
pub struct PowTauG1AffineBatch(Vec<G1PrecomputeAffine<512, VarTime>>);

impl PowTauG1AffineBatch {
    pub fn new<I>(i: I) -> Self
    where I: IntoIterator, I::Item: Borrow<G1ProjectiveA>{
        Self(
            [G1ProjectiveA::generator()].into_iter().chain(i.into_iter().map(|g| *g.borrow()))
                .map(|g| G1PrecomputeAffine::from(G1Precompute::from(g))).collect()
        )
    }

    fn eval(&self, poly: &[Scalar]) -> G1ProjectiveA<VarTime> {
        G1PrecomputeAffine::dot_product(&self.0, &poly)
    }
}


/// A KZG prover which can generate polynomial commitment and proofs
impl PowTauG1AffineBatch {
    /// Generate a polynomial and its commitment from a `set` of points
    pub fn poly_commitment_from_set(&self, set: &[(Scalar, Scalar)]) -> (Poly, G1ProjectiveA<VarTime>) {
        let poly = Poly::lagrange(set);
        let v = poly.iter().cloned().collect_vec();
        (poly, self.eval(v.as_slice()))
    }

    /// Generates a proof that `points` exists in `set`
    #[allow(non_snake_case)]
    pub fn prove<'a, 'b: 'a>(&self, poly: Poly<'a>, points: &[(Scalar, Scalar)]) -> G1ProjectiveA<VarTime> {
        // compute a lagrange polynomial I that have all the points to proof that are in the set
        // compute the polynomial Z that has roots (y=0) in all x's of I,
        // so this is I=(x-x0)(x-x1)...(x-xn)
        let I = Poly::lagrange(points);
        self.prove_with_poly(poly, &I, points)
    }

    /// Generates a proof that `points` exists in `set` with a pre-calculated lagrange polynomial
    #[allow(non_snake_case)]
    fn prove_with_poly<'a, 'b: 'a>(&self, mut poly: Poly<'a>, I: &Poly<'b>, points: &[(Scalar, Scalar)]) -> G1ProjectiveA<VarTime> {
        //let Z = Poly::z_poly_of(points);

        // now compute that Q = ( P - I(x) ) / Z(x)
        // also check that the division does not have remainder
        poly -= I;
        // let (Q, remainder) = poly / Z;
        // assert!(remainder.is_zero());
        let Q = poly.div_by_z_poly_of(points);

        // the proof is evaluating the Q at tau in G1
        let v = Q.iter().cloned().collect_vec();
        self.eval(v.as_slice())
    }
}



pub type Proof = G1Projective;
pub type Commitment = G1Projective;


#[cfg(test)]
mod test {
    use ff::Field;
    use super::*;

    #[test]
    fn test_zero_commit() {
        // Create a trusted setup
        let tau = TrustedTau(Scalar::random(rand::thread_rng()));
        let prvr = TrustedProver::new(tau);
        let vrfr = TrustedVerifier::new(tau);
        
        // define the set of points (the "population")
        let set = vec![
            (Scalar::from(1), Scalar::from(2)),
            (Scalar::from(2), Scalar::from(3)),
            (Scalar::from(3), Scalar::from(4)),
            (Scalar::from(4), Scalar::from(57)),
        ];
        
        // create a polynomial for them, plus the polynomial commitment
        // see the polynomial commitment like the "hash" of the polynomial
        let (p, c) = prvr.poly_commitment_from_set(&set);
        let c = c.into();
        
        // generate a proof that (1,2) and (2,3) are in the set
        let proof0 = prvr.prove(p.clone(), &vec![set[0].clone()]).into();
        let proof01 = prvr.prove(p.clone(), &vec![set[0].clone(), set[1].clone()]).into();
        
        // prove that the whole set exists in the whole set
        let proof0123 = prvr.prove(p, &set).into();
        
        // Create the untrusted setup
        assert!(vrfr.verify(&c, &vec![set[0].clone()], &proof0));
        // prove that (1,2) and (2,3) are in the set
        assert!(vrfr.verify(&c, &vec![set[0].clone(), set[1].clone()], &proof01));
        assert!(vrfr.verify(&c, &vec![set[1].clone(), set[0].clone()], &proof01));
        // other proofs will fail since the proof only works for exactly (1,2) AND (2,3)
        assert!(!vrfr.verify(&c, &vec![set[0].clone()], &proof01));
        assert!(!vrfr.verify(&c, &vec![set[0].clone(), set[2].clone()], &proof01));
        
        // verify that the whole set exists in the whole set
        assert!(vrfr.verify(&c, &set, &proof0123));

        let g1: Vec<_> = tau.g1_projective_iter().take(3).collect();
        let g2: Vec<_> = tau.g2_projective_iter().take(3).collect();
        let vrfr = UntrustedVerifier::new((PowTauG1Projective(|| g1.iter()), PowTauG2Projective(|| g2.iter())));
        assert!(vrfr.verify(&c, &vec![set[0].clone()], &proof0));
        // prove that (1,2) and (2,3) are in the set
        assert!(vrfr.verify(&c, &vec![set[0].clone(), set[1].clone()], &proof01));
        assert!(vrfr.verify(&c, &vec![set[1].clone(), set[0].clone()], &proof01));
        // other proofs will fail since the proof only works for exactly (1,2) AND (2,3)
        assert!(!vrfr.verify(&c, &vec![set[0].clone()], &proof01));
        assert!(!vrfr.verify(&c, &vec![set[0].clone(), set[2].clone()], &proof01));
        
        // verify that the whole set exists in the whole set
        assert!(vrfr.verify(&c, &set, &proof0123));
    }
    #[test]
    fn test_batch_commit() {
        use bls12_381::{G1ProjectiveA, G1Affine, G1AffineA};
        let points = (0..64)
                .map(|_| (Scalar::random(rand::thread_rng()), Scalar::random(rand::thread_rng())))
                .collect::<Vec<_>>();

        let tau = TrustedTau(Scalar::random(rand::thread_rng()));
        let batch: Vec<G1ProjectiveA> = tau.g1_projective_a_iter().take(points.len()).collect();
        let affine: Vec<_> = tau.g1_affine_iter().take(points.len()).collect();


        let prvr_b = PowTauG1AffineBatch::new(batch.iter());
        let prvr_a = UntrustedProver::new(PowTauG1Affine(|| affine.iter()));

        let (p, c) = prvr_a.poly_commitment_from_set(&points);
        let (bp, bc) = prvr_b.poly_commitment_from_set(&points);

        let ca = G1Affine::from(c);
        let bca = G1AffineA::from(bc);
        assert_eq!(p, bp);
        assert_eq!(ca.to_compressed(), bca.to_compressed());
    }
}