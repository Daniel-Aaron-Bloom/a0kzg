pub mod kzg;
mod poly;
mod fixed_poly;

pub use kzg::{
    Commitment, Proof, Prover, TrustedProver, TrustedTau, TrustedVerifier, UntrustedProver,
    UntrustedVerifier, Verifier,
};
pub use poly::Poly;

pub type Scalar = bls12_381::Scalar<0, true>;