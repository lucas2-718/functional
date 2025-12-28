#![warn(missing_docs)]

//! This crate implements dependent type equations at runtime, allowing proofs of simple things such as a + b = b + a
//! To convert proofs from another proof language into this language: 
//! - the function [ctypes::lam_helper] and [ctypes::pi_helper] (and their polymorphic variants) will be useful for creating functions and pi types
//! - the enum [ctypes::Term::Sig] will serve as the sigma type
//! - for most normal stuff with equality types, use [equals::straight_eq], [equals::refl], and Axiom J from [equals::EqualTheorems]
//! - refer to the variants in [ctypes::Term] for more fine control over the proofs
//! - there is no way to construct inductive types, but many can be constructed by creating a larger type than intended and pruning it by pairing it with an equality that only holds in some cases
//! - refer to [mod@bool] for an example implementation of this concept.
//! - use [ctypes::FinalTerm] to finalize a proof and ensure that it is correct - i.e. doesn't rely on lambda parameters that don't exist

mod unique;
/// The module that handles all of the internals of the prover
/// The main thing to remember is [ctypes::Term::ctn] is necessary to build nested structs, as it interns the values to improve performance
pub mod ctypes;
/// The module that handles displaying terms
/// The term display portion is pretty basic, but miles more readable than raw de bruijn indices
pub mod display;
/// The module that creates theorems about basic natural numbers
/// So far, produces the addition function and that it is symmetric
pub mod numbers;
/// Produces translation theorems between axiom-j equality and cubical equality for convenience
pub mod equals;
// mod bucket;

/// The module that describes the booleans in terms of the natural numbers
pub mod bool;
/// The module that describes the false type
pub mod impossible;

