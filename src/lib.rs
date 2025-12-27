#![allow(unused,non_snake_case)]
#![warn(missing_docs)]

//! This crate implements dependent type equations at runtime, allowing proofs of simple things such as a + b = b + a
//! To convert proofs from another proof language into this language: 
//! - the function [ctypes::lam_helper] and [ctypes::pi_helper] (and their polymorphic variants) will be useful for creating functions and pi types
//! - the enum [ctypes::Term::Sig] will serve as the sigma type
//! - for most normal stuff with equality types, use [equals::straight_eq], [equals::refl], and Axiom J from [equals::Theorems]
//! - refer to the variants in [ctypes::Term] for more fine control over the proofs
//! - there is no way to construct inductive types, but many can be constructed by creating a larger type than intended and pruning it by pairing it with an equality that only holds in some cases
//! - refer to [bool] for an example implementation of this concept.

mod unique;
/// The module that handles all of the internals of the prover
/// The main thing to remember is [ctypes::Term::ctn] is necessary to build nested structs, as it interns the values to improve performance
pub mod ctypes;
mod notation;
/// The module that handles displaying terms
pub mod display;
/// The module that creates theorems about basic natural numbers
/// Still work-in-progress
pub mod numbers;
/// Produces translation theorems between axiom-j equality and cubical equality for convenience
pub mod equals;
// mod bucket;

pub mod bool;
pub mod impossible;

