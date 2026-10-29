#![allow(dead_code)]
//! P-256 group law (Phase 5d): proofs of `lemma_scalar_mult_double` and
//! `lemma_scalar_mult_g_nonzero` over the frozen `crate::p256` spec, with no new trusted base.
//! Exported lemmas are `mod.rs` wrappers: proof fns are erased, so `use` re-exports fail to build.

mod nt;
mod field;
mod pratt;
mod torsion;
mod torsion_cert;
mod poly;
mod red;
mod rcb;
mod grid_small;
mod assoc_id;
mod grid_assoc_a;
mod grid_assoc_b;
mod grid_assoc_c;
mod grid_assoc_d;
mod group;
