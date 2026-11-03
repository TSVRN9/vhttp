//! Verified MIR front end of the constant-time checker (Phase 8c). `json` reads the dump bytes,
//! with `print` (serde_json's compact writer as a spec) tying each parsed value to rustc's output.
//! `mir` mirrors the rustc_public types the dump holds, and `schema` decodes a parsed dump into
//! them against `decode_*`, serde's derive conventions as a spec.
#![allow(unused_braces)]
use vstd::prelude::*;

verus! {

// x86-64 (the dump's layouts are)
global size_of usize == 8;

} // verus!

pub mod json;
pub mod look;
pub mod lower;
pub mod lower_const;
pub mod lower_fn;
pub mod lower_term;
pub mod mir;
pub mod policy;
pub mod rel;
pub mod schema;
pub mod sem;
pub mod sem_sanity;
pub mod sem_subset;
pub mod sim;
pub mod sim_exec;
pub mod sim_const;
pub mod sim_op;
pub mod sim_pure;
pub mod sim_rv;
pub mod sim_run;
pub mod sim_stmt;
