//! Verified MIR front end of the constant-time checker (Phase 8c). `json` reads the dump bytes,
//! with `print` (serde_json's compact writer as a spec) tying each parsed value to rustc's output.
pub mod json;
