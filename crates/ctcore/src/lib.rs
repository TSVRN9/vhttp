//! Core language of the constant-time checker (Phase 8a): syntax, and its trusted spec semantics
//! with leakage events and step counts; the CT typing and its value/place lemmas.
pub mod ct;
pub mod ct_lemmas;
pub mod ni;
pub mod sem;
pub mod sem_sanity;
pub mod syntax;
