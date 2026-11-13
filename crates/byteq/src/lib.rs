//! Byte buffers with proved growth (9b2): `CapVec`, a `Vec` that is never pushed past the capacity it was created
//! with, so it never reallocates.
pub mod capvec;
pub mod queue;
