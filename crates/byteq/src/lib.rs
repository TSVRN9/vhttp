//! Byte buffers with proved growth (9b2): `CapVec`, a `Vec` that is never pushed past the capacity it was created
//! with, so it never reallocates; and `avl` (9b1, moved from quic in 9b3), a verified AVL tree keyed by `u64` with a
//! ghost cost per op.
pub mod avl;
pub mod capvec;
pub mod queue;
