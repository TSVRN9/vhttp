//! Trusted shim: every RustCrypto call lives here. Plain Rust outside `verus!`; removed in phase 5.
use sha2::{Digest, Sha256};

pub(crate) fn sha256(m: &[u8]) -> [u8; 32] {
    Sha256::digest(m).into()
}
