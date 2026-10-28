//! Trusted shim: every RustCrypto call lives here. Plain Rust outside `verus!`; removed in phase 5.
use sha2::{Digest, Sha256};

pub(crate) fn sha256(m: &[u8]) -> [u8; 32] {
    Sha256::digest(m).into()
}

pub(crate) fn hmac_sha256(key: &[u8], msg: &[u8]) -> [u8; 32] {
    use hmac::{Hmac, KeyInit, Mac};
    // unreachable: HMAC accepts any key length
    let mut m = <Hmac<Sha256> as KeyInit>::new_from_slice(key).unwrap();
    m.update(msg);
    m.finalize().into_bytes().into()
}

pub(crate) fn hkdf_extract(salt: &[u8], ikm: &[u8]) -> [u8; 32] {
    hkdf::Hkdf::<Sha256>::extract(Some(salt), ikm).0.into()
}

pub(crate) fn hkdf_expand(prk: &[u8], info: &[u8], len: usize) -> Vec<u8> {
    // unreachable: requires prk@.len() == 32
    let k = hkdf::Hkdf::<Sha256>::from_prk(prk).unwrap();
    let mut out = vec![0u8; len];
    // unreachable: requires len <= 8160
    k.expand(info, &mut out).unwrap();
    out
}
