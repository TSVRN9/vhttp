//! HKDF-SHA256 (RFC 5869 §2.2-2.3): specs and exec signatures backed by the trusted shim.
#[allow(unused_imports)]
use crate::bytes::*;
#[allow(unused_imports)]
use crate::hmac::*;
use vstd::prelude::*;

verus! {

/// RFC 5869 §2.2 Extract: PRK = HMAC-Hash(salt, IKM). "Salt not provided" is an empty `salt`;
/// HMAC zero-pads keys to 64 bytes, so it equals HashLen zeros (checked by tests/hmac_hkdf.rs).
pub open spec fn spec_hkdf_extract(salt: Seq<u8>, ikm: Seq<u8>) -> Seq<u8> {
    spec_hmac_sha256(salt, ikm)
}

/// RFC 5869 §2.3: T(0) is empty; T(i) = HMAC-Hash(PRK, T(i-1) | info | i as one octet).
pub open spec fn hkdf_t(prk: Seq<u8>, info: Seq<u8>, i: nat) -> Seq<u8>
    decreases i,
{
    if i == 0 {
        Seq::empty()
    } else {
        spec_hmac_sha256(prk, hkdf_t(prk, info, (i - 1) as nat) + info + seq![i as u8])
    }
}

/// RFC 5869 §2.3: T(1) | T(2) | ... | T(n).
pub open spec fn hkdf_t_cat(prk: Seq<u8>, info: Seq<u8>, n: nat) -> Seq<u8>
    decreases n,
{
    if n == 0 {
        Seq::empty()
    } else {
        hkdf_t_cat(prk, info, (n - 1) as nat) + hkdf_t(prk, info, n)
    }
}

/// RFC 5869 §2.3 Expand: OKM = first L octets of T(1) | ... | T(N), N = ceil(L / HashLen).
pub open spec fn spec_hkdf_expand(prk: Seq<u8>, info: Seq<u8>, len: nat) -> Seq<u8> {
    hkdf_t_cat(prk, info, ((len + 31) / 32) as nat).take(len as int)
}

/// Trusted shim: the body is RustCrypto hkdf; the ensures is the trusted statement.
#[verifier::external_body]
pub fn hkdf_extract(salt: &[u8], ikm: &[u8]) -> (r: [u8; 32])
    requires
        salt@.len() <= MAX_INPUT_LEN,
        ikm@.len() <= MAX_INPUT_LEN,
    ensures
        r@ == spec_hkdf_extract(salt@, ikm@),
{
    crate::shim::hkdf_extract(salt, ikm)
}

/// Trusted shim: the body is RustCrypto hkdf; 8160 = 255 * HashLen is the RFC 5869 output bound.
#[verifier::external_body]
pub fn hkdf_expand(prk: &[u8], info: &[u8], len: usize) -> (r: Vec<u8>)
    requires
        prk@.len() == 32,
        info@.len() <= MAX_INPUT_LEN,
        len <= 8160,
    ensures
        r@ == spec_hkdf_expand(prk@, info@, len as nat),
{
    crate::shim::hkdf_expand(prk, info, len)
}

} // verus!
