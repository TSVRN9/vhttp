//! HKDF-SHA256 (RFC 5869 §2.2-2.3): specs and exec signatures backed by the trusted shim.
#[allow(unused_imports)]
use crate::bytes::*;
#[allow(unused_imports)]
use crate::hmac::*;
use vstd::prelude::*;

verus! {

/// RFC 5869 §2.2 Extract: PRK = HMAC-Hash(salt, IKM). "Salt not provided" is an empty `salt`;
/// HMAC zero-pads keys to 64 bytes, so it equals HashLen zeros (not machine-checked here;
/// tests/hmac_hkdf.rs exercises the shim only).
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

proof fn lemma_hkdf_t_len(prk: Seq<u8>, info: Seq<u8>, i: nat)
    requires
        i >= 1,
    ensures
        hkdf_t(prk, info, i).len() == 32,
{
    crate::sha256::lemma_spec_sha256_len(
        xor_bytes(hmac_k0(prk), Seq::new(64, |j: int| 0x5cu8)) + crate::sha256::spec_sha256(
            xor_bytes(hmac_k0(prk), Seq::new(64, |j: int| 0x36u8)) + (hkdf_t(prk, info, (i - 1) as nat) + info + seq![i as u8]),
        ),
    );
}

proof fn lemma_hkdf_t_cat_len(prk: Seq<u8>, info: Seq<u8>, n: nat)
    ensures
        hkdf_t_cat(prk, info, n).len() == 32 * n,
    decreases n,
{
    if n > 0 {
        lemma_hkdf_t_cat_len(prk, info, (n - 1) as nat);
        lemma_hkdf_t_len(prk, info, n);
    }
}

/// `spec_hkdf_expand` yields exactly `len` octets.
pub proof fn lemma_spec_hkdf_expand_len(prk: Seq<u8>, info: Seq<u8>, len: nat)
    ensures
        spec_hkdf_expand(prk, info, len).len() == len,
{
    lemma_hkdf_t_cat_len(prk, info, ((len + 31) / 32) as nat);
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
