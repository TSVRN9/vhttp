//! HMAC-SHA256 (RFC 2104 §2, B = 64, L = 32): spec and an exec signature backed by the trusted shim.
#[allow(unused_imports)]
use crate::bytes::*;
#[allow(unused_imports)]
use crate::sha256::*;
use vstd::prelude::*;

verus! {

/// RFC 2104 §2: K0, the key hashed if longer than B = 64 bytes, then right-padded with zeros to B.
pub open spec fn hmac_k0(key: Seq<u8>) -> Seq<u8> {
    let k = if key.len() > 64 {
        spec_sha256(key)
    } else {
        key
    };
    k + Seq::new((64 - k.len()) as nat, |i: int| 0u8)
}

/// RFC 2104 §2: H((K0 xor opad) || H((K0 xor ipad) || msg)), ipad = 64 x 0x36, opad = 64 x 0x5c.
pub open spec fn spec_hmac_sha256(key: Seq<u8>, msg: Seq<u8>) -> Seq<u8> {
    let k0 = hmac_k0(key);
    let ipad = Seq::new(64, |i: int| 0x36u8);
    let opad = Seq::new(64, |i: int| 0x5cu8);
    spec_sha256(xor_bytes(k0, opad) + spec_sha256(xor_bytes(k0, ipad) + msg))
}

/// Trusted shim: the body is RustCrypto hmac; the ensures is the trusted statement.
#[verifier::external_body]
pub fn hmac_sha256(key: &[u8], msg: &[u8]) -> (r: [u8; 32])
    requires
        key@.len() <= MAX_INPUT_LEN,
        msg@.len() <= MAX_INPUT_LEN,
    ensures
        r@ == spec_hmac_sha256(key@, msg@),
{
    crate::shim::hmac_sha256(key, msg)
}

} // verus!
