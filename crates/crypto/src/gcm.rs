//! AES-128-GCM (NIST SP 800-38D, 96-bit IV, 128-bit tag): spec and exec signatures backed by the trusted shim.
#[allow(unused_imports)]
use crate::aes::*;
#[allow(unused_imports)]
use crate::bytes::*;
use vstd::prelude::*;

verus! {

/// SP 800-38D §5.2.1.1: len(P) <= 2^39 - 256 bits, i.e. 2^36 - 32 bytes.
pub const GCM_MAX_PT_LEN: usize = 0xF_FFFF_FFE0;

/// SP 800-38D §6.3 Algorithm 1, steps 2-3 from loop index i: bit x_i is `(x >> (127 - i)) & 1`.
pub open spec fn gf128_loop(x: u128, z: u128, v: u128, i: nat) -> u128
    decreases 128 - i,
{
    if i >= 128 {
        z
    } else {
        let z2 = if (x >> ((127 - i) as u128)) & 1 == 1 {
            z ^ v
        } else {
            z
        };
        let v2 = if v & 1 == 1 {
            (v >> 1) ^ (0xE1u128 << 120u128)
        } else {
            v >> 1
        };
        gf128_loop(x, z2, v2, i + 1)
    }
}

/// SP 800-38D §6.3 Algorithm 1: x . y in GF(2^128), Z0 = 0, V0 = Y, R = 11100001 || 0^120.
pub open spec fn gf128_mul(x: u128, y: u128) -> u128 {
    gf128_loop(x, 0, y, 0)
}

/// SP 800-38D §6.4: Y_0 = 0, Y_i = (Y_{i-1} xor X_i) . H, result Y_m.
pub open spec fn ghash(h: u128, x: Seq<u8>) -> u128
    recommends
        x.len() % 16 == 0,
    decreases x.len(),
{
    if x.len() < 16 {
        0
    } else {
        let n = (x.len() - 16) as nat;
        gf128_mul(ghash(h, x.subrange(0, n as int)) ^ (os2ip(x.subrange(n as int, x.len() as int)) as u128), h)
    }
}

/// SP 800-38D §6.2: increment the rightmost 32 bits of the block, mod 2^32, as a big-endian integer.
pub open spec fn inc32(cb: Seq<u8>) -> Seq<u8> {
    cb.subrange(0, 12) + i2osp((os2ip(cb.subrange(12, 16)) + 1) % 4294967296, 4)
}

/// SP 800-38D §6.5 GCTR: X_i xor CIPH_K(CB_i), CB_{i+1} = inc32(CB_i); a final partial block
/// uses the leading bytes of CIPH_K(CB_n).
pub open spec fn gctr(key: Seq<u8>, icb: Seq<u8>, x: Seq<u8>) -> Seq<u8>
    decreases x.len(),
{
    if x.len() == 0 {
        Seq::empty()
    } else {
        let n: int = if x.len() >= 16 {
            16
        } else {
            x.len() as int
        };
        let ks = spec_aes128_encrypt(key, icb);
        xor_bytes(x.subrange(0, n), ks.subrange(0, n)) + gctr(
            key,
            inc32(icb),
            x.subrange(n, x.len() as int),
        )
    }
}

/// Zero padding of `s` up to a multiple of 16 bytes (the 0^v and 0^u of SP 800-38D §7.1 step 4).
pub open spec fn zero_pad16(s: Seq<u8>) -> Seq<u8> {
    Seq::new(((16 - s.len() % 16) % 16) as nat, |i: int| 0u8)
}

/// SP 800-38D §7.1 step 2: J0 = IV || 0^31 || 1 for a 96-bit IV.
pub open spec fn gcm_j0(nonce: Seq<u8>) -> Seq<u8> {
    nonce + seq![0u8, 0u8, 0u8, 1u8]
}

/// SP 800-38D §7.1 steps 1, 2, 5, 6: T = GCTR_K(J0, S), S = GHASH_H(A || 0^v || C || 0^u || [len(A)]_64 || [len(C)]_64),
/// lengths in bits.
pub open spec fn gcm_tag(key: Seq<u8>, nonce: Seq<u8>, aad: Seq<u8>, c: Seq<u8>) -> Seq<u8> {
    let h = os2ip(spec_aes128_encrypt(key, Seq::new(16, |i: int| 0u8))) as u128;
    let s = ghash(
        h,
        aad + zero_pad16(aad) + c + zero_pad16(c) + i2osp(8 * aad.len(), 8) + i2osp(8 * c.len(), 8),
    );
    gctr(key, gcm_j0(nonce), i2osp(s as nat, 16))
}

/// SP 800-38D §7.1: C = GCTR_K(inc32(J0), P); the output is C || T.
pub open spec fn spec_gcm_seal(key: Seq<u8>, nonce: Seq<u8>, aad: Seq<u8>, pt: Seq<u8>) -> Seq<u8> {
    let c = gctr(key, inc32(gcm_j0(nonce)), pt);
    c + gcm_tag(key, nonce, aad, c)
}

/// SP 800-38D §7.2: None if the input is shorter than the tag or the tag does not match.
pub open spec fn spec_gcm_open(key: Seq<u8>, nonce: Seq<u8>, aad: Seq<u8>, ct: Seq<u8>) -> Option<
    Seq<u8>,
> {
    if ct.len() < 16 {
        None
    } else {
        let c = ct.subrange(0, ct.len() - 16);
        let t = ct.subrange(ct.len() - 16, ct.len() as int);
        if t != gcm_tag(key, nonce, aad, c) {
            None
        } else {
            Some(gctr(key, inc32(gcm_j0(nonce)), c))
        }
    }
}

/// Trusted shim: the body is RustCrypto aes-gcm; the ensures is the trusted statement.
#[verifier::external_body]
pub fn aes128_gcm_seal(key: &[u8], nonce: &[u8], aad: &[u8], pt: &[u8]) -> (r: Vec<u8>)
    requires
        key@.len() == 16,
        nonce@.len() == 12,
        aad@.len() <= MAX_INPUT_LEN,
        pt@.len() <= GCM_MAX_PT_LEN,
    ensures
        r@ == spec_gcm_seal(key@, nonce@, aad@, pt@),
{
    crate::shim::aes128_gcm_seal(key, nonce, aad, pt)
}

/// Trusted shim: the body is RustCrypto aes-gcm; the ensures is the trusted statement.
#[verifier::external_body]
pub fn aes128_gcm_open(key: &[u8], nonce: &[u8], aad: &[u8], ct: &[u8]) -> (r: Option<Vec<u8>>)
    requires
        key@.len() == 16,
        nonce@.len() == 12,
        aad@.len() <= MAX_INPUT_LEN,
        ct@.len() <= GCM_MAX_PT_LEN + 16,
    ensures
        r.deep_view() == spec_gcm_open(key@, nonce@, aad@, ct@),
{
    crate::shim::aes128_gcm_open(key, nonce, aad, ct)
}

} // verus!
