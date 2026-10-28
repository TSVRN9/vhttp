//! HMAC-SHA256 (RFC 2104 §2, B = 64, L = 32): spec and verified exec code.
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

/// `hmac_k0` is 64 octets: the hashed key (if longer than 64) or the key, then zeros.
proof fn lemma_hmac_k0(key: Seq<u8>)
    ensures
        hmac_k0(key).len() == 64,
        forall|j: int|
            0 <= j < 64 ==> #[trigger] hmac_k0(key)[j] == if key.len() > 64 && j < 32 {
                spec_sha256(key)[j]
            } else if key.len() <= 64 && j < key.len() {
                key[j]
            } else {
                0u8
            },
{
    lemma_spec_sha256_len(key);
}

// RFC 2104 §2 steps (1)-(7), with the core's 2^61-byte hash bound on msg.
pub(crate) fn hmac_sha256_core(key: &[u8], msg: &[u8]) -> (r: [u8; 32])
    requires
        key@.len() <= MAX_INPUT_LEN,
        msg@.len() + 64 < 0x2000_0000_0000_0000,
    ensures
        r@ == spec_hmac_sha256(key@, msg@),
{
    let long = key.len() > 64;
    let kh = if long {
        sha256(key)
    } else {
        [0u8; 32]
    };
    let ghost k0 = hmac_k0(key@);
    let ghost xi = xor_bytes(k0, Seq::new(64, |i: int| 0x36u8));
    let ghost xo = xor_bytes(k0, Seq::new(64, |i: int| 0x5cu8));
    proof {
        lemma_hmac_k0(key@);
    }
    let mut ipad = [0u8; 64];
    let mut opad = [0u8; 64];
    let mut j: usize = 0;
    while j < 64
        invariant
            j <= 64,
            long == (key@.len() > 64),
            long ==> kh@ == spec_sha256(key@),
            k0 == hmac_k0(key@),
            xi == xor_bytes(k0, Seq::new(64, |i: int| 0x36u8)),
            xo == xor_bytes(k0, Seq::new(64, |i: int| 0x5cu8)),
            forall|i: int| 0 <= i < j ==> #[trigger] ipad@[i] == xi[i],
            forall|i: int| 0 <= i < j ==> #[trigger] opad@[i] == xo[i],
        decreases 64 - j,
    {
        proof {
            lemma_hmac_k0(key@);
        }
        let b: u8 = if long {
            if j < 32 {
                kh[j]
            } else {
                0
            }
        } else if j < key.len() {
            key[j]
        } else {
            0
        };
        ipad[j] = b ^ 0x36;
        opad[j] = b ^ 0x5c;
        j += 1;
    }
    assert(ipad@ =~= xi);
    assert(opad@ =~= xo);
    let inner = sha256_cat(ipad.as_slice(), msg);
    proof {
        lemma_spec_sha256_len(xi + msg@);
    }
    sha256_cat(opad.as_slice(), inner.as_slice())
}

/// RFC 2104 §2 (B = 64, L = 32); verified against spec_hmac_sha256.
pub fn hmac_sha256(key: &[u8], msg: &[u8]) -> (r: [u8; 32])
    requires
        key@.len() <= MAX_INPUT_LEN,
        msg@.len() <= MAX_INPUT_LEN,
    ensures
        r@ == spec_hmac_sha256(key@, msg@),
{
    hmac_sha256_core(key, msg)
}

} // verus!
