//! HKDF-SHA256 (RFC 5869 §2.2-2.3): specs and verified exec code.
#[allow(unused_imports)]
use crate::bytes::*;
#[allow(unused_imports)]
use crate::hmac::*;
use vstd::prelude::*;

verus! {

/// RFC 5869 §2.2 Extract: PRK = HMAC-Hash(salt, IKM). "Salt not provided" is an empty `salt`;
/// HMAC zero-pads keys to 64 bytes, so it equals HashLen zeros (not proved; checked by
/// `rfc5869_hkdf` in tests/hmac_hkdf.rs through the verified exec).
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

/// RFC 5869 §2.2; verified against spec_hkdf_extract.
pub fn hkdf_extract(salt: &[u8], ikm: &[u8]) -> (r: [u8; 32])
    requires
        salt@.len() <= MAX_INPUT_LEN,
        ikm@.len() <= MAX_INPUT_LEN,
    ensures
        r@ == spec_hkdf_extract(salt@, ikm@),
{
    hmac_sha256(salt, ikm)
}

/// RFC 5869 §2.3; verified against spec_hkdf_expand. 8160 = 255 * HashLen is the output bound.
pub fn hkdf_expand(prk: &[u8], info: &[u8], len: usize) -> (r: Vec<u8>)
    requires
        prk@.len() == 32,
        info@.len() <= MAX_INPUT_LEN,
        len <= 8160,
    ensures
        r@ == spec_hkdf_expand(prk@, info@, len as nat),
{
    let n = (len + 31) / 32;
    let mut out: Vec<u8> = Vec::with_capacity(len);
    if n == 0 {
        assert(out@ =~= spec_hkdf_expand(prk@, info@, len as nat));
        return out;
    }
    // ponytail: info is copied once into buf; a streaming HMAC would avoid the copy if info ever
    // gets large (TLS HkdfLabel is <= 520 bytes).
    // buf is T(i-1) | info | i; T(0) is empty, so T(1) hashes buf[32..].
    let mut buf: Vec<u8> = Vec::with_capacity(info.len() + 33);
    buf.extend_from_slice([0u8; 32].as_slice());
    buf.extend_from_slice(info);
    buf.push(1);
    let ghost il = info@.len() as int;
    proof {
        assert(buf@.subrange(32, buf@.len() as int) =~= hkdf_t(prk@, info@, 0) + info@ + seq![1u8]);
        lemma_hkdf_t_len(prk@, info@, 1);
    }
    let mut t = hmac_sha256_core(prk, vstd::slice::slice_subrange(buf.as_slice(), 32, buf.len()));
    let k = if len < 32 {
        len
    } else {
        32
    };
    out.extend_from_slice(vstd::slice::slice_subrange(t.as_slice(), 0, k));
    proof {
        assert(hkdf_t_cat(prk@, info@, 0) + hkdf_t(prk@, info@, 1) =~= hkdf_t(prk@, info@, 1));
        assert(out@ =~= hkdf_t_cat(prk@, info@, 1).take(k as int));
    }
    let mut i: usize = 1;
    while i < n
        invariant
            prk@.len() == 32,
            info@.len() <= MAX_INPUT_LEN,
            len <= 8160,
            n == (len + 31) / 32,
            1 <= i <= n <= 255,
            buf@.len() == il + 33,
            il == info@.len(),
            buf@.subrange(32, il + 32) == info@,
            t@ == hkdf_t(prk@, info@, i as nat),
            out@.len() == if len < 32 * i {
                len as int
            } else {
                32 * i
            },
            out@ == hkdf_t_cat(prk@, info@, i as nat).take(out@.len() as int),
        decreases n - i,
    {
        let mut j: usize = 0;
        while j < 32
            invariant
                j <= 32,
                prk@.len() == 32,
                info@.len() <= MAX_INPUT_LEN,
                len <= 8160,
                n == (len + 31) / 32,
                1 <= i < n <= 255,
                il == info@.len(),
                t@ == hkdf_t(prk@, info@, i as nat),
                out@.len() == if len < 32 * i {
                    len as int
                } else {
                    32 * i
                },
                out@ == hkdf_t_cat(prk@, info@, i as nat).take(out@.len() as int),
                buf@.len() == il + 33,
                buf@.subrange(32, il + 32) == info@,
                forall|x: int| 0 <= x < j ==> #[trigger] buf@[x] == t@[x],
            decreases 32 - j,
        {
            proof {
                assert(buf@.update(j as int, t[j as int]).subrange(32, il + 32) =~= buf@.subrange(32, il + 32));
            }
            buf.set(j, t[j]);
            j += 1;
        }
        i += 1;
        let last = buf.len() - 1;
        proof {
            assert(buf@.update(last as int, i as u8).subrange(32, il + 32) =~= buf@.subrange(32, il + 32));
        }
        buf.set(last, i as u8);
        proof {
            lemma_hkdf_t_cat_len(prk@, info@, (i - 1) as nat);
            lemma_hkdf_t_len(prk@, info@, i as nat);
            assert(buf@ =~= hkdf_t(prk@, info@, (i - 1) as nat) + info@ + seq![i as u8]);
        }
        t = hmac_sha256_core(prk, buf.as_slice());
        let k = if len - out.len() < 32 {
            len - out.len()
        } else {
            32
        };
        let ghost o0 = out@;
        out.extend_from_slice(vstd::slice::slice_subrange(t.as_slice(), 0, k));
        proof {
            assert(o0 =~= hkdf_t_cat(prk@, info@, (i - 1) as nat));
            assert(out@ =~= hkdf_t_cat(prk@, info@, i as nat).take(out@.len() as int));
        }
    }
    proof {
        lemma_hkdf_t_cat_len(prk@, info@, n as nat);
    }
    out
}

} // verus!
