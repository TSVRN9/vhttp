//! AEAD packet protection (RFC 9001 §5.3): the per-packet nonce and AEAD_AES_128_GCM with the
//! header as associated data, over crypto's verified GCM.
//!
//! Timing (RFC 9001 §9.5), constant time in style: `nonce` runs a fixed 8 iterations with
//! shifts and XOR only, so no branch, loop count or index depends on the packet number.
//! `seal_packet` and `open_packet` add no branch of their own. Not met, a known gap: the GCM
//! work depends on the payload length, which is the packet length minus the packet number
//! length, and nothing checks quic at the MIR or binary level.
// Used only in ghost code, which a plain `cargo build` erases.
#[allow(unused_imports)]
use crypto::aes::*;
#[allow(unused_imports)]
use crypto::bytes::*;
use crypto::gcm::*;
#[allow(unused_imports)]
use vstd::arithmetic::div_mod::*;
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;
#[allow(unused_imports)]
use vstd::bits::*;
use vstd::prelude::*;

verus! {

/// The largest UDP payload; the shell's receive buffer, and the bound below which datagrams are
/// opened.
pub const MAX_UDP_PAYLOAD: usize = 65535;

/// One direction's packet protection keys (RFC 9001 §5.1): AEAD key, IV and header protection key.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PacketKeys {
    pub key: [u8; 16],
    pub iv: [u8; 12],
    pub hp: [u8; 16],
}

pub struct SpecKeys {
    pub key: Seq<u8>,
    pub iv: Seq<u8>,
    pub hp: Seq<u8>,
}

impl View for PacketKeys {
    type V = SpecKeys;

    open spec fn view(&self) -> SpecKeys {
        SpecKeys { key: self.key@, iv: self.iv@, hp: self.hp@ }
    }
}

/// The keys of one packet number space: `rx` removes protection, `tx` applies it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct KeyPair {
    pub rx: PacketKeys,
    pub tx: PacketKeys,
}

pub struct SpecKeyPair {
    pub rx: SpecKeys,
    pub tx: SpecKeys,
}

impl View for KeyPair {
    type V = SpecKeyPair;

    open spec fn view(&self) -> SpecKeyPair {
        SpecKeyPair { rx: self.rx@, tx: self.tx@ }
    }
}

// =============================================================================
// RFC 9001 transcription
// =============================================================================

//= https://www.rfc-editor.org/rfc/rfc9001#section-5.3
//# The nonce, N, is formed by combining the packet
//# protection IV with the packet number.  The 62 bits of the
//# reconstructed QUIC packet number in network byte order are left-
//# padded with zeros to the size of the IV.  The exclusive OR of the
//# padded packet number and the IV forms the AEAD nonce.
/// The packet number, big-endian and left-padded to 12 bytes, XORed with the IV. Callers pass
/// packet numbers of at most 62 bits (`PN_MAX`), for which the 8-byte encoding is the 62 bits
/// padded.
pub open spec fn rfc_nonce(iv: Seq<u8>, pn: u64) -> Seq<u8> {
    xor_bytes(iv, i2osp(pn as nat, 12))
}

// =============================================================================
// Proofs
// =============================================================================

proof fn bv_xor_twice(x: u8, y: u8)
    by (bit_vector)
    ensures
        (x ^ y) ^ y == x,
        x ^ 0u8 == x,
{
}

proof fn bv_cast(y: u64)
    by (bit_vector)
    ensures
        y as u8 == (y % 256) as u8,
{
}

/// Byte `j` of `i2osp(x, len)` is `x / 256^(len - 1 - j) % 256`.
proof fn lemma_i2osp_index(x: nat, len: nat, j: nat)
    requires
        j < len,
    ensures
        i2osp(x, len)[j as int] == ((x / pow2(8 * (len - 1 - j) as nat)) % 256) as u8,
    decreases len,
{
    lemma_i2osp_len(x / 256, (len - 1) as nat);
    if j == len - 1 {
        lemma2_to64();
        assert(x / pow2(0) == x);
    } else {
        lemma_i2osp_index(x / 256, (len - 1) as nat, j);
        let e = 8 * (len - 2 - j) as nat;
        lemma_pow2_pos(e);
        lemma2_to64();
        lemma_pow2_adds(8, e);
        assert(8 * (len - 1 - j) as nat == 8 + e);
        lemma_div_denominator(x as int, 256, pow2(e) as int);
    }
}

/// GCTR with the same key and counter block undoes itself: each block is XORed with the same
/// key stream.
pub proof fn lemma_gctr_involution(key: Seq<u8>, icb: Seq<u8>, x: Seq<u8>)
    ensures
        gctr(key, icb, gctr(key, icb, x)) == x,
    decreases x.len(),
{
    hide(spec_aes128_encrypt);
    if x.len() > 0 {
        let n: int = if x.len() >= 16 {
            16
        } else {
            x.len() as int
        };
        let ks = spec_aes128_encrypt(key, icb);
        let rest = x.subrange(n, x.len() as int);
        let head = xor_bytes(x.subrange(0, n), ks.subrange(0, n));
        let y = gctr(key, icb, x);
        lemma_gctr_len(key, inc32(icb), rest);
        assert(y == head + gctr(key, inc32(icb), rest));
        assert(y.subrange(0, n) =~= head);
        assert(y.subrange(n, y.len() as int) =~= gctr(key, inc32(icb), rest));
        lemma_gctr_involution(key, inc32(icb), rest);
        assert forall|i: int| 0 <= i < n implies #[trigger] xor_bytes(head, ks.subrange(0, n))[i]
            == x[i] by {
            bv_xor_twice(x[i], ks.subrange(0, n)[i]);
        }
        assert(xor_bytes(head, ks.subrange(0, n)) + rest =~= x);
    }
}

/// Opening what was sealed with the same key, nonce and AAD gives the plaintext back, and the
/// sealed output is 16 bytes (the tag) longer than the plaintext.
pub proof fn lemma_gcm_open_seal(key: Seq<u8>, nonce: Seq<u8>, aad: Seq<u8>, pt: Seq<u8>)
    ensures
        spec_gcm_open(key, nonce, aad, spec_gcm_seal(key, nonce, aad, pt)) == Some(pt),
        spec_gcm_seal(key, nonce, aad, pt).len() == pt.len() + 16,
{
    hide(spec_aes128_encrypt);
    hide(ghash);
    hide(gctr);
    let icb = inc32(gcm_j0(nonce));
    let c = gctr(key, icb, pt);
    lemma_gctr_len(key, icb, pt);
    let t = gcm_tag(key, nonce, aad, c);
    let h = os2ip(spec_aes128_encrypt(key, Seq::new(16, |i: int| 0u8))) as u128;
    let s = ghash(
        h,
        aad + zero_pad16(aad) + c + zero_pad16(c) + i2osp(8 * aad.len(), 8) + i2osp(8 * c.len(), 8),
    );
    // The tag: 16 bytes of GCTR over a 16-byte block.
    lemma_i2osp_len(s as nat, 16);
    lemma_gctr_len(key, gcm_j0(nonce), i2osp(s as nat, 16));
    assert(t.len() == 16);
    let ct = c + t;
    assert(ct == spec_gcm_seal(key, nonce, aad, pt));
    assert(ct.subrange(0, ct.len() - 16) =~= c);
    assert(ct.subrange(ct.len() - 16, ct.len() as int) =~= t);
    lemma_gctr_involution(key, icb, pt);
}

// =============================================================================
// Exec
// =============================================================================

/// The §5.3 nonce: `iv[4 + i] ^= (pn >> (56 - 8i)) as u8` for the 8 low bytes; the high 4 bytes
/// of the padded packet number are zero.
pub fn nonce(iv: &[u8; 12], pn: u64) -> (n: [u8; 12])
    ensures
        n@ == rfc_nonce(iv@, pn),
{
    let mut n: [u8; 12] = *iv;
    let mut i: usize = 0;
    while i < 8
        invariant
            i <= 8,
            forall|j: int|
                0 <= j < 12 ==> #[trigger] n@[j] == if 4 <= j < 4 + i {
                    iv@[j] ^ ((pn >> (56 - 8 * (j - 4)) as u64) as u8)
                } else {
                    iv@[j]
                },
        decreases 8 - i,
    {
        n[4 + i] = iv[4 + i] ^ ((pn >> (56 - 8 * i as u64)) as u8);
        i += 1;
    }
    proof {
        let p = i2osp(pn as nat, 12);
        lemma_i2osp_len(pn as nat, 12);
        lemma2_to64();
        assert forall|j: int| 0 <= j < 12 implies #[trigger] n@[j] == rfc_nonce(iv@, pn)[j] by {
            lemma_i2osp_index(pn as nat, 12, j as nat);
            let e = 8 * (11 - j) as nat;
            if j < 4 {
                lemma_pow2_adds(64, (e - 64) as nat);
                lemma_pow2_pos((e - 64) as nat);
                assert(pn as nat / pow2(e) == 0) by {
                    assert(pow2(e) >= pow2(64)) by (nonlinear_arith)
                        requires
                            pow2(e) == pow2(64) * pow2((e - 64) as nat),
                            pow2((e - 64) as nat) > 0,
                    ;
                    lemma_basic_div(pn as int, pow2(e) as int);
                }
                bv_xor_twice(iv@[j], 0u8);
            } else {
                let sh = (56 - 8 * (j - 4)) as u64;
                assert(sh as nat == e);
                lemma_u64_shr_is_div(pn, sh);
                bv_cast(pn >> sh);
            }
        }
        assert(n@ =~= rfc_nonce(iv@, pn));
    }
    n
}

//= https://www.rfc-editor.org/rfc/rfc9001#section-5.3
//# The associated data, A, for the AEAD is the contents of the QUIC
//# header, starting from the first byte of either the short or long
//# header, up to and including the unprotected packet number.
//
//= https://www.rfc-editor.org/rfc/rfc9001#section-5.3
//# When constructing packets, the AEAD function is applied prior to
//# applying header protection; see Section 5.4.
/// AEAD_AES_128_GCM over `payload` with the unprotected `header` as associated data. The
/// AEAD function is applied prior to applying header protection: callers apply `apply_hp` to
/// `header ++ c` afterwards.
pub fn seal_packet(k: &PacketKeys, pn: u64, header: &[u8], payload: &[u8]) -> (c: Vec<u8>)
    requires
        header@.len() <= MAX_UDP_PAYLOAD,
        payload@.len() <= MAX_UDP_PAYLOAD,
    ensures
        c@ == spec_gcm_seal(k.key@, rfc_nonce(k.iv@, pn), header@, payload@),
        c@.len() == payload@.len() + 16,
{
    hide(spec_gcm_seal);
    hide(spec_gcm_open);
    hide(rfc_nonce);
    let n = nonce(&k.iv, pn);
    let c = aes128_gcm_seal(k.key.as_slice(), n.as_slice(), header, payload);
    proof {
        lemma_gcm_open_seal(k.key@, n@, header@, payload@);
    }
    c
}

/// AEAD_AES_128_GCM decryption with the unprotected `header` as associated data; `None` when
/// the tag does not match.
pub fn open_packet(k: &PacketKeys, pn: u64, header: &[u8], ct: &[u8]) -> (r: Option<Vec<u8>>)
    requires
        header@.len() <= MAX_UDP_PAYLOAD,
        ct@.len() <= MAX_UDP_PAYLOAD,
    ensures
        r.deep_view() == spec_gcm_open(k.key@, rfc_nonce(k.iv@, pn), header@, ct@),
{
    hide(spec_gcm_seal);
    hide(spec_gcm_open);
    hide(rfc_nonce);
    let n = nonce(&k.iv, pn);
    aes128_gcm_open(k.key.as_slice(), n.as_slice(), header, ct)
}

} // verus!
