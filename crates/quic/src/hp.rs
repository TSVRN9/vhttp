//! Header protection (RFC 9001 §5.4): a 5-byte AES-ECB mask over a 16-byte ciphertext sample
//! (§5.4.2, §5.4.3), applied to the first byte and the packet number as in Figure 6.
//!
//! Timing: `hp_mask` and `apply_hp` have no branch or index on the key or the mask; `apply_hp`
//! loops over the packet number length read before masking. `remove_hp` loops over the length
//! read after unmasking, which it computes from the mask, so its loop count depends on the mask.
//! Both are the length header protection hides on the wire (RFC 9001 §9.5), 1 to 4 bytes. This
//! is a known gap; the code is not CT-checked.
use crypto::aes::*;
use vstd::prelude::*;
use vstd::slice::{slice_subrange, slice_to_vec};

#[allow(unused_imports)]
use crate::header::*;

verus! {

// =============================================================================
// RFC 9001 transcription
// =============================================================================

//= https://www.rfc-editor.org/rfc/rfc9001#section-5.4.2
//# sample_offset = pn_offset + 4
//
//= https://www.rfc-editor.org/rfc/rfc9001#section-5.4.2
//# sample = packet[sample_offset..sample_offset+sample_length]
//
//= https://www.rfc-editor.org/rfc/rfc9001#section-5.4.3
//# This algorithm samples 16 bytes from the packet ciphertext.
/// The 16 ciphertext bytes from 4 bytes after the start of the Packet Number field.
pub open spec fn rfc_sample(pkt: Seq<u8>, pn_offset: nat) -> Seq<u8> {
    pkt.subrange(pn_offset + 4int, pn_offset + 20int)
}

//= https://www.rfc-editor.org/rfc/rfc9001#section-5.4.1
//# Before a TLS cipher suite can be used with QUIC, a header protection
//# algorithm MUST be specified for the AEAD used with that cipher suite.
//
//= https://www.rfc-editor.org/rfc/rfc9001#section-5.4.1
//# The output of this algorithm is a 5-byte mask that is applied to the
//# protected header fields using exclusive OR.
//
//= https://www.rfc-editor.org/rfc/rfc9001#section-5.4.3
//# header_protection(hp_key, sample):
//# mask = AES-ECB(hp_key, sample)
/// AES-128 header protection (§5.4.3), the one for AEAD_AES_128_GCM, our only AEAD.
pub open spec fn rfc_hp_mask(hp: Seq<u8>, sample: Seq<u8>) -> Seq<u8> {
    spec_aes128_encrypt(hp, sample).take(5)
}

//= https://www.rfc-editor.org/rfc/rfc9001#section-5.4.1
//# if (packet[0] & 0x80) == 0x80:
//
//= https://www.rfc-editor.org/rfc/rfc9001#section-5.4.1
//# packet[0] ^= mask[0] & 0x0f
//# else:
//
//= https://www.rfc-editor.org/rfc/rfc9001#section-5.4.1
//# packet[0] ^= mask[0] & 0x1f
/// Figure 6's first-byte step: the 4 low bits of a long header, the 5 low bits of a short one.
pub open spec fn hp_first_byte(b: u8, m: u8) -> u8 {
    if b & 0x80u8 == 0x80u8 {
        b ^ (m & 0x0fu8)
    } else {
        b ^ (m & 0x1fu8)
    }
}

//= https://www.rfc-editor.org/rfc/rfc9001#section-5.4.1
//# packet[pn_offset:pn_offset+pn_length] ^= mask[1:1+pn_length]
/// `pkt` with byte 0 replaced by `b0` and the `n` bytes from `o` XORed with `mask[1..1 + n]`.
pub open spec fn hp_xor(pkt: Seq<u8>, o: nat, mask: Seq<u8>, b0: u8, n: nat) -> Seq<u8> {
    Seq::new(
        pkt.len(),
        |i: int|
            if i == 0 {
                b0
            } else if o <= i < o + n {
                pkt[i] ^ mask[i - o + 1]
            } else {
                pkt[i]
            },
    )
}

//= https://www.rfc-editor.org/rfc/rfc9001#section-5.4.1
//# pn_length = (packet[0] & 0x03) + 1
/// Figure 6: the packet number length is read from byte 0 before it is masked.
/// `spec_pn_len(b)` is `(b & 0x03) + 1`.
pub open spec fn rfc_hp_apply(pkt: Seq<u8>, pn_offset: nat, mask: Seq<u8>) -> Seq<u8> {
    hp_xor(pkt, pn_offset, mask, hp_first_byte(pkt[0], mask[0]), spec_pn_len(pkt[0]) as nat)
}

//= https://www.rfc-editor.org/rfc/rfc9001#section-5.4.1
//# Removing header protection only differs in the order in which the
//# packet number length (pn_length) is determined
/// Figure 6 for removal: the packet number length is read from byte 0 after it is unmasked.
pub open spec fn rfc_hp_remove(pkt: Seq<u8>, pn_offset: nat, mask: Seq<u8>) -> Seq<u8> {
    let b0 = hp_first_byte(pkt[0], mask[0]);
    hp_xor(pkt, pn_offset, mask, b0, spec_pn_len(b0) as nat)
}

// =============================================================================
// Proofs
// =============================================================================

proof fn bv_first_byte(b: u8, m: u8)
    by (bit_vector)
    ensures
        (b ^ (m & 0x0fu8)) & 0x80u8 == b & 0x80u8,
        (b ^ (m & 0x1fu8)) & 0x80u8 == b & 0x80u8,
        (b ^ (m & 0x0fu8)) ^ (m & 0x0fu8) == b,
        (b ^ (m & 0x1fu8)) ^ (m & 0x1fu8) == b,
        (b ^ (m & 0x0fu8)) & 0xf0u8 == b & 0xf0u8,
        (b ^ (m & 0x1fu8)) & 0xe0u8 == b & 0xe0u8,
{
}

proof fn bv_xor_twice(x: u8, y: u8)
    by (bit_vector)
    ensures
        (x ^ y) ^ y == x,
{
}

proof fn bv_pn_len(b: u8)
    by (bit_vector)
    ensures
        (b & 3u8) < 4u8,
{
}

/// Removing protection with the same mask gives the packet back: the first-byte step keeps
/// 0x80 (so removal takes the same branch) and is an involution, so removal reads the same
/// packet number length, and XOR with the same mask bytes undoes itself.
pub proof fn lemma_hp_roundtrip(pkt: Seq<u8>, pn_offset: nat, mask: Seq<u8>)
    requires
        pn_offset >= 1,
        pn_offset + 4 <= pkt.len(),
        mask.len() == 5,
    ensures
        rfc_hp_remove(rfc_hp_apply(pkt, pn_offset, mask), pn_offset, mask) == pkt,
{
    let a = rfc_hp_apply(pkt, pn_offset, mask);
    bv_first_byte(pkt[0], mask[0]);
    bv_pn_len(pkt[0]);
    assert(hp_first_byte(a[0], mask[0]) == pkt[0]);
    let n = spec_pn_len(pkt[0]) as nat;
    assert forall|i: int| pn_offset <= i < pn_offset + n implies (#[trigger] a[i]) ^ mask[i
        - pn_offset + 1] == pkt[i] by {
        bv_xor_twice(pkt[i], mask[i - pn_offset + 1]);
    }
    assert(rfc_hp_remove(a, pn_offset, mask) =~= pkt);
}

/// What `rfc_hp_apply` keeps: the length, the bits of byte 0 that header protection does not
/// cover (0xf0 for a long header, 0xe0 for a short one), every byte outside byte 0 and the
/// 4 bytes from `pn_offset`, and hence the sample. `rfc_header` reads only those.
pub proof fn lemma_hp_frame(pkt: Seq<u8>, pn_offset: nat, mask: Seq<u8>)
    requires
        pn_offset >= 1,
        pn_offset + 4 <= pkt.len(),
        mask.len() == 5,
    ensures
        rfc_hp_apply(pkt, pn_offset, mask).len() == pkt.len(),
        pkt[0] & 0x80u8 == 0x80u8 ==> rfc_hp_apply(pkt, pn_offset, mask)[0] & 0xf0u8 == pkt[0]
            & 0xf0u8,
        pkt[0] & 0x80u8 != 0x80u8 ==> rfc_hp_apply(pkt, pn_offset, mask)[0] & 0xe0u8 == pkt[0]
            & 0xe0u8,
        forall|i: int|
            0 < i < pkt.len() && !(pn_offset <= i < pn_offset + 4) ==> #[trigger] rfc_hp_apply(
                pkt,
                pn_offset,
                mask,
            )[i] == pkt[i],
        rfc_hp_apply(pkt, pn_offset, mask).subrange(1, pn_offset as int) == pkt.subrange(
            1,
            pn_offset as int,
        ),
        pn_offset + 20 <= pkt.len() ==> rfc_sample(rfc_hp_apply(pkt, pn_offset, mask), pn_offset)
            == rfc_sample(pkt, pn_offset),
{
    let a = rfc_hp_apply(pkt, pn_offset, mask);
    bv_first_byte(pkt[0], mask[0]);
    bv_pn_len(pkt[0]);
    assert(a.subrange(1, pn_offset as int) =~= pkt.subrange(1, pn_offset as int));
    if pn_offset + 20 <= pkt.len() {
        assert(rfc_sample(a, pn_offset) =~= rfc_sample(pkt, pn_offset));
    }
}

// =============================================================================
// Exec
// =============================================================================

/// The §5.4.3 mask: the first 5 bytes of AES-128 over the sample.
pub fn hp_mask(hp: &[u8; 16], sample: &[u8]) -> (m: [u8; 5])
    requires
        sample@.len() == 16,
    ensures
        m@ == rfc_hp_mask(hp@, sample@),
{
    hide(spec_aes128_encrypt);
    let r = aes128_encrypt_block(hp.as_slice(), sample);
    let m = [r[0], r[1], r[2], r[3], r[4]];
    assert(m@ =~= r@.take(5));
    m
}

fn first_byte(b: u8, m: u8) -> (r: u8)
    ensures
        r == hp_first_byte(b, m),
{
    if b & 0x80 == 0x80 {
        b ^ (m & 0x0f)
    } else {
        b ^ (m & 0x1f)
    }
}

/// `hp_xor` in place over the packet that starts at `start`.
fn xor_header(buf: &mut Vec<u8>, start: usize, o: usize, m: &[u8; 5], b0: u8, n: usize)
    requires
        o >= 1,
        1 <= n <= 4,
        start + o + 4 <= old(buf)@.len(),
    ensures
        final(buf)@ == old(buf)@.take(start as int) + hp_xor(
            old(buf)@.skip(start as int),
            o as nat,
            m@,
            b0,
            n as nat,
        ),
{
    let ghost b = buf@;
    let _len = buf.len();
    buf.set(start, b0);
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n <= 4,
            o >= 1,
            start + o + 4 <= b.len() == _len,
            buf@.len() == b.len(),
            forall|j: int|
                0 <= j < b.len() ==> #[trigger] buf@[j] == if j == start {
                    b0
                } else if start + o <= j < start + o + i {
                    b[j] ^ m@[j - start - o + 1]
                } else {
                    b[j]
                },
        decreases n - i,
    {
        let k = start + o + i;
        let v = buf[k] ^ m[i + 1];
        buf.set(k, v);
        i += 1;
    }
    assert(buf@ =~= b.take(start as int) + hp_xor(b.skip(start as int), o as nat, m@, b0, n as nat));
}

/// Figure 6 in place on the packet that starts at `buf[start]`, whose Packet Number field
/// starts `pn_offset` bytes in.
pub fn apply_hp(buf: &mut Vec<u8>, start: usize, pn_offset: usize, hp: &[u8; 16])
    requires
        pn_offset >= 1,
        start + pn_offset + 20 <= old(buf)@.len(),
    ensures
        final(buf)@ == old(buf)@.take(start as int) + rfc_hp_apply(
            old(buf)@.skip(start as int),
            pn_offset as nat,
            rfc_hp_mask(hp@, rfc_sample(old(buf)@.skip(start as int), pn_offset as nat)),
        ),
{
    hide(spec_aes128_encrypt);
    let ghost w = buf@.skip(start as int);
    let _len = buf.len();
    let s = start + pn_offset + 4;
    let m = hp_mask(hp, slice_subrange(buf.as_slice(), s, s + 16));
    assert(buf@.subrange(s as int, s + 16) =~= rfc_sample(w, pn_offset as nat));
    let b = buf[start];
    proof {
        bv_pn_len(b);
    }
    let n = (b & 3) as usize + 1;
    xor_header(buf, start, pn_offset, &m, first_byte(b, m[0]), n);
}

/// Figure 6 for removal, on a copy of the packet.
pub fn remove_hp(pkt: &[u8], pn_offset: usize, hp: &[u8; 16]) -> (u: Vec<u8>)
    requires
        pn_offset >= 1,
        pn_offset + 20 <= pkt@.len(),
    ensures
        u@ == rfc_hp_remove(
            pkt@,
            pn_offset as nat,
            rfc_hp_mask(hp@, rfc_sample(pkt@, pn_offset as nat)),
        ),
{
    hide(spec_aes128_encrypt);
    let _len = pkt.len();
    let s = pn_offset + 4;
    let m = hp_mask(hp, slice_subrange(pkt, s, s + 16));
    let b0 = first_byte(pkt[0], m[0]);
    proof {
        bv_pn_len(b0);
    }
    let n = (b0 & 3) as usize + 1;
    let mut u = slice_to_vec(pkt);
    xor_header(&mut u, 0, pn_offset, &m, b0, n);
    assert(pkt@.skip(0) =~= pkt@);
    assert(pkt@.take(0) + hp_xor(pkt@, pn_offset as nat, m@, b0, n as nat) =~= hp_xor(
        pkt@,
        pn_offset as nat,
        m@,
        b0,
        n as nat,
    ));
    u
}

} // verus!
