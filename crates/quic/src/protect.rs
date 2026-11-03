//! Packet and datagram protection, send side (RFC 9001 §5.3, §5.4): the header and the padded
//! payload of an `OutPacket`, AEAD over the payload with the header as associated data, then
//! header protection, appended to a datagram buffer.
//!
//! Timing (RFC 9001 §9.5), constant time in style: no branch or loop count on the packet number
//! or its length. The header's packet number bytes come from `put_pn`, which copies the last
//! `pn_len` of 4 computed bytes; `nonce` and `apply_hp` are branch-free over both. The branches
//! that remain are on public values: the packet type, the key phase and spin bits, the Length
//! varint (sent in clear) and the padding count. Not met, a known gap: the packet layout itself
//! depends on `pn_len` (the copy length, the offset of everything after the packet number, and
//! the GCM work over a payload of the packet length minus `pn_len`), and nothing checks quic at
//! the MIR or binary level.
#[allow(unused_imports)]
use crypto::aes::*;
#[allow(unused_imports)]
use crypto::gcm::*;
use vstd::prelude::*;
#[allow(unused_imports)]
use wire::varint::*;

use crate::aead::*;
#[allow(unused_imports)]
use crate::codes::*;
#[allow(unused_imports)]
use crate::conn::*;
use crate::datagram::*;
#[allow(unused_imports)]
use crate::frame::*;
use crate::header::*;
use crate::hp::*;
use crate::payload::*;
#[allow(unused_imports)]
use crate::pn::*;

verus! {

// =============================================================================
// Specs
// =============================================================================

//= https://www.rfc-editor.org/rfc/rfc9001#section-5.4.2
//# To ensure that sufficient data is available for sampling, packets are
//# padded so that the combined lengths of the encoded packet number and
//# protected payload is at least 4 bytes longer than the sample required
//# for header protection.
/// A packet `protect` accepts: `out_packet_wf` without the `pn_len_ok` minimality clauses,
/// plus a packet number within `PN_MAX` (the nonce's domain). With the 16-byte tag, the
/// `MIN_PN_AND_PAYLOAD` clause makes the packet number and protected payload 20 bytes: the
/// 4 bytes assumed for the packet number and the 16-byte sample.
pub open spec fn protect_ok(p: SpecOutPacket) -> bool {
    &&& out_packet_sized(p)
    &&& p.pn_len + plaintext_len(p) >= MIN_PN_AND_PAYLOAD
    &&& p.kind is OneRtt ==> p.scid.len() == 0
    &&& p.pn <= PN_MAX
}

/// A packet 3d2's `transmit_ok` hands over (P7) is protectable once its packet number is within
/// `PN_MAX` (P4 with `Sent`'s `next_pn <= PN_MAX`).
pub proof fn lemma_wf_protect_ok(p: SpecOutPacket, la: Option<u64>)
    requires
        out_packet_wf(p, la),
        p.pn <= PN_MAX,
    ensures
        protect_ok(p),
{
}

/// The long header type of an Initial or Handshake packet.
pub open spec fn long_ty(k: PacketKind) -> LongType {
    if k is Initial {
        LongType::Initial
    } else {
        LongType::Handshake
    }
}

/// The unprotected header through the packet number. A short header has key phase 0 (until
/// Phase 4) and writes `p.spin`.
pub open spec fn spec_header_bytes(p: SpecOutPacket) -> Seq<u8> {
    if p.kind is OneRtt {
        spec_short_header_bytes(p.dcid, false, p.spin, p.pn, p.pn_len)
    } else {
        spec_long_header_bytes(
            long_ty(p.kind),
            p.dcid,
            p.scid,
            p.pn,
            p.pn_len,
            (plaintext_len(p) + AEAD_TAG_LEN) as nat,
        )
    }
}

/// The payload before protection: the frames, then `padding` zero bytes (PADDING frames).
pub open spec fn spec_plaintext(p: SpecOutPacket) -> Seq<u8> {
    spec_frames_bytes(p.frames) + Seq::new(p.padding, |i: int| 0u8)
}

/// AEAD first, then header protection (§5.3, §5.4.1).
pub open spec fn rfc_protect(p: SpecOutPacket, k: SpecKeys) -> Seq<u8> {
    let h = spec_header_bytes(p);
    let o = (h.len() - p.pn_len) as nat;
    let w = h + spec_gcm_seal(k.key, rfc_nonce(k.iv, p.pn), h, spec_plaintext(p));
    rfc_hp_apply(w, o, rfc_hp_mask(k.hp, rfc_sample(w, o)))
}

/// Every packet of `ps` has keys in its space.
pub open spec fn all_keyed(ps: Seq<SpecOutPacket>, keys: Seq<Option<SpecKeyPair>>) -> bool {
    forall|i: int| 0 <= i < ps.len() ==> (#[trigger] keys[space_idx(ps[i].kind)]) is Some
}

/// The packets of `ps` that have keys, each protected with its space's `tx` keys, in order.
pub open spec fn protect_keyed(ps: Seq<SpecOutPacket>, keys: Seq<Option<SpecKeyPair>>) -> Seq<u8>
    decreases ps.len(),
{
    if ps.len() == 0 {
        Seq::empty()
    } else {
        protect_keyed(ps.drop_last(), keys) + match keys[space_idx(ps.last().kind)] {
            Some(kp) => rfc_protect(ps.last(), kp.tx),
            None => Seq::empty(),
        }
    }
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-14.1
//# Similarly, a server MUST expand the payload of all UDP
//# datagrams carrying ack-eliciting Initial packets to at least the
//# smallest allowed maximum datagram size of 1200 bytes.
/// Decision 4. Every packet keyed: all of them, in order. Otherwise, if an ack-eliciting
/// Initial is in the datagram, nothing: dropping an unkeyed packet would leave it under 1200
/// bytes. Otherwise the keyed packets, in order.
pub open spec fn rfc_protect_datagram(d: SpecOutDatagram, keys: Seq<Option<SpecKeyPair>>) -> Seq<
    u8,
> {
    if all_keyed(d.packets, keys) {
        protect_keyed(d.packets, keys)
    } else if has_eliciting_initial(d.packets) {
        Seq::empty()
    } else {
        protect_keyed(d.packets, keys)
    }
}

// =============================================================================
// Proofs
// =============================================================================

/// The header's length, and so the packet's, from 3b's header layout.
proof fn lemma_header_len(p: SpecOutPacket)
    requires
        out_packet_sized(p),
    ensures
        spec_header_bytes(p).len() + plaintext_len(p) + AEAD_TAG_LEN == out_packet_len(p),
        spec_header_bytes(p).len() >= p.pn_len + 1,
{
    lemma_pn_roundtrip(p.pn, p.pn_len as nat);
    if !(p.kind is OneRtt) {
        theorem_serialize_matches_rfc(length_field(p) as u64);
        assert((p.pn_len + (plaintext_len(p) + AEAD_TAG_LEN)) as u64 == length_field(p) as u64);
    }
}

/// `rfc_protect` writes exactly `out_packet_len` bytes.
pub proof fn lemma_rfc_protect_len(p: SpecOutPacket, k: SpecKeys)
    requires
        protect_ok(p),
    ensures
        rfc_protect(p, k).len() == out_packet_len(p),
{
    hide(spec_aes128_encrypt);
    hide(spec_gcm_seal);
    let h = spec_header_bytes(p);
    lemma_header_len(p);
    lemma_gcm_open_seal(k.key, rfc_nonce(k.iv, p.pn), h, spec_plaintext(p));
}

/// The keyed packets are at most the datagram, and all of it when every packet is keyed.
proof fn lemma_keyed_len(ps: Seq<SpecOutPacket>, keys: Seq<Option<SpecKeyPair>>)
    requires
        forall|i: int| 0 <= i < ps.len() ==> protect_ok(#[trigger] ps[i]),
    ensures
        protect_keyed(ps, keys).len() <= packets_len(ps),
        all_keyed(ps, keys) ==> protect_keyed(ps, keys).len() == packets_len(ps),
    decreases ps.len(),
{
    hide(rfc_protect);
    if ps.len() > 0 {
        let q = ps.drop_last();
        assert forall|i: int| 0 <= i < q.len() implies protect_ok(#[trigger] q[i]) by {
            assert(q[i] == ps[i]);
        }
        lemma_keyed_len(q, keys);
        if all_keyed(ps, keys) {
            assert forall|i: int| 0 <= i < q.len() implies (#[trigger] keys[space_idx(
                q[i].kind,
            )]) is Some by {
                assert(q[i] == ps[i]);
            }
        }
        assert(protect_ok(ps[ps.len() - 1]));
        match keys[space_idx(ps.last().kind)] {
            Some(kp) => lemma_rfc_protect_len(ps.last(), kp.tx),
            None => {
                assert(!all_keyed(ps, keys) || keys[space_idx(ps[ps.len() - 1].kind)] is Some);
            },
        }
    }
}

// =============================================================================
// Exec
// =============================================================================

fn sidx(k: PacketKind) -> (r: usize)
    ensures
        r == space_idx(k),
{
    match k {
        PacketKind::Initial => 0,
        PacketKind::Handshake => 1,
        PacketKind::OneRtt => 2,
    }
}

/// The padded plaintext: the frames, then `padding` zero bytes.
fn plaintext(p: &OutPacket) -> (pt: Vec<u8>)
    requires
        out_packet_sized(p@),
    ensures
        pt@ == spec_plaintext(p@),
        pt@.len() == plaintext_len(p@) < 16384,
{
    let ghost pv = p@;
    let mut pt: Vec<u8> = Vec::new();
    serialize_payload(p.frames.as_slice(), p.kind, &mut pt);
    assert(pt@ =~= spec_frames_bytes(pv.frames) + Seq::new(0nat, |j: int| 0u8));
    let mut i: usize = 0;
    while i < p.padding
        invariant
            i <= p.padding,
            pv == p@,
            pt@ == spec_frames_bytes(pv.frames) + Seq::new(i as nat, |j: int| 0u8),
        decreases p.padding - i,
    {
        pt.push(0u8);
        i += 1;
        assert(pt@ =~= spec_frames_bytes(pv.frames) + Seq::new(i as nat, |j: int| 0u8));
    }
    assert(pt@ =~= spec_plaintext(pv));
    pt
}

/// The unprotected header for a plaintext of `pt_len` bytes, and the packet number offset.
fn header(p: &OutPacket, pt_len: usize) -> (r: (Vec<u8>, usize))
    requires
        out_packet_sized(p@),
        pt_len == plaintext_len(p@),
    ensures
        r.0@ == spec_header_bytes(p@),
        r.1 + p@.pn_len == r.0@.len(),
        r.1 >= 1,
        r.0@.len() <= 64,
{
    proof {
        lemma_header_len(p@);
    }
    let mut h: Vec<u8> = Vec::new();
    let o = match p.kind {
        PacketKind::OneRtt => serialize_short_header(
            p.dcid.as_slice(),
            false,
            p.spin,
            p.pn,
            p.pn_len,
            &mut h,
        ),
        PacketKind::Initial => serialize_long_header(
            LongType::Initial,
            p.dcid.as_slice(),
            p.scid.as_slice(),
            p.pn,
            p.pn_len,
            pt_len + AEAD_TAG_LEN,
            &mut h,
        ),
        PacketKind::Handshake => serialize_long_header(
            LongType::Handshake,
            p.dcid.as_slice(),
            p.scid.as_slice(),
            p.pn,
            p.pn_len,
            pt_len + AEAD_TAG_LEN,
            &mut h,
        ),
    };
    assert(h@ =~= spec_header_bytes(p@));
    (h, o)
}

/// Appends `rfc_protect(p, k)`: the header and the padded payload in scratch buffers, the AEAD
/// over the payload with the header as AAD, header then ciphertext onto `out`, then header
/// protection in place.
#[verifier::spinoff_prover]
pub fn protect(p: &OutPacket, k: &PacketKeys, out: &mut Vec<u8>)
    requires
        protect_ok(p@),
    ensures
        final(out)@ == old(out)@ + rfc_protect(p@, k@),
        rfc_protect(p@, k@).len() == out_packet_len(p@),
{
    hide(spec_aes128_encrypt);
    hide(gctr);
    hide(ghash);
    hide(spec_gcm_seal);
    hide(spec_header_bytes);
    hide(spec_plaintext);
    hide(rfc_hp_apply);
    let pt = plaintext(p);
    let (h, o) = header(p, pt.len());
    let c = seal_packet(k, p.pn, h.as_slice(), pt.as_slice());
    let ghost before = out@;
    let start = out.len();
    out.extend_from_slice(h.as_slice());
    out.extend_from_slice(c.as_slice());
    let ghost w = h@ + c@;
    assert(out@ =~= before + w);
    assert(out@.take(start as int) =~= before);
    assert(out@.skip(start as int) =~= w);
    apply_hp(out, start, o, &k.hp);
    proof {
        lemma_rfc_protect_len(p@, k@);
    }
}

/// Pass 1 of `protect_datagram`: whether every packet is keyed, and whether an ack-eliciting
/// Initial is among them.
fn scan(d: &OutDatagram, keys: &[Option<KeyPair>; 3]) -> (r: (bool, bool))
    ensures
        r.0 == all_keyed(d@.packets, keys.deep_view()),
        r.1 == has_eliciting_initial(d@.packets),
{
    let ghost kd = keys.deep_view();
    let ghost ps = d@.packets;
    let mut all = true;
    let mut elic = false;
    let mut i: usize = 0;
    while i < d.packets.len()
        invariant
            i <= d.packets.len() == ps.len(),
            ps == d@.packets,
            kd == keys.deep_view(),
            all ==> forall|j: int| 0 <= j < i ==> (#[trigger] kd[space_idx(ps[j].kind)]) is Some,
            !all ==> !all_keyed(ps, kd),
            elic ==> has_eliciting_initial(ps),
            !elic ==> forall|j: int, f: int|
                0 <= j < i && ps[j].kind is Initial && 0 <= f < ps[j].frames.len() ==> !ack_eliciting(
                    spec_frame_type(#[trigger] ps[j].frames[f]),
                ),
        decreases d.packets.len() - i,
    {
        let p = &d.packets[i];
        assert(ps[i as int] == p@);
        let si = sidx(p.kind);
        assert(kd[si as int] == keys@[si as int].deep_view());
        if keys[si].is_none() {
            all = false;
            assert(kd[space_idx(ps[i as int].kind)] is None);
        }
        let initial = match p.kind {
            PacketKind::Initial => true,
            _ => false,
        };
        if initial && is_ack_eliciting(p.frames.as_slice()) {
            proof {
                let f = choose|f: int|
                    0 <= f < p.frames@.len() && ack_eliciting(
                        spec_frame_type(#[trigger] p.frames@[f]@),
                    );
                assert(ps[i as int].frames[f] == p.frames@[f]@);
                assert(ack_eliciting(spec_frame_type(ps[i as int].frames[f])));
            }
            elic = true;
        } else {
            proof {
                assert forall|f: int|
                    ps[i as int].kind is Initial && 0 <= f < ps[i as int].frames.len() implies !ack_eliciting(
                    spec_frame_type(#[trigger] ps[i as int].frames[f]),
                ) by {
                    assert(ps[i as int].frames[f] == p.frames@[f]@);
                }
            }
        }
        i += 1;
    }
    proof {
        if !elic && has_eliciting_initial(ps) {
            let (a, b) = choose|a: int, b: int|
                0 <= a < ps.len() && ps[a].kind is Initial && 0 <= b < ps[a].frames.len()
                    && ack_eliciting(spec_frame_type(#[trigger] ps[a].frames[b]));
            assert(!ack_eliciting(spec_frame_type(ps[a].frames[b])));
        }
    }
    (all, elic)
}

/// Appends `rfc_protect_datagram(d, keys)`: the packets in order, each with its space's `tx`
/// keys, skipping unkeyed ones unless that would leave an ack-eliciting Initial short of 1200
/// bytes, in which case nothing is written.
#[verifier::spinoff_prover]
pub fn protect_datagram(d: &OutDatagram, keys: &[Option<KeyPair>; 3], out: &mut Vec<u8>)
    requires
        forall|i: int| 0 <= i < d@.packets.len() ==> protect_ok(#[trigger] d@.packets[i]),
    ensures
        final(out)@ == old(out)@ + rfc_protect_datagram(d@, keys.deep_view()),
        final(out)@.len() <= old(out)@.len() + out_datagram_len(d@),
        all_keyed(d@.packets, keys.deep_view()) ==> final(out)@.len() == old(out)@.len()
            + out_datagram_len(d@),
{
    hide(rfc_protect);
    let ghost kd = keys.deep_view();
    let ghost ps = d@.packets;
    let ghost start = out@;
    proof {
        lemma_keyed_len(ps, kd);
    }
    let (all, elic) = scan(d, keys);
    if !all && elic {
        assert(rfc_protect_datagram(d@, kd) =~= Seq::<u8>::empty());
        assert(out@ =~= start + rfc_protect_datagram(d@, kd));
        return ;
    }
    // Pass 2: protect each keyed packet, in order.
    let mut i: usize = 0;
    while i < d.packets.len()
        invariant
            i <= d.packets.len() == ps.len(),
            ps == d@.packets,
            kd == keys.deep_view(),
            forall|j: int| 0 <= j < ps.len() ==> protect_ok(#[trigger] ps[j]),
            out@ == start + protect_keyed(ps.take(i as int), kd),
        decreases d.packets.len() - i,
    {
        let p = &d.packets[i];
        assert(ps[i as int] == p@);
        let si = sidx(p.kind);
        assert(kd[si as int] == keys@[si as int].deep_view());
        assert(ps.take(i + 1).drop_last() =~= ps.take(i as int));
        assert(ps.take(i + 1).last() == ps[i as int]);
        match &keys[si] {
            Some(kp) => {
                assert(protect_ok(ps[i as int]));
                protect(p, &kp.tx, out);
            },
            None => {},
        }
        i += 1;
        assert(out@ =~= start + protect_keyed(ps.take(i as int), kd));
    }
    assert(ps.take(ps.len() as int) =~= ps);
}

} // verus!
