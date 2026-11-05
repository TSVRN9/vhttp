//! Packet and datagram protection (RFC 9001 §5.3, §5.4). Send side: the header and the padded
//! payload of an `OutPacket`, AEAD over the payload with the header as associated data, then
//! header protection, appended to a datagram buffer. Receive side: `unprotect` parses a header,
//! removes header protection, recovers the packet number, removes packet protection and parses
//! the payload; `open_datagram` does so for each coalesced packet. `theorem_unprotect_protect`
//! proves that the receive side undoes the send side.
//!
//! Timing (RFC 9001 §9.5), constant time in style: no branch on the packet number or its length
//! in this module, `put_pn`, `nonce` or `apply_hp`. The header's packet number bytes come from
//! `put_pn`, which copies the last `pn_len` of 4 computed bytes. The other branches are on
//! public values: the packet type, the key phase and spin bits, the Length varint (sent in
//! clear) and which spaces have keys. Not met, a known gap: the packet layout depends on
//! `pn_len`, namely `put_pn`'s copy length, the offset of everything after the packet number,
//! the padding count (a datagram padded to a fixed size pads by a count that falls as `pn_len`
//! grows, and the padding loop runs that many times) and the GCM work over a payload of the
//! packet length minus `pn_len`; and nothing checks quic at the MIR or binary level.
//!
//! On receipt, HP removal, packet number recovery and AEAD run together in `open_one`, with no
//! branch or loop count on the packet number or its length: `remove_hp` and `read_pn_masked`
//! touch all 4 candidate packet number bytes, `decode_pn` selects by masks, and no packet is
//! discarded as a duplicate before AEAD. The branches before HP removal are on public values
//! (the header, which spaces have keys, the largest packet number processed); the reserved bits
//! are judged only after AEAD succeeds. Not met, the same gap: the AEAD's associated data and
//! ciphertext split at `pn_offset + pn_len`, so the GCM work shows `pn_len`.
#[allow(unused_imports)]
use crypto::aes::*;
#[allow(unused_imports)]
use crypto::gcm::*;
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;
use vstd::slice::slice_subrange;
#[allow(unused_imports)]
use wire::varint::*;

use crate::aead::*;
use crate::cid::LOCAL_CID_LEN;
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
/// `PN_MAX`, which `Connection::poll_transmit` ensures for every packet it returns (`pn <
/// PN_MAX`; proved in conn.rs by `lemma_transmit_pn_max` from P4 and `SentPackets::wf`).
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

/// An ack-eliciting Initial among the packets that have keys: the Initial space is keyed and an
/// Initial of `ps` is ack-eliciting.
pub open spec fn kept_eliciting_initial(ps: Seq<SpecOutPacket>, keys: Seq<Option<SpecKeyPair>>) -> bool {
    keys[space_idx(PacketKind::Initial)] is Some && has_eliciting_initial(ps)
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-14.1
//# Similarly, a server MUST expand the payload of all UDP
//# datagrams carrying ack-eliciting Initial packets to at least the
//# smallest allowed maximum datagram size of 1200 bytes.
/// Decision 4. Every packet keyed: all of them, in order. Otherwise, if an ack-eliciting
/// Initial would go out (its space is keyed), nothing: dropping an unkeyed packet would leave
/// it under 1200 bytes. Otherwise the keyed packets, in order; an unkeyed Initial is not on
/// the wire, so §14.1 does not hold the rest back.
pub open spec fn rfc_protect_datagram(d: SpecOutDatagram, keys: Seq<Option<SpecKeyPair>>) -> Seq<
    u8,
> {
    if all_keyed(d.packets, keys) {
        protect_keyed(d.packets, keys)
    } else if kept_eliciting_initial(d.packets, keys) {
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
    hide(has_eliciting_initial);
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
        // §14.1: a keyed ack-eliciting Initial goes out with the whole datagram or not at all.
        kept_eliciting_initial(d@.packets, keys.deep_view()) && final(out)@.len() > old(out)@.len()
            ==> final(out)@.len() == old(out)@.len() + out_datagram_len(d@),
{
    hide(rfc_protect);
    hide(has_eliciting_initial);
    hide(all_keyed);
    let ghost kd = keys.deep_view();
    let ghost ps = d@.packets;
    let ghost start = out@;
    proof {
        lemma_keyed_len(ps, kd);
    }
    let (all, elic) = scan(d, keys);
    assert(kd[0] == keys@[0].deep_view());
    if !all && elic && keys[0].is_some() {
        assert(rfc_protect_datagram(d@, kd) =~= Seq::<u8>::empty());
        assert(out@ =~= start + rfc_protect_datagram(d@, kd));
        return ;
    }
    protect_kept(d, keys, out);
}

/// Pass 2 of `protect_datagram`: each keyed packet, protected with its space's `tx` keys, in
/// order.
#[verifier::spinoff_prover]
fn protect_kept(d: &OutDatagram, keys: &[Option<KeyPair>; 3], out: &mut Vec<u8>)
    requires
        forall|i: int| 0 <= i < d@.packets.len() ==> protect_ok(#[trigger] d@.packets[i]),
    ensures
        final(out)@ == old(out)@ + protect_keyed(d@.packets, keys.deep_view()),
{
    hide(rfc_protect);
    hide(protect_ok);
    let ghost kd = keys.deep_view();
    let ghost ps = d@.packets;
    let ghost start = out@;
    assert(ps.take(0) =~= Seq::<SpecOutPacket>::empty());
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

// =============================================================================
// Receive side: specs
// =============================================================================

/// The packets of one received datagram, in order: those that decrypted and parsed, the first
/// connection error (which stops the datagram), and the last 16 bytes when the first packet
/// did not decrypt (a stateless reset candidate, RFC 9000 §10.3.1).
#[derive(Debug, PartialEq, Eq)]
pub struct Rx {
    pub packets: Vec<PlainPacket>,
    pub error: Option<(u64, PlainPacket)>,
    pub reset_tail: Option<[u8; 16]>,
}

pub struct SpecRx {
    pub packets: Seq<SpecPlain>,
    pub error: Option<(u64, SpecPlain)>,
    pub reset_tail: Option<Seq<u8>>,
}

pub open spec fn plains_view(ps: Seq<PlainPacket>) -> Seq<SpecPlain> {
    ps.map_values(|p: PlainPacket| p@)
}

pub open spec fn error_view(e: Option<(u64, PlainPacket)>) -> Option<(u64, SpecPlain)> {
    match e {
        Some((c, h)) => Some((c, h@)),
        None => None,
    }
}

impl View for Rx {
    type V = SpecRx;

    open spec fn view(&self) -> SpecRx {
        SpecRx {
            packets: plains_view(self.packets@),
            error: error_view(self.error),
            reset_tail: match self.reset_tail {
                Some(t) => Some(t@),
                None => None,
            },
        }
    }
}

/// `unprotect`'s result as a spec value (vstd has no `DeepView` for `Result`).
pub open spec fn unprotect_view(
    r: Result<(Option<PlainPacket>, usize), (u64, PlainPacket)>,
) -> Result<(Option<SpecPlain>, nat), (u64, SpecPlain)> {
    match r {
        Ok((p, n)) => Ok(
            (
                match p {
                    Some(q) => Some(q@),
                    None => None,
                },
                n as nat,
            ),
        ),
        Err((c, h)) => Err((c, h@)),
    }
}

pub open spec fn open_view(r: Option<(u64, Result<Vec<Frame>, u64>)>) -> Option<
    (u64, Result<Seq<SpecFrame>, u64>),
> {
    match r {
        None => None,
        Some((pn, Ok(v))) => Some((pn, Ok(frames_view(v@)))),
        Some((pn, Err(c))) => Some((pn, Err(c))),
    }
}

/// The largest packet number processed is at `PN_MAX` or above: no next packet number exists
/// in the space, and `decode_pn` requires one.
pub open spec fn pn_exhausted(largest: Option<u64>) -> bool {
    largest matches Some(l) && l >= PN_MAX
}

/// Header protection removal (Figure 6, the packet number length read after unmasking), packet
/// number recovery (RFC 9000 Appendix A.3) and AEAD with the unprotected header as associated
/// data (§5.3), over the packet `pkt` whose Packet Number field starts at `o`. `None` when AEAD
/// fails; otherwise the packet number and the payload's frames, or the connection error: the
/// reserved bits are checked only after both protections are removed.
pub open spec fn rfc_open(
    pkt: Seq<u8>,
    kind: PacketKind,
    o: nat,
    k: SpecKeys,
    largest: Option<u64>,
) -> Option<(u64, Result<Seq<SpecFrame>, u64>)> {
    let u = rfc_hp_remove(pkt, o, rfc_hp_mask(k.hp, rfc_sample(pkt, o)));
    let n = spec_pn_len(u[0]) as nat;
    let e = (o + n) as int;
    let pn = rfc_decode_pn(largest, be_val(u.subrange(o as int, e)) as u64, 8 * n) as u64;
    match spec_gcm_open(k.key, rfc_nonce(k.iv, pn), u.take(e), u.subrange(e, pkt.len() as int)) {
        None => None,
        Some(pt) => Some(
            (
                pn,
                if !spec_reserved_bits_zero(u[0], !(kind is OneRtt)) {
                    Err(PROTOCOL_VIOLATION)
                } else {
                    rfc_payload(pt, kind)
                },
            ),
        ),
    }
}

/// `rfc_unprotect` once the header is parsed: the packet `pkt` (its whole length) of kind
/// `kind`, Packet Number field at `o`. Every drop consumes the packet.
pub open spec fn rfc_unprotect_at(
    pkt: Seq<u8>,
    kind: PacketKind,
    dcid: Seq<u8>,
    scid: Seq<u8>,
    token: Seq<u8>,
    o: nat,
    keys: Seq<Option<SpecKeyPair>>,
    largest: Seq<Option<u64>>,
) -> Result<(Option<SpecPlain>, nat), (u64, SpecPlain)> {
    let end = pkt.len();
    let si = space_idx(kind);
    match keys[si] {
        None => Ok((None, end)),
        Some(kp) => if end < o + 20 || pn_exhausted(largest[si]) {
            Ok((None, end))
        } else {
            match rfc_open(pkt, kind, o, kp.rx, largest[si]) {
                None => Ok((None, end)),
                Some((pn, Err(c))) => Err(
                    (c, SpecPlain { kind, dcid, scid, token, pn, frames: Seq::empty() }),
                ),
                Some((pn, Ok(fs))) => Ok(
                    (Some(SpecPlain { kind, dcid, scid, token, pn, frames: fs }), end),
                ),
            }
        },
    }
}

/// The packet at the front of `b`, as a server receives it with the keys and largest packet
/// numbers of each space: `Ok((Some(p), n))` a packet, `Ok((None, n))` a drop, each consuming
/// `n` bytes (the rest of `b` for a short header, or what the header does not parse); `Err` a
/// connection error with the packet's header.
pub open spec fn rfc_unprotect(
    b: Seq<u8>,
    keys: Seq<Option<SpecKeyPair>>,
    largest: Seq<Option<u64>>,
) -> Result<(Option<SpecPlain>, nat), (u64, SpecPlain)> {
    if b.len() > MAX_UDP_PAYLOAD {
        Ok((None, b.len()))
    } else {
        match rfc_header(b, LOCAL_CID_LEN as nat) {
            Some(SpecHeader::Long { ty, dcid, scid, token, pn_offset, packet_end }) => if ty
                is ZeroRtt {
                Ok((None, packet_end))
            } else {
                rfc_unprotect_at(
                    b.take(packet_end as int),
                    if ty is Initial {
                        PacketKind::Initial
                    } else {
                        PacketKind::Handshake
                    },
                    dcid,
                    scid,
                    token,
                    pn_offset,
                    keys,
                    largest,
                )
            },
            Some(SpecHeader::Short { dcid, pn_offset }) => rfc_unprotect_at(
                b,
                PacketKind::OneRtt,
                dcid,
                Seq::empty(),
                Seq::empty(),
                pn_offset,
                keys,
                largest,
            ),
            _ => Ok((None, b.len())),
        }
    }
}

/// The packets of `d` from offset `off`, each `rfc_unprotect`ed in turn, and the first error.
pub open spec fn open_from(
    d: Seq<u8>,
    off: nat,
    keys: Seq<Option<SpecKeyPair>>,
    largest: Seq<Option<u64>>,
) -> (Seq<SpecPlain>, Option<(u64, SpecPlain)>)
    decreases d.len() - off,
{
    if off >= d.len() {
        (Seq::empty(), None)
    } else {
        match rfc_unprotect(d.skip(off as int), keys, largest) {
            Err(e) => (Seq::empty(), Some(e)),
            Ok((p, n)) => if n == 0 || off + n > d.len() {
                (Seq::empty(), None)
            } else {
                let r = open_from(d, off + n, keys, largest);
                (
                    match p {
                        Some(q) => seq![q] + r.0,
                        None => r.0,
                    },
                    r.1,
                )
            },
        }
    }
}

/// A received datagram: its packets in order, until the first error. A datagram longer than
/// any UDP payload is not opened.
pub open spec fn rfc_open_datagram(
    d: Seq<u8>,
    keys: Seq<Option<SpecKeyPair>>,
    largest: Seq<Option<u64>>,
) -> SpecRx {
    if d.len() > MAX_UDP_PAYLOAD {
        SpecRx { packets: Seq::empty(), error: None, reset_tail: None }
    } else {
        let r = open_from(d, 0, keys, largest);
        SpecRx {
            packets: r.0,
            error: r.1,
            reset_tail: if d.len() >= MIN_SHORT_PACKET && rfc_unprotect(d, keys, largest)
                matches Ok((None, _)) {
                Some(d.subrange(d.len() - RESET_TOKEN_LEN, d.len() as int))
            } else {
                None
            },
        }
    }
}

// =============================================================================
// Receive side: proofs
// =============================================================================

/// The bounds `rfc_header` guarantees: CIDs of at most 20 bytes, a long packet that ends
/// within `b` after its Packet Number field starts, a short one of at least 21 bytes.
proof fn lemma_header_bounds(b: Seq<u8>)
    ensures
        rfc_header(b, LOCAL_CID_LEN as nat) matches Some(
            SpecHeader::Long { dcid, scid, pn_offset, packet_end, .. },
        ) ==> dcid.len() <= MAX_CID_LEN && scid.len() <= MAX_CID_LEN && 7 <= pn_offset
            <= packet_end <= b.len(),
        rfc_header(b, LOCAL_CID_LEN as nat) matches Some(SpecHeader::Short { dcid, pn_offset })
            ==> dcid.len() == LOCAL_CID_LEN && pn_offset == 1 + LOCAL_CID_LEN && b.len()
            >= MIN_SHORT_PACKET,
{
    hide(rfc_varint_decode);
    if b.len() > 0 && b[0] & 0x80u8 != 0 && rfc_long_header(b) is Some {
        let d = b[5] as int;
        let s = b[6 + d] as int;
        let p = 7 + d + s;
        if let Some(SpecHeader::Long { ty, .. }) = rfc_long_header(b) {
            match rfc_token(b, ty, p) {
                Some((t, q)) => {
                    if ty == LongType::Initial {
                        lemma_decode_len_bounds(b.skip(p));
                    }
                    lemma_decode_len_bounds(b.skip(q));
                },
                None => {},
            }
        }
    }
}

/// What every `rfc_open` result satisfies: a packet number within `PN_MAX`, frames as
/// `parse_payload` returns them, and an error code of FRAME_ENCODING_ERROR or PROTOCOL_VIOLATION.
proof fn lemma_open_wf(pkt: Seq<u8>, kind: PacketKind, o: nat, k: SpecKeys, largest: Option<u64>)
    requires
        o + 20 <= pkt.len(),
        !pn_exhausted(largest),
    ensures
        rfc_open(pkt, kind, o, k, largest) matches Some((pn, res)) ==> pn <= PN_MAX
            && (res matches Ok(fs) ==> frames_received(fs, kind))
            && (res matches Err(c) ==> c == FRAME_ENCODING_ERROR || c == PROTOCOL_VIOLATION),
{
    hide(spec_aes128_encrypt);
    hide(spec_gcm_open);
    hide(rfc_payload);
    hide(rfc_decode_pn);
    let u = rfc_hp_remove(pkt, o, rfc_hp_mask(k.hp, rfc_sample(pkt, o)));
    assert(u.len() == pkt.len());
    let b0 = u[0];
    let n = spec_pn_len(b0);
    assert(1 <= n <= 4) by (bit_vector)
        requires
            n == ((b0 & 3u8) + 1) as u8,
    ;
    let s = u.subrange(o as int, o + n);
    lemma_be_val_bound(s);
    lemma2_to64();
    assert(pow2(8 * n as nat) <= pow2(32)) by {
        lemma_pow2_adds(8 * n as nat, 8 * (4 - n) as nat);
        lemma_pow2_pos(8 * (4 - n) as nat);
    }
    lemma_decode_pn_bound(largest, be_val(s) as u64, n);
    if let Some((pn, _)) = rfc_open(pkt, kind, o, k, largest) {
        let pn_i = rfc_decode_pn(largest, be_val(s) as u64, 8 * n as nat);
        assert(pn == pn_i as u64);
        let e = (o + n) as int;
        let ct = u.subrange(e, pkt.len() as int);
        if let Some(pt) = spec_gcm_open(k.key, rfc_nonce(k.iv, pn), u.take(e), ct) {
            theorem_payload_received_wf(pt, kind);
            theorem_payload_error_codes(pt, kind);
        }
    }
}

/// The facts `Connection` relies on (3d's `accept`, `on_datagram` and `close` require them):
/// a drop or packet consumes 1 to `b.len()` bytes, and a 1-RTT packet all of them; every packet
/// and error header is `plain_wf`; every error code fits a varint.
pub proof fn lemma_unprotect_wf(
    b: Seq<u8>,
    keys: Seq<Option<SpecKeyPair>>,
    largest: Seq<Option<u64>>,
)
    requires
        keys.len() == 3,
        largest.len() == 3,
    ensures
        rfc_unprotect(b, keys, largest) matches Ok((_, n)) ==> (b.len() > 0 ==> 0 < n <= b.len()),
        rfc_unprotect(b, keys, largest) matches Ok((Some(p), n)) ==> plain_wf(p)
            && (p.kind is OneRtt ==> n == b.len()),
        rfc_unprotect(b, keys, largest) matches Err((c, h)) ==> c <= VARINT_MAX && plain_wf(h),
        // A long header within a UDP payload: any packet or drop consumes exactly `packet_end`
        // (RFC 9000 §12.2), and 0-RTT is dropped whatever the keys (RFC 9001 §4.6.2).
        b.len() <= MAX_UDP_PAYLOAD ==> (rfc_header(b, LOCAL_CID_LEN as nat) matches Some(
            SpecHeader::Long { ty, packet_end, .. },
        ) ==> (rfc_unprotect(b, keys, largest) matches Ok((_, n)) ==> n == packet_end) && (ty
            is ZeroRtt ==> rfc_unprotect(b, keys, largest) == Ok::<
            (Option<SpecPlain>, nat),
            (u64, SpecPlain),
        >((None, packet_end)))),
{
    hide(rfc_open);
    hide(rfc_header);
    lemma_header_bounds(b);
    if b.len() <= MAX_UDP_PAYLOAD {
        match rfc_header(b, LOCAL_CID_LEN as nat) {
            Some(SpecHeader::Long { ty, dcid, scid, token, pn_offset, packet_end }) => {
                if !(ty is ZeroRtt) {
                    let kind = if ty is Initial {
                        PacketKind::Initial
                    } else {
                        PacketKind::Handshake
                    };
                    let pkt = b.take(packet_end as int);
                    if let Some(kp) = keys[space_idx(kind)] {
                        if !(pkt.len() < pn_offset + 20 || pn_exhausted(largest[space_idx(kind)])) {
                            lemma_open_wf(pkt, kind, pn_offset, kp.rx, largest[space_idx(kind)]);
                        }
                    }
                }
            },
            Some(SpecHeader::Short { dcid, pn_offset }) => {
                if let Some(kp) = keys[2] {
                    if !(b.len() < pn_offset + 20 || pn_exhausted(largest[2])) {
                        lemma_open_wf(b, PacketKind::OneRtt, pn_offset, kp.rx, largest[2]);
                    }
                }
            },
            _ => {},
        }
    }
}

/// Decoding a varint reads only the bytes it occupies.
proof fn lemma_decode_same(x: Seq<u8>, y: Seq<u8>, n: nat)
    requires
        rfc_varint_decode(x) matches Some((m, _)) && m == n,
        n <= y.len(),
        y.take(n as int) == x.take(n as int),
    ensures
        rfc_varint_decode(y) == rfc_varint_decode(x),
{
    lemma_decode_len_bounds(x);
    assert(y[0] == y.take(n as int)[0]);
    assert(x[0] == x.take(n as int)[0]);
    assert(y.subrange(1, n as int) =~= y.take(n as int).subrange(1, n as int));
    assert(x.subrange(1, n as int) =~= x.take(n as int).subrange(1, n as int));
}

/// `rfc_header` reads only what header protection leaves alone: the length, byte 0's high
/// nibble (long) or 3 high bits (short), and the bytes before the Packet Number field at `o`.
proof fn lemma_header_frame(a: Seq<u8>, u: Seq<u8>, o: nat)
    requires
        (rfc_header(u, LOCAL_CID_LEN as nat) matches Some(SpecHeader::Long { pn_offset, .. })
            && pn_offset == o) || (rfc_header(u, LOCAL_CID_LEN as nat) matches Some(
            SpecHeader::Short { pn_offset, .. },
        ) && pn_offset == o),
        a.len() == u.len(),
        u.len() > 0 && u[0] & 0x80u8 != 0 ==> a[0] & 0xf0u8 == u[0] & 0xf0u8,
        u.len() > 0 && u[0] & 0x80u8 == 0 ==> a[0] & 0xe0u8 == u[0] & 0xe0u8,
        a.subrange(1, o as int) == u.subrange(1, o as int),
    ensures
        rfc_header(a, LOCAL_CID_LEN as nat) == rfc_header(u, LOCAL_CID_LEN as nat),
{
    hide(rfc_varint_decode);
    let (a0, u0) = (a[0], u[0]);
    assert forall|i: int| 1 <= i < o implies a[i] == u[i] by {
        assert(a.subrange(1, o as int)[i - 1] == a[i]);
        assert(u.subrange(1, o as int)[i - 1] == u[i]);
    }
    if u0 & 0x80u8 == 0 {
        assert(a0 & 0x80u8 == 0 && (a0 & 0x40u8 == 0) == (u0 & 0x40u8 == 0)) by (bit_vector)
            requires
                a0 & 0xe0u8 == u0 & 0xe0u8,
                u0 & 0x80u8 == 0,
        ;
        assert(a.subrange(1, 1 + LOCAL_CID_LEN as int) =~= u.subrange(1, 1 + LOCAL_CID_LEN as int));
    } else {
        assert(a0 & 0x80u8 != 0 && (a0 & 0x40u8 == 0) == (u0 & 0x40u8 == 0) && (a0 >> 4u8) & 3u8
            == (u0 >> 4u8) & 3u8) by (bit_vector)
            requires
                a0 & 0xf0u8 == u0 & 0xf0u8,
                u0 & 0x80u8 != 0,
        ;
        let d = u[5] as int;
        let s = u[6 + d] as int;
        let p = 7 + d + s;
        let ty = spec_long_type(u0).unwrap();
        let (token, q) = rfc_token(u, ty, p).unwrap();
        if ty == LongType::Initial {
            lemma_decode_len_bounds(u.skip(p));
            let n = rfc_varint_decode(u.skip(p)).unwrap().0;
            assert(a.skip(p).take(n as int) =~= u.skip(p).take(n as int));
            lemma_decode_same(u.skip(p), a.skip(p), n);
            assert(a.subrange(p + n, q) =~= u.subrange(p + n, q));
        }
        assert(rfc_token(a, ty, p) == rfc_token(u, ty, p));
        lemma_decode_len_bounds(u.skip(q));
        let m = rfc_varint_decode(u.skip(q)).unwrap().0;
        assert(a.skip(q).take(m as int) =~= u.skip(q).take(m as int));
        lemma_decode_same(u.skip(q), a.skip(q), m);
        assert(spec_version(a) == spec_version(u));
        assert(a.subrange(6, 6 + d) =~= u.subrange(6, 6 + d));
        assert(a.subrange(7 + d, p) =~= u.subrange(7 + d, p));
    }
}

/// The header protection mask is 5 bytes.
proof fn lemma_mask_len(hp: Seq<u8>, s: Seq<u8>)
    ensures
        rfc_hp_mask(hp, s).len() == 5,
{
    hide(aes128_rounds);
}

/// The protected packet: `w`, the header and AEAD output, under header protection whose
/// sample is the same before and after.
proof fn lemma_protected_shape(p: SpecOutPacket, k: SpecKeys)
    requires
        protect_ok(p),
    ensures
        ({
            let h = spec_header_bytes(p);
            let o = (h.len() - p.pn_len) as nat;
            let w = h + spec_gcm_seal(k.key, rfc_nonce(k.iv, p.pn), h, spec_plaintext(p));
            let mask = rfc_hp_mask(k.hp, rfc_sample(w, o));
            &&& w.len() == out_packet_len(p)
            &&& 1 <= o
            &&& o + 20 <= w.len()
            &&& mask.len() == 5
            &&& rfc_protect(p, k) == rfc_hp_apply(w, o, mask)
            &&& rfc_sample(rfc_protect(p, k), o) == rfc_sample(w, o)
            &&& rfc_protect(p, k).len() == w.len()
            &&& rfc_protect(p, k).subrange(1, o as int) == w.subrange(1, o as int)
            &&& (w[0] & 0x80u8 == 0x80u8 ==> rfc_protect(p, k)[0] & 0xf0u8 == w[0] & 0xf0u8)
            &&& (w[0] & 0x80u8 != 0x80u8 ==> rfc_protect(p, k)[0] & 0xe0u8 == w[0] & 0xe0u8)
        }),
{
    hide(spec_aes128_encrypt);
    hide(spec_gcm_seal);
    let h = spec_header_bytes(p);
    let o = (h.len() - p.pn_len) as nat;
    let pt = spec_plaintext(p);
    let w = h + spec_gcm_seal(k.key, rfc_nonce(k.iv, p.pn), h, pt);
    let mask = rfc_hp_mask(k.hp, rfc_sample(w, o));
    lemma_header_len(p);
    lemma_gcm_open_seal(k.key, rfc_nonce(k.iv, p.pn), h, pt);
    assert(pt.len() == plaintext_len(p));
    lemma_mask_len(k.hp, rfc_sample(w, o));
    lemma_hp_frame(w, o, mask);
}

proof fn lemma_header_long(b: Seq<u8>)
    requires
        b.len() > 0,
        b[0] & 0x80u8 != 0,
    ensures
        rfc_header(b, LOCAL_CID_LEN as nat) == rfc_long_header(b),
{
    hide(rfc_long_header);
}

/// The facts both header lemmas start from: the unprotected `w + rest` and the protected
/// `prot + rest` agree on bytes 1 to `o`.
proof fn lemma_protected_prefix(p: SpecOutPacket, k: SpecKeys, rest: Seq<u8>)
    requires
        protect_ok(p),
    ensures
        ({
            let h = spec_header_bytes(p);
            let o = (h.len() - p.pn_len) as nat;
            let w = h + spec_gcm_seal(k.key, rfc_nonce(k.iv, p.pn), h, spec_plaintext(p));
            let prot = rfc_protect(p, k);
            &&& (prot + rest).len() == (w + rest).len()
            &&& (prot + rest).subrange(1, o as int) == (w + rest).subrange(1, o as int)
            &&& (prot + rest)[0] == prot[0]
            &&& (w + rest)[0] == w[0] == h[0]
            &&& spec_gcm_seal(k.key, rfc_nonce(k.iv, p.pn), h, spec_plaintext(p)).len()
                == plaintext_len(p) + AEAD_TAG_LEN
        }),
{
    hide(spec_aes128_encrypt);
    hide(spec_gcm_seal);
    hide(rfc_protect);
    hide(rfc_hp_apply);
    hide(spec_header_bytes);
    let h = spec_header_bytes(p);
    let o = (h.len() - p.pn_len) as nat;
    let pt = spec_plaintext(p);
    let w = h + spec_gcm_seal(k.key, rfc_nonce(k.iv, p.pn), h, pt);
    let prot = rfc_protect(p, k);
    lemma_protected_shape(p, k);
    lemma_header_len(p);
    lemma_gcm_open_seal(k.key, rfc_nonce(k.iv, p.pn), h, pt);
    assert(pt.len() == plaintext_len(p));
    assert((prot + rest).subrange(1, o as int) =~= prot.subrange(1, o as int));
    assert((w + rest).subrange(1, o as int) =~= w.subrange(1, o as int));
}

/// A protected long header parses as the unprotected one does (3b's round trip).
proof fn lemma_protected_long(p: SpecOutPacket, k: SpecKeys, rest: Seq<u8>)
    requires
        protect_ok(p),
        !(p.kind is OneRtt),
    ensures
        rfc_header(rfc_protect(p, k) + rest, LOCAL_CID_LEN as nat) == Some(
            SpecHeader::Long {
                ty: long_ty(p.kind),
                dcid: p.dcid,
                scid: p.scid,
                token: Seq::empty(),
                pn_offset: (spec_header_bytes(p).len() - p.pn_len) as nat,
                packet_end: out_packet_len(p),
            },
        ),
{
    hide(spec_aes128_encrypt);
    hide(spec_gcm_seal);
    hide(rfc_header);
    hide(rfc_long_header);
    hide(rfc_protect);
    hide(rfc_hp_apply);
    let h = spec_header_bytes(p);
    let n = p.pn_len;
    let o = (h.len() - n) as nat;
    let c = spec_gcm_seal(k.key, rfc_nonce(k.iv, p.pn), h, spec_plaintext(p));
    let w = h + c;
    let prot = rfc_protect(p, k);
    lemma_protected_shape(p, k);
    lemma_protected_prefix(p, k, rest);
    lemma_header_len(p);
    let ty = long_ty(p.kind);
    theorem_long_header_roundtrip(ty, p.dcid, p.scid, p.pn, n, c, rest);
    bv_long_first_byte(long_type_code(ty), (n - 1) as u8);
    let b0 = h[0];
    assert(b0 & 0x80u8 == 0x80u8) by (bit_vector)
        requires
            b0 & 0x80u8 != 0,
    ;
    lemma_header_long(w + rest);
    lemma_header_frame(prot + rest, w + rest, o);
}

/// A protected short header parses as the unprotected one does (3b's round trip).
proof fn lemma_protected_short(p: SpecOutPacket, k: SpecKeys)
    requires
        protect_ok(p),
        p.kind is OneRtt,
        p.dcid.len() == LOCAL_CID_LEN,
    ensures
        rfc_header(rfc_protect(p, k), LOCAL_CID_LEN as nat) == Some(
            SpecHeader::Short {
                dcid: p.dcid,
                pn_offset: (spec_header_bytes(p).len() - p.pn_len) as nat,
            },
        ),
{
    hide(spec_aes128_encrypt);
    hide(spec_gcm_seal);
    hide(rfc_header);
    hide(rfc_protect);
    hide(rfc_hp_apply);
    let h = spec_header_bytes(p);
    let n = p.pn_len;
    let o = (h.len() - n) as nat;
    let c = spec_gcm_seal(k.key, rfc_nonce(k.iv, p.pn), h, spec_plaintext(p));
    let w = h + c;
    let e = Seq::<u8>::empty();
    let prot = rfc_protect(p, k);
    lemma_protected_shape(p, k);
    lemma_protected_prefix(p, k, e);
    lemma_header_len(p);
    lemma_pn_roundtrip(p.pn, n as nat);
    theorem_short_header_roundtrip(p.dcid, false, p.spin, p.pn, n, c);
    bv_short_first_byte(
        if p.spin {
            0x20u8
        } else {
            0u8
        },
        0u8,
        (n - 1) as u8,
    );
    assert(prot + e =~= prot);
    assert(w + e =~= w);
    lemma_header_frame(prot, w, o);
}

/// What `rfc_open` reads of the unprotected header: the packet number length and zero
/// reserved bits from byte 0, and the packet number at the end.
proof fn lemma_header_pn(p: SpecOutPacket)
    requires
        protect_ok(p),
    ensures
        ({
            let h = spec_header_bytes(p);
            &&& spec_pn_len(h[0]) == p.pn_len
            &&& spec_reserved_bits_zero(h[0], !(p.kind is OneRtt))
            &&& h.subrange(h.len() - p.pn_len, h.len() as int) == pn_be(p.pn, p.pn_len as nat)
        }),
{
    let h = spec_header_bytes(p);
    let n = p.pn_len;
    let b0 = h[0];
    lemma_pn_roundtrip(p.pn, n as nat);
    if p.kind is OneRtt {
        bv_short_first_byte(
            if p.spin {
                0x20u8
            } else {
                0u8
            },
            0u8,
            (n - 1) as u8,
        );
        assert(h =~= (seq![b0] + p.dcid) + pn_be(p.pn, n as nat));
    } else {
        let ty = long_ty(p.kind);
        bv_long_first_byte(long_type_code(ty), (n - 1) as u8);
        assert(h =~= (spec_long_head(ty, p.dcid, p.scid, n) + spec_token_field(ty) + spec_varint(
            (n + (plaintext_len(p) + AEAD_TAG_LEN)) as u64,
        )) + pn_be(p.pn, n as nat));
    }
    assert(h.subrange(h.len() - n, h.len() as int) =~= pn_be(p.pn, n as nat));
}

/// Removing protection with the same keys gives back the packet number and the frames.
proof fn lemma_protected_open(p: SpecOutPacket, k: SpecKeys, largest: Option<u64>)
    requires
        protect_ok(p),
        forall|i: int| 0 <= i < p.frames.len() ==> !(#[trigger] p.frames[i] is HandshakeDone),
        expected_pn(largest) - pow2((8 * p.pn_len - 1) as nat) < p.pn <= expected_pn(largest)
            + pow2((8 * p.pn_len - 1) as nat),
    ensures
        rfc_open(
            rfc_protect(p, k),
            p.kind,
            (spec_header_bytes(p).len() - p.pn_len) as nat,
            k,
            largest,
        ) == Some((p.pn, Ok::<Seq<SpecFrame>, u64>(non_padding(p.frames)))),
{
    hide(spec_aes128_encrypt);
    hide(spec_gcm_seal);
    hide(spec_gcm_open);
    hide(rfc_payload);
    hide(rfc_header);
    hide(rfc_protect);
    hide(rfc_hp_remove);
    hide(rfc_hp_apply);
    hide(rfc_decode_pn);
    hide(pn_be);
    hide(be_val);
    hide(spec_header_bytes);
    let h = spec_header_bytes(p);
    let n = p.pn_len;
    let o = (h.len() - n) as nat;
    let pt = spec_plaintext(p);
    let c = spec_gcm_seal(k.key, rfc_nonce(k.iv, p.pn), h, pt);
    let w = h + c;
    let mask = rfc_hp_mask(k.hp, rfc_sample(w, o));
    lemma_protected_shape(p, k);
    lemma_header_len(p);
    lemma_hp_roundtrip(w, o, mask);
    lemma_header_pn(p);
    lemma_pn_roundtrip(p.pn, n as nat);
    assert(w[0] == h[0]);
    assert(w.subrange(o as int, o + n) =~= h.subrange(o as int, h.len() as int));
    theorem_decode_pn_recovers(p.pn, largest, n);
    lemma_gcm_open_seal(k.key, rfc_nonce(k.iv, p.pn), h, pt);
    assert(w.take(o + n) =~= h);
    assert(w.subrange(o + n, w.len() as int) =~= c);
    theorem_payload_padded(p.frames, p.padding, p.kind);
}

/// Unprotecting what `protect` wrote with the same keys gives back the packet: its header
/// fields, packet number and frames (PADDING dropped), consuming exactly the packet, whatever
/// follows it in the datagram. Needs: the packet number within half a window of the largest
/// one processed (`theorem_decode_pn_recovers`), no HANDSHAKE_DONE (a server rejects it), our
/// connection ID length on a short header, which ends the datagram, and a datagram within
/// `MAX_UDP_PAYLOAD`.
pub proof fn theorem_unprotect_protect(
    p: SpecOutPacket,
    k: SpecKeyPair,
    keys: Seq<Option<SpecKeyPair>>,
    largest: Seq<Option<u64>>,
    rest: Seq<u8>,
)
    requires
        protect_ok(p),
        keys[space_idx(p.kind)] == Some(k),
        forall|i: int| 0 <= i < p.frames.len() ==> !(#[trigger] p.frames[i] is HandshakeDone),
        p.kind is OneRtt ==> p.dcid.len() == LOCAL_CID_LEN && rest.len() == 0,
        largest[space_idx(p.kind)] matches Some(l) ==> l < PN_MAX,
        expected_pn(largest[space_idx(p.kind)]) - pow2((8 * p.pn_len - 1) as nat) < p.pn
            <= expected_pn(largest[space_idx(p.kind)]) + pow2((8 * p.pn_len - 1) as nat),
        out_packet_len(p) + rest.len() <= MAX_UDP_PAYLOAD,
    ensures
        rfc_unprotect(rfc_protect(p, k.rx) + rest, keys, largest) == Ok::<
            (Option<SpecPlain>, nat),
            (u64, SpecPlain),
        >(
            (
                Some(
                    SpecPlain {
                        kind: p.kind,
                        dcid: p.dcid,
                        scid: p.scid,
                        token: Seq::empty(),
                        pn: p.pn,
                        frames: non_padding(p.frames),
                    },
                ),
                out_packet_len(p),
            ),
        ),
{
    hide(spec_aes128_encrypt);
    hide(spec_gcm_seal);
    hide(rfc_open);
    hide(rfc_protect);
    hide(rfc_header);
    let o = (spec_header_bytes(p).len() - p.pn_len) as nat;
    let prot = rfc_protect(p, k.rx);
    let b = prot + rest;
    lemma_protected_shape(p, k.rx);
    if p.kind is OneRtt {
        lemma_protected_short(p, k.rx);
    } else {
        lemma_protected_long(p, k.rx, rest);
    }
    lemma_protected_open(p, k.rx, largest[space_idx(p.kind)]);
    assert(b.take(out_packet_len(p) as int) =~= prot);
    if p.kind is OneRtt {
        assert(b =~= prot);
        assert(p.scid =~= Seq::<u8>::empty());
    }
}

// =============================================================================
// Receive side: exec
// =============================================================================

/// HP removal, packet number recovery and AEAD, in that order, on the packet `pkt` (RFC 9001
/// §9.5: constant time in style, no branch or loop count on the packet number or its length;
/// `remove_hp` and `read_pn_masked` touch all 4 candidate bytes, `decode_pn` is masked).
#[verifier::spinoff_prover]
fn open_one(pkt: &[u8], kind: PacketKind, o: usize, k: &PacketKeys, largest: Option<u64>) -> (r:
    Option<(u64, Result<Vec<Frame>, u64>)>)
    requires
        o >= 1,
        o + 20 <= pkt.len() <= MAX_UDP_PAYLOAD,
        !pn_exhausted(largest),
    ensures
        open_view(r) == rfc_open(pkt@, kind, o as nat, k@, largest),
{
    hide(spec_aes128_encrypt);
    hide(spec_gcm_open);
    hide(rfc_payload);
    hide(rfc_decode_pn);
    let u = remove_hp(pkt, o, &k.hp);
    let ghost uv = u@;
    assert(uv.len() == pkt@.len());
    let n = first_byte_pn_len(u[0]);
    let t = read_pn_masked(slice_subrange(u.as_slice(), o, o + 4), n);
    assert(u@.subrange(o as int, o + 4).take(n as int) =~= u@.subrange(o as int, o + n));
    let pn = decode_pn(largest, t, n);
    let aad = slice_subrange(u.as_slice(), 0, o + n as usize);
    let ct = slice_subrange(u.as_slice(), o + n as usize, u.len());
    assert(aad@ =~= uv.take(o + n));
    assert(ct@ =~= uv.subrange(o + n, pkt@.len() as int));
    match open_packet(k, pn, aad, ct) {
        // A packet that fails AEAD is discarded (RFC 9001 §5.5); 3e has one key per space, so
        // the key-update cases of §5.5 are Phase 4's.
        None => None,
        Some(pt) => {
            let long = match kind {
                PacketKind::OneRtt => false,
                _ => true,
            };
            //= https://www.rfc-editor.org/rfc/rfc9000#section-17.2
            //# An endpoint MUST
            //# treat receipt of a packet that has a non-zero value for these bits
            //# after removing both packet and header protection as a connection
            //# error of type PROTOCOL_VIOLATION.
            //
            //= https://www.rfc-editor.org/rfc/rfc9000#section-17.3.1
            //# An endpoint MUST treat receipt of a
            //# packet that has a non-zero value for these bits, after removing
            //# both packet and header protection, as a connection error of type
            //# PROTOCOL_VIOLATION.
            if !reserved_bits_zero(u[0], long) {
                Some((pn, Err(PROTOCOL_VIOLATION)))
            } else {
                Some((pn, parse_payload(pt.as_slice(), kind)))
            }
        },
    }
}

/// `rfc_unprotect_at`: the drops before any decryption, then `open_one`.
#[verifier::spinoff_prover]
fn unprotect_at(
    pkt: &[u8],
    kind: PacketKind,
    dcid: Vec<u8>,
    scid: Vec<u8>,
    token: Vec<u8>,
    o: usize,
    keys: &[Option<KeyPair>; 3],
    largest: &[Option<u64>; 3],
) -> (r: Result<(Option<PlainPacket>, usize), (u64, PlainPacket)>)
    requires
        1 <= o <= pkt.len() <= MAX_UDP_PAYLOAD,
    ensures
        unprotect_view(r) == rfc_unprotect_at(
            pkt@,
            kind,
            dcid@,
            scid@,
            token@,
            o as nat,
            keys.deep_view(),
            largest@,
        ),
{
    hide(rfc_open);
    let si = sidx(kind);
    assert(keys.deep_view()[si as int] == keys@[si as int].deep_view());
    let end = pkt.len();
    let k = match &keys[si] {
        None => return Ok((None, end)),
        Some(kp) => &kp.rx,
    };
    let exhausted = match largest[si] {
        Some(l) => l >= PN_MAX,
        None => false,
    };
    //= https://www.rfc-editor.org/rfc/rfc9001#section-5.4.2
    //# An endpoint MUST discard packets that are not long enough to contain
    //# a complete sample.
    if end < o + 20 || exhausted {
        return Ok((None, end));
    }
    match open_one(pkt, kind, o, k, largest[si]) {
        None => Ok((None, end)),
        Some((pn, Err(c))) => {
            let frames = Vec::new();
            assert(frames_view(frames@) =~= Seq::<SpecFrame>::empty());
            Err((c, PlainPacket { kind, dcid, scid, token, pn, frames }))
        },
        Some((pn, Ok(frames))) => Ok(
            (Some(PlainPacket { kind, dcid, scid, token, pn, frames }), end),
        ),
    }
}

/// Removes protection from the packet at the front of `b` (RFC 9001 §5.3, §5.4): its header is
/// parsed with our connection ID length, and it is dropped, decrypted and parsed as
/// `rfc_unprotect` says. Packet numbers decode against `largest` in the packet's space.
#[verifier::spinoff_prover]
pub fn unprotect(b: &[u8], keys: &[Option<KeyPair>; 3], largest: &[Option<u64>; 3]) -> (r: Result<
    (Option<PlainPacket>, usize),
    (u64, PlainPacket),
>)
    ensures
        unprotect_view(r) == rfc_unprotect(b@, keys.deep_view(), largest@),
        r matches Ok((_, n)) ==> (b.len() > 0 ==> 0 < n <= b.len()),
        r matches Ok((Some(p), n)) ==> plain_wf(p@) && (p.kind is OneRtt ==> n == b.len()),
        r matches Err((c, h)) ==> c <= VARINT_MAX && plain_wf(h@),
        b.len() <= MAX_UDP_PAYLOAD ==> (rfc_header(b@, LOCAL_CID_LEN as nat) matches Some(
            SpecHeader::Long { ty, packet_end, .. },
        ) ==> (r matches Ok((_, n)) ==> n == packet_end) && (ty is ZeroRtt
            ==> unprotect_view(r) == Ok::<(Option<SpecPlain>, nat), (u64, SpecPlain)>(
            (None, packet_end),
        ))),
{
    hide(rfc_unprotect_at);
    hide(rfc_header);
    proof {
        lemma_unprotect_wf(b@, keys.deep_view(), largest@);
        lemma_header_bounds(b@);
    }
    if b.len() > MAX_UDP_PAYLOAD {
        return Ok((None, b.len()));
    }
    match parse_header(b, LOCAL_CID_LEN) {
        Some(Header::Long { ty, dcid, scid, token, pn_offset, packet_end }) => {
            let kind = match ty {
                // We always reject 0-RTT, so 0-RTT packets are dropped unprocessed (RFC 9001
                // §4.6.2), consuming the packet.
                LongType::ZeroRtt => return Ok((None, packet_end)),
                LongType::Initial => PacketKind::Initial,
                LongType::Handshake => PacketKind::Handshake,
            };
            let pkt = slice_subrange(b, 0, packet_end);
            assert(pkt@ =~= b@.take(packet_end as int));
            unprotect_at(pkt, kind, dcid, scid, token, pn_offset, keys, largest)
        },
        Some(Header::Short { dcid, pn_offset }) => unprotect_at(
            b,
            PacketKind::OneRtt,
            dcid,
            Vec::new(),
            Vec::new(),
            pn_offset,
            keys,
            largest,
        ),
        _ => Ok((None, b.len())),
    }
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-10.3.1
//# However, the comparison MUST be performed
//# when the first packet in an incoming datagram either cannot be
//# associated with a connection or cannot be decrypted.
/// The last 16 bytes of `d` when its first packet did not decrypt and `d` could be a stateless
/// reset (at least 21 bytes).
fn reset_candidate(d: &[u8], first_dropped: bool) -> (t: Option<[u8; 16]>)
    ensures
        t matches Some(x) ==> x@ == d@.subrange(d.len() - RESET_TOKEN_LEN, d.len() as int),
        t is Some <==> first_dropped && d.len() >= MIN_SHORT_PACKET,
{
    if !first_dropped || d.len() < MIN_SHORT_PACKET {
        return None;
    }
    let s = d.len() - 16;
    let t = [
        d[s],
        d[s + 1],
        d[s + 2],
        d[s + 3],
        d[s + 4],
        d[s + 5],
        d[s + 6],
        d[s + 7],
        d[s + 8],
        d[s + 9],
        d[s + 10],
        d[s + 11],
        d[s + 12],
        d[s + 13],
        d[s + 14],
        d[s + 15],
    ];
    assert(t@ =~= d@.subrange(s as int, d.len() as int));
    Some(t)
}

/// Opens a received datagram: `unprotect` from offset 0, advancing by the bytes each packet
/// consumes, keeping the packets in order, stopping at the first error.
// ponytail: one largest per space for the whole datagram; coalesced same-space packets
// decode against it.
#[verifier::spinoff_prover]
pub fn open_datagram(d: &[u8], keys: &[Option<KeyPair>; 3], largest: &[Option<u64>; 3]) -> (r: Rx)
    ensures
        r@ == rfc_open_datagram(d@, keys.deep_view(), largest@),
        forall|i: int| 0 <= i < r.packets.len() ==> plain_wf(#[trigger] r.packets@[i]@),
        r.error matches Some((c, h)) ==> c <= VARINT_MAX && plain_wf(h@),
        // 3d2 binding: a short header runs to the end of the datagram.
        forall|i: int|
            0 <= i < r.packets.len() && (#[trigger] r.packets@[i]).kind is OneRtt ==> i
                == r.packets.len() - 1,
{
    hide(rfc_unprotect);
    let ghost kd = keys.deep_view();
    let ghost lv = largest@;
    if d.len() > MAX_UDP_PAYLOAD {
        let r = Rx { packets: Vec::new(), error: None, reset_tail: None };
        assert(r@.packets =~= rfc_open_datagram(d@, kd, lv).packets);
        return r;
    }
    let mut packets: Vec<PlainPacket> = Vec::new();
    let mut first_dropped = false;
    let mut off: usize = 0;
    assert(d@.skip(0) =~= d@);
    assert(plains_view(packets@) + open_from(d@, 0, kd, lv).0 =~= open_from(d@, 0, kd, lv).0);
    while off < d.len()
        invariant
            off <= d.len() <= MAX_UDP_PAYLOAD,
            kd == keys.deep_view(),
            lv == largest@,
            d@.skip(0) == d@,
            open_from(d@, 0, kd, lv) == (
                plains_view(packets@) + open_from(d@, off as nat, kd, lv).0,
                open_from(d@, off as nat, kd, lv).1,
            ),
            off == 0 ==> !first_dropped && packets.len() == 0,
            off > 0 ==> first_dropped == (rfc_unprotect(d@, kd, lv) matches Ok((None, _))),
            forall|i: int| 0 <= i < packets.len() ==> plain_wf(#[trigger] packets@[i]@),
            forall|i: int|
                0 <= i < packets.len() && (#[trigger] packets@[i]).kind is OneRtt ==> i
                    == packets.len() - 1 && off == d.len(),
        decreases d.len() - off,
    {
        let b = slice_subrange(d, off, d.len());
        assert(b@ =~= d@.skip(off as int));
        let ghost acc = plains_view(packets@);
        let ghost before = off;
        let ghost prev = packets@;
        match unprotect(b, keys, largest) {
            Err((c, h)) => {
                let reset_tail = reset_candidate(d, first_dropped);
                let r = Rx { packets, error: Some((c, h)), reset_tail };
                assert(r@.packets =~= rfc_open_datagram(d@, kd, lv).packets);
                return r;
            },
            Ok((p, n)) => {
                if off == 0 && p.is_none() {
                    first_dropped = true;
                }
                match p {
                    Some(q) => {
                        packets.push(q);
                        proof {
                            assert(plains_view(packets@) =~= acc.push(q@));
                            assert forall|i: int| 0 <= i < packets.len() implies plain_wf(
                                #[trigger] packets@[i]@,
                            ) by {
                                if i < packets.len() - 1 {
                                    assert(packets@[i] == prev[i]);
                                }
                            }
                        }
                    },
                    None => {},
                }
                off = off + n;
                proof {
                    let r = open_from(d@, off as nat, kd, lv);
                    assert(open_from(d@, before as nat, kd, lv).1 == r.1);
                    let r0 = open_from(d@, before as nat, kd, lv).0;
                    assert(plains_view(packets@) + r.0 =~= acc + r0);
                }
            },
        }
    }
    let reset_tail = reset_candidate(d, first_dropped);
    let r = Rx { packets, error: None, reset_tail };
    assert(r@.packets =~= rfc_open_datagram(d@, kd, lv).packets);
    r
}

} // verus!
