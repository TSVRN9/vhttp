//! The protection boundary (3e): a received packet after header and payload decryption
//! (`PlainPacket`), and the packets of an outgoing datagram before protection (`OutPacket`,
//! `OutDatagram`), with their exact protected lengths (RFC 9000 §12.2, §14, §17.2-17.3;
//! RFC 9001 §5.4.2). 3e's `protect` produces `out_packet_len(p@)` bytes for each packet.
use vstd::prelude::*;
use wire::varint::*;

// Used only in ghost code, which a plain `cargo build` erases.
#[allow(unused_imports)]
use crate::codes::*;
use crate::frame::*;
use crate::payload::*;
#[allow(unused_imports)]
use crate::pn::*;

verus! {

pub type PathId = u64;

//= https://www.rfc-editor.org/rfc/rfc9000#section-14.2
//# In
//# the absence of these mechanisms, QUIC endpoints SHOULD NOT send
//# datagrams larger than the smallest allowed maximum datagram size.
//
// §14.2's cease-sending MUST (a path that cannot carry 1200 bytes): a failed MTU probe sets
// `Paths::mtu_failed`, and conn.rs's send gate cites it there.
/// Our maximum datagram size: no PMTU discovery, so the smallest allowed one.
pub const MAX_DATAGRAM: usize = 1200;

/// AEAD_AES_128_GCM's tag (RFC 9001 §5.3).
pub const AEAD_TAG_LEN: usize = 16;

/// The packet number and payload together span at least 4 bytes, so the header protection
/// sample (16 bytes from `pn_offset + 4`) lies inside the packet (RFC 9001 §5.4.2).
pub const MIN_PN_AND_PAYLOAD: usize = 4;

// =============================================================================
// Received packets
// =============================================================================

/// A received packet after decryption: the header fields and the parsed frames.
#[derive(Debug, PartialEq, Eq)]
pub struct PlainPacket {
    pub kind: PacketKind,
    pub dcid: Vec<u8>,
    pub scid: Vec<u8>,
    pub token: Vec<u8>,
    pub pn: u64,
    pub frames: Vec<Frame>,
}

pub struct SpecPlain {
    pub kind: PacketKind,
    pub dcid: Seq<u8>,
    pub scid: Seq<u8>,
    pub token: Seq<u8>,
    pub pn: u64,
    pub frames: Seq<SpecFrame>,
}

impl View for PlainPacket {
    type V = SpecPlain;

    open spec fn view(&self) -> SpecPlain {
        SpecPlain {
            kind: self.kind,
            dcid: self.dcid@,
            scid: self.scid@,
            token: self.token@,
            pn: self.pn,
            frames: frames_view(self.frames@),
        }
    }
}

/// What 3e guarantees of a packet it hands over: the frames `parse_payload` accepts (each
/// `frame_wf`, permitted, neither PADDING nor HANDSHAKE_DONE), CIDs of at most 20 bytes,
/// and a decoded packet number within `PN_MAX`.
pub open spec fn plain_wf(p: SpecPlain) -> bool {
    &&& frames_received(p.frames, p.kind)
    &&& p.dcid.len() <= MAX_CID_LEN
    &&& p.scid.len() <= MAX_CID_LEN
    &&& p.pn <= PN_MAX
}

// =============================================================================
// Outgoing packets and their lengths
// =============================================================================

/// A packet to protect and send. `padding` zero bytes (PADDING frames) follow the frames;
/// `spin` is the 1-RTT spin bit, ignored for long headers.
#[derive(Debug, PartialEq, Eq)]
pub struct OutPacket {
    pub kind: PacketKind,
    pub dcid: Vec<u8>,
    pub scid: Vec<u8>,
    pub pn: u64,
    pub pn_len: u8,
    pub frames: Vec<Frame>,
    pub padding: usize,
    pub spin: bool,
}

pub struct SpecOutPacket {
    pub kind: PacketKind,
    pub dcid: Seq<u8>,
    pub scid: Seq<u8>,
    pub pn: u64,
    pub pn_len: u8,
    pub frames: Seq<SpecFrame>,
    pub padding: nat,
    pub spin: bool,
}

impl View for OutPacket {
    type V = SpecOutPacket;

    open spec fn view(&self) -> SpecOutPacket {
        SpecOutPacket {
            kind: self.kind,
            dcid: self.dcid@,
            scid: self.scid@,
            pn: self.pn,
            pn_len: self.pn_len,
            frames: frames_view(self.frames@),
            padding: self.padding as nat,
            spin: self.spin,
        }
    }
}

/// The packets of one UDP datagram, in order, on path `path`.
#[derive(Debug, PartialEq, Eq)]
pub struct OutDatagram {
    pub path: PathId,
    pub packets: Vec<OutPacket>,
}

pub struct SpecOutDatagram {
    pub path: u64,
    pub packets: Seq<SpecOutPacket>,
}

pub open spec fn packets_view(ps: Seq<OutPacket>) -> Seq<SpecOutPacket> {
    ps.map_values(|p: OutPacket| p@)
}

impl View for OutDatagram {
    type V = SpecOutDatagram;

    open spec fn view(&self) -> SpecOutDatagram {
        SpecOutDatagram { path: self.path, packets: packets_view(self.packets@) }
    }
}

/// The frames' bytes, without the padding.
pub open spec fn frames_len(p: SpecOutPacket) -> nat {
    spec_frames_bytes(p.frames).len()
}

/// The payload before protection: the frames, then `padding` zero bytes.
pub open spec fn plaintext_len(p: SpecOutPacket) -> nat {
    frames_len(p) + p.padding
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-17.2
//# Length:  This is the length of the remainder of the packet (that is,
//# the Packet Number and Payload fields) in bytes, encoded as a
//# variable-length integer (Section 16).
/// A long header's Length: the packet number and the protected payload.
pub open spec fn length_field(p: SpecOutPacket) -> nat {
    (p.pn_len + plaintext_len(p) + AEAD_TAG_LEN) as nat
}

/// The packet's protected length. Long headers: first byte, Version, both CIDs with their
/// length bytes (7 + |dcid| + |scid|), Token Length 0 for Initial (`+ 1`), Length, the packet
/// number, the payload and the tag. Short headers: first byte, DCID, packet number, payload
/// and tag.
pub open spec fn out_packet_len(p: SpecOutPacket) -> nat {
    match p.kind {
        PacketKind::OneRtt => (1 + p.dcid.len() + p.pn_len + plaintext_len(p) + AEAD_TAG_LEN) as nat,
        PacketKind::Initial => (7 + p.dcid.len() + p.scid.len() + 1 + rfc_varint_min_len(
            length_field(p) as u64,
        ) + p.pn_len + plaintext_len(p) + AEAD_TAG_LEN) as nat,
        PacketKind::Handshake => (7 + p.dcid.len() + p.scid.len() + rfc_varint_min_len(
            length_field(p) as u64,
        ) + p.pn_len + plaintext_len(p) + AEAD_TAG_LEN) as nat,
    }
}

pub open spec fn packets_len(s: Seq<SpecOutPacket>) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        packets_len(s.drop_last()) + out_packet_len(s.last())
    }
}

pub open spec fn out_datagram_len(d: SpecOutDatagram) -> nat {
    packets_len(d.packets)
}

/// What measuring a packet needs: frames `serialize_payload` accepts, a 1-4 byte packet
/// number, CIDs of at most 20 bytes, and a Length that fits a 2-byte varint.
pub open spec fn out_packet_sized(p: SpecOutPacket) -> bool {
    &&& p.frames.len() >= 1
    &&& frames_sendable(p.frames, p.kind)
    &&& 1 <= p.pn_len <= 4
    &&& p.dcid.len() <= MAX_CID_LEN
    &&& p.scid.len() <= MAX_CID_LEN
    &&& length_field(p) < 16384
}

/// A packet 3e may protect: `out_packet_sized`, a packet number length that is
/// `pn_encode_len`'s answer for `largest_acked`, room for the header protection sample, and
/// no Source Connection ID in a short header.
pub open spec fn out_packet_wf(p: SpecOutPacket, largest_acked: Option<u64>) -> bool {
    &&& out_packet_sized(p)
    &&& pn_len_ok(p.pn, largest_acked, p.pn_len as nat)
    &&& forall|m: nat| 1 <= m < p.pn_len ==> !pn_len_ok(p.pn, largest_acked, m)
    &&& p.pn_len + plaintext_len(p) >= MIN_PN_AND_PAYLOAD
    &&& p.kind is OneRtt ==> p.scid.len() == 0
}

/// Up to one packet per number space, each measurable.
pub open spec fn out_datagram_sized(d: SpecOutDatagram) -> bool {
    &&& d.packets.len() <= 3
    &&& forall|i: int| 0 <= i < d.packets.len() ==> out_packet_sized(#[trigger] d.packets[i])
}

/// `p` with `x` more padding bytes.
pub open spec fn padded(p: SpecOutPacket, x: nat) -> SpecOutPacket {
    SpecOutPacket { padding: p.padding + x, ..p }
}

pub open spec fn is_long(p: SpecOutPacket) -> bool {
    !(p.kind is OneRtt)
}

/// `s` with packet `i` padded by `pad_amount`.
pub open spec fn pad_result(s: Seq<SpecOutPacket>, i: int, target: nat) -> Seq<SpecOutPacket> {
    s.update(i, padded(s[i], pad_amount(s, i, target) as nat))
}

/// The padding `pad_datagram` adds to packet `i` to reach `target`: the gap, less the byte a
/// long header's Length gains when it grows from one byte to two.
pub open spec fn pad_amount(s: Seq<SpecOutPacket>, i: int, target: nat) -> int {
    let gap = target - packets_len(s);
    if is_long(s[i]) && length_field(s[i]) < 64 {
        gap - 1
    } else {
        gap
    }
}

// =============================================================================
// Proofs
// =============================================================================

/// The bytes outside a packet's Length value (or its analogue, for a short header) number
/// at most 50.
proof fn lemma_overhead(p: SpecOutPacket)
    requires
        out_packet_sized(p),
    ensures
        length_field(p) < out_packet_len(p) <= length_field(p) + 50,
{
}

/// Padding `x` more bytes grows the packet by `x`, plus one when a long header's Length
/// varint grows from one byte to two.
proof fn lemma_pad_one(p: SpecOutPacket, x: nat)
    requires
        out_packet_sized(p),
        length_field(p) + x < 16384,
    ensures
        out_packet_sized(padded(p, x)),
        length_field(padded(p, x)) == length_field(p) + x,
        out_packet_len(padded(p, x)) == out_packet_len(p) + x + (if is_long(p) && length_field(p)
            < 64 && length_field(p) + x >= 64 {
            1int
        } else {
            0
        }),
{
}

proof fn lemma_packets_len_update(s: Seq<SpecOutPacket>, i: int, q: SpecOutPacket)
    requires
        0 <= i < s.len(),
    ensures
        packets_len(s.update(i, q)) + out_packet_len(s[i]) == packets_len(s) + out_packet_len(q),
    decreases s.len(),
{
    let u = s.update(i, q);
    if i == s.len() - 1 {
        assert(u.drop_last() =~= s.drop_last());
    } else {
        assert(u.drop_last() =~= s.drop_last().update(i, q));
        lemma_packets_len_update(s.drop_last(), i, q);
    }
}

proof fn lemma_packets_len_le(s: Seq<SpecOutPacket>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        out_packet_len(s[i]) <= packets_len(s),
    decreases s.len(),
{
    if i < s.len() - 1 {
        lemma_packets_len_le(s.drop_last(), i);
    }
}

proof fn lemma_packets_len_bound(s: Seq<SpecOutPacket>, m: nat)
    requires
        forall|j: int| 0 <= j < s.len() ==> out_packet_len(#[trigger] s[j]) <= m,
    ensures
        packets_len(s) <= s.len() * m,
    decreases s.len(),
{
    if s.len() > 0 {
        let t = s.drop_last();
        assert forall|j: int| 0 <= j < t.len() implies out_packet_len(#[trigger] t[j]) <= m by {
            assert(t[j] == s[j]);
        }
        lemma_packets_len_bound(t, m);
        assert(packets_len(s) <= s.len() * m) by (nonlinear_arith)
            requires
                packets_len(s) == packets_len(t) + out_packet_len(s.last()),
                packets_len(t) <= t.len() * m,
                out_packet_len(s.last()) <= m,
                t.len() + 1 == s.len(),
        ;
    }
}

/// Padding packet `i`, the first with the most packet number and plaintext bytes, by
/// `pad_amount` makes the datagram exactly `target` bytes. Each packet's bytes outside its
/// Length value are at most 50, so with at most 3 packets the padded Length ends at least
/// (1200 - 150) / 3 = 350 > 63; a Length below 64 was therefore 1 byte and becomes 2
/// (never more: it stays below 16384), and the datagram was then at most 3 · (50 + 63) =
/// 339 bytes, so the gap is positive.
pub proof fn lemma_pad_exact(s: Seq<SpecOutPacket>, i: int, target: nat)
    requires
        1 <= s.len() <= 3,
        forall|j: int| 0 <= j < s.len() ==> out_packet_sized(#[trigger] s[j]),
        0 <= i < s.len(),
        forall|j: int|
            0 <= j < s.len() ==> (#[trigger] s[j]).pn_len + plaintext_len(s[j]) <= s[i].pn_len
                + plaintext_len(s[i]),
        packets_len(s) <= target,
        MIN_INITIAL_DATAGRAM <= target <= MAX_DATAGRAM,
    ensures
        pad_amount(s, i, target) >= 0,
        packets_len(pad_result(s, i, target)) == target,
        forall|k: int|
            0 <= k < s.len() ==> out_packet_sized(#[trigger] pad_result(s, i, target)[k]),
        forall|k: int, la: Option<u64>|
            #![trigger out_packet_wf(pad_result(s, i, target)[k], la)]
            0 <= k < s.len() && out_packet_wf(s[k], la) ==> out_packet_wf(
                pad_result(s, i, target)[k],
                la,
            ),
{
    let lf = length_field(s[i]);
    assert forall|j: int| 0 <= j < s.len() implies out_packet_len(#[trigger] s[j]) <= 50 + lf by {
        lemma_overhead(s[j]);
    }
    lemma_packets_len_bound(s, 50 + lf);
    assert(packets_len(s) <= 3 * (50 + lf)) by (nonlinear_arith)
        requires
            packets_len(s) <= s.len() * (50 + lf),
            s.len() <= 3,
    ;
    lemma_packets_len_le(s, i);
    lemma_overhead(s[i]);
    let x = pad_amount(s, i, target);
    assert(x >= 0);
    lemma_pad_one(s[i], x as nat);
    lemma_packets_len_update(s, i, padded(s[i], x as nat));
    let u = pad_result(s, i, target);
    assert forall|k: int| 0 <= k < s.len() implies out_packet_sized(#[trigger] u[k]) by {
        if k != i {
            assert(u[k] == s[k]);
        }
    }
    assert forall|k: int, la: Option<u64>|
        #![trigger out_packet_wf(u[k], la)]
        0 <= k < s.len() && out_packet_wf(s[k], la) implies out_packet_wf(u[k], la) by {
        if k != i {
            assert(u[k] == s[k]);
        }
    }
}

// =============================================================================
// Executable code
// =============================================================================

// ponytail: measures frames by serializing them into a scratch buffer (at most 16 KiB of our
// own frames, never peer-sized); a per-variant frame_len if 3e profiles this as hot.
fn frames_byte_len(frames: &Vec<Frame>, kind: PacketKind) -> (n: usize)
    requires
        frames.len() >= 1,
        frames_sendable(frames_view(frames@), kind),
    ensures
        n == spec_frames_bytes(frames_view(frames@)).len(),
{
    let mut buf: Vec<u8> = Vec::new();
    serialize_payload(frames.as_slice(), kind, &mut buf);
    assert(buf@ =~= spec_frames_bytes(frames_view(frames@)));
    buf.len()
}

/// `plaintext_len(p@)`.
fn plain_len(p: &OutPacket) -> (n: usize)
    requires
        out_packet_sized(p@),
    ensures
        n == plaintext_len(p@),
{
    frames_byte_len(&p.frames, p.kind) + p.padding
}

/// The packet's protected length, given its plaintext length `pt`.
fn len_from(p: &OutPacket, pt: usize) -> (n: usize)
    requires
        out_packet_sized(p@),
        pt == plaintext_len(p@),
    ensures
        n == out_packet_len(p@),
{
    let lf = p.pn_len as usize + pt + AEAD_TAG_LEN;
    match p.kind {
        PacketKind::OneRtt => 1 + p.dcid.len() + p.pn_len as usize + pt + AEAD_TAG_LEN,
        PacketKind::Initial => 7 + p.dcid.len() + p.scid.len() + 1 + varint_len(lf as u64)
            + p.pn_len as usize + pt + AEAD_TAG_LEN,
        PacketKind::Handshake => 7 + p.dcid.len() + p.scid.len() + varint_len(lf as u64)
            + p.pn_len as usize + pt + AEAD_TAG_LEN,
    }
}

/// The packet's protected length.
pub fn packet_len(p: &OutPacket) -> (n: usize)
    requires
        out_packet_sized(p@),
    ensures
        n == out_packet_len(p@),
{
    len_from(p, plain_len(p))
}

/// The datagram's length: its packets' protected lengths summed.
pub fn datagram_len(d: &OutDatagram) -> (n: usize)
    requires
        out_datagram_sized(d@),
    ensures
        n == out_datagram_len(d@),
{
    let ghost s = d@.packets;
    let mut total: usize = 0;
    let mut j: usize = 0;
    while j < d.packets.len()
        invariant
            s == d@.packets,
            out_datagram_sized(d@),
            j <= s.len(),
            total == packets_len(s.take(j as int)),
            total <= 16434 * j,
        decreases s.len() - j,
    {
        let ghost sj = s.take(j as int + 1);
        proof {
            assert(sj.drop_last() =~= s.take(j as int));
            assert(sj.last() == s[j as int]);
            lemma_overhead(s[j as int]);
        }
        total = total + packet_len(&d.packets[j]);
        j += 1;
    }
    assert(s.take(j as int) =~= s);
    total
}

/// Pads `p` so its packet number and payload span at least 4 bytes (`MIN_PN_AND_PAYLOAD`):
/// `padding = max(padding, 4 - pn_len - frames_len)`.
pub fn add_sample_padding(p: &mut OutPacket)
    requires
        out_packet_sized(old(p)@),
    ensures
        final(p)@ == padded(old(p)@, (final(p)@.padding - old(p)@.padding) as nat),
        final(p)@.padding == if old(p)@.pn_len + plaintext_len(old(p)@) < MIN_PN_AND_PAYLOAD {
            MIN_PN_AND_PAYLOAD - old(p)@.pn_len - frames_len(old(p)@)
        } else {
            old(p)@.padding as int
        },
        out_packet_sized(final(p)@),
        final(p)@.pn_len + plaintext_len(final(p)@) >= MIN_PN_AND_PAYLOAD,
{
    let f = frames_byte_len(&p.frames, p.kind);
    let used = p.pn_len as usize + f + p.padding;
    if used < MIN_PN_AND_PAYLOAD {
        p.padding = MIN_PN_AND_PAYLOAD - p.pn_len as usize - f;
    }
}

proof fn lemma_take_step(s: Seq<SpecOutPacket>, j: int)
    requires
        0 <= j < s.len(),
    ensures
        packets_len(s.take(j + 1)) == packets_len(s.take(j)) + out_packet_len(s[j]),
{
    assert(s.take(j + 1).drop_last() =~= s.take(j));
}

/// The first packet with the most packet number and plaintext bytes, its Length, and the
/// datagram length; each packet is serialized once.
#[verifier::spinoff_prover]
fn pick(ps: &Vec<OutPacket>) -> (r: (usize, usize, usize))
    requires
        1 <= ps.len() <= 3,
        forall|k: int| 0 <= k < ps.len() ==> out_packet_sized(#[trigger] ps@[k]@),
    ensures
        r.0 < ps.len(),
        r.1 == length_field(ps@[r.0 as int]@),
        r.2 == packets_len(packets_view(ps@)),
        forall|k: int|
            0 <= k < ps.len() ==> (#[trigger] ps@[k]@).pn_len + plaintext_len(ps@[k]@)
                <= ps@[r.0 as int]@.pn_len + plaintext_len(ps@[r.0 as int]@),
{
    let ghost s = packets_view(ps@);
    let pt0 = plain_len(&ps[0]);
    let mut best_i: usize = 0;
    let mut best: usize = ps[0].pn_len as usize + pt0;
    let mut total: usize = len_from(&ps[0], pt0);
    let mut j: usize = 1;
    proof {
        lemma_take_step(s, 0);
        assert(s.take(0) =~= Seq::<SpecOutPacket>::empty());
        lemma_overhead(ps@[0]@);
    }
    while j < ps.len()
        invariant
            s == packets_view(ps@),
            1 <= ps.len() <= 3,
            forall|k: int| 0 <= k < ps.len() ==> out_packet_sized(#[trigger] ps@[k]@),
            1 <= j <= ps.len(),
            best_i < ps.len(),
            best == ps@[best_i as int]@.pn_len + plaintext_len(ps@[best_i as int]@),
            forall|k: int|
                0 <= k < j ==> (#[trigger] ps@[k]@).pn_len + plaintext_len(ps@[k]@) <= best,
            total == packets_len(s.take(j as int)),
            total <= 16434 * j,
        decreases ps.len() - j,
    {
        proof {
            lemma_take_step(s, j as int);
            lemma_overhead(ps@[j as int]@);
        }
        let pt = plain_len(&ps[j]);
        let q = ps[j].pn_len as usize + pt;
        if q > best {
            best = q;
            best_i = j;
        }
        total = total + len_from(&ps[j], pt);
        j += 1;
    }
    assert(s.take(j as int) =~= s);
    (best_i, best + AEAD_TAG_LEN, total)
}

/// Pads one packet of `d` (the first with the most packet number and plaintext bytes) so the
/// datagram is exactly `target` bytes. 3d2 calls it with 1200 for every datagram that carries
/// an ack-eliciting Initial.
#[verifier::spinoff_prover]
pub fn pad_datagram(d: &mut OutDatagram, target: usize)
    requires
        1 <= old(d)@.packets.len() <= 3,
        out_datagram_sized(old(d)@),
        out_datagram_len(old(d)@) <= target,
        MIN_INITIAL_DATAGRAM <= target <= MAX_DATAGRAM,
    ensures
        final(d)@.path == old(d)@.path,
        final(d)@.packets.len() == old(d)@.packets.len(),
        out_datagram_len(final(d)@) == target,
        out_datagram_sized(final(d)@),
        exists|i: int|
            #![trigger final(d)@.packets[i]]
            0 <= i < old(d)@.packets.len() && final(d)@.packets == old(d)@.packets.update(
                i,
                padded(old(d)@.packets[i], (final(d)@.packets[i].padding - old(d)@.packets[i].padding) as nat),
            ) && final(d)@.packets[i].padding >= old(d)@.packets[i].padding,
        forall|i: int, la: Option<u64>|
            #![trigger out_packet_wf(final(d)@.packets[i], la)]
            0 <= i < old(d)@.packets.len() && out_packet_wf(old(d)@.packets[i], la) ==> out_packet_wf(
                final(d)@.packets[i],
                la,
            ),
{
    let ghost s = old(d)@.packets;
    proof {
        assert forall|k: int| 0 <= k < d.packets.len() implies out_packet_sized(
            #[trigger] d.packets@[k]@,
        ) by {
            assert(s[k] == d.packets@[k]@);
        }
    }
    let (i, lf, total) = pick(&d.packets);
    let gap = target - total;
    let long = match d.packets[i].kind {
        PacketKind::OneRtt => false,
        _ => true,
    };
    proof {
        lemma_pad_exact(s, i as int, target as nat);
    }
    let x = if long && lf < 64 {
        gap - 1
    } else {
        gap
    };
    let ghost ps0 = d.packets@;
    let mut p = d.packets.remove(i);
    p.padding = p.padding + x;
    d.packets.insert(i, p);
    proof {
        // The padding is `lemma_pad_exact`'s: the gap, less one for a 1-byte Length.
        assert(x == pad_amount(s, i as int, target as nat));
        let q = padded(s[i as int], x as nat);
        assert(p@ == q);
        assert(d.packets@ =~= ps0.update(i as int, p));
        assert(d@.packets =~= pad_result(s, i as int, target as nat));
        assert(d@.packets[i as int].padding - s[i as int].padding == x);
    }
}

} // verus!
