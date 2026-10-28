//! QUIC packet payloads (RFC 9000 §12.4, §12.5): a payload is a sequence of whole frames,
//! and each packet type admits only some frame types.
use vstd::prelude::*;
use vstd::slice::slice_subrange;
// Used only in ghost code, which a plain `cargo build` erases.
#[allow(unused_imports)]
use wire::varint::*;

// Used only in ghost code, which a plain `cargo build` erases.
#[allow(unused_imports)]
use crate::ack::*;
use crate::codes::*;
use crate::frame::*;

verus! {

/// The packet types whose payloads carry frames. 0-RTT is absent: a server discards 0-RTT
/// packets before reading their payload.
#[derive(Clone, Copy)]
pub enum PacketKind {
    Initial,
    Handshake,
    OneRtt,
}

// =============================================================================
// RFC 9000 transcription
// =============================================================================

// RFC 9000 Table 3, "Pkts" and "Spec" columns (I Initial, H Handshake, 0 0-RTT, 1 1-RTT;
// "ih": only type 0x1c in Initial or Handshake):
//
//   0x00       PADDING              IH01  NP
//   0x01       PING                 IH01
//   0x02-0x03  ACK                  IH_1  NC
//   0x04       RESET_STREAM         __01
//   0x05       STOP_SENDING         __01
//   0x06       CRYPTO               IH_1
//   0x07       NEW_TOKEN            ___1
//   0x08-0x0f  STREAM               __01  F
//   0x10       MAX_DATA             __01
//   0x11       MAX_STREAM_DATA      __01
//   0x12-0x13  MAX_STREAMS          __01
//   0x14       DATA_BLOCKED         __01
//   0x15       STREAM_DATA_BLOCKED  __01
//   0x16-0x17  STREAMS_BLOCKED      __01
//   0x18       NEW_CONNECTION_ID    __01  P
//   0x19       RETIRE_CONNECTION_ID __01
//   0x1a       PATH_CHALLENGE       __01  P
//   0x1b       PATH_RESPONSE        ___1  P
//   0x1c-0x1d  CONNECTION_CLOSE     ih01  N
//   0x1e       HANDSHAKE_DONE       ___1
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-12.4
//# Note
//# that all frames can appear in 1-RTT packets.  An endpoint MUST treat
//# receipt of a frame in a packet type that is not permitted as a
//# connection error of type PROTOCOL_VIOLATION.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-17.2.4
//# The payload of this packet contains CRYPTO frames and could contain
//# PING, PADDING, or ACK frames.  Handshake packets MAY contain
//# CONNECTION_CLOSE frames of type 0x1c.  Endpoints MUST treat receipt
//# of Handshake packets with other frames as a connection error of type
//# PROTOCOL_VIOLATION.
/// Whether a frame of type `ty` may appear in a packet of kind `k`.
pub open spec fn frame_permitted(ty: u64, k: PacketKind) -> bool {
    match k {
        PacketKind::OneRtt => ty <= FRAME_HANDSHAKE_DONE,
        _ => ty == FRAME_PADDING || ty == FRAME_PING || ty == FRAME_ACK || ty == FRAME_ACK_ECN
            || ty == FRAME_CRYPTO || ty == FRAME_CONNECTION_CLOSE,
    }
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-12.4
//# N:   Packets containing only frames with this marking are not ack-
//# eliciting; see Section 13.2.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-13.2
//# However,
//# only ack-eliciting packets cause an ACK frame to be sent within the
//# maximum ack delay.
/// Whether a frame of type `ty` makes its packet ack-eliciting (Table 3 "N" is unmarked).
pub open spec fn ack_eliciting(ty: u64) -> bool {
    !(ty == FRAME_PADDING || ty == FRAME_ACK || ty == FRAME_ACK_ECN || ty
        == FRAME_CONNECTION_CLOSE || ty == FRAME_CONNECTION_CLOSE_APP)
}

/// The frames from offset `p` to the end of `b`, PADDING dropped, as a server receives them
/// in a packet of kind `k`. Each frame's type is judged (unknown, then not permitted) before
/// its body is read, and the first error wins.
pub open spec fn rfc_frames(b: Seq<u8>, p: int, k: PacketKind) -> Result<Seq<SpecFrame>, u64>
    decreases (if p < b.len() {
        b.len() - p
    } else {
        0
    }),
{
    if p >= b.len() {
        Ok(Seq::empty())
    } else {
        let c = b.skip(p);
        match rfc_frame_type(c) {
            Err(e) => Err(e),
            Ok((ty, n)) => if ty > FRAME_HANDSHAKE_DONE {
                Err(FRAME_ENCODING_ERROR)
            } else if !frame_permitted(ty, k) {
                Err(PROTOCOL_VIOLATION)
            } else {
                match rfc_frame_body(ty, c.skip(n as int)) {
                    Err(e) => Err(e),
                    Ok((f, m)) => match rfc_frames(b, p + n + m, k) {
                        Err(e) => Err(e),
                        Ok(fs) => Ok(
                            if f is Padding {
                                fs
                            } else {
                                seq![f] + fs
                            },
                        ),
                    },
                }
            },
        }
    }
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-12.4
//# An endpoint MUST treat receipt of a packet containing no frames as a
//# connection error of type PROTOCOL_VIOLATION.
/// A packet payload of kind `k` as a server receives it: its frames, PADDING dropped.
pub open spec fn rfc_payload(b: Seq<u8>, k: PacketKind) -> Result<Seq<SpecFrame>, u64> {
    if b.len() == 0 {
        Err(PROTOCOL_VIOLATION)
    } else {
        rfc_frames(b, 0, k)
    }
}

// =============================================================================
// Serialization specs
// =============================================================================

/// The frames written one after another.
pub open spec fn spec_frames_bytes(fs: Seq<SpecFrame>) -> Seq<u8>
    decreases fs.len(),
{
    if fs.len() == 0 {
        Seq::empty()
    } else {
        spec_frame_bytes(fs[0]) + spec_frames_bytes(fs.skip(1))
    }
}

/// `fs` without its PADDING frames.
pub open spec fn non_padding(fs: Seq<SpecFrame>) -> Seq<SpecFrame>
    decreases fs.len(),
{
    if fs.len() == 0 {
        Seq::empty()
    } else if fs[0] is Padding {
        non_padding(fs.skip(1))
    } else {
        seq![fs[0]] + non_padding(fs.skip(1))
    }
}

/// The frames a payload of kind `k` may carry, as `serialize_payload` requires them.
pub open spec fn frames_sendable(fs: Seq<SpecFrame>, k: PacketKind) -> bool {
    forall|i: int|
        0 <= i < fs.len() ==> frame_wf(#[trigger] fs[i]) && frame_permitted(
            spec_frame_type(fs[i]),
            k,
        )
}

/// What every frame `rfc_payload` accepts satisfies: sendable in a packet of kind `k`, and
/// neither HANDSHAKE_DONE (rejected on receipt) nor PADDING (dropped).
pub open spec fn frames_received(fs: Seq<SpecFrame>, k: PacketKind) -> bool {
    &&& frames_sendable(fs, k)
    &&& forall|i: int|
        0 <= i < fs.len() ==> !(#[trigger] fs[i] is HandshakeDone) && !(fs[i] is Padding)
}

/// `n` PADDING frames.
pub open spec fn paddings(n: nat) -> Seq<SpecFrame> {
    Seq::new(n, |i: int| SpecFrame::Padding)
}

/// The exec frames as spec values.
pub open spec fn frames_view(fs: Seq<Frame>) -> Seq<SpecFrame> {
    fs.map_values(|f: Frame| f@)
}

/// `r` with `acc` in front of its frames.
pub open spec fn prepend(acc: Seq<SpecFrame>, r: Result<Seq<SpecFrame>, u64>) -> Result<
    Seq<SpecFrame>,
    u64,
> {
    match r {
        Ok(fs) => Ok(acc + fs),
        Err(e) => Err(e),
    }
}

// =============================================================================
// Proofs
// =============================================================================

/// One frame written in front of `tail` reads back: its type, then its body.
proof fn lemma_frame_step(f: SpecFrame, tail: Seq<u8>, k: PacketKind)
    requires
        frame_wf(f),
        frame_permitted(spec_frame_type(f), k),
        !(f is HandshakeDone),
    ensures
        ({
            let c = spec_frame_bytes(f) + tail;
            let ty = spec_frame_type(f);
            let n = spec_varint(ty).len();
            &&& ty <= FRAME_HANDSHAKE_DONE
            &&& n <= spec_frame_bytes(f).len()
            &&& rfc_frame_type(c) == Ok::<(u64, nat), u64>((ty, n))
            &&& rfc_frame_body(ty, c.skip(n as int)) == Ok::<(SpecFrame, nat), u64>(
                (f, (spec_frame_bytes(f).len() - n) as nat),
            )
        }),
{
    // Each fact about the type comes from `lemma_varint_at`, and the body's from the frame
    // round trip; unfolding the decoder or the frame codec only adds noise.
    hide(rfc_varint_decode);
    hide(rfc_frame_body);
    hide(spec_frame_body);
    hide(spec_frame_type);
    hide(frame_wf);
    let ty = spec_frame_type(f);
    let c = spec_frame_bytes(f) + tail;
    assert(c =~= spec_varint(ty) + (spec_frame_body(f) + tail));
    theorem_serialize_matches_rfc(ty);
    lemma_skip0(c);
    lemma_varint_at(c, 0, ty, spec_frame_body(f) + tail);
    theorem_frame_roundtrip(f, tail);
}

/// The frames written after any prefix `pre` parse back from the end of `pre`.
proof fn lemma_frames_rt(pre: Seq<u8>, fs: Seq<SpecFrame>, k: PacketKind)
    requires
        frames_sendable(fs, k),
        forall|i: int| 0 <= i < fs.len() ==> !(#[trigger] fs[i] is HandshakeDone),
    ensures
        rfc_frames(pre + spec_frames_bytes(fs), pre.len() as int, k) == Ok::<
            Seq<SpecFrame>,
            u64,
        >(non_padding(fs)),
    decreases fs.len(),
{
    hide(rfc_frame_type);
    hide(rfc_frame_body);
    hide(spec_frame_bytes);
    hide(spec_frame_type);
    hide(frame_wf);
    hide(frame_permitted);
    let b = pre + spec_frames_bytes(fs);
    if fs.len() == 0 {
        assert(b.len() == pre.len());
    } else {
        let f = fs[0];
        let rest = fs.skip(1);
        let fb = spec_frame_bytes(f);
        let tail = spec_frames_bytes(rest);
        assert(frame_wf(fs[0]) && frame_permitted(spec_frame_type(fs[0]), k));
        assert(!(fs[0] is HandshakeDone));
        assert(b.skip(pre.len() as int) =~= fb + tail);
        lemma_frame_step(f, tail, k);
        assert(frames_sendable(rest, k)) by {
            assert forall|i: int| 0 <= i < rest.len() implies frame_wf(#[trigger] rest[i])
                && frame_permitted(spec_frame_type(rest[i]), k) by {
                assert(rest[i] == fs[i + 1]);
            }
        }
        assert forall|i: int| 0 <= i < rest.len() implies !(#[trigger] rest[i] is HandshakeDone) by {
            assert(rest[i] == fs[i + 1]);
        }
        lemma_frames_rt(pre + fb, rest, k);
        assert(b =~= (pre + fb) + tail);
    }
}

/// Parsing what `serialize_payload` wrote recovers the frames, PADDING dropped.
/// HANDSHAKE_DONE is excluded: a server sends it but rejects it.
pub proof fn theorem_payload_roundtrip(fs: Seq<SpecFrame>, k: PacketKind)
    requires
        fs.len() >= 1,
        frames_sendable(fs, k),
        forall|i: int| 0 <= i < fs.len() ==> !(#[trigger] fs[i] is HandshakeDone),
    ensures
        rfc_payload(spec_frames_bytes(fs), k) == Ok::<Seq<SpecFrame>, u64>(non_padding(fs)),
{
    let b = spec_frames_bytes(fs);
    assert(frame_wf(fs[0]) && frame_permitted(spec_frame_type(fs[0]), k));
    lemma_frame_step(fs[0], Seq::empty(), k);
    theorem_serialize_matches_rfc(spec_frame_type(fs[0]));
    assert(b.len() >= 1);
    lemma_frames_rt(Seq::empty(), fs, k);
    assert(Seq::<u8>::empty() + b =~= b);
}

/// The frames from offset `p` on are `frames_received`; every failure is
/// FRAME_ENCODING_ERROR or PROTOCOL_VIOLATION.
proof fn lemma_frames_received(b: Seq<u8>, p: int, k: PacketKind)
    requires
        0 <= p,
    ensures
        rfc_frames(b, p, k) matches Ok(fs) ==> frames_received(fs, k),
        rfc_frames(b, p, k) matches Err(e) ==> e == FRAME_ENCODING_ERROR || e == PROTOCOL_VIOLATION,
    decreases (if p < b.len() {
        b.len() - p
    } else {
        0
    }),
{
    hide(rfc_frame_body);
    hide(frame_wf);
    hide(spec_frame_type);
    if p < b.len() {
        let c = b.skip(p);
        lemma_decode_len_bounds(c);
        if let Ok((ty, n)) = rfc_frame_type(c) {
            if ty <= FRAME_HANDSHAKE_DONE && frame_permitted(ty, k) {
                lemma_frame_body_received(ty, c.skip(n as int));
                if let Ok((f, m)) = rfc_frame_body(ty, c.skip(n as int)) {
                    lemma_frames_received(b, p + n + m, k);
                    if let Ok(fs) = rfc_frames(b, p + n + m, k) {
                        if !(f is Padding) {
                            assert(frame_permitted(spec_frame_type(f), k));
                            let r = seq![f] + fs;
                            assert forall|i: int| 0 <= i < r.len() implies frame_wf(#[trigger] r[i])
                                && frame_permitted(spec_frame_type(r[i]), k) && !(r[i] is HandshakeDone)
                                && !(r[i] is Padding) by {
                                if i > 0 {
                                    assert(r[i] == fs[i - 1]);
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

/// Every frame a server accepts in a packet of kind `k` is well-formed, permitted in `k`,
/// and neither HANDSHAKE_DONE nor PADDING: the facts 3c and 3d need from a parse, and the
/// precondition `serialize_payload` and `theorem_payload_roundtrip` ask of their frames.
pub proof fn theorem_payload_received_wf(b: Seq<u8>, k: PacketKind)
    ensures
        rfc_payload(b, k) matches Ok(fs) ==> frames_received(fs, k),
{
    lemma_frames_received(b, 0, k);
}

/// Every payload a server rejects is FRAME_ENCODING_ERROR or PROTOCOL_VIOLATION.
pub proof fn theorem_payload_error_codes(b: Seq<u8>, k: PacketKind)
    ensures
        rfc_payload(b, k) matches Err(e) ==> e == FRAME_ENCODING_ERROR || e == PROTOCOL_VIOLATION,
{
    lemma_frames_received(b, 0, k);
}

/// PADDING frames are zero bytes and drop out of `non_padding`.
proof fn lemma_paddings(fs: Seq<SpecFrame>, n: nat)
    ensures
        spec_frames_bytes(fs + paddings(n)) == spec_frames_bytes(fs) + Seq::new(n, |i: int| 0u8),
        non_padding(fs + paddings(n)) == non_padding(fs),
    decreases fs.len() + n,
{
    let z = Seq::new(n, |i: int| 0u8);
    if fs.len() > 0 {
        lemma_paddings(fs.skip(1), n);
        assert((fs + paddings(n)).skip(1) =~= fs.skip(1) + paddings(n));
        assert((fs + paddings(n))[0] == fs[0]);
        assert(spec_frame_bytes(fs[0]) + (spec_frames_bytes(fs.skip(1)) + z) =~= (spec_frame_bytes(
            fs[0],
        ) + spec_frames_bytes(fs.skip(1))) + z);
    } else if n > 0 {
        lemma_paddings(fs, (n - 1) as nat);
        let z1 = Seq::new((n - 1) as nat, |i: int| 0u8);
        assert(fs + paddings(n) =~= paddings(n));
        assert(fs + paddings((n - 1) as nat) =~= paddings((n - 1) as nat));
        assert(paddings(n).skip(1) =~= paddings((n - 1) as nat));
        assert(paddings(n)[0] is Padding);
        lemma_serialize_bytes::<true>(0);
        assert(spec_frame_bytes(SpecFrame::Padding) =~= seq![0u8]);
        assert(seq![0u8] + z1 =~= z);
        assert(spec_frames_bytes(fs) =~= Seq::<u8>::empty());
        assert(Seq::<u8>::empty() + z =~= z);
        assert(Seq::<u8>::empty() + z1 =~= z1);
    } else {
        assert(fs + paddings(n) =~= fs);
        assert(spec_frames_bytes(fs) + z =~= spec_frames_bytes(fs));
    }
}

/// `theorem_payload_roundtrip` with `n` PADDING frames appended: the payload is the frames'
/// bytes followed by `n` zero bytes, and it parses back to the same frames.
pub proof fn theorem_payload_padded(fs: Seq<SpecFrame>, n: nat, k: PacketKind)
    requires
        fs.len() + n >= 1,
        frames_sendable(fs, k),
        forall|i: int| 0 <= i < fs.len() ==> !(#[trigger] fs[i] is HandshakeDone),
    ensures
        spec_frames_bytes(fs + paddings(n)) == spec_frames_bytes(fs) + Seq::new(n, |i: int| 0u8),
        non_padding(fs + paddings(n)) == non_padding(fs),
        rfc_payload(spec_frames_bytes(fs) + Seq::new(n, |i: int| 0u8), k) == Ok::<
            Seq<SpecFrame>,
            u64,
        >(non_padding(fs)),
{
    let g = fs + paddings(n);
    lemma_paddings(fs, n);
    assert forall|i: int| 0 <= i < g.len() implies frame_wf(#[trigger] g[i]) && frame_permitted(
        spec_frame_type(g[i]),
        k,
    ) && !(g[i] is HandshakeDone) by {
        if i < fs.len() {
            assert(g[i] == fs[i]);
        } else {
            assert(g[i] == paddings(n)[i - fs.len()]);
        }
    }
    theorem_payload_roundtrip(g, k);
}

// =============================================================================
// Executable code
// =============================================================================

/// Whether a frame of type `ty` may appear in a packet of kind `k`.
pub fn is_frame_permitted(ty: u64, k: PacketKind) -> (r: bool)
    ensures
        r == frame_permitted(ty, k),
{
    match k {
        PacketKind::OneRtt => ty <= FRAME_HANDSHAKE_DONE,
        _ => ty == FRAME_PADDING || ty == FRAME_PING || ty == FRAME_ACK || ty == FRAME_ACK_ECN
            || ty == FRAME_CRYPTO || ty == FRAME_CONNECTION_CLOSE,
    }
}

/// Whether a packet carrying `frames` is ack-eliciting: some frame is not PADDING, ACK or
/// CONNECTION_CLOSE.
pub fn is_ack_eliciting(frames: &[Frame]) -> (r: bool)
    ensures
        r == exists|i: int|
            0 <= i < frames.len() && ack_eliciting(spec_frame_type(#[trigger] frames@[i]@)),
{
    let mut i: usize = 0;
    while i < frames.len()
        invariant
            i <= frames.len(),
            forall|j: int|
                0 <= j < i ==> !ack_eliciting(spec_frame_type(#[trigger] frames@[j]@)),
        decreases frames.len() - i,
    {
        let ty = frame_type_of(&frames[i]);
        if !(ty == FRAME_PADDING || ty == FRAME_ACK || ty == FRAME_ACK_ECN || ty
            == FRAME_CONNECTION_CLOSE || ty == FRAME_CONNECTION_CLOSE_APP) {
            return true;
        }
        i += 1;
    }
    false
}

/// A packet payload of kind `k` as a server receives it: its frames, PADDING dropped.
/// Every frame consumes at least one byte, so there are at most `b.len()` of them.
// ponytail: a run of 1-byte frames (PING) gives one `Frame` per byte, bounded by the
// datagram size; coalesce PINGs if a caller ever holds many payloads at once.
pub fn parse_payload(b: &[u8], k: PacketKind) -> (r: Result<Vec<Frame>, u64>)
    ensures
        match r {
            Ok(v) => rfc_payload(b@, k) == Ok::<Seq<SpecFrame>, u64>(frames_view(v@))
                && v@.len() <= b@.len() && frames_received(frames_view(v@), k),
            Err(e) => rfc_payload(b@, k) == Err::<Seq<SpecFrame>, u64>(e) && (e
                == FRAME_ENCODING_ERROR || e == PROTOCOL_VIOLATION),
        },
{
    hide(rfc_varint_decode);
    hide(rfc_frame_body);
    hide(frame_permitted);
    proof {
        theorem_payload_received_wf(b@, k);
        theorem_payload_error_codes(b@, k);
    }
    if b.len() == 0 {
        return Err(PROTOCOL_VIOLATION);
    }
    let mut out: Vec<Frame> = Vec::new();
    let mut p: usize = 0;
    proof {
        if let Ok(fs) = rfc_frames(b@, 0, k) {
            assert(frames_view(out@) + fs =~= fs);
        }
    }
    while p < b.len()
        invariant
            p <= b.len(),
            out@.len() <= p,
            rfc_frames(b@, 0, k) == prepend(frames_view(out@), rfc_frames(b@, p as int, k)),
            rfc_payload(b@, k) matches Ok(fs) ==> frames_received(fs, k),
            rfc_payload(b@, k) matches Err(e) ==> e == FRAME_ENCODING_ERROR || e
                == PROTOCOL_VIOLATION,
        decreases b.len() - p,
    {
        let c = slice_subrange(b, p, b.len());
        proof {
            assert(c@ =~= b@.skip(p as int));
        }
        let (ty, n) = match parse_frame_type(c) {
            Ok(x) => x,
            Err(e) => return Err(e),
        };
        proof {
            lemma_decode_len_bounds(c@);
        }
        if ty > FRAME_HANDSHAKE_DONE {
            return Err(FRAME_ENCODING_ERROR);
        }
        if !is_frame_permitted(ty, k) {
            return Err(PROTOCOL_VIOLATION);
        }
        let body = slice_subrange(c, n, c.len());
        proof {
            assert(body@ =~= c@.skip(n as int));
        }
        let (f, m) = match parse_frame_body(ty, body) {
            Ok(x) => x,
            Err(e) => return Err(e),
        };
        let ghost fv = f@;
        let ghost acc = frames_view(out@);
        match f {
            Frame::Padding => {},
            _ => out.push(f),
        }
        p = p + n + m;
        proof {
            if let Ok(fs) = rfc_frames(b@, p as int, k) {
                if fv is Padding {
                    assert(frames_view(out@) =~= acc);
                } else {
                    assert(frames_view(out@) =~= acc.push(fv));
                    assert(acc + (seq![fv] + fs) =~= acc.push(fv) + fs);
                }
            }
        }
    }
    Ok(out)
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-12.4
//# The payload of a packet that contains frames MUST contain at least
//# one frame, and MAY contain multiple frames and multiple frame types.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-12.5
//# CONNECTION_CLOSE
//# frames signaling application errors (type 0x1d) MUST only appear
//# in the application data packet number space.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-12.5
//# All other frame types MUST only be sent in the application data
//# packet number space.
/// Writes `frames` back to back as the payload of a packet of kind `k`: at least one frame,
/// each one permitted in that packet type.
// `k` is read only by `requires`, which a plain `cargo build` erases.
#[allow(unused_variables)]
pub fn serialize_payload(frames: &[Frame], k: PacketKind, out: &mut Vec<u8>)
    requires
        frames.len() >= 1,
        frames_sendable(frames_view(frames@), k),
    ensures
        final(out)@ == old(out)@ + spec_frames_bytes(frames_view(frames@)),
{
    let ghost fs = frames_view(frames@);
    let ghost start = out@;
    let mut i: usize = 0;
    proof {
        assert(fs.skip(0) =~= fs);
    }
    while i < frames.len()
        invariant
            i <= frames.len(),
            fs == frames_view(frames@),
            frames_sendable(fs, k),
            start + spec_frames_bytes(fs) == out@ + spec_frames_bytes(fs.skip(i as int)),
        decreases frames.len() - i,
    {
        proof {
            assert(fs.skip(i as int).skip(1) =~= fs.skip(i as int + 1));
            assert(fs.skip(i as int)[0] == fs[i as int]);
            assert(frame_wf(fs[i as int]));
        }
        let ghost before = out@;
        serialize_frame(&frames[i], out);
        proof {
            let fb = spec_frame_bytes(fs[i as int]);
            assert(before + (fb + spec_frames_bytes(fs.skip(i as int + 1))) =~= (before + fb)
                + spec_frames_bytes(fs.skip(i as int + 1)));
        }
        i += 1;
    }
    proof {
        assert(fs.skip(i as int) =~= Seq::<SpecFrame>::empty());
        assert(out@ + Seq::<u8>::empty() =~= out@);
    }
}

} // verus!
