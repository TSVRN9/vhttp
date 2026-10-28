//! The peer's unidirectional streams (RFC 9114 §6.2, RFC 9204 §4.2): an RFC-transcribed spec
//! over every byte a stream has delivered, and an incremental machine proven to agree with it
//! after every call, however the bytes are split into chunks.
//!
//! Proof shape: the machine keeps the unconsumed bytes `buf` and the invariant `split_ok`: for
//! every future suffix `t`, the spec of `all + t` is the events emitted so far followed by the
//! spec of the stream remainder `buf + t`. Consuming a complete frame or instruction from the
//! front of `buf` preserves it (prefix stability), so the spec of exactly the bytes received
//! (`t` empty) is what each call reports.
use vstd::prelude::*;
use vstd::slice::{slice_subrange, slice_to_vec};
// Used only in ghost code, which a plain `cargo build` erases.
#[allow(unused_imports)]
use wire::varint::*;

use crate::codes::*;
use crate::frame::*;
use crate::limits::*;
use crate::qpack::instructions::*;

verus! {

/// A stream's role, fixed by its type varint (RFC 9114 §6.2).
pub enum UniKind {
    Undetermined,
    Control,
    QpackEncoder,
    QpackDecoder,
    Ignored,
}

#[derive(Debug, PartialEq, Eq)]
pub enum UniEvent {
    PeerSettings(Vec<(u64, u64)>),
    PeerGoaway(u64),
    PeerMaxPushId(u64),
}

pub enum SpecUniEvent {
    PeerSettings(Seq<(u64, u64)>),
    PeerGoaway(u64),
    PeerMaxPushId(u64),
}

impl View for UniEvent {
    type V = SpecUniEvent;

    open spec fn view(&self) -> SpecUniEvent {
        match self {
            UniEvent::PeerSettings(v) => SpecUniEvent::PeerSettings(v@),
            UniEvent::PeerGoaway(id) => SpecUniEvent::PeerGoaway(*id),
            UniEvent::PeerMaxPushId(id) => SpecUniEvent::PeerMaxPushId(*id),
        }
    }
}

/// The critical stream types the peer has opened, shared by all of its uni streams.
pub struct SeenUni {
    pub control: bool,
    pub encoder: bool,
    pub decoder: bool,
}

/// `SeenUni` holds only bools, so it is its own spec value.
pub type SpecSeen = SeenUni;

/// Control-stream state: SETTINGS received, the last MAX_PUSH_ID and the last GOAWAY ID.
pub struct CtrlState {
    pub settings: bool,
    pub max_push_id: Option<u64>,
    pub goaway: Option<u64>,
}

pub open spec fn ctrl_init() -> CtrlState {
    CtrlState { settings: false, max_push_id: None, goaway: None }
}

pub open spec fn views(s: Seq<UniEvent>) -> Seq<SpecUniEvent> {
    s.map_values(|e: UniEvent| e@)
}

pub open spec fn prepend(e: Seq<SpecUniEvent>, r: (Seq<SpecUniEvent>, Option<u64>)) -> (
    Seq<SpecUniEvent>,
    Option<u64>,
) {
    (e + r.0, r.1)
}

// =============================================================================
// RFC 9114 §6.2 / §7.2 and RFC 9204 §4.2 transcription
// =============================================================================

//= https://www.rfc-editor.org/rfc/rfc9114#section-6.2.1
//# If either control
//# stream is closed at any point, this MUST be treated as a connection
//# error of type H3_CLOSED_CRITICAL_STREAM.
//= https://www.rfc-editor.org/rfc/rfc9204#section-4.2
//# Closure of either unidirectional stream type MUST be treated as a
//# connection error of type H3_CLOSED_CRITICAL_STREAM.
/// A critical stream's FIN, wherever it lands (including inside a frame or instruction).
pub open spec fn fin_err(fin: bool) -> Option<u64> {
    if fin {
        Some(H3_CLOSED_CRITICAL_STREAM)
    } else {
        None
    }
}

//= https://www.rfc-editor.org/rfc/rfc9114#section-6.2.1
//# If the first frame of the control stream is any other frame
//# type, this MUST be treated as a connection error of type
//# H3_MISSING_SETTINGS.
//= https://www.rfc-editor.org/rfc/rfc9114#section-7.2.4
//# If an endpoint receives a second SETTINGS
//# frame on the control stream, the endpoint MUST respond with a
//# connection error of type H3_FRAME_UNEXPECTED.
//= https://www.rfc-editor.org/rfc/rfc9114#section-7.2.1
//# If
//# a DATA frame is received on a control stream, the recipient MUST
//# respond with a connection error of type H3_FRAME_UNEXPECTED.
//= https://www.rfc-editor.org/rfc/rfc9114#section-7.2.2
//# If a HEADERS frame is received on a control stream, the recipient
//# MUST respond with a connection error of type H3_FRAME_UNEXPECTED.
//= https://www.rfc-editor.org/rfc/rfc9114#section-7.2.5
//# A server MUST treat the
//# receipt of a PUSH_PROMISE frame as a connection error of type
//# H3_FRAME_UNEXPECTED.
//= https://www.rfc-editor.org/rfc/rfc9114#section-7.2.8
//# These frame
//# types MUST NOT be sent, and their receipt MUST be treated as a
//# connection error of type H3_FRAME_UNEXPECTED.
//= https://www.rfc-editor.org/rfc/rfc9114#section-7.2.3
//# If a server receives a CANCEL_PUSH frame for a push
//# ID that has not yet been mentioned by a PUSH_PROMISE frame, this MUST
//# be treated as a connection error of type H3_ID_ERROR.
/// The error a control-stream frame earns from its header alone. We never promise a push, so
/// every CANCEL_PUSH names an unmentioned push ID. The size caps are our limits
/// (`h3::limits`), checked before any payload is buffered.
pub open spec fn rfc_control_header_error(st: CtrlState, ty: u64, len: u64) -> Option<u64> {
    if !st.settings && ty != FRAME_SETTINGS {
        Some(H3_MISSING_SETTINGS)
    } else if (ty == FRAME_SETTINGS && st.settings) || ty == FRAME_DATA || ty == FRAME_HEADERS
        || ty == FRAME_PUSH_PROMISE || is_h2_reserved_frame_spec(ty) {
        Some(H3_FRAME_UNEXPECTED)
    } else if ty == FRAME_CANCEL_PUSH {
        Some(H3_ID_ERROR)
    } else if len > (if ty == FRAME_SETTINGS {
        MAX_SETTINGS_FRAME
    } else {
        MAX_CONTROL_FRAME
    }) {
        Some(H3_EXCESSIVE_LOAD)
    } else {
        None
    }
}

//= https://www.rfc-editor.org/rfc/rfc9114#section-7.2.7
//# A MAX_PUSH_ID frame cannot reduce the maximum push
//# ID; receipt of a MAX_PUSH_ID frame that contains a smaller value than
//# previously received MUST be treated as a connection error of type
//# H3_ID_ERROR.
//= https://www.rfc-editor.org/rfc/rfc9114#section-5.2
//# Receiving a GOAWAY containing a larger identifier than previously
//# received MUST be treated as a connection error of type H3_ID_ERROR.
//= https://www.rfc-editor.org/rfc/rfc9114#section-7.2.8
//# Endpoints MUST
//# NOT consider these frames to have any meaning upon receipt.
/// Events and next state for a frame that passed the header checks. Unknown and grease frames
/// (and the types the header check already rejected) change nothing.
pub open spec fn rfc_control_frame(st: CtrlState, f: SpecFrame) -> Result<
    (Seq<SpecUniEvent>, CtrlState),
    u64,
> {
    match f {
        SpecFrame::Settings(s) => Ok(
            (
                seq![SpecUniEvent::PeerSettings(s)],
                CtrlState { settings: true, max_push_id: st.max_push_id, goaway: st.goaway },
            ),
        ),
        SpecFrame::Goaway(id) => if st.goaway is Some && id > st.goaway->0 {
            Err(H3_ID_ERROR)
        } else {
            Ok(
                (
                    seq![SpecUniEvent::PeerGoaway(id)],
                    CtrlState { settings: st.settings, max_push_id: st.max_push_id, goaway: Some(id) },
                ),
            )
        },
        SpecFrame::MaxPushId(id) => if st.max_push_id is Some && id < st.max_push_id->0 {
            Err(H3_ID_ERROR)
        } else {
            Ok(
                (
                    seq![SpecUniEvent::PeerMaxPushId(id)],
                    CtrlState { settings: st.settings, max_push_id: Some(id), goaway: st.goaway },
                ),
            )
        },
        _ => Ok((Seq::empty(), st)),
    }
}

#[verifier::decreases_by]
proof fn control_decreases(b: Seq<u8>, st: CtrlState, fin: bool) {
    lemma_frame_header_bounds(b);
}

//= https://www.rfc-editor.org/rfc/rfc9114#section-6.2.1
//# Data on this
//# stream consists of HTTP/3 frames, as defined in Section 7.2.
/// The control stream after its type byte: events up to the first error, and that error.
/// Payload errors from the frame codec pass through.
pub open spec fn rfc_control(b: Seq<u8>, st: CtrlState, fin: bool) -> (
    Seq<SpecUniEvent>,
    Option<u64>,
)
    decreases b.len(),
    via control_decreases
{
    match rfc_frame_header(b) {
        None => (Seq::empty(), fin_err(fin)),
        Some((h, ty, len)) => if rfc_control_header_error(st, ty, len) is Some {
            (Seq::empty(), rfc_control_header_error(st, ty, len))
        } else if b.len() < h + len {
            (Seq::empty(), fin_err(fin))
        } else {
            match rfc_frame_payload(ty, b.subrange(h as int, h + len)) {
                Err(e) => (Seq::empty(), Some(e)),
                Ok(f) => match rfc_control_frame(st, f) {
                    Err(e) => (Seq::empty(), Some(e)),
                    Ok((evs, st2)) => prepend(evs, rfc_control(b.skip(h + len), st2, fin)),
                },
            }
        },
    }
}

//= https://www.rfc-editor.org/rfc/rfc9114#section-6.2.1
//# A control stream is indicated by a stream type of 0x00.
//= https://www.rfc-editor.org/rfc/rfc9204#section-4.2
//# An encoder stream is a unidirectional stream of type 0x02.
//= https://www.rfc-editor.org/rfc/rfc9204#section-4.2
//# A decoder stream is a unidirectional stream of type 0x03.
pub open spec fn rfc_kind_of(ty: u64) -> UniKind {
    if ty == STREAM_CONTROL {
        UniKind::Control
    } else if ty == STREAM_QPACK_ENCODER {
        UniKind::QpackEncoder
    } else if ty == STREAM_QPACK_DECODER {
        UniKind::QpackDecoder
    } else {
        UniKind::Ignored
    }
}

/// The kind the received bytes give a stream. A push stream (0x01) maps to `Ignored`; it is
/// rejected on arrival, so its kind never matters.
pub open spec fn kind_of_bytes(b: Seq<u8>) -> UniKind {
    match rfc_varint_decode(b) {
        None => UniKind::Undetermined,
        Some((_, ty)) => rfc_kind_of(ty),
    }
}

pub open spec fn qpack_end(r: Result<nat, u64>, fin: bool) -> (Seq<SpecUniEvent>, Option<u64>) {
    match r {
        Ok(_) => (Seq::empty(), fin_err(fin)),
        Err(c) => (Seq::empty(), Some(c)),
    }
}

//= https://www.rfc-editor.org/rfc/rfc9204#section-4.2
//# An endpoint MUST allow its peer to create an encoder stream and a
//# decoder stream even if the connection's settings prevent their use.
/// The stream after its type varint, for a stream of kind `k` in control state `st`.
pub open spec fn rfc_tail(k: UniKind, st: CtrlState, b: Seq<u8>, fin: bool) -> (
    Seq<SpecUniEvent>,
    Option<u64>,
) {
    match k {
        UniKind::Control => rfc_control(b, st, fin),
        UniKind::QpackEncoder => qpack_end(rfc_encoder_stream(b), fin),
        UniKind::QpackDecoder => qpack_end(rfc_decoder_stream(b), fin),
        _ => (Seq::empty(), None),
    }
}

//= https://www.rfc-editor.org/rfc/rfc9114#section-6.2.1
//# Only one control stream per peer is permitted;
//# receipt of a second stream claiming to be a control stream MUST be
//# treated as a connection error of type H3_STREAM_CREATION_ERROR.
//= https://www.rfc-editor.org/rfc/rfc9204#section-4.2
//# Receipt of a second instance of either stream type MUST be
//# treated as a connection error of type H3_STREAM_CREATION_ERROR.
pub open spec fn rfc_duplicate(s: SeenUni, ty: u64) -> bool {
    (ty == STREAM_CONTROL && s.control) || (ty == STREAM_QPACK_ENCODER && s.encoder) || (ty
        == STREAM_QPACK_DECODER && s.decoder)
}

pub open spec fn seen_mark(s: SeenUni, ty: u64) -> SeenUni {
    SeenUni {
        control: s.control || ty == STREAM_CONTROL,
        encoder: s.encoder || ty == STREAM_QPACK_ENCODER,
        decoder: s.decoder || ty == STREAM_QPACK_DECODER,
    }
}

/// `seen` once `b` has been received on a stream whose type was unknown before.
pub open spec fn seen_after(s: SeenUni, b: Seq<u8>) -> SeenUni {
    match rfc_varint_decode(b) {
        None => s,
        Some((_, ty)) => seen_mark(s, ty),
    }
}

//= https://www.rfc-editor.org/rfc/rfc9114#section-6.2
//# The purpose is indicated by a stream type, which is sent
//# as a variable-length integer at the start of the stream.
//= https://www.rfc-editor.org/rfc/rfc9114#section-6.2
//# Recipients of unknown stream types MUST
//# either abort reading of the stream or discard incoming data without
//# further processing.
//= https://www.rfc-editor.org/rfc/rfc9114#section-6.2
//# The recipient MUST NOT consider unknown stream types
//# to be a connection error of any kind.
//= https://www.rfc-editor.org/rfc/rfc9114#section-6.2
//# A receiver MUST tolerate unidirectional streams being
//# closed or reset prior to the reception of the unidirectional stream
//# header.
//= https://www.rfc-editor.org/rfc/rfc9114#section-6.2.2
//# Only servers can push; if a server receives a client-initiated push
//# stream, this MUST be treated as a connection error of type
//# H3_STREAM_CREATION_ERROR.
//= https://www.rfc-editor.org/rfc/rfc9114#section-6.2.3
//# Endpoints MUST NOT consider these streams to have any meaning upon
//# receipt.
/// Events and connection error for the `bytes` a peer uni stream has delivered so far (`fin`:
/// they are all of it). `seen_before` is the shared `SeenUni` when the type arrived. The type
/// varint may use any encoding length. Unknown and reserved types are discarded, never an error.
pub open spec fn rfc_uni_stream(bytes: Seq<u8>, fin: bool, seen_before: SpecSeen) -> (
    Seq<SpecUniEvent>,
    Option<u64>,
) {
    match rfc_varint_decode(bytes) {
        None => (Seq::empty(), None),
        Some((n, ty)) => if ty == STREAM_PUSH || rfc_duplicate(seen_before, ty) {
            (Seq::empty(), Some(H3_STREAM_CREATION_ERROR))
        } else {
            rfc_tail(rfc_kind_of(ty), ctrl_init(), bytes.skip(n as int), fin)
        },
    }
}

pub open spec fn err_of(r: Result<(), u64>) -> Option<u64> {
    match r {
        Ok(_) => None,
        Err(c) => Some(c),
    }
}

// =============================================================================
// Lemmas
// =============================================================================

/// For every suffix `t`, the spec of `all + t` is `emitted` followed by the tail spec of
/// `buf + t`: the invariant that makes the result independent of chunking.
pub open spec fn split_ok(
    all: Seq<u8>,
    seen0: SeenUni,
    emitted: Seq<SpecUniEvent>,
    k: UniKind,
    st: CtrlState,
    buf: Seq<u8>,
) -> bool {
    forall|t: Seq<u8>, f: bool| #[trigger]
        rfc_uni_stream(all + t, f, seen0) == prepend(emitted, rfc_tail(k, st, buf + t, f))
}

/// The control-stream analogue of `split_ok`, relative to a buffer `b`.
pub open spec fn ctrl_split(
    b: Seq<u8>,
    st: CtrlState,
    evs: Seq<SpecUniEvent>,
    rest: Seq<u8>,
    st2: CtrlState,
) -> bool {
    forall|t: Seq<u8>, f: bool| #[trigger]
        rfc_control(b + t, st, f) == prepend(evs, rfc_control(rest + t, st2, f))
}

/// One control frame whose header is complete: with the header in hand, an error is decided
/// for every extension; with the payload too, the rest of the stream continues after it.
proof fn lemma_control_frame(
    b: Seq<u8>,
    st: CtrlState,
    h: nat,
    ty: u64,
    len: u64,
    t: Seq<u8>,
    f: bool,
)
    requires
        rfc_frame_header(b) == Some((h, ty, len)),
    ensures
        rfc_control_header_error(st, ty, len) is Some ==> rfc_control(b + t, st, f) == (
            Seq::<SpecUniEvent>::empty(),
            rfc_control_header_error(st, ty, len),
        ),
        rfc_control_header_error(st, ty, len) is None && h + len <= b.len() ==> rfc_control(
            b + t,
            st,
            f,
        ) == match rfc_frame_payload(ty, b.subrange(h as int, h + len)) {
            Err(e) => (Seq::<SpecUniEvent>::empty(), Some(e)),
            Ok(fr) => match rfc_control_frame(st, fr) {
                Err(e) => (Seq::<SpecUniEvent>::empty(), Some(e)),
                Ok((evs, st2)) => prepend(evs, rfc_control(b.skip(h + len) + t, st2, f)),
            },
        },
{
    lemma_frame_header_prefix(b, t);
    if h + len <= b.len() {
        assert((b + t).subrange(h as int, h + len) =~= b.subrange(h as int, h + len));
        assert((b + t).skip(h + len) =~= b.skip(h + len) + t);
    }
}

proof fn lemma_views_push(s: Seq<UniEvent>, k: int, x: UniEvent)
    requires
        0 <= k <= s.len(),
    ensures
        views(s.push(x).skip(k)) == views(s.skip(k)) + seq![x@],
        s.push(x).take(k) == s.take(k),
{
    assert(views(s.push(x).skip(k)) =~= views(s.skip(k)) + seq![x@]);
    assert(s.push(x).take(k) =~= s.take(k));
}

// =============================================================================
// Executable machine
// =============================================================================

fn kind_of(ty: u64) -> (k: UniKind)
    ensures
        k == rfc_kind_of(ty),
{
    if ty == STREAM_CONTROL {
        UniKind::Control
    } else if ty == STREAM_QPACK_ENCODER {
        UniKind::QpackEncoder
    } else if ty == STREAM_QPACK_DECODER {
        UniKind::QpackDecoder
    } else {
        UniKind::Ignored
    }
}

fn control_header_error(st: &CtrlState, ty: u64, len: u64) -> (r: Option<u64>)
    ensures
        r == rfc_control_header_error(*st, ty, len),
{
    if !st.settings && ty != FRAME_SETTINGS {
        Some(H3_MISSING_SETTINGS)
    } else if (ty == FRAME_SETTINGS && st.settings) || ty == FRAME_DATA || ty == FRAME_HEADERS
        || ty == FRAME_PUSH_PROMISE || is_h2_reserved_frame(ty) {
        Some(H3_FRAME_UNEXPECTED)
    } else if ty == FRAME_CANCEL_PUSH {
        Some(H3_ID_ERROR)
    } else if len > (if ty == FRAME_SETTINGS {
        MAX_SETTINGS_FRAME
    } else {
        MAX_CONTROL_FRAME
    }) {
        Some(H3_EXCESSIVE_LOAD)
    } else {
        None
    }
}

/// Consumes the frame at the front of `b`, dispatching on its type before parsing any payload.
/// `Ok(0)`: `b` is an incomplete frame that passed its header checks, or an incomplete header.
fn control_frame(b: &[u8], st: &mut CtrlState, events: &mut Vec<UniEvent>) -> (r: Result<
    usize,
    u64,
>)
    ensures
        final(events)@.len() >= old(events)@.len(),
        final(events)@.take(old(events)@.len() as int) == old(events)@,
        match r {
            Ok(k) => if k == 0 {
                &&& final(events)@ == old(events)@
                &&& *final(st) == *old(st)
                &&& forall|f: bool| #[trigger]
                    rfc_control(b@, *old(st), f) == (Seq::<SpecUniEvent>::empty(), fin_err(f))
            } else {
                &&& k <= b@.len()
                &&& ctrl_split(
                    b@,
                    *old(st),
                    views(final(events)@.skip(old(events)@.len() as int)),
                    b@.skip(k as int),
                    *final(st),
                )
            },
            Err(e) => {
                &&& final(events)@ == old(events)@
                &&& forall|t: Seq<u8>, f: bool| #[trigger]
                    rfc_control(b@ + t, *old(st), f) == (Seq::<SpecUniEvent>::empty(), Some(e))
            },
        },
{
    let ghost st1 = *st;
    let ghost ev0 = events@;
    proof {
        assert(events@.take(ev0.len() as int) =~= ev0);
    }
    let (ty, len, hdr_len) = match parse_frame_header(b) {
        FrameHeader::Incomplete => return Ok(0),
        FrameHeader::Complete { ty, len, hdr_len } => (ty, len, hdr_len),
    };
    proof {
        lemma_frame_header_bounds(b@);
    }
    if let Some(e) = control_header_error(st, ty, len) {
        proof {
            assert forall|t: Seq<u8>, f: bool| #[trigger]
                rfc_control(b@ + t, st1, f) == (Seq::<SpecUniEvent>::empty(), Some(e)) by {
                lemma_control_frame(b@, st1, hdr_len as nat, ty, len, t, f);
            }
        }
        return Err(e);
    }
    // The header check caps `len` at MAX_CONTROL_FRAME.
    let len = len as usize;
    if b.len() - hdr_len < len {
        return Ok(0);
    }
    let k = hdr_len + len;
    let payload = slice_subrange(b, hdr_len, k);
    proof {
        assert(payload@ =~= b@.subrange(hdr_len as int, k as int));
    }
    let frame = match parse_frame_payload(ty, payload) {
        Ok(f) => f,
        Err(e) => {
            proof {
                assert forall|t: Seq<u8>, f: bool| #[trigger]
                    rfc_control(b@ + t, st1, f) == (Seq::<SpecUniEvent>::empty(), Some(e)) by {
                    lemma_control_frame(b@, st1, hdr_len as nat, ty, len as u64, t, f);
                }
            }
            return Err(e);
        },
    };
    let ghost fv = frame@;
    let id_err = match frame {
        Frame::Settings(v) => {
            st.settings = true;
            events.push(UniEvent::PeerSettings(v));
            false
        },
        Frame::Goaway(id) => if st.goaway.is_some() && id > st.goaway.unwrap() {
            true
        } else {
            st.goaway = Some(id);
            events.push(UniEvent::PeerGoaway(id));
            false
        },
        Frame::MaxPushId(id) => if st.max_push_id.is_some() && id < st.max_push_id.unwrap() {
            true
        } else {
            st.max_push_id = Some(id);
            events.push(UniEvent::PeerMaxPushId(id));
            false
        },
        _ => false,
    };
    if id_err {
        proof {
            assert forall|t: Seq<u8>, f: bool| #[trigger]
                rfc_control(b@ + t, st1, f) == (Seq::<SpecUniEvent>::empty(), Some(H3_ID_ERROR)) by {
                lemma_control_frame(b@, st1, hdr_len as nat, ty, len as u64, t, f);
            }
        }
        return Err(H3_ID_ERROR);
    }
    proof {
        let (evs, st2) = rfc_control_frame(st1, fv)->Ok_0;
        assert(*st == st2);
        let mine = views(events@.skip(ev0.len() as int));
        if events@.len() > ev0.len() {
            let x = events@.last();
            assert(events@ == ev0.push(x));
            lemma_views_push(ev0, ev0.len() as int, x);
            assert(ev0.skip(ev0.len() as int) =~= Seq::<UniEvent>::empty());
            assert(views(Seq::<UniEvent>::empty()) =~= Seq::<SpecUniEvent>::empty());
            assert(mine =~= evs);
        } else {
            assert(events@.skip(ev0.len() as int) =~= Seq::<UniEvent>::empty());
            assert(mine =~= evs);
        }
        assert forall|t: Seq<u8>, f: bool| #[trigger]
            rfc_control(b@ + t, st1, f) == prepend(mine, rfc_control(b@.skip(k as int) + t, st2, f)) by {
            lemma_control_frame(b@, st1, hdr_len as nat, ty, len as u64, t, f);
        }
    }
    Ok(k)
}

proof fn lemma_views_split(s1: Seq<UniEvent>, s2: Seq<UniEvent>, a: int)
    requires
        0 <= a <= s1.len() <= s2.len(),
        s2.take(s1.len() as int) == s1,
    ensures
        views(s2.skip(a)) == views(s1.skip(a)) + views(s2.skip(s1.len() as int)),
        s2.take(a) == s1.take(a),
{
    assert forall|i: int| 0 <= i < s1.len() implies s2[i] == s1[i] by {
        assert(s2.take(s1.len() as int)[i] == s2[i]);
    }
    assert(views(s2.skip(a)) =~= views(s1.skip(a)) + views(s2.skip(s1.len() as int)));
    assert(s2.take(a) =~= s1.take(a));
}

/// Consumes the complete frames at the front of `buf`. `Ok(n)`: `buf[n..]` is an incomplete
/// frame that passed its header checks, or an incomplete header.
fn control_frames(buf: &[u8], st: &mut CtrlState, events: &mut Vec<UniEvent>) -> (r: Result<
    usize,
    u64,
>)
    ensures
        final(events)@.len() >= old(events)@.len(),
        final(events)@.take(old(events)@.len() as int) == old(events)@,
        match r {
            Ok(n) => {
                &&& n <= buf@.len()
                &&& ctrl_split(
                    buf@,
                    *old(st),
                    views(final(events)@.skip(old(events)@.len() as int)),
                    buf@.skip(n as int),
                    *final(st),
                )
                &&& forall|f: bool|
                    #[trigger] rfc_control(buf@.skip(n as int), *final(st), f) == (
                        Seq::<SpecUniEvent>::empty(),
                        fin_err(f),
                    )
            },
            Err(e) => forall|t: Seq<u8>, f: bool| #[trigger]
                rfc_control(buf@ + t, *old(st), f) == (
                    views(final(events)@.skip(old(events)@.len() as int)),
                    Some(e),
                ),
        },
{
    let ghost st0 = *st;
    let ghost ev0 = events@;
    let mut pos: usize = 0;
    proof {
        assert(buf@.skip(0) =~= buf@);
        assert(events@.skip(ev0.len() as int) =~= Seq::<UniEvent>::empty());
        assert(views(Seq::<UniEvent>::empty()) =~= Seq::<SpecUniEvent>::empty());
        assert forall|t: Seq<u8>, f: bool| #[trigger]
            rfc_control(buf@ + t, st0, f) == prepend(
                views(events@.skip(ev0.len() as int)),
                rfc_control(buf@.skip(0) + t, st0, f),
            ) by {
            let x = rfc_control(buf@ + t, st0, f);
            assert(Seq::<SpecUniEvent>::empty() + x.0 =~= x.0);
        }
        assert(events@.take(ev0.len() as int) =~= ev0);
    }
    loop
        invariant
            ev0 == old(events)@,
            st0 == *old(st),
            pos <= buf@.len(),
            events@.len() >= ev0.len(),
            events@.take(ev0.len() as int) == ev0,
            ctrl_split(buf@, st0, views(events@.skip(ev0.len() as int)), buf@.skip(pos as int), *st),
        decreases buf@.len() - pos,
    {
        let rest = slice_subrange(buf, pos, buf.len());
        assert(rest@ =~= buf@.skip(pos as int));
        let ghost done = views(events@.skip(ev0.len() as int));
        let ghost st1 = *st;
        let ghost ev1 = events@;
        let r = control_frame(rest, st, events);
        proof {
            lemma_views_split(ev1, events@, ev0.len() as int);
            let mine = views(events@.skip(ev1.len() as int));
            assert(views(events@.skip(ev0.len() as int)) == done + mine);
        }
        match r {
            Err(e) => {
                proof {
                    assert(events@.skip(ev1.len() as int) =~= Seq::<UniEvent>::empty());
                    assert(views(Seq::<UniEvent>::empty()) =~= Seq::<SpecUniEvent>::empty());
                    assert(done + Seq::<SpecUniEvent>::empty() =~= done);
                    assert forall|t: Seq<u8>, f: bool| #[trigger]
                        rfc_control(buf@ + t, st0, f) == (done, Some(e)) by {
                        assert(rfc_control(rest@ + t, st1, f) == (Seq::<SpecUniEvent>::empty(), Some(e)));
                    }
                }
                return Err(e);
            },
            Ok(k) => {
                if k == 0 {
                    return Ok(pos);
                }
                proof {
                    let mine = views(events@.skip(ev1.len() as int));
                    let next = buf@.skip(pos + k);
                    assert(rest@.skip(k as int) =~= next);
                    assert forall|t: Seq<u8>, f: bool| #[trigger]
                        rfc_control(buf@ + t, st0, f) == prepend(done + mine, rfc_control(next + t, *st, f)) by {
                        assert(rfc_control(rest@ + t, st1, f) == prepend(mine, rfc_control(rest@.skip(k as int) + t, *st, f)));
                        let x = rfc_control(next + t, *st, f);
                        assert(done + (mine + x.0) =~= (done + mine) + x.0);
                    }
                }
                pos = pos + k;
            },
        }
    }
}

/// One peer-initiated unidirectional stream.
pub struct UniStream {
    kind: UniKind,
    /// Received bytes not yet consumed: part of the type varint, or one incomplete frame or
    /// QPACK instruction. Bounded between calls: a control frame's size passed the header check
    /// (at most MAX_CONTROL_FRAME plus its header), and an incomplete instruction is an opcode
    /// byte plus at most 10 prefix-integer continuation bytes.
    buf: Vec<u8>,
    ctrl: CtrlState,
    done: bool,
    all: Ghost<Seq<u8>>,
    seen0: Ghost<SeenUni>,
    emitted: Ghost<Seq<SpecUniEvent>>,
}

impl UniStream {
    /// Every byte received on this stream.
    pub closed spec fn all(&self) -> Seq<u8> {
        self.all@
    }

    /// The shared `SeenUni` at the call that determined the stream type.
    pub closed spec fn seen_before(&self) -> SeenUni {
        self.seen0@
    }

    /// Every event this stream has returned.
    pub closed spec fn emitted(&self) -> Seq<SpecUniEvent> {
        self.emitted@
    }

    /// The stream has returned an error or seen its FIN; it takes no more data.
    pub closed spec fn done(&self) -> bool {
        self.done
    }

    pub closed spec fn wf(&self) -> bool {
        &&& self.kind == kind_of_bytes(self.all@)
        &&& !self.done ==> match self.kind {
            UniKind::Undetermined => {
                &&& self.all@ == self.buf@
                &&& self.emitted@.len() == 0
                &&& self.ctrl == ctrl_init()
            },
            _ => split_ok(self.all@, self.seen0@, self.emitted@, self.kind, self.ctrl, self.buf@),
        }
    }

    pub fn new() -> (r: Self)
        ensures
            r.wf(),
            r.all() == Seq::<u8>::empty(),
            r.emitted() == Seq::<SpecUniEvent>::empty(),
            !r.done(),
    {
        let r = UniStream {
            kind: UniKind::Undetermined,
            buf: Vec::new(),
            ctrl: CtrlState { settings: false, max_push_id: None, goaway: None },
            done: false,
            all: Ghost(Seq::empty()),
            seen0: Ghost(SeenUni { control: false, encoder: false, decoder: false }),
            emitted: Ghost(Seq::empty()),
        };
        proof {
            assert(rfc_varint_decode(Seq::<u8>::empty()) is None);
        }
        r
    }

    pub fn is_done(&self) -> (r: bool)
        ensures
            r == self.done(),
    {
        self.done
    }

    pub fn kind(&self) -> (k: UniKind)
        requires
            self.wf(),
        ensures
            k == kind_of_bytes(self.all()),
    {
        match self.kind {
            UniKind::Undetermined => UniKind::Undetermined,
            UniKind::Control => UniKind::Control,
            UniKind::QpackEncoder => UniKind::QpackEncoder,
            UniKind::QpackDecoder => UniKind::QpackDecoder,
            UniKind::Ignored => UniKind::Ignored,
        }
    }

    /// Feeds the next `data` (`fin`: the stream ends after it). `Err(code)` is a connection
    /// error. Afterwards the cumulative events and error are exactly `rfc_uni_stream` of every
    /// byte received, so they don't depend on how the bytes were chunked.
    pub fn on_data(
        &mut self,
        data: &[u8],
        fin: bool,
        seen: &mut SeenUni,
        events: &mut Vec<UniEvent>,
    ) -> (r: Result<(), u64>)
        requires
            old(self).wf(),
            !old(self).done(),
        ensures
            final(self).wf(),
            final(self).all() == old(self).all() + data@,
            final(self).done() == (r is Err || fin),
            final(events)@.len() >= old(events)@.len(),
            final(events)@.take(old(events)@.len() as int) == old(events)@,
            final(self).emitted() == old(self).emitted() + views(
                final(events)@.skip(old(events)@.len() as int),
            ),
            rfc_uni_stream(final(self).all(), fin, final(self).seen_before()) == (
                final(self).emitted(),
                err_of(r),
            ),
            kind_of_bytes(old(self).all()) is Undetermined ==> final(self).seen_before() == *old(
                seen,
            ) && *final(seen) == seen_after(*old(seen), final(self).all()),
            !(kind_of_bytes(old(self).all()) is Undetermined) ==> final(self).seen_before()
                == old(self).seen_before() && *final(seen) == *old(seen),
    {
        let ghost all0 = self.all@;
        let ghost ev0 = events@;
        let ghost em0 = self.emitted@;
        self.all = Ghost(self.all@ + data@);
        self.done = true;
        proof {
            assert(events@.take(ev0.len() as int) =~= ev0);
            assert(events@.skip(ev0.len() as int) =~= Seq::<UniEvent>::empty());
            assert(views(Seq::<UniEvent>::empty()) =~= Seq::<SpecUniEvent>::empty());
            assert(em0 + Seq::<SpecUniEvent>::empty() =~= em0);
            assert(self.all@ + Seq::<u8>::empty() =~= self.all@);
        }
        match self.kind {
            UniKind::Ignored => {
                proof {
                    lemma_decode_prefix(all0, data@);
                    assert forall|t: Seq<u8>, f: bool| #[trigger]
                        rfc_uni_stream(self.all@ + t, f, self.seen0@) == prepend(
                            em0,
                            rfc_tail(UniKind::Ignored, self.ctrl, self.buf@ + t, f),
                        ) by {
                        assert(all0 + (data@ + t) =~= self.all@ + t);
                        assert(rfc_uni_stream(all0 + (data@ + t), f, self.seen0@) == prepend(
                            em0,
                            rfc_tail(UniKind::Ignored, self.ctrl, self.buf@ + (data@ + t), f),
                        ));
                    }
                    assert(rfc_uni_stream(self.all@ + Seq::empty(), fin, self.seen0@) == prepend(
                        em0,
                        rfc_tail(UniKind::Ignored, self.ctrl, self.buf@ + Seq::empty(), fin),
                    ));
                }
                self.done = fin;
                return Ok(());
            },
            UniKind::Undetermined => {
                self.seen0 = Ghost(*seen);
                let mut d = slice_to_vec(data);
                self.buf.append(&mut d);
                let (n, ty) = match parse_varint(self.buf.as_slice()) {
                    None => {
                        proof {
                            assert(self.buf@ =~= self.all@);
                            assert(em0 =~= Seq::<SpecUniEvent>::empty());
                        }
                        self.done = fin;
                        return Ok(());
                    },
                    Some(x) => x,
                };
                let ghost b = self.buf@;
                proof {
                    assert(b =~= self.all@);
                    assert(em0 =~= Seq::<SpecUniEvent>::empty());
                    assert forall|t: Seq<u8>| #[trigger] rfc_varint_decode(b + t) == Some((n as nat, ty)) by {
                        lemma_decode_prefix(b, t);
                    }
                }
                self.kind = kind_of(ty);
                if ty == STREAM_PUSH || (ty == STREAM_CONTROL && seen.control) || (ty
                    == STREAM_QPACK_ENCODER && seen.encoder) || (ty == STREAM_QPACK_DECODER
                    && seen.decoder) {
                    proof {
                        assert(seen_mark(self.seen0@, ty) == self.seen0@);
                    }
                    return Err(H3_STREAM_CREATION_ERROR);
                }
                seen.control = seen.control || ty == STREAM_CONTROL;
                seen.encoder = seen.encoder || ty == STREAM_QPACK_ENCODER;
                seen.decoder = seen.decoder || ty == STREAM_QPACK_DECODER;
                if let UniKind::Ignored = self.kind {
                    self.buf = Vec::new();
                    proof {
                        assert forall|t: Seq<u8>, f: bool| #[trigger]
                            rfc_uni_stream(self.all@ + t, f, self.seen0@) == prepend(
                                em0,
                                rfc_tail(UniKind::Ignored, self.ctrl, self.buf@ + t, f),
                            ) by {
                            assert(rfc_varint_decode(b + t) == Some((n as nat, ty)));
                        }
                    }
                    self.done = fin;
                    return Ok(());
                }
                self.buf = slice_to_vec(slice_subrange(self.buf.as_slice(), n, self.buf.len()));
                proof {
                    assert forall|t: Seq<u8>, f: bool| #[trigger]
                        rfc_uni_stream(self.all@ + t, f, self.seen0@) == prepend(
                            em0,
                            rfc_tail(self.kind, self.ctrl, self.buf@ + t, f),
                        ) by {
                        assert(rfc_varint_decode(b + t) == Some((n as nat, ty)));
                        assert((b + t).skip(n as int) =~= self.buf@ + t);
                        let x = rfc_tail(self.kind, self.ctrl, self.buf@ + t, f);
                        assert(em0 + x.0 =~= x.0);
                    }
                }
            },
            _ => {
                let ghost buf0 = self.buf@;
                let mut d = slice_to_vec(data);
                self.buf.append(&mut d);
                proof {
                    lemma_decode_prefix(all0, data@);
                    assert forall|t: Seq<u8>, f: bool| #[trigger]
                        rfc_uni_stream(self.all@ + t, f, self.seen0@) == prepend(
                            em0,
                            rfc_tail(self.kind, self.ctrl, self.buf@ + t, f),
                        ) by {
                        assert(all0 + (data@ + t) =~= self.all@ + t);
                        assert(buf0 + (data@ + t) =~= self.buf@ + t);
                        assert(rfc_uni_stream(all0 + (data@ + t), f, self.seen0@) == prepend(
                            em0,
                            rfc_tail(self.kind, self.ctrl, buf0 + (data@ + t), f),
                        ));
                    }
                }
            },
        }
        let r = self.consume(fin, events);
        match r {
            Ok(()) => {
                self.done = false;
                Ok(())
            },
            Err(e) => Err(e),
        }
    }

    /// Consumes what the critical stream's buffer completes, given `split_ok` for its current
    /// state; then a FIN is H3_CLOSED_CRITICAL_STREAM.
    fn consume(&mut self, fin: bool, events: &mut Vec<UniEvent>) -> (r: Result<(), u64>)
        requires
            consumable(*old(self)),
        ensures
            consumed(*old(self), *final(self), old(events)@, final(events)@, fin, r),
    {
        if let UniKind::Control = self.kind {
            self.consume_control(fin, events)
        } else {
            let r = self.consume_qpack(fin);
            proof {
                assert(events@.take(events@.len() as int) =~= events@);
                assert(events@.skip(events@.len() as int) =~= Seq::<UniEvent>::empty());
                assert(views(Seq::<UniEvent>::empty()) =~= Seq::<SpecUniEvent>::empty());
                assert(self.emitted@ + Seq::<SpecUniEvent>::empty() =~= self.emitted@);
            }
            r
        }
    }

    fn consume_control(&mut self, fin: bool, events: &mut Vec<UniEvent>) -> (r: Result<(), u64>)
        requires
            consumable(*old(self)),
            old(self).kind is Control,
        ensures
            consumed(*old(self), *final(self), old(events)@, final(events)@, fin, r),
    {
        let ghost ev0 = events@;
        let ghost em0 = self.emitted@;
        let ghost b = self.buf@;
        let ghost st1 = self.ctrl;
        proof {
            assert(self.all@ + Seq::<u8>::empty() =~= self.all@);
            assert(b + Seq::<u8>::empty() =~= b);
            assert(rfc_uni_stream(self.all@ + Seq::empty(), fin, self.seen0@) == prepend(
                em0,
                rfc_tail(self.kind, st1, b + Seq::empty(), fin),
            ));
        }
        let n = match control_frames(self.buf.as_slice(), &mut self.ctrl, events) {
            Ok(n) => n,
            Err(e) => {
                self.emitted = Ghost(em0 + views(events@.skip(ev0.len() as int)));
                return Err(e);
            },
        };
        // Drain only when something was consumed, so a frame trickled in byte by byte is not
        // copied once per byte.
        if n > 0 {
            self.buf = slice_to_vec(slice_subrange(self.buf.as_slice(), n, self.buf.len()));
        }
        self.emitted = Ghost(em0 + views(events@.skip(ev0.len() as int)));
        proof {
            let evs = views(events@.skip(ev0.len() as int));
            assert(b.skip(n as int) =~= self.buf@);
            assert forall|t: Seq<u8>, f: bool| #[trigger]
                rfc_uni_stream(self.all@ + t, f, self.seen0@) == prepend(
                    self.emitted@,
                    rfc_tail(self.kind, self.ctrl, self.buf@ + t, f),
                ) by {
                assert(rfc_uni_stream(self.all@ + t, f, self.seen0@) == prepend(
                    em0,
                    rfc_tail(self.kind, st1, b + t, f),
                ));
                assert(rfc_control(b + t, st1, f) == prepend(
                    evs,
                    rfc_control(self.buf@ + t, self.ctrl, f),
                ));
                let x = rfc_tail(self.kind, self.ctrl, self.buf@ + t, f);
                assert(em0 + (evs + x.0) =~= self.emitted@ + x.0);
            }
            assert(self.buf@ + Seq::empty() =~= self.buf@);
            assert(rfc_uni_stream(self.all@ + Seq::empty(), fin, self.seen0@) == prepend(
                self.emitted@,
                rfc_tail(self.kind, self.ctrl, self.buf@ + Seq::empty(), fin),
            ));
            assert(rfc_control(self.buf@, self.ctrl, fin) == (
                Seq::<SpecUniEvent>::empty(),
                fin_err(fin),
            ));
            assert(self.emitted@ + Seq::<SpecUniEvent>::empty() =~= self.emitted@);
        }
        if fin {
            return Err(H3_CLOSED_CRITICAL_STREAM);
        }
        Ok(())
    }

    /// QPACK streams emit no events, so only `buf` and the result change.
    fn consume_qpack(&mut self, fin: bool) -> (r: Result<(), u64>)
        requires
            consumable(*old(self)),
            old(self).kind is QpackEncoder || old(self).kind is QpackDecoder,
        ensures
            final(self).all@ == old(self).all@,
            final(self).seen0@ == old(self).seen0@,
            final(self).kind == old(self).kind,
            final(self).done == old(self).done,
            final(self).emitted@ == old(self).emitted@,
            final(self).ctrl == old(self).ctrl,
            rfc_uni_stream(final(self).all@, fin, final(self).seen0@) == (
                final(self).emitted@,
                err_of(r),
            ),
            r is Ok ==> !fin && split_ok(
                final(self).all@,
                final(self).seen0@,
                final(self).emitted@,
                final(self).kind,
                final(self).ctrl,
                final(self).buf@,
            ),
    {
        let ghost b = self.buf@;
        let ghost em0 = self.emitted@;
        proof {
            assert(self.all@ + Seq::<u8>::empty() =~= self.all@);
            assert(b + Seq::<u8>::empty() =~= b);
            assert(rfc_uni_stream(self.all@ + Seq::empty(), fin, self.seen0@) == prepend(
                em0,
                rfc_tail(self.kind, self.ctrl, b + Seq::empty(), fin),
            ));
            assert(em0 + Seq::<SpecUniEvent>::empty() =~= em0);
        }
        let scanned = if let UniKind::QpackEncoder = self.kind {
            process_encoder_stream(self.buf.as_slice())
        } else {
            process_decoder_stream(self.buf.as_slice())
        };
        let n = match scanned {
            Ok(n) => n,
            Err(e) => return Err(e),
        };
        proof {
            lemma_qpack_split(self.kind, self.ctrl, b, n as nat);
        }
        if n > 0 {
            self.buf = slice_to_vec(slice_subrange(self.buf.as_slice(), n, self.buf.len()));
        }
        proof {
            assert(b.skip(n as int) =~= self.buf@);
            assert forall|t: Seq<u8>, f: bool| #[trigger]
                rfc_uni_stream(self.all@ + t, f, self.seen0@) == prepend(
                    em0,
                    rfc_tail(self.kind, self.ctrl, self.buf@ + t, f),
                ) by {
                assert(rfc_uni_stream(self.all@ + t, f, self.seen0@) == prepend(
                    em0,
                    rfc_tail(self.kind, self.ctrl, b + t, f),
                ));
                assert(rfc_tail(self.kind, self.ctrl, b + t, f) == rfc_tail(
                    self.kind,
                    self.ctrl,
                    self.buf@ + t,
                    f,
                ));
            }
            assert(rfc_tail(self.kind, self.ctrl, b, fin) == rfc_tail(
                self.kind,
                self.ctrl,
                self.buf@,
                fin,
            ));
        }
        if fin {
            return Err(H3_CLOSED_CRITICAL_STREAM);
        }
        Ok(())
    }
}

/// The QPACK tail spec ignores the complete instructions at the front of the buffer.
proof fn lemma_qpack_split(k: UniKind, st: CtrlState, b: Seq<u8>, n: nat)
    requires
        k is QpackEncoder ==> rfc_encoder_stream(b) == Ok::<nat, u64>(n),
        k is QpackDecoder ==> rfc_decoder_stream(b) == Ok::<nat, u64>(n),
        k is QpackEncoder || k is QpackDecoder,
    ensures
        n <= b.len(),
        forall|t: Seq<u8>, f: bool| #[trigger]
            rfc_tail(k, st, b + t, f) == rfc_tail(k, st, b.skip(n as int) + t, f),
        forall|f: bool| #[trigger]
            rfc_tail(k, st, b, f) == (Seq::<SpecUniEvent>::empty(), fin_err(f)),
        forall|f: bool| #[trigger]
            rfc_tail(k, st, b.skip(n as int), f) == (Seq::<SpecUniEvent>::empty(), fin_err(f)),
{
    assert(b + Seq::<u8>::empty() =~= b);
    assert(b.skip(n as int) + Seq::<u8>::empty() =~= b.skip(n as int));
    if k is QpackEncoder {
        lemma_encoder_stream_split(b, Seq::empty());
        assert forall|t: Seq<u8>, f: bool| #[trigger]
            rfc_tail(k, st, b + t, f) == rfc_tail(k, st, b.skip(n as int) + t, f) by {
            lemma_encoder_stream_split(b, t);
        }
    } else {
        lemma_decoder_stream_split(b, Seq::empty());
        assert forall|t: Seq<u8>, f: bool| #[trigger]
            rfc_tail(k, st, b + t, f) == rfc_tail(k, st, b.skip(n as int) + t, f) by {
            lemma_decoder_stream_split(b, t);
        }
    }
}

/// `s` is a critical stream whose state satisfies `split_ok`.
spec fn consumable(s: UniStream) -> bool {
    &&& s.kind is Control || s.kind is QpackEncoder || s.kind is QpackDecoder
    &&& split_ok(s.all@, s.seen0@, s.emitted@, s.kind, s.ctrl, s.buf@)
}

/// What `consume` guarantees, from `s0`/`e0` to `s1`/`e1`.
spec fn consumed(
    s0: UniStream,
    s1: UniStream,
    e0: Seq<UniEvent>,
    e1: Seq<UniEvent>,
    fin: bool,
    r: Result<(), u64>,
) -> bool {
    &&& s1.all@ == s0.all@
    &&& s1.seen0@ == s0.seen0@
    &&& s1.kind == s0.kind
    &&& s1.done == s0.done
    &&& e1.len() >= e0.len()
    &&& e1.take(e0.len() as int) == e0
    &&& s1.emitted@ == s0.emitted@ + views(e1.skip(e0.len() as int))
    &&& rfc_uni_stream(s1.all@, fin, s1.seen0@) == (s1.emitted@, err_of(r))
    &&& r is Ok ==> !fin && split_ok(s1.all@, s1.seen0@, s1.emitted@, s1.kind, s1.ctrl, s1.buf@)
}

} // verus!
