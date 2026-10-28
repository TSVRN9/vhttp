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
#[allow(unused_imports)]
use crate::qpack::int::PREFIX_INT_MAX_CONT;

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
/// A FIN inside a frame gets §6.2.1's H3_CLOSED_CRITICAL_STREAM, not §7.1's H3_FRAME_ERROR: both
/// are connection errors, and §6.2.1 is the rule specific to the control stream.
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
//= https://www.rfc-editor.org/rfc/rfc9114#section-7.1
//# A frame payload that contains additional bytes
//# after the identified fields or a frame payload that terminates before
//# the end of the identified fields MUST be treated as a connection
//# error of type H3_FRAME_ERROR.
//= https://www.rfc-editor.org/rfc/rfc9114#section-9
//# Implementations MUST ignore unknown or unsupported values in all
//# extensible protocol elements.
/// The error a control-stream frame earns from its header alone. We never promise a push, so
/// every CANCEL_PUSH names an unmentioned push ID. A one-varint payload (CANCEL_PUSH, GOAWAY,
/// MAX_PUSH_ID) longer than 8 bytes must have extra bytes. The SETTINGS cap is our limit
/// (`h3::limits`). Unknown and grease frames have no length limit: their payload is skipped.
pub open spec fn rfc_control_header_error(st: CtrlState, ty: u64, len: u64) -> Option<u64> {
    if !st.settings && ty != FRAME_SETTINGS {
        Some(H3_MISSING_SETTINGS)
    } else if (ty == FRAME_SETTINGS && st.settings) || ty == FRAME_DATA || ty == FRAME_HEADERS
        || ty == FRAME_PUSH_PROMISE || is_h2_reserved_frame_spec(ty) {
        Some(H3_FRAME_UNEXPECTED)
    } else if (ty == FRAME_CANCEL_PUSH || ty == FRAME_GOAWAY || ty == FRAME_MAX_PUSH_ID) && len > 8 {
        Some(H3_FRAME_ERROR)
    } else if ty == FRAME_CANCEL_PUSH {
        Some(H3_ID_ERROR)
    } else if ty == FRAME_SETTINGS && len > MAX_SETTINGS_FRAME {
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
// Machine invariants and lemmas
// =============================================================================

/// Bound on a live stream's unconsumed bytes: a frame header (at most 16 bytes) plus a
/// buffered payload. Only SETTINGS, GOAWAY and MAX_PUSH_ID payloads are ever buffered, and the
/// header check caps them at MAX_SETTINGS_FRAME; unknown payloads are skipped as they arrive.
/// Equal to `16 + MAX_SETTINGS_FRAME`; the bound proof fails if that limit outgrows it.
pub const UNI_BUF_CAP: usize = 1040;

/// Frame types the control stream buffers and parses; every other type that passes the header
/// check is unknown, and its payload is skipped.
pub open spec fn is_buffered_control_frame(ty: u64) -> bool {
    ty == FRAME_SETTINGS || ty == FRAME_GOAWAY || ty == FRAME_MAX_PUSH_ID
}

/// The control stream after `skip` more payload bytes of an unknown frame are discarded.
pub open spec fn skipping(skip: u64, st: CtrlState, b: Seq<u8>, fin: bool) -> (
    Seq<SpecUniEvent>,
    Option<u64>,
) {
    if b.len() < skip {
        (Seq::empty(), fin_err(fin))
    } else {
        rfc_control(b.skip(skip as int), st, fin)
    }
}

/// What follows the consumed bytes, as the machine tracks it.
pub open spec fn tail_of(k: UniKind, st: CtrlState, skip: u64, b: Seq<u8>, fin: bool) -> (
    Seq<SpecUniEvent>,
    Option<u64>,
) {
    if k is Control {
        skipping(skip, st, b, fin)
    } else {
        rfc_tail(k, st, b, fin)
    }
}

/// For every suffix `t`, the spec of `all + t` is `emitted` followed by the tail spec of
/// `buf + t`: the invariant that makes the result independent of chunking.
pub open spec fn split_ok(
    all: Seq<u8>,
    seen0: SeenUni,
    emitted: Seq<SpecUniEvent>,
    k: UniKind,
    st: CtrlState,
    skip: u64,
    buf: Seq<u8>,
) -> bool {
    forall|t: Seq<u8>, f: bool| #[trigger]
        rfc_uni_stream(all + t, f, seen0) == prepend(emitted, tail_of(k, st, skip, buf + t, f))
}

/// `buf` completes nothing: without more bytes, only a FIN could still change the result.
pub open spec fn settled(k: UniKind, st: CtrlState, skip: u64, buf: Seq<u8>) -> bool {
    forall|f: bool| #[trigger]
        tail_of(k, st, skip, buf, f) == (Seq::<SpecUniEvent>::empty(), fin_err(f))
}

/// A critical stream between steps: `split_ok`, a bounded buffer that is empty while skipping,
/// and skipping only on the control stream.
pub open spec fn live(
    all: Seq<u8>,
    seen0: SeenUni,
    emitted: Seq<SpecUniEvent>,
    k: UniKind,
    st: CtrlState,
    skip: u64,
    buf: Seq<u8>,
) -> bool {
    &&& k is Control || k is QpackEncoder || k is QpackDecoder
    &&& split_ok(all, seen0, emitted, k, st, skip, buf)
    &&& buf.len() <= UNI_BUF_CAP
    &&& skip > 0 ==> buf.len() == 0
    &&& !(k is Control) ==> skip == 0
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

/// An unknown frame whose header is complete: the stream continues after its payload,
/// wherever that payload ends.
proof fn lemma_unknown_frame(
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
        rfc_control_header_error(st, ty, len) is None,
        !is_buffered_control_frame(ty),
    ensures
        rfc_control(b + t, st, f) == skipping(len, st, b.skip(h as int) + t, f),
{
    lemma_frame_header_prefix(b, t);
    lemma_frame_header_bounds(b);
    let bt = b + t;
    let r = b.skip(h as int) + t;
    assert(bt.skip(h as int) =~= r);
    if bt.len() >= h + len {
        assert(bt.skip(h + len) =~= r.skip(len as int));
        let x = rfc_control(r.skip(len as int), st, f);
        assert(Seq::<SpecUniEvent>::empty() + x.0 =~= x.0);
    }
}

/// Discarding `d` bytes of a pending skip.
proof fn lemma_skip_discard(skip: u64, st: CtrlState, b: Seq<u8>, d: nat, t: Seq<u8>, f: bool)
    requires
        d <= skip,
        d <= b.len(),
    ensures
        skipping(skip, st, b + t, f) == skipping((skip - d) as u64, st, b.skip(d as int) + t, f),
{
    let r = b.skip(d as int) + t;
    if (b + t).len() >= skip {
        assert((b + t).skip(skip as int) =~= r.skip(skip - d));
    }
}

proof fn lemma_skipping_zero(st: CtrlState, b: Seq<u8>, f: bool)
    ensures
        skipping(0, st, b, f) == rfc_control(b, st, f),
{
    assert(b.skip(0) =~= b);
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

/// Appending `p` to both the received bytes and the buffer preserves `split_ok`.
proof fn lemma_split_append(
    all: Seq<u8>,
    seen0: SeenUni,
    emitted: Seq<SpecUniEvent>,
    k: UniKind,
    st: CtrlState,
    skip: u64,
    buf: Seq<u8>,
    p: Seq<u8>,
)
    requires
        split_ok(all, seen0, emitted, k, st, skip, buf),
    ensures
        split_ok(all + p, seen0, emitted, k, st, skip, buf + p),
{
    assert forall|t: Seq<u8>, f: bool| #[trigger]
        rfc_uni_stream((all + p) + t, f, seen0) == prepend(
            emitted,
            tail_of(k, st, skip, (buf + p) + t, f),
        ) by {
        assert(all + (p + t) =~= (all + p) + t);
        assert(buf + (p + t) =~= (buf + p) + t);
        assert(rfc_uni_stream(all + (p + t), f, seen0) == prepend(
            emitted,
            tail_of(k, st, skip, buf + (p + t), f),
        ));
    }
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
    } else if (ty == FRAME_CANCEL_PUSH || ty == FRAME_GOAWAY || ty == FRAME_MAX_PUSH_ID) && len > 8 {
        Some(H3_FRAME_ERROR)
    } else if ty == FRAME_CANCEL_PUSH {
        Some(H3_ID_ERROR)
    } else if ty == FRAME_SETTINGS && len > MAX_SETTINGS_FRAME {
        Some(H3_EXCESSIVE_LOAD)
    } else {
        None
    }
}

/// Consumes the frame at the front of `b`, dispatching on its type before parsing any payload.
/// `Ok((0, 0))`: `b` is an incomplete header, or an incomplete buffered frame that passed its
/// header checks. `Ok((b.len(), s))` with `s > 0`: an unknown frame whose last `s` payload bytes
/// have not arrived. Otherwise `Ok((k, 0))`: one complete frame of `k` bytes.
fn control_frame(b: &[u8], st: &mut CtrlState, events: &mut Vec<UniEvent>) -> (r: Result<
    (usize, u64),
    u64,
>)
    ensures
        final(events)@.len() >= old(events)@.len(),
        final(events)@.take(old(events)@.len() as int) == old(events)@,
        match r {
            Ok((k, s)) => {
                &&& k <= b@.len()
                &&& k == 0 ==> {
                    &&& s == 0
                    &&& final(events)@ == old(events)@
                    &&& *final(st) == *old(st)
                    &&& b@.len() < UNI_BUF_CAP
                    &&& forall|f: bool| #[trigger]
                        rfc_control(b@, *old(st), f) == (Seq::<SpecUniEvent>::empty(), fin_err(f))
                }
                &&& k > 0 && s == 0 ==> ctrl_split(
                    b@,
                    *old(st),
                    views(final(events)@.skip(old(events)@.len() as int)),
                    b@.skip(k as int),
                    *final(st),
                )
                &&& s > 0 ==> {
                    &&& k == b@.len()
                    &&& final(events)@ == old(events)@
                    &&& *final(st) == *old(st)
                    &&& forall|t: Seq<u8>, f: bool| #[trigger]
                        rfc_control(b@ + t, *old(st), f) == skipping(s, *old(st), t, f)
                }
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
        FrameHeader::Incomplete => {
            proof {
                lemma_frame_header_bounds(b@);
            }
            return Ok((0, 0));
        },
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
    let avail = b.len() - hdr_len;
    if len > avail as u64 {
        if ty == FRAME_SETTINGS || ty == FRAME_GOAWAY || ty == FRAME_MAX_PUSH_ID {
            // The header check capped `len` at MAX_SETTINGS_FRAME.
            return Ok((0, 0));
        }
        // Unknown frame: drop the payload present and skip the rest as it arrives.
        proof {
            assert(b@.skip(hdr_len as int).skip(avail as int) =~= Seq::<u8>::empty());
            assert forall|t: Seq<u8>, f: bool| #[trigger]
                rfc_control(b@ + t, st1, f) == skipping((len - avail) as u64, st1, t, f) by {
                lemma_unknown_frame(b@, st1, hdr_len as nat, ty, len, t, f);
                lemma_skip_discard(len, st1, b@.skip(hdr_len as int), avail as nat, t, f);
                assert(Seq::<u8>::empty() + t =~= t);
            }
        }
        return Ok((b.len(), len - avail as u64));
    }
    let len = len as usize;
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
    Ok((k, 0))
}

/// Consumes the complete frames at the front of `buf`. `Ok((n, s))`: `s` bytes of an unknown
/// payload are still to be skipped (then `n == buf.len()`), and `buf[n..]` completes nothing.
fn control_frames(buf: &[u8], st: &mut CtrlState, events: &mut Vec<UniEvent>) -> (r: Result<
    (usize, u64),
    u64,
>)
    ensures
        final(events)@.len() >= old(events)@.len(),
        final(events)@.take(old(events)@.len() as int) == old(events)@,
        match r {
            Ok((n, s)) => {
                &&& n <= buf@.len()
                &&& s > 0 ==> n == buf@.len()
                &&& buf@.len() - n < UNI_BUF_CAP
                &&& forall|t: Seq<u8>, f: bool| #[trigger]
                    rfc_control(buf@ + t, *old(st), f) == prepend(
                        views(final(events)@.skip(old(events)@.len() as int)),
                        skipping(s, *final(st), buf@.skip(n as int) + t, f),
                    )
                &&& settled(UniKind::Control, *final(st), s, buf@.skip(n as int))
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
            Ok((k, s)) => {
                if k == 0 {
                    proof {
                        assert(events@.skip(ev1.len() as int) =~= Seq::<UniEvent>::empty());
                        assert(views(Seq::<UniEvent>::empty()) =~= Seq::<SpecUniEvent>::empty());
                        assert(done + Seq::<SpecUniEvent>::empty() =~= done);
                        assert forall|t: Seq<u8>, f: bool| #[trigger]
                            rfc_control(buf@ + t, st0, f) == prepend(
                                done,
                                skipping(0, *st, rest@ + t, f),
                            ) by {
                            lemma_skipping_zero(*st, rest@ + t, f);
                        }
                        assert forall|f: bool| #[trigger]
                            tail_of(UniKind::Control, *st, 0, rest@, f) == (
                                Seq::<SpecUniEvent>::empty(),
                                fin_err(f),
                            ) by {
                            lemma_skipping_zero(*st, rest@, f);
                        }
                    }
                    return Ok((pos, 0));
                }
                if s > 0 {
                    proof {
                        assert(events@.skip(ev1.len() as int) =~= Seq::<UniEvent>::empty());
                        assert(views(Seq::<UniEvent>::empty()) =~= Seq::<SpecUniEvent>::empty());
                        assert(done + Seq::<SpecUniEvent>::empty() =~= done);
                        assert(buf@.skip(buf@.len() as int) =~= Seq::<u8>::empty());
                        assert forall|t: Seq<u8>, f: bool| #[trigger]
                            rfc_control(buf@ + t, st0, f) == prepend(
                                done,
                                skipping(s, *st, buf@.skip(buf@.len() as int) + t, f),
                            ) by {
                            assert(Seq::<u8>::empty() + t =~= t);
                            assert(rfc_control(rest@ + t, st1, f) == skipping(s, st1, t, f));
                            let x = skipping(s, st1, t, f);
                            assert(done + x.0 =~= done + x.0);
                        }
                    }
                    return Ok((buf.len(), s));
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
    /// Received bytes not yet consumed: part of the type varint, or one incomplete frame header,
    /// SETTINGS/GOAWAY/MAX_PUSH_ID frame or QPACK instruction. Under UNI_BUF_CAP (proven).
    buf: Vec<u8>,
    ctrl: CtrlState,
    /// Payload bytes of an unknown control frame still to discard as they arrive.
    skip: u64,
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

    /// How many received bytes the stream holds unconsumed.
    pub closed spec fn buffered(&self) -> nat {
        self.buf@.len()
    }

    pub closed spec fn wf(&self) -> bool {
        &&& self.kind == kind_of_bytes(self.all@)
        &&& !self.done ==> wf_live(*self)
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
            skip: 0,
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
            !final(self).done() ==> final(self).buffered() < UNI_BUF_CAP,
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
        let ghost em0 = self.emitted@;
        self.done = true;
        proof {
            lemma_grew_refl(*self, events@);
            assert((all0 + data@) + Seq::<u8>::empty() =~= all0 + data@);
        }
        if let UniKind::Ignored = self.kind {
            let ghost buf0 = self.buf@;
            self.all = Ghost(all0 + data@);
            proof {
                lemma_decode_prefix(all0, data@);
                lemma_split_append(all0, self.seen0@, em0, self.kind, self.ctrl, self.skip, buf0, data@);
                assert forall|t: Seq<u8>, f: bool| #[trigger]
                    rfc_uni_stream(self.all@ + t, f, self.seen0@) == prepend(
                        em0,
                        tail_of(self.kind, self.ctrl, self.skip, self.buf@ + t, f),
                    ) by {
                    assert(rfc_uni_stream(self.all@ + t, f, self.seen0@) == prepend(
                        em0,
                        tail_of(self.kind, self.ctrl, self.skip, buf0 + data@ + t, f),
                    ));
                }
                assert(rfc_uni_stream(self.all@ + Seq::empty(), fin, self.seen0@) == prepend(
                    em0,
                    tail_of(self.kind, self.ctrl, self.skip, self.buf@ + Seq::empty(), fin),
                ));
            }
            self.done = fin;
            return Ok(());
        }
        let ghost was_undetermined = self.kind is Undetermined;
        let mut i: usize = 0;
        if let UniKind::Undetermined = self.kind {
            match self.determine(data, seen) {
                Err(e) => {
                    proof {
                        lemma_grew_refl(*self, events@);
                    }
                    return Err(e);
                },
                Ok(None) => {
                    proof {
                        lemma_grew_refl(*self, events@);
                    }
                    self.done = fin;
                    return Ok(());
                },
                Ok(Some(k)) => {
                    i = k;
                },
            }
        }
        let rest = slice_subrange(data, i, data.len());
        proof {
            assert(data@.take(i as int) + rest@ =~= data@);
            assert(self.all@ + rest@ =~= all0 + data@);
            if !was_undetermined {
                assert(data@.take(0) =~= Seq::<u8>::empty());
                assert(all0 + Seq::<u8>::empty() =~= all0);
                lemma_decode_prefix(all0, data@);
            }
        }
        let r = self.consume(rest, fin, events);
        match r {
            Ok(()) => {
                self.done = false;
                Ok(())
            },
            Err(e) => Err(e),
        }
    }

    /// Reads the stream type from at most the 8 bytes a varint can take. `Ok(Some(i))`: a
    /// critical stream, with `data[i..]` still to feed; `Ok(None)`: all of `data` is consumed.
    fn determine(&mut self, data: &[u8], seen: &mut SeenUni) -> (r: Result<Option<usize>, u64>)
        requires
            old(self).kind is Undetermined,
            wf_live(*old(self)),
        ensures
            final(self).seen0@ == *old(seen),
            *final(seen) == seen_after(*old(seen), old(self).all@ + data@),
            final(self).done == old(self).done,
            final(self).emitted@ == old(self).emitted@,
            final(self).kind == kind_of_bytes(old(self).all@ + data@),
            match r {
                Err(e) => {
                    &&& final(self).all@ == old(self).all@ + data@
                    &&& forall|f: bool| #[trigger]
                        rfc_uni_stream(final(self).all@, f, final(self).seen0@) == (
                            final(self).emitted@,
                            Some(e),
                        )
                },
                Ok(None) => {
                    &&& final(self).all@ == old(self).all@ + data@
                    &&& wf_live(*final(self))
                    &&& forall|f: bool| #[trigger]
                        rfc_uni_stream(final(self).all@, f, final(self).seen0@) == (
                            final(self).emitted@,
                            None::<u64>,
                        )
                },
                Ok(Some(i)) => {
                    &&& i <= data@.len()
                    &&& final(self).all@ == old(self).all@ + data@.take(i as int)
                    &&& live_s(*final(self))
                },
            },
    {
        let ghost all0 = self.all@;
        let ghost em0 = self.emitted@;
        self.seen0 = Ghost(*seen);
        let room = 8 - self.buf.len();
        let i = if data.len() < room {
            data.len()
        } else {
            room
        };
        let mut d = slice_to_vec(slice_subrange(data, 0, i));
        self.buf.append(&mut d);
        self.all = Ghost(all0 + data@.take(i as int));
        let ghost b = self.buf@;
        proof {
            assert(b =~= self.all@);
            assert(em0 =~= Seq::<SpecUniEvent>::empty());
            assert(data@.take(i as int) + data@.skip(i as int) =~= data@);
            assert(b + data@.skip(i as int) =~= all0 + data@);
        }
        let (n, ty) = match parse_varint(self.buf.as_slice()) {
            None => {
                proof {
                    lemma_decode_none_short(b);
                    assert(data@.take(i as int) =~= data@);
                }
                self.all = Ghost(all0 + data@);
                return Ok(None);
            },
            Some(x) => x,
        };
        proof {
            assert forall|t: Seq<u8>| #[trigger] rfc_varint_decode(b + t) == Some((n as nat, ty)) by {
                lemma_decode_prefix(b, t);
            }
            assert(rfc_varint_decode(b + data@.skip(i as int)) == Some((n as nat, ty)));
        }
        self.kind = kind_of(ty);
        if ty == STREAM_PUSH || (ty == STREAM_CONTROL && seen.control) || (ty
            == STREAM_QPACK_ENCODER && seen.encoder) || (ty == STREAM_QPACK_DECODER
            && seen.decoder) {
            self.all = Ghost(all0 + data@);
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
            self.all = Ghost(all0 + data@);
            proof {
                assert forall|t: Seq<u8>, f: bool| #[trigger]
                    rfc_uni_stream(self.all@ + t, f, self.seen0@) == prepend(
                        em0,
                        tail_of(UniKind::Ignored, self.ctrl, self.skip, self.buf@ + t, f),
                    ) by {
                    assert(b + (data@.skip(i as int) + t) =~= self.all@ + t);
                    assert(rfc_varint_decode(b + (data@.skip(i as int) + t)) == Some(
                        (n as nat, ty),
                    ));
                }
                assert(self.all@ + Seq::<u8>::empty() =~= self.all@);
                assert(rfc_uni_stream(self.all@ + Seq::empty(), false, self.seen0@) == prepend(
                    em0,
                    tail_of(UniKind::Ignored, self.ctrl, self.skip, self.buf@ + Seq::empty(), false),
                ));
                assert(rfc_uni_stream(self.all@ + Seq::empty(), true, self.seen0@) == prepend(
                    em0,
                    tail_of(UniKind::Ignored, self.ctrl, self.skip, self.buf@ + Seq::empty(), true),
                ));
            }
            return Ok(None);
        }
        self.buf = slice_to_vec(slice_subrange(self.buf.as_slice(), n, self.buf.len()));
        proof {
            assert forall|t: Seq<u8>, f: bool| #[trigger]
                rfc_uni_stream(self.all@ + t, f, self.seen0@) == prepend(
                    em0,
                    tail_of(self.kind, self.ctrl, self.skip, self.buf@ + t, f),
                ) by {
                assert(rfc_varint_decode(b + t) == Some((n as nat, ty)));
                assert((b + t).skip(n as int) =~= self.buf@ + t);
                lemma_skipping_zero(self.ctrl, self.buf@ + t, f);
                let x = tail_of(self.kind, self.ctrl, self.skip, self.buf@ + t, f);
                assert(em0 + x.0 =~= x.0);
            }
        }
        Ok(Some(i))
    }

    /// Feeds `seg` to a critical stream; then a FIN is H3_CLOSED_CRITICAL_STREAM.
    fn consume(&mut self, seg: &[u8], fin: bool, events: &mut Vec<UniEvent>) -> (r: Result<
        (),
        u64,
    >)
        requires
            live_s(*old(self)),
        ensures
            consumed(*old(self), *final(self), seg@, old(events)@, final(events)@, fin, r),
    {
        if let UniKind::Control = self.kind {
            self.consume_control(seg, fin, events)
        } else {
            let r = self.consume_qpack(seg, fin);
            proof {
                assert(events@.take(events@.len() as int) =~= events@);
                assert(events@.skip(events@.len() as int) =~= Seq::<UniEvent>::empty());
                assert(views(Seq::<UniEvent>::empty()) =~= Seq::<SpecUniEvent>::empty());
                assert(self.emitted@ + Seq::<SpecUniEvent>::empty() =~= self.emitted@);
            }
            r
        }
    }

    /// Unknown payloads are discarded straight from `seg`; `buf` only ever receives enough of
    /// `seg` to complete a pending frame, never more than UNI_BUF_CAP bytes in total.
    fn consume_control(&mut self, seg: &[u8], fin: bool, events: &mut Vec<UniEvent>) -> (r: Result<
        (),
        u64,
    >)
        requires
            live_s(*old(self)),
            old(self).kind is Control,
        ensures
            consumed(*old(self), *final(self), seg@, old(events)@, final(events)@, fin, r),
    {
        let mut j: usize = 0;
        proof {
            lemma_grew_refl(*self, events@);
            assert(self.all@ + seg@.take(0) =~= self.all@);
        }
        while j < seg.len()
            invariant
                j <= seg@.len(),
                self.kind is Control,
                same_id(*old(self), *self),
                grew(*old(self), *self, old(events)@, events@),
                self.all@ == old(self).all@ + seg@.take(j as int),
                live_s(*self),
            decreases seg@.len() - j,
        {
            let ghost s1 = *self;
            let ghost e1 = events@;
            let ghost all1 = self.all@;
            let settled_ok = self.settle(events);
            proof {
                lemma_grew_trans(*old(self), s1, *self, old(events)@, e1, events@);
            }
            let ghost s2 = *self;
            let ghost e2 = events@;
            let r = match settled_ok {
                Ok(()) => self.step(seg, j, events),
                Err(e) => {
                    proof {
                        lemma_grew_refl(*self, events@);
                    }
                    Err(e)
                },
            };
            proof {
                lemma_grew_trans(*old(self), s2, *self, old(events)@, e2, events@);
                assert(all1 + seg@.skip(j as int) =~= old(self).all@ + seg@);
            }
            match r {
                Err(e) => {
                    self.all = Ghost(old(self).all@ + seg@);
                    proof {
                        assert(self.all@ + Seq::<u8>::empty() =~= self.all@);
                        assert(rfc_uni_stream(all1 + seg@.skip(j as int), fin, self.seen0@) == (
                            self.emitted@,
                            Some(e),
                        ));
                    }
                    return Err(e);
                },
                Ok(j2) => {
                    proof {
                        assert(seg@.take(j as int) + seg@.subrange(j as int, j2 as int) =~= seg@.take(
                            j2 as int,
                        ));
                        assert(old(self).all@ + seg@.take(j as int) + seg@.subrange(j as int, j2 as int)
                            =~= old(self).all@ + seg@.take(j2 as int));
                    }
                    j = j2;
                },
            }
        }
        let ghost s1 = *self;
        let ghost e1 = events@;
        proof {
            assert(seg@.take(seg@.len() as int) =~= seg@);
        }
        match self.settle(events) {
            Err(e) => {
                proof {
                    lemma_grew_trans(*old(self), s1, *self, old(events)@, e1, events@);
                    assert(self.all@ + Seq::<u8>::empty() =~= self.all@);
                    assert(rfc_uni_stream(self.all@ + Seq::empty(), fin, self.seen0@) == (
                        self.emitted@,
                        Some(e),
                    ));
                }
                return Err(e);
            },
            Ok(()) => {},
        }
        proof {
            lemma_grew_trans(*old(self), s1, *self, old(events)@, e1, events@);
            assert(self.buf@ + Seq::<u8>::empty() =~= self.buf@);
            assert(self.all@ + Seq::<u8>::empty() =~= self.all@);
            assert(rfc_uni_stream(self.all@ + Seq::empty(), fin, self.seen0@) == prepend(
                self.emitted@,
                tail_of(self.kind, self.ctrl, self.skip, self.buf@ + Seq::empty(), fin),
            ));
            assert(self.emitted@ + Seq::<SpecUniEvent>::empty() =~= self.emitted@);
        }
        if fin {
            return Err(H3_CLOSED_CRITICAL_STREAM);
        }
        Ok(())
    }

    /// One step of progress through `seg[j..]` once `buf` is settled.
    fn step(&mut self, seg: &[u8], j: usize, events: &mut Vec<UniEvent>) -> (r: Result<
        usize,
        u64,
    >)
        requires
            ready(*old(self)),
            old(self).kind is Control,
            j < seg@.len(),
        ensures
            same_id(*old(self), *final(self)),
            grew(*old(self), *final(self), old(events)@, final(events)@),
            match r {
                Ok(j2) => {
                    &&& j < j2 <= seg@.len()
                    &&& final(self).all@ == old(self).all@ + seg@.subrange(j as int, j2 as int)
                    &&& live_s(*final(self))
                },
                Err(e) => {
                    &&& final(self).all@ == old(self).all@ + seg@.skip(j as int)
                    &&& dead_with(*final(self), e)
                },
            },
    {
        if self.skip > 0 {
            let j2 = self.discard(seg, j);
            proof {
                lemma_grew_refl(*self, events@);
            }
            Ok(j2)
        } else if self.buf.len() == 0 {
            let r = self.parse_direct(seg, j, events);
            proof {
                assert(seg@.skip(j as int) =~= seg@.subrange(j as int, seg@.len() as int));
            }
            match r {
                Ok(()) => Ok(seg.len()),
                Err(e) => Err(e),
            }
        } else {
            let j2 = self.top_up(seg, j);
            proof {
                lemma_grew_refl(*self, events@);
            }
            Ok(j2)
        }
    }

    /// Consumes the frames `buf` completes (a no-op while skipping or when `buf` is empty).
    fn settle(&mut self, events: &mut Vec<UniEvent>) -> (r: Result<(), u64>)
        requires
            live_s(*old(self)),
            old(self).kind is Control,
        ensures
            same_id(*old(self), *final(self)),
            grew(*old(self), *final(self), old(events)@, final(events)@),
            final(self).all@ == old(self).all@,
            match r {
                Ok(()) => ready(*final(self)),
                Err(e) => dead_with(*final(self), e),
            },
    {
        proof {
            lemma_grew_refl(*self, events@);
        }
        if self.skip > 0 || self.buf.len() == 0 {
            proof {
                lemma_settled_empty(self.ctrl, self.skip);
                assert(self.buf@ =~= Seq::<u8>::empty());
            }
            return Ok(());
        }
        let ghost ev0 = events@;
        let ghost b = self.buf@;
        let ghost st1 = self.ctrl;
        let ghost e1 = self.emitted@;
        let res = control_frames(self.buf.as_slice(), &mut self.ctrl, events);
        self.emitted = Ghost(e1 + views(events@.skip(ev0.len() as int)));
        match res {
            Err(e) => {
                proof {
                    lemma_settle_err(self.all@, self.seen0@, e1, st1, b, views(events@.skip(ev0.len() as int)), e);
                }
                Err(e)
            },
            Ok((n, s)) => {
                if n > 0 {
                    self.buf = slice_to_vec(slice_subrange(self.buf.as_slice(), n, self.buf.len()));
                }
                self.skip = s;
                proof {
                    assert(b.skip(n as int) =~= self.buf@);
                    lemma_settle(
                        self.all@,
                        self.seen0@,
                        e1,
                        st1,
                        b,
                        views(events@.skip(ev0.len() as int)),
                        self.ctrl,
                        s,
                        n as nat,
                    );
                }
                Ok(())
            },
        }
    }

    /// Discards the next bytes of `seg` that belong to a skipped unknown payload.
    fn discard(&mut self, seg: &[u8], j: usize) -> (r: usize)
        requires
            live_s(*old(self)),
            old(self).kind is Control,
            old(self).skip > 0,
            j < seg@.len(),
        ensures
            same_id(*old(self), *final(self)),
            final(self).emitted@ == old(self).emitted@,
            j < r <= seg@.len(),
            final(self).all@ == old(self).all@ + seg@.subrange(j as int, r as int),
            live_s(*final(self)),
    {
        let avail = seg.len() - j;
        let d: usize = if self.skip < avail as u64 {
            self.skip as usize
        } else {
            avail
        };
        let ghost p = seg@.subrange(j as int, j + d);
        let ghost all1 = self.all@;
        let ghost buf1 = self.buf@;
        let ghost skip1 = self.skip;
        self.skip = self.skip - d as u64;
        self.all = Ghost(self.all@ + p);
        proof {
            assert(p.skip(d as int) =~= Seq::<u8>::empty());
            assert forall|t: Seq<u8>, f: bool| #[trigger]
                rfc_uni_stream(self.all@ + t, f, self.seen0@) == prepend(
                    self.emitted@,
                    tail_of(self.kind, self.ctrl, self.skip, self.buf@ + t, f),
                ) by {
                assert(all1 + (p + t) =~= self.all@ + t);
                assert(buf1 + (p + t) =~= p + t);
                assert(self.buf@ + t =~= p.skip(d as int) + t);
                assert(rfc_uni_stream(all1 + (p + t), f, self.seen0@) == prepend(
                    self.emitted@,
                    tail_of(self.kind, self.ctrl, skip1, buf1 + (p + t), f),
                ));
                lemma_skip_discard(skip1, self.ctrl, p, d as nat, t, f);
            }
        }
        j + d
    }

    /// With nothing pending, parses frames straight from `seg[j..]` and keeps only its tail.
    fn parse_direct(&mut self, seg: &[u8], j: usize, events: &mut Vec<UniEvent>) -> (r: Result<
        (),
        u64,
    >)
        requires
            live_s(*old(self)),
            old(self).kind is Control,
            old(self).skip == 0,
            old(self).buf@.len() == 0,
            j <= seg@.len(),
        ensures
            same_id(*old(self), *final(self)),
            grew(*old(self), *final(self), old(events)@, final(events)@),
            final(self).all@ == old(self).all@ + seg@.skip(j as int),
            match r {
                Ok(()) => live_s(*final(self)),
                Err(e) => dead_with(*final(self), e),
            },
    {
        let s = slice_subrange(seg, j, seg.len());
        let ghost ev0 = events@;
        let ghost all1 = self.all@;
        let ghost buf1 = self.buf@;
        let ghost st1 = self.ctrl;
        let ghost e1 = self.emitted@;
        let res = control_frames(s, &mut self.ctrl, events);
        self.emitted = Ghost(e1 + views(events@.skip(ev0.len() as int)));
        self.all = Ghost(self.all@ + s@);
        let ghost mine = views(events@.skip(ev0.len() as int));
        proof {
            assert(s@ =~= seg@.skip(j as int));
            assert forall|t: Seq<u8>, f: bool|
                #![trigger rfc_uni_stream(self.all@ + t, f, self.seen0@)]
                rfc_uni_stream(self.all@ + t, f, self.seen0@) == prepend(
                    e1,
                    rfc_control(s@ + t, st1, f),
                ) by {
                assert(all1 + (s@ + t) =~= self.all@ + t);
                assert(buf1 + (s@ + t) =~= s@ + t);
                assert(rfc_uni_stream(all1 + (s@ + t), f, self.seen0@) == prepend(
                    e1,
                    tail_of(self.kind, st1, 0, buf1 + (s@ + t), f),
                ));
                lemma_skipping_zero(st1, s@ + t, f);
            }
        }
        match res {
            Err(e) => Err(e),
            Ok((n, sk)) => {
                self.buf = slice_to_vec(slice_subrange(s, n, s.len()));
                self.skip = sk;
                proof {
                    assert(s@.subrange(n as int, s@.len() as int) =~= s@.skip(n as int));
                    assert forall|t: Seq<u8>, f: bool| #[trigger]
                        rfc_uni_stream(self.all@ + t, f, self.seen0@) == prepend(
                            self.emitted@,
                            tail_of(self.kind, self.ctrl, self.skip, self.buf@ + t, f),
                        ) by {
                        let x = skipping(sk, self.ctrl, self.buf@ + t, f);
                        assert(e1 + (mine + x.0) =~= self.emitted@ + x.0);
                    }
                }
                Ok(())
            },
        }
    }

    /// Moves just enough of `seg[j..]` into `buf` to complete a pending frame (at most
    /// UNI_BUF_CAP - buf.len() bytes).
    fn top_up(&mut self, seg: &[u8], j: usize) -> (r: usize)
        requires
            live_s(*old(self)),
            old(self).skip == 0,
            old(self).buf@.len() < UNI_BUF_CAP,
            j < seg@.len(),
        ensures
            same_id(*old(self), *final(self)),
            final(self).emitted@ == old(self).emitted@,
            j < r <= seg@.len(),
            final(self).all@ == old(self).all@ + seg@.subrange(j as int, r as int),
            live_s(*final(self)),
    {
        let room = UNI_BUF_CAP - self.buf.len();
        let avail = seg.len() - j;
        let k = if avail < room {
            avail
        } else {
            room
        };
        let piece = slice_subrange(seg, j, j + k);
        let ghost all1 = self.all@;
        let ghost buf1 = self.buf@;
        let mut v = slice_to_vec(piece);
        self.buf.append(&mut v);
        self.all = Ghost(self.all@ + piece@);
        proof {
            lemma_split_append(all1, self.seen0@, self.emitted@, self.kind, self.ctrl, self.skip, buf1, piece@);
            assert(self.buf@ =~= buf1 + piece@);
        }
        j + k
    }

    /// QPACK streams emit no events, so only `buf` and the result change.
    fn consume_qpack(&mut self, seg: &[u8], fin: bool) -> (r: Result<(), u64>)
        requires
            live_s(*old(self)),
            old(self).kind is QpackEncoder || old(self).kind is QpackDecoder,
        ensures
            final(self).all@ == old(self).all@ + seg@,
            final(self).seen0@ == old(self).seen0@,
            final(self).kind == old(self).kind,
            final(self).done == old(self).done,
            final(self).emitted@ == old(self).emitted@,
            final(self).ctrl == old(self).ctrl,
            final(self).skip == old(self).skip,
            rfc_uni_stream(final(self).all@, fin, final(self).seen0@) == (
                final(self).emitted@,
                err_of(r),
            ),
            r is Ok ==> !fin && ready(*final(self)),
    {
        let ghost em0 = self.emitted@;
        let ghost all0 = self.all@;
        let ghost buf0 = self.buf@;
        let mut v = slice_to_vec(seg);
        self.buf.append(&mut v);
        self.all = Ghost(self.all@ + seg@);
        let ghost b = self.buf@;
        proof {
            lemma_split_append(all0, self.seen0@, em0, self.kind, self.ctrl, self.skip, buf0, seg@);
            assert(self.all@ + Seq::<u8>::empty() =~= self.all@);
            assert(b + Seq::<u8>::empty() =~= b);
            assert(rfc_uni_stream(self.all@ + Seq::empty(), fin, self.seen0@) == prepend(
                em0,
                tail_of(self.kind, self.ctrl, self.skip, b + Seq::empty(), fin),
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
                    tail_of(self.kind, self.ctrl, self.skip, self.buf@ + t, f),
                ) by {
                assert(rfc_uni_stream(self.all@ + t, f, self.seen0@) == prepend(
                    em0,
                    tail_of(self.kind, self.ctrl, self.skip, b + t, f),
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
            assert forall|f: bool| #[trigger]
                tail_of(self.kind, self.ctrl, self.skip, self.buf@, f) == (
                    Seq::<SpecUniEvent>::empty(),
                    fin_err(f),
                ) by {
                assert(rfc_tail(self.kind, self.ctrl, b.skip(n as int), f) == (
                    Seq::<SpecUniEvent>::empty(),
                    fin_err(f),
                ));
            }
        }
        if fin {
            return Err(H3_CLOSED_CRITICAL_STREAM);
        }
        Ok(())
    }
}

/// The QPACK tail spec ignores the complete instructions at the front of the buffer, and what
/// remains is at most one incomplete instruction.
proof fn lemma_qpack_split(k: UniKind, st: CtrlState, b: Seq<u8>, n: nat)
    requires
        k is QpackEncoder ==> rfc_encoder_stream(b) == Ok::<nat, u64>(n),
        k is QpackDecoder ==> rfc_decoder_stream(b) == Ok::<nat, u64>(n),
        k is QpackEncoder || k is QpackDecoder,
    ensures
        n <= b.len(),
        b.len() - n <= 1 + PREFIX_INT_MAX_CONT,
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

/// What `consume` guarantees, from `s0`/`e0` to `s1`/`e1`, having fed `seg`.
spec fn consumed(
    s0: UniStream,
    s1: UniStream,
    seg: Seq<u8>,
    e0: Seq<UniEvent>,
    e1: Seq<UniEvent>,
    fin: bool,
    r: Result<(), u64>,
) -> bool {
    &&& s1.all@ == s0.all@ + seg
    &&& s1.seen0@ == s0.seen0@
    &&& s1.kind == s0.kind
    &&& s1.done == s0.done
    &&& e1.len() >= e0.len()
    &&& e1.take(e0.len() as int) == e0
    &&& s1.emitted@ == s0.emitted@ + views(e1.skip(e0.len() as int))
    &&& rfc_uni_stream(s1.all@, fin, s1.seen0@) == (s1.emitted@, err_of(r))
    &&& r is Ok ==> !fin && ready(s1)
}

/// The part of `wf` that holds while the stream takes data.
spec fn wf_live(s: UniStream) -> bool {
    match s.kind {
        UniKind::Undetermined => {
            &&& s.all@ == s.buf@
            &&& s.buf@.len() < 8
            &&& s.emitted@.len() == 0
            &&& s.ctrl == ctrl_init()
            &&& s.skip == 0
        },
        UniKind::Ignored => {
            &&& s.buf@.len() == 0
            &&& split_ok(s.all@, s.seen0@, s.emitted@, s.kind, s.ctrl, s.skip, s.buf@)
        },
        _ => ready(s),
    }
}

spec fn live_s(s: UniStream) -> bool {
    live(s.all@, s.seen0@, s.emitted@, s.kind, s.ctrl, s.skip, s.buf@)
}

/// Live, under the cap, and nothing left in `buf` to consume.
spec fn ready(s: UniStream) -> bool {
    &&& live_s(s)
    &&& s.buf@.len() < UNI_BUF_CAP
    &&& settled(s.kind, s.ctrl, s.skip, s.buf@)
}

spec fn same_id(s0: UniStream, s1: UniStream) -> bool {
    &&& s1.seen0@ == s0.seen0@
    &&& s1.kind == s0.kind
    &&& s1.done == s0.done
}

/// `e1` extends `e0`, and `s1` records exactly the added events.
spec fn grew(s0: UniStream, s1: UniStream, e0: Seq<UniEvent>, e1: Seq<UniEvent>) -> bool {
    &&& e1.len() >= e0.len()
    &&& e1.take(e0.len() as int) == e0
    &&& s1.emitted@ == s0.emitted@ + views(e1.skip(e0.len() as int))
}

/// Every extension of what `s` received ends in error `e` after `s`'s events.
spec fn dead_with(s: UniStream, e: u64) -> bool {
    forall|t: Seq<u8>, f: bool| #[trigger]
        rfc_uni_stream(s.all@ + t, f, s.seen0@) == (s.emitted@, Some(e))
}

proof fn lemma_settled_empty(st: CtrlState, skip: u64)
    ensures
        settled(UniKind::Control, st, skip, Seq::empty()),
{
    assert forall|f: bool| #[trigger]
        tail_of(UniKind::Control, st, skip, Seq::empty(), f) == (
            Seq::<SpecUniEvent>::empty(),
            fin_err(f),
        ) by {
        lemma_skipping_zero(st, Seq::empty(), f);
        lemma_frame_header_bounds(Seq::<u8>::empty());
    }
}

/// Consuming what `control_frames` reports moves `split_ok` past those frames.
proof fn lemma_settle(
    all: Seq<u8>,
    seen0: SeenUni,
    e1: Seq<SpecUniEvent>,
    st1: CtrlState,
    b: Seq<u8>,
    mine: Seq<SpecUniEvent>,
    st2: CtrlState,
    s: u64,
    n: nat,
)
    requires
        split_ok(all, seen0, e1, UniKind::Control, st1, 0, b),
        n <= b.len(),
        forall|t: Seq<u8>, f: bool| #[trigger]
            rfc_control(b + t, st1, f) == prepend(mine, skipping(s, st2, b.skip(n as int) + t, f)),
    ensures
        split_ok(all, seen0, e1 + mine, UniKind::Control, st2, s, b.skip(n as int)),
{
    assert forall|t: Seq<u8>, f: bool| #[trigger]
        rfc_uni_stream(all + t, f, seen0) == prepend(
            e1 + mine,
            tail_of(UniKind::Control, st2, s, b.skip(n as int) + t, f),
        ) by {
        assert(rfc_uni_stream(all + t, f, seen0) == prepend(
            e1,
            tail_of(UniKind::Control, st1, 0, b + t, f),
        ));
        lemma_skipping_zero(st1, b + t, f);
        let x = skipping(s, st2, b.skip(n as int) + t, f);
        assert(rfc_control(b + t, st1, f) == prepend(mine, x));
        assert(e1 + (mine + x.0) =~= (e1 + mine) + x.0);
    }
}

proof fn lemma_settle_err(
    all: Seq<u8>,
    seen0: SeenUni,
    e1: Seq<SpecUniEvent>,
    st1: CtrlState,
    b: Seq<u8>,
    mine: Seq<SpecUniEvent>,
    e: u64,
)
    requires
        split_ok(all, seen0, e1, UniKind::Control, st1, 0, b),
        forall|t: Seq<u8>, f: bool| #[trigger] rfc_control(b + t, st1, f) == (mine, Some(e)),
    ensures
        forall|t: Seq<u8>, f: bool| #[trigger]
            rfc_uni_stream(all + t, f, seen0) == (e1 + mine, Some(e)),
{
    assert forall|t: Seq<u8>, f: bool| #[trigger]
        rfc_uni_stream(all + t, f, seen0) == (e1 + mine, Some(e)) by {
        assert(rfc_uni_stream(all + t, f, seen0) == prepend(
            e1,
            tail_of(UniKind::Control, st1, 0, b + t, f),
        ));
        lemma_skipping_zero(st1, b + t, f);
        assert(rfc_control(b + t, st1, f) == (mine, Some(e)));
    }
}

proof fn lemma_grew_refl(s: UniStream, e: Seq<UniEvent>)
    ensures
        grew(s, s, e, e),
{
    assert(e.take(e.len() as int) =~= e);
    assert(e.skip(e.len() as int) =~= Seq::<UniEvent>::empty());
    assert(views(Seq::<UniEvent>::empty()) =~= Seq::<SpecUniEvent>::empty());
    assert(s.emitted@ + Seq::<SpecUniEvent>::empty() =~= s.emitted@);
}

proof fn lemma_grew_trans(
    s0: UniStream,
    s1: UniStream,
    s2: UniStream,
    e0: Seq<UniEvent>,
    e1: Seq<UniEvent>,
    e2: Seq<UniEvent>,
)
    requires
        grew(s0, s1, e0, e1),
        grew(s1, s2, e1, e2),
    ensures
        grew(s0, s2, e0, e2),
{
    lemma_views_split(e1, e2, e0.len() as int);
    assert(s0.emitted@ + views(e1.skip(e0.len() as int)) + views(e2.skip(e1.len() as int))
        =~= s0.emitted@ + views(e2.skip(e0.len() as int)));
}

} // verus!
