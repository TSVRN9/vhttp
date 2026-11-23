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
use vstd::slice::slice_subrange;
use byteq::capvec::CapVec;
use byteq::queue::ByteQueue;
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

/// The SETTINGS pairs in the uni-stream events `e`.
pub open spec fn ev_pairs(e: Seq<SpecUniEvent>) -> nat
    decreases e.len(),
{
    if e.len() == 0 {
        0
    } else {
        match e.last() {
            SpecUniEvent::PeerSettings(p) => ev_pairs(e.drop_last()) + p.len(),
            _ => ev_pairs(e.drop_last()),
        }
    }
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

/// 1 until the peer's SETTINGS arrives: an empty SETTINGS frame is the one event-bearing control frame shorter than 3
/// bytes, and only the stream's first frame can be one.
spec fn tok(st: CtrlState) -> nat {
    if st.settings {
        0
    } else {
        1
    }
}

/// The control buffer between steps: an incomplete frame header, or an incomplete frame that passed its header
/// checks.
spec fn one_frame(b: Seq<u8>) -> bool {
    match rfc_frame_header(b) {
        None => true,
        Some((h, _, len)) => b.len() < h + len && h + len <= UNI_BUF_CAP,
    }
}

/// After a top-up: at most one frame, so a frame `settle` completes ends the buffer.
spec fn at_most_one(b: Seq<u8>) -> bool {
    match rfc_frame_header(b) {
        None => true,
        Some((h, _, len)) => b.len() <= h + len,
    }
}

/// The events a control stream may still return from `rem` more bytes of a call: one for the frame `buf` holds
/// (completed by at least one of them), then one per 3 bytes, an empty SETTINGS counting as 3.
spec fn ev_room(held: bool, st: CtrlState, rem: nat) -> nat {
    if held && rem > 0 {
        1 + rem / 3
    } else {
        (rem + tok(st)) / 3
    }
}

/// `control_frame`'s cost constant: per byte of the frame it completes, its payload parse (a SETTINGS payload within
/// MAX_SETTINGS_FRAME sorts at 275 per byte plus 25, `lemma_settings_cost`; any other at most `c_pfp()` per byte plus
/// 10), the 16-byte header parse (17) and the event push or the free of a dropped frame; the constant of a call that
/// completes none.
#[verifier::inline]
spec fn c_cf() -> nat {
    280
}

/// `control_frames`' cost constant: a `control_frame` and its loop iteration, per byte.
#[verifier::inline]
spec fn c_cfs() -> nat {
    281
}

/// `settle`'s constant beside the held bytes: a `control_frame` that completes nothing, `drop_front` (2) and 1.
#[verifier::inline]
spec fn c_set() -> nat {
    283
}

/// `step`'s cost per byte of the segment it consumes, with the held bytes' potential: `parse_direct` (`control_frames`
/// twice over, the tail's push and its `c_uni_frame()` per byte), the most of its three branches.
#[verifier::inline]
spec fn c_stp() -> nat {
    854
}

/// `consume`'s cost per byte of its segment: `step` and its loop iteration.
#[verifier::inline]
spec fn c_csm() -> nat {
    855
}

/// `on_data`'s cost per byte given (and per byte of the 16 the constant terms take): `consume`, `determine` (at most
/// 80) and 1.
#[verifier::inline]
pub open spec fn c_uni() -> nat {
    856
}

/// `on_data`'s cost per byte held before the call (the `F` term): the frame a call completes from its held bytes is
/// parsed once.
#[verifier::inline]
pub open spec fn c_uni_frame() -> nat {
    280
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

/// A type varint that decodes from `b` is all in `b.take(n)`, and is longer than any prefix `b.take(bl)` that did not
/// decode (split out of `determine` for the rlimit).
proof fn lemma_decode_take(b: Seq<u8>, n: nat, ty: u64, bl: nat)
    requires
        rfc_varint_decode(b) == Some((n, ty)),
        bl <= b.len(),
        rfc_varint_decode(b.take(bl as int)) is None,
    ensures
        bl < n <= b.len(),
        forall|t: Seq<u8>| #[trigger] rfc_varint_decode(b.take(n as int) + t) == Some((n, ty)),
{
    lemma_decode_len_bounds(b);
    let q = b.take(n as int);
    assert(q[0] == b[0]);
    assert(q.subrange(1, n as int) =~= b.subrange(1, n as int));
    assert(rfc_varint_decode(q) == rfc_varint_decode(b));
    if n <= bl {
        let p = b.take(bl as int);
        assert(q + p.skip(n as int) =~= p);
        lemma_decode_prefix(q, p.skip(n as int));
    }
    assert forall|t: Seq<u8>| #[trigger] rfc_varint_decode(b.take(n as int) + t) == Some((n, ty)) by {
        lemma_decode_prefix(q, t);
    }
}

/// A stream whose type varint decodes from `b`, with `b[n..]` still to feed (split out of
/// `determine` for the rlimit).
proof fn lemma_determined(b: Seq<u8>, n: nat, ty: u64, seen0: SeenUni)
    requires
        n <= b.len(),
        forall|t: Seq<u8>| #[trigger] rfc_varint_decode(b + t) == Some((n, ty)),
        ty != STREAM_PUSH,
        !rfc_duplicate(seen0, ty),
    ensures
        split_ok(b, seen0, Seq::empty(), rfc_kind_of(ty), ctrl_init(), 0, b.skip(n as int)),
{
    assert forall|t: Seq<u8>, f: bool| #[trigger]
        rfc_uni_stream(b + t, f, seen0) == prepend(
            Seq::empty(),
            tail_of(rfc_kind_of(ty), ctrl_init(), 0, b.skip(n as int) + t, f),
        ) by {
        assert(rfc_varint_decode(b + t) == Some((n, ty)));
        assert((b + t).skip(n as int) =~= b.skip(n as int) + t);
        lemma_skipping_zero(ctrl_init(), b.skip(n as int) + t, f);
        let x = tail_of(rfc_kind_of(ty), ctrl_init(), 0, b.skip(n as int) + t, f);
        assert(Seq::<SpecUniEvent>::empty() + x.0 =~= x.0);
    }
}

proof fn lemma_empty_events(e: Seq<SpecUniEvent>)
    requires
        e.len() == 0,
    ensures
        e == Seq::<SpecUniEvent>::empty(),
{
    assert(e =~= Seq::<SpecUniEvent>::empty());
}

proof fn lemma_empty_bytes(e: Seq<u8>)
    requires
        e.len() == 0,
    ensures
        e == Seq::<u8>::empty(),
{
    assert(e =~= Seq::<u8>::empty());
}

/// A push stream or a second critical stream of one type (split out of `determine` for the rlimit).
proof fn lemma_creation_err(b: Seq<u8>, n: nat, ty: u64, seen0: SeenUni)
    requires
        rfc_varint_decode(b) == Some((n, ty)),
        ty == STREAM_PUSH || rfc_duplicate(seen0, ty),
    ensures
        forall|f: bool| #[trigger]
            rfc_uni_stream(b, f, seen0) == (Seq::<SpecUniEvent>::empty(), Some(H3_STREAM_CREATION_ERROR)),
{
}

/// `wf_live` of a stream whose type has not arrived (for callers that hide `wf_live`).
proof fn lemma_undetermined_def(s: UniStream)
    requires
        s.kind is Undetermined,
    ensures
        wf_live(s) == (s.buf.wf() && s.all@ == s.buf@ && s.buf@.len() < 8 && s.emitted@.len() == 0 && s.ctrl
            == ctrl_init() && s.skip == 0),
{
}

/// `wf_live` of a stream of an unknown type (for callers that hide `wf_live`).
proof fn lemma_ignored_def(s: UniStream)
    requires
        s.kind is Ignored,
    ensures
        wf_live(s) == (s.buf.wf() && s.buf@.len() == 0 && split_ok(
            s.all@,
            s.seen0@,
            s.emitted@,
            s.kind,
            s.ctrl,
            s.skip,
            s.buf@,
        )),
{
}

/// A critical stream whose type varint is all of `q`: live with nothing held (split out of `determine` for the
/// rlimit).
proof fn lemma_determined_live(s: UniStream, q: Seq<u8>, n: nat, ty: u64)
    requires
        s.all@ == q,
        n == q.len(),
        forall|t: Seq<u8>| #[trigger] rfc_varint_decode(q + t) == Some((n, ty)),
        ty != STREAM_PUSH,
        !rfc_duplicate(s.seen0@, ty),
        s.kind == rfc_kind_of(ty),
        s.kind is Control || s.kind is QpackEncoder || s.kind is QpackDecoder,
        s.buf.wf(),
        s.buf@.len() == 0,
        s.ctrl == ctrl_init(),
        s.skip == 0,
        s.emitted@ == Seq::<SpecUniEvent>::empty(),
    ensures
        live_s(s),
{
    lemma_determined(q, n, ty, s.seen0@);
    assert(q.skip(n as int) =~= s.buf@);
}

/// No stream type yet: nothing happens (split out of `determine` for the rlimit).
proof fn lemma_undetermined(b: Seq<u8>, seen0: SeenUni)
    requires
        rfc_varint_decode(b) is None,
    ensures
        forall|f: bool| #[trigger]
            rfc_uni_stream(b, f, seen0) == (Seq::<SpecUniEvent>::empty(), None::<u64>),
{
}

/// An ignored stream type with `rest` after `b`: the stream is discarded (split out of
/// `determine` for the rlimit).
proof fn lemma_determined_ignored(b: Seq<u8>, n: nat, ty: u64, seen0: SeenUni, rest: Seq<u8>)
    requires
        rfc_varint_decode(b) == Some((n, ty)),
        ty != STREAM_PUSH,
        !rfc_duplicate(seen0, ty),
        rfc_kind_of(ty) is Ignored,
    ensures
        split_ok(b + rest, seen0, Seq::empty(), UniKind::Ignored, ctrl_init(), 0, Seq::empty()),
        forall|f: bool| #[trigger]
            rfc_uni_stream(b + rest, f, seen0) == (Seq::<SpecUniEvent>::empty(), None::<u64>),
{
    assert forall|t: Seq<u8>, f: bool| #[trigger]
        rfc_uni_stream((b + rest) + t, f, seen0) == prepend(
            Seq::empty(),
            tail_of(UniKind::Ignored, ctrl_init(), 0, Seq::<u8>::empty() + t, f),
        ) by {
        assert(b + (rest + t) =~= (b + rest) + t);
        lemma_decode_prefix(b, rest + t);
        assert(Seq::<SpecUniEvent>::empty() + Seq::<SpecUniEvent>::empty() =~= Seq::<
            SpecUniEvent,
        >::empty());
    }
    assert forall|f: bool| #[trigger]
        rfc_uni_stream(b + rest, f, seen0) == (Seq::<SpecUniEvent>::empty(), None::<u64>) by {
        assert(b + (rest + Seq::empty()) =~= b + rest);
        lemma_decode_prefix(b, rest + Seq::empty());
        assert(Seq::<SpecUniEvent>::empty() + Seq::<SpecUniEvent>::empty() =~= Seq::<
            SpecUniEvent,
        >::empty());
    }
}

/// Data on an ignored stream changes nothing (split out of `on_data` for the rlimit).
proof fn lemma_ignored_data(
    all0: Seq<u8>,
    seen0: SeenUni,
    em0: Seq<SpecUniEvent>,
    st: CtrlState,
    skip: u64,
    buf: Seq<u8>,
    data: Seq<u8>,
    fin: bool,
)
    requires
        rfc_varint_decode(all0) is Some,
        split_ok(all0, seen0, em0, UniKind::Ignored, st, skip, buf),
    ensures
        rfc_varint_decode(all0 + data) == rfc_varint_decode(all0),
        split_ok(all0 + data, seen0, em0, UniKind::Ignored, st, skip, buf),
        rfc_uni_stream(all0 + data, fin, seen0) == (em0, None::<u64>),
{
    lemma_decode_prefix(all0, data);
    lemma_split_append(all0, seen0, em0, UniKind::Ignored, st, skip, buf, data);
    assert forall|t: Seq<u8>, f: bool| #[trigger]
        rfc_uni_stream((all0 + data) + t, f, seen0) == prepend(
            em0,
            tail_of(UniKind::Ignored, st, skip, buf + t, f),
        ) by {
        assert(rfc_uni_stream((all0 + data) + t, f, seen0) == prepend(
            em0,
            tail_of(UniKind::Ignored, st, skip, (buf + data) + t, f),
        ));
    }
    assert((all0 + data) + Seq::<u8>::empty() =~= all0 + data);
    assert(buf + Seq::<u8>::empty() =~= buf);
    assert(rfc_uni_stream((all0 + data) + Seq::empty(), fin, seen0) == prepend(
        em0,
        tail_of(UniKind::Ignored, st, skip, buf + Seq::empty(), fin),
    ));
    assert(em0 + Seq::<SpecUniEvent>::empty() =~= em0);
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

/// `ev_pairs` adds up over a concatenation.
proof fn lemma_pairs_append(a: Seq<SpecUniEvent>, b: Seq<SpecUniEvent>)
    ensures
        ev_pairs(a + b) == ev_pairs(a) + ev_pairs(b),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
    } else {
        lemma_pairs_append(a, b.drop_last());
        assert((a + b).drop_last() =~= a + b.drop_last());
        assert((a + b).last() == b.last());
    }
}

/// The pairs of the events after `a` add up over an extension of `s1` to `s2`.
proof fn lemma_pairs_split(s1: Seq<UniEvent>, s2: Seq<UniEvent>, a: int)
    requires
        0 <= a <= s1.len() <= s2.len(),
        s2.take(s1.len() as int) == s1,
    ensures
        ev_pairs(views(s2.skip(a))) == ev_pairs(views(s1.skip(a))) + ev_pairs(views(s2.skip(s1.len() as int))),
{
    lemma_views_split(s1, s2, a);
    lemma_pairs_append(views(s1.skip(a)), views(s2.skip(s1.len() as int)));
}

/// No events added: no pairs.
proof fn lemma_pairs_none(s: Seq<UniEvent>)
    ensures
        ev_pairs(views(s.skip(s.len() as int))) == 0,
{
    assert(views(s.skip(s.len() as int)) =~= Seq::<SpecUniEvent>::empty());
}

/// One event pushed after `s`: its pairs.
proof fn lemma_pairs_push(s: Seq<UniEvent>, x: UniEvent)
    ensures
        ev_pairs(views(s.push(x).skip(s.len() as int))) == ev_pairs(seq![x@]),
        ev_pairs(seq![x@]) == match x@ {
            SpecUniEvent::PeerSettings(p) => p.len(),
            _ => 0,
        },
{
    assert(views(s.push(x).skip(s.len() as int)) =~= seq![x@]);
    assert(seq![x@].drop_last() =~= Seq::<SpecUniEvent>::empty());
    assert(seq![x@].last() == x@);
    assert(ev_pairs(Seq::<SpecUniEvent>::empty()) == 0);
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
/// have not arrived. Otherwise `Ok((k, 0))`: one complete frame of `k` bytes. The header is parsed from `b`'s first 16
/// bytes at most (N5). It returns at most one event, from a frame of at least 3 bytes or the stream's first (an empty
/// SETTINGS has 2).
fn control_frame(b: &[u8], st: &mut CtrlState, events: &mut CapVec<UniEvent>) -> (r: (
    Result<(usize, u64), u64>,
    Ghost<nat>,
))
    requires
        old(events).wf(),
        b@.len() + tok(*old(st)) >= 3 ==> old(events)@.len() < old(events).cap(),
    ensures
        final(events).wf(),
        final(events).cap() == old(events).cap(),
        final(events)@.len() >= old(events)@.len(),
        final(events)@.len() <= old(events)@.len() + 1,
        final(events)@.take(old(events)@.len() as int) == old(events)@,
        final(events)@.len() > old(events)@.len() ==> (r.0 matches Ok((k, s)) && s == 0 && 3 <= k + tok(*old(st))
            && tok(*final(st)) == 0),
        tok(*final(st)) <= tok(*old(st)),
        2 * ev_pairs(views(final(events)@.skip(old(events)@.len() as int))) <= match r.0 {
            Ok((k, _)) => k as nat,
            Err(_) => 0nat,
        },
        match r.0 {
            Ok((k, s)) => {
                &&& k <= b@.len()
                &&& k == 0 ==> {
                    &&& s == 0
                    &&& final(events)@ == old(events)@
                    &&& *final(st) == *old(st)
                    &&& b@.len() < UNI_BUF_CAP
                    &&& one_frame(b@)
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
                &&& k > 0 && s == 0 ==> (rfc_frame_header(b@) matches Some((h, _, len)) && k == h + len)
                &&& s > 0 ==> {
                    &&& k == b@.len()
                    &&& final(events)@ == old(events)@
                    &&& *final(st) == *old(st)
                    &&& forall|t: Seq<u8>, f: bool| #[trigger]
                        rfc_control(b@ + t, *old(st), f) == skipping(s, *old(st), t, f)
                }
                &&& if k > 0 && s == 0 {
                    r.1@ <= c_cf() * k
                } else {
                    r.1@ <= c_cf()
                }
            },
            Err(e) => {
                &&& final(events)@ == old(events)@
                &&& forall|t: Seq<u8>, f: bool| #[trigger]
                    rfc_control(b@ + t, *old(st), f) == (Seq::<SpecUniEvent>::empty(), Some(e))
                &&& r.1@ <= c_cf() * (b@.len() + 1)
            },
        },
{
    hide(rfc_control);
    hide(rfc_frame_payload);
    hide(rfc_varint_decode);
    hide(skipping);
    let ghost st1 = *st;
    let ghost ev0 = events@;
    proof {
        assert(events@.take(ev0.len() as int) =~= ev0);
        lemma_pairs_none(ev0);
    }
    let m = if b.len() < 16 {
        b.len()
    } else {
        16
    };
    let hp = slice_subrange(b, 0, m);
    proof {
        assert(hp@ =~= b@.take(m as int));
        crate::request::lemma_header_take(b@, m as int);
        lemma_frame_header_bounds(b@);
    }
    // The header parse's proved cost: at most c_fhdr() (17).
    let (fh, Ghost(ch)) = parse_frame_header_w(hp);
    let (ty, len, hdr_len) = match fh {
        FrameHeader::Incomplete => {
            proof {
                lemma_control_incomplete(b@, st1);
            }
            return (Ok((0, 0)), Ghost(ch));
        },
        FrameHeader::Complete { ty, len, hdr_len } => (ty, len, hdr_len),
    };
    if let Some(e) = control_header_error(st, ty, len) {
        proof {
            assert forall|t: Seq<u8>, f: bool| #[trigger]
                rfc_control(b@ + t, st1, f) == (Seq::<SpecUniEvent>::empty(), Some(e)) by {
                lemma_control_frame(b@, st1, hdr_len as nat, ty, len, t, f);
            }
        }
        return (Err(e), Ghost(ch + 1));
    }
    let avail = b.len() - hdr_len;
    if len > avail as u64 {
        if ty == FRAME_SETTINGS || ty == FRAME_GOAWAY || ty == FRAME_MAX_PUSH_ID {
            // The header check capped `len` at MAX_SETTINGS_FRAME.
            proof {
                lemma_control_incomplete(b@, st1);
            }
            return (Ok((0, 0)), Ghost(ch + 1));
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
        return (Ok((b.len(), len - avail as u64)), Ghost(ch + 1));
    }
    let len = len as usize;
    let k = hdr_len + len;
    let payload = slice_subrange(b, hdr_len, k);
    proof {
        assert(payload@ =~= b@.subrange(hdr_len as int, k as int));
    }
    let (pr, Ghost(wp)) = parse_frame_payload(ty, payload);
    proof {
        lemma_payload_cost(ty, len as nat, wp);
    }
    let frame = match pr {
        Ok(f) => f,
        Err(e) => {
            proof {
                assert forall|t: Seq<u8>, f: bool| #[trigger]
                    rfc_control(b@ + t, st1, f) == (Seq::<SpecUniEvent>::empty(), Some(e)) by {
                    lemma_control_frame(b@, st1, hdr_len as nat, ty, len as u64, t, f);
                }
            }
            return (Err(e), Ghost(wp + ch + 1));
        },
    };
    let ghost fv = frame@;
    proof {
        lemma_event_frame_len(ty, payload@, fv);
    }
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
        // A dropped HEADERS or PUSH_PROMISE frame frees its buffer: one unit of the 20 charged below.
        _ => false,
    };
    if id_err {
        proof {
            assert forall|t: Seq<u8>, f: bool| #[trigger]
                rfc_control(b@ + t, st1, f) == (Seq::<SpecUniEvent>::empty(), Some(H3_ID_ERROR)) by {
                lemma_control_frame(b@, st1, hdr_len as nat, ty, len as u64, t, f);
            }
        }
        return (Err(H3_ID_ERROR), Ghost(wp + ch + 3));
    }
    proof {
        let (evs, st2) = rfc_control_frame(st1, fv)->Ok_0;
        assert(*st == st2);
        let mine = views(events@.skip(ev0.len() as int));
        if events@.len() > ev0.len() {
            let x = events@.last();
            assert(events@ == ev0.push(x));
            lemma_pairs_push(ev0, x);
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
    (Ok((k, 0)), Ghost(wp + ch + 3))
}

/// A control buffer that completes no frame: an incomplete header, or a frame that passed its header checks and whose
/// payload has not all arrived (split out of `control_frame` for the rlimit).
proof fn lemma_control_incomplete(b: Seq<u8>, st: CtrlState)
    requires
        rfc_frame_header(b) matches Some((h, ty, len)) ==> rfc_control_header_error(st, ty, len) is None && b.len()
            < h + len,
    ensures
        forall|f: bool| #[trigger] rfc_control(b, st, f) == (Seq::<SpecUniEvent>::empty(), fin_err(f)),
{
}

/// The frame types that return an event, and a GOAWAY or MAX_PUSH_ID payload is a varint, so at least one byte (split
/// out of `control_frame` for the rlimit).
proof fn lemma_event_frame_len(ty: u64, p: Seq<u8>, fv: SpecFrame)
    requires
        rfc_frame_payload(ty, p) == Ok::<SpecFrame, u64>(fv),
    ensures
        fv is Goaway || fv is MaxPushId ==> p.len() >= 1,
        fv is Settings ==> ty == FRAME_SETTINGS,
        fv is Goaway ==> ty == FRAME_GOAWAY,
        fv is MaxPushId ==> ty == FRAME_MAX_PUSH_ID,
{
    lemma_decode_len_bounds(p);
}

/// `parse_frame_payload`'s cost on a frame that passed the control stream's header checks: SETTINGS within
/// MAX_SETTINGS_FRAME is linear (split out of `control_frame` for the rlimit).
proof fn lemma_payload_cost(ty: u64, len: nat, wp: nat)
    requires
        ty == FRAME_SETTINGS ==> len <= MAX_SETTINGS_FRAME,
        ty == FRAME_SETTINGS ==> wp <= c_pset() * (len * (clog2(len) + 1) + 1),
        ty != FRAME_SETTINGS ==> wp <= c_pfp() * (len + 1),
    ensures
        wp + 20 <= c_cf() * (len + 2),
{
    if ty == FRAME_SETTINGS {
        lemma_settings_cost(len);
    }
}

/// Consumes the complete frames at the front of `buf`. `Ok((n, s))`: `s` bytes of an unknown
/// payload are still to be skipped (then `n == buf.len()`), and `buf[n..]` completes nothing. It returns at most one
/// event per 3 bytes of `buf`, the stream's first frame's counting as 3 (`tok`).
fn control_frames(buf: &[u8], st: &mut CtrlState, events: &mut CapVec<UniEvent>) -> (r: (
    Result<(usize, u64), u64>,
    Ghost<nat>,
))
    requires
        old(events).wf(),
        old(events)@.len() + (buf@.len() + tok(*old(st))) / 3 <= old(events).cap(),
    ensures
        final(events).wf(),
        final(events).cap() == old(events).cap(),
        final(events)@.len() >= old(events)@.len(),
        final(events)@.take(old(events)@.len() as int) == old(events)@,
        r.1@ <= c_cfs() * (buf@.len() + 1),
        2 * ev_pairs(views(final(events)@.skip(old(events)@.len() as int))) <= match r.0 {
            Ok((n, _)) => n as nat,
            Err(_) => buf@.len(),
        },
        match r.0 {
            Ok((n, s)) => {
                &&& n <= buf@.len()
                &&& s > 0 ==> n == buf@.len()
                &&& buf@.len() - n < UNI_BUF_CAP
                &&& one_frame(buf@.skip(n as int))
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
    hide(rfc_control);
    hide(rfc_frame_header);
    hide(rfc_frame_payload);
    hide(rfc_varint_decode);
    let ghost st0 = *st;
    let ghost ev0 = events@;
    let ghost mut work: nat = 0;
    let mut pos: usize = 0;
    proof {
        lemma_pairs_none(ev0);
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
    while pos < buf.len()
        invariant
            ev0 == old(events)@,
            st0 == *old(st),
            pos <= buf@.len(),
            events.wf(),
            events.cap() == old(events).cap(),
            events@.len() >= ev0.len(),
            events@.take(ev0.len() as int) == ev0,
            events@.len() + (buf@.len() - pos + tok(*st)) / 3 <= events.cap(),
            work <= c_cfs() * pos,
            2 * ev_pairs(views(events@.skip(ev0.len() as int))) <= pos,
            ctrl_split(buf@, st0, views(events@.skip(ev0.len() as int)), buf@.skip(pos as int), *st),
        decreases buf@.len() - pos,
    {
        let rest = slice_subrange(buf, pos, buf.len());
        assert(rest@ =~= buf@.skip(pos as int));
        let ghost done = views(events@.skip(ev0.len() as int));
        let ghost st1 = *st;
        let ghost ev1 = events@;
        let (r, Ghost(w)) = control_frame(rest, st, events);
        proof {
            lemma_pairs_split(ev1, events@, ev0.len() as int);
            lemma_views_split(ev1, events@, ev0.len() as int);
            let mine = views(events@.skip(ev1.len() as int));
            assert(views(events@.skip(ev0.len() as int)) == done + mine);
            // this iteration's charge, before the exits after it (rca-early-return-cost)
            work = work + w + 1;
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
                return (Err(e), Ghost(work));
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
                    return (Ok((pos, 0)), Ghost(work));
                }
                if s > 0 {
                    proof {
                        assert(events@.skip(ev1.len() as int) =~= Seq::<UniEvent>::empty());
                        assert(views(Seq::<UniEvent>::empty()) =~= Seq::<SpecUniEvent>::empty());
                        assert(done + Seq::<SpecUniEvent>::empty() =~= done);
                        assert(buf@.skip(buf@.len() as int) =~= Seq::<u8>::empty());
                        lemma_frame_header_bounds(Seq::<u8>::empty());
                        lemma_settled_empty(*st, s);
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
                    return (Ok((buf.len(), s)), Ghost(work));
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
    proof {
        assert(buf@.skip(pos as int) =~= Seq::<u8>::empty());
        lemma_frame_header_bounds(Seq::<u8>::empty());
        lemma_settled_empty(*st, 0);
        assert forall|t: Seq<u8>, f: bool| #[trigger]
            rfc_control(buf@ + t, st0, f) == prepend(
                views(events@.skip(ev0.len() as int)),
                skipping(0, *st, buf@.skip(pos as int) + t, f),
            ) by {
            lemma_skipping_zero(*st, buf@.skip(pos as int) + t, f);
        }
    }
    (Ok((pos, 0)), Ghost(work + 1))
}

/// One peer-initiated unidirectional stream.
pub struct UniStream {
    kind: UniKind,
    /// Received bytes not yet consumed: part of the type varint, or one incomplete frame header,
    /// SETTINGS/GOAWAY/MAX_PUSH_ID frame or QPACK instruction. Under UNI_BUF_CAP (proven).
    buf: ByteQueue,
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
        &&& self.buf.wf()
        &&& self.kind == kind_of_bytes(self.all@)
        &&& !self.done ==> wf_live(*self)
    }

    pub fn new() -> (r: Self)
        ensures
            r.wf(),
            r.all() == Seq::<u8>::empty(),
            r.emitted() == Seq::<SpecUniEvent>::empty(),
            !r.done(),
            r.buffered() == 0,
    {
        let r = UniStream {
            kind: UniKind::Undetermined,
            buf: ByteQueue::new(),
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

    pub fn buffered_len(&self) -> (r: usize)
        requires
            self.wf(),
        ensures
            r == self.buffered(),
    {
        self.buf.len()
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
    /// byte received, so they don't depend on how the bytes were chunked. A call returns at most `data.len() / 3 + 1`
    /// events and costs at most `c_uni()` per byte given (and 16 more) plus `c_uni_frame()` per byte held before it
    /// (`fed`).
    pub fn on_data(
        &mut self,
        data: &[u8],
        fin: bool,
        seen: &mut SeenUni,
        events: &mut CapVec<UniEvent>,
    ) -> (r: (Result<(), u64>, Ghost<nat>))
        requires
            old(self).wf(),
            !old(self).done(),
            old(events).wf(),
            old(events)@.len() + data@.len() / 3 + 1 <= old(events).cap(),
        ensures
            fed(*old(self), *final(self), data@, fin, *old(seen), *final(seen), *old(events), *final(events), r.0, r.1@),
    {
        hide(fed);
        hide(rfc_uni_stream);
        hide(tail_of);
        hide(ready);
        hide(live_s);
        hide(split_ok);
        hide(one_frame);
        hide(rfc_varint_decode);
        hide(kind_of_bytes);
        hide(consumed);
        hide(wf_live);
        let ghost s0 = *self;
        let ghost seen0 = *seen;
        let ghost e0 = *events;
        proof {
            lemma_wf_unfold(s0);
        }
        if let UniKind::Ignored = self.kind {
            self.all = Ghost(s0.all@ + data@);
            self.done = fin;
            proof {
                lemma_fed_ignored(s0, *self, data@, fin, seen0, e0);
            }
            return (Ok(()), Ghost(1));
        }
        self.done = true;
        let mut i: usize = 0;
        let ghost mut wd: nat = 0;
        if let UniKind::Undetermined = self.kind {
            proof {
                lemma_undetermined_done(s0, *self);
            }
            let (dr, Ghost(w)) = self.determine(data, seen);
            match dr {
                Err(e) => {
                    proof {
                        lemma_fed_det_err(s0, *self, data@, fin, seen0, *seen, e0, e, w);
                    }
                    return (Err(e), Ghost(w + 1));
                },
                Ok(None) => {
                    let ghost s1 = *self;
                    self.done = fin;
                    proof {
                        lemma_fed_det_none(s0, s1, *self, data@, fin, seen0, *seen, e0, w);
                    }
                    return (Ok(()), Ghost(w + 1));
                },
                Ok(Some(k)) => {
                    proof {
                        wd = w;
                        lemma_live_empty(*self);
                    }
                    i = k;
                },
            }
        } else {
            proof {
                lemma_set_done(s0, true);
            }
        }
        let ghost sm = *self;
        let ghost seen1 = *seen;
        let rest = slice_subrange(data, i, data.len());
        let (r, Ghost(wc)) = self.consume(rest, fin, events);
        let ghost sc = *self;
        if r.is_ok() {
            self.done = false;
        }
        proof {
            lemma_fed_consume(s0, sm, sc, *self, data@, i as nat, rest@, fin, seen0, seen1, e0, *events, r, wd, wc);
        }
        (r, Ghost(wd + wc + 1))
    }

    /// Reads the stream type from at most the 8 bytes a varint can take. `Ok(Some(i))`: a
    /// critical stream, with `data[i..]` still to feed and nothing held (bytes after the varint stay in `data`);
    /// `Ok(None)`: all of `data` is consumed (`determined`).
    #[verifier::spinoff_prover]
    fn determine(&mut self, data: &[u8], seen: &mut SeenUni) -> (r: (Result<Option<usize>, u64>, Ghost<nat>))
        requires
            old(self).kind is Undetermined,
            old(self).kind == kind_of_bytes(old(self).all@),
            wf_live(*old(self)),
        ensures
            determined(*old(self), *final(self), data@, *old(seen), *final(seen), r.0, r.1@),
    {
        hide(determined);
        hide(rfc_varint_decode);
        hide(live_s);
        hide(wf_live);
        hide(rfc_uni_stream);
        hide(kind_of_bytes);
        hide(seen_after);
        let ghost s0 = *self;
        let ghost seen0 = *seen;
        proof {
            lemma_undetermined_def(s0);
        }
        self.seen0 = Ghost(*seen);
        let bl = self.buf.len();
        let room = 8 - bl;
        let i = if data.len() < room {
            data.len()
        } else {
            room
        };
        let head = slice_subrange(data, 0, i);
        let Ghost(wp) = self.buf.push_slice(head);
        let ghost b = self.buf@;
        // The varint parse's proved cost: at most c_varint() (8).
        let (pv, Ghost(cv)) = parse_varint_w(self.buf.as_slice());
        let (n, ty) = match pv {
            None => {
                self.all = Ghost(s0.all@ + data@);
                proof {
                    lemma_det_none(s0, *self, data@, i as nat, head@, seen0, (wp + cv) as nat);
                }
                return (Ok(None), Ghost(wp + cv));
            },
            Some(x) => x,
        };
        self.kind = kind_of(ty);
        if ty == STREAM_PUSH || (ty == STREAM_CONTROL && seen.control) || (ty
            == STREAM_QPACK_ENCODER && seen.encoder) || (ty == STREAM_QPACK_DECODER
            && seen.decoder) {
            self.all = Ghost(s0.all@ + data@);
            proof {
                lemma_det_err(s0, *self, data@, i as nat, head@, n as nat, ty, seen0, (wp + cv) as nat);
            }
            return (Err(H3_STREAM_CREATION_ERROR), Ghost(wp + cv));
        }
        seen.control = seen.control || ty == STREAM_CONTROL;
        seen.encoder = seen.encoder || ty == STREAM_QPACK_ENCODER;
        seen.decoder = seen.decoder || ty == STREAM_QPACK_DECODER;
        let Ghost(wd) = self.buf.drop_front(self.buf.len());
        if let UniKind::Ignored = self.kind {
            self.all = Ghost(s0.all@ + data@);
            proof {
                lemma_det_ignored(s0, *self, data@, i as nat, head@, b, n as nat, ty, seen0, *seen, (wp + wd + cv) as nat);
            }
            return (Ok(None), Ghost(wp + wd + cv));
        }
        proof {
            lemma_det_decoded(s0, data@, i as nat, head@, b, n as nat, ty);
        }
        let k = n - bl;
        self.all = Ghost(s0.all@ + data@.take(k as int));
        proof {
            lemma_det_some(s0, *self, data@, i as nat, head@, b, n as nat, ty, seen0, *seen, (wp + wd + cv) as nat);
        }
        (Ok(Some(k)), Ghost(wp + wd + cv))
    }

    /// Feeds `seg` to a critical stream; then a FIN is H3_CLOSED_CRITICAL_STREAM.
    fn consume(&mut self, seg: &[u8], fin: bool, events: &mut CapVec<UniEvent>) -> (r: (
        Result<(), u64>,
        Ghost<nat>,
    ))
        requires
            wf_live(*old(self)),
            old(self).kind is Control || old(self).kind is QpackEncoder || old(self).kind is QpackDecoder,
            old(events).wf(),
            old(events)@.len() + seg@.len() / 3 + 1 <= old(events).cap(),
        ensures
            consumed(*old(self), *final(self), seg@, old(events)@, final(events)@, fin, r.0),
            final(events).wf(),
            final(events).cap() == old(events).cap(),
            r.1@ <= c_uni_frame() * old(self).buf@.len() + c_csm() * (seg@.len() + 1),
            2 * ev_pairs(views(final(events)@.skip(old(events)@.len() as int))) <= old(self).buf@.len() + seg@.len(),
    {
        if let UniKind::Control = self.kind {
            self.consume_control(seg, fin, events)
        } else {
            let r = self.consume_qpack(seg, fin);
            proof {
                lemma_pairs_none(events@);
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
    fn consume_control(&mut self, seg: &[u8], fin: bool, events: &mut CapVec<UniEvent>) -> (r: (
        Result<(), u64>,
        Ghost<nat>,
    ))
        requires
            wf_live(*old(self)),
            old(self).kind is Control,
            old(events).wf(),
            old(events)@.len() + seg@.len() / 3 + 1 <= old(events).cap(),
        ensures
            consumed(*old(self), *final(self), seg@, old(events)@, final(events)@, fin, r.0),
            final(events).wf(),
            final(events).cap() == old(events).cap(),
            r.1@ <= c_uni_frame() * old(self).buf@.len() + c_csm() * (seg@.len() + 1),
            2 * ev_pairs(views(final(events)@.skip(old(events)@.len() as int))) <= old(self).buf@.len() + seg@.len(),
    {
        hide(rfc_control);
        hide(rfc_tail);
        hide(rfc_frame_payload);
        hide(rfc_frame_header);
        hide(rfc_varint_decode);
        let mut j: usize = 0;
        let ghost b0 = self.buf@.len();
        let ghost mut work: nat = 0;
        proof {
            lemma_grew_refl(*self, events@);
            lemma_pairs_none(events@);
            assert(self.all@ + seg@.take(0) =~= self.all@);
            lemma_room_start(self.buf@.len() > 0, self.ctrl, seg@.len());
        }
        while j < seg.len()
            invariant
                j <= seg@.len(),
                self.kind is Control,
                same_id(*old(self), *self),
                grew(*old(self), *self, old(events)@, events@),
                self.all@ == old(self).all@ + seg@.take(j as int),
                wf_live(*self),
                events.wf(),
                events.cap() == old(events).cap(),
                events@.len() + ev_room(self.buf@.len() > 0, self.ctrl, (seg@.len() - j) as nat) <= events.cap(),
                b0 == old(self).buf@.len(),
                work + c_uni_frame() * self.buf@.len() <= c_uni_frame() * b0 + c_csm() * j,
                2 * ev_pairs(views(events@.skip(old(events)@.len() as int))) + self.buf@.len() <= b0 + j,
            decreases seg@.len() - j,
        {
            let ghost s1 = *self;
            let ghost e1 = events@;
            let ghost all1 = self.all@;
            let (r, Ghost(w)) = self.step(seg, j, events);
            proof {
                lemma_pairs_split(e1, events@, old(events)@.len() as int);
                lemma_grew_trans(*old(self), s1, *self, old(events)@, e1, events@);
                assert(all1 + seg@.skip(j as int) =~= old(self).all@ + seg@);
                // this iteration's charge, before the exits after it (rca-early-return-cost)
                work = work + w + 1;
            }
            match r {
                Err(e) => {
                    proof {
                        assert(self.all@ + Seq::<u8>::empty() =~= self.all@);
                        assert(rfc_uni_stream(self.all@ + Seq::empty(), fin, self.seen0@) == (
                            self.emitted@,
                            Some(e),
                        ));
                    }
                    return (Err(e), Ghost(work));
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
        proof {
            assert(seg@.take(seg@.len() as int) =~= seg@);
            assert(self.buf@ + Seq::<u8>::empty() =~= self.buf@);
            assert(self.all@ + Seq::<u8>::empty() =~= self.all@);
            assert(rfc_uni_stream(self.all@ + Seq::empty(), fin, self.seen0@) == prepend(
                self.emitted@,
                tail_of(self.kind, self.ctrl, self.skip, self.buf@ + Seq::empty(), fin),
            ));
            assert(self.emitted@ + Seq::<SpecUniEvent>::empty() =~= self.emitted@);
        }
        if fin {
            return (Err(H3_CLOSED_CRITICAL_STREAM), Ghost(work + 1));
        }
        (Ok(()), Ghost(work + 1))
    }

    /// One step of progress through `seg[j..]`: discard a skipped payload, parse frames straight from `seg` when
    /// nothing is held, or top up the held frame and settle it.
    fn step(&mut self, seg: &[u8], j: usize, events: &mut CapVec<UniEvent>) -> (r: (
        Result<usize, u64>,
        Ghost<nat>,
    ))
        requires
            wf_live(*old(self)),
            old(self).kind is Control,
            j < seg@.len(),
            old(events).wf(),
            old(events)@.len() + ev_room(old(self).buf@.len() > 0, old(self).ctrl, (seg@.len() - j) as nat)
                <= old(events).cap(),
        ensures
            same_id(*old(self), *final(self)),
            grew(*old(self), *final(self), old(events)@, final(events)@),
            final(self).buf.wf(),
            final(events).wf(),
            final(events).cap() == old(events).cap(),
            match r.0 {
                Ok(j2) => {
                    &&& j < j2 <= seg@.len()
                    &&& final(self).all@ == old(self).all@ + seg@.subrange(j as int, j2 as int)
                    &&& wf_live(*final(self))
                    &&& final(events)@.len() + ev_room(
                        final(self).buf@.len() > 0,
                        final(self).ctrl,
                        (seg@.len() - j2) as nat,
                    ) <= final(events).cap()
                    &&& r.1@ + c_uni_frame() * final(self).buf@.len() <= c_uni_frame() * old(self).buf@.len()
                        + c_stp() * (j2 - j)
                    &&& 2 * ev_pairs(views(final(events)@.skip(old(events)@.len() as int))) + final(self).buf@.len() <= old(self).buf@.len() + (j2 - j)
                },
                Err(e) => {
                    &&& final(self).all@ == old(self).all@ + seg@.skip(j as int)
                    &&& dead_with(*final(self), e)
                    &&& r.1@ <= c_uni_frame() * old(self).buf@.len() + c_stp() * (seg@.len() - j)
                    &&& 2 * ev_pairs(views(final(events)@.skip(old(events)@.len() as int))) <= old(self).buf@.len() + (seg@.len() - j)
                },
            },
    {
        if self.skip > 0 {
            let (j2, Ghost(w)) = self.discard(seg, j);
            proof {
                lemma_grew_refl(*self, events@);
                lemma_live_empty(*self);
                lemma_pairs_none(events@);
            }
            (Ok(j2), Ghost(w))
        } else if self.buf.len() == 0 {
            let (r, Ghost(w)) = self.parse_direct(seg, j, events);
            proof {
                assert(seg@.skip(j as int) =~= seg@.subrange(j as int, seg@.len() as int));
            }
            proof {
                events.lemma_wf();
            }
            match r {
                Ok(()) => (Ok(seg.len()), Ghost(w)),
                Err(e) => (Err(e), Ghost(w)),
            }
        } else {
            let ghost st0 = self.ctrl;
            let ghost l0 = events@.len();
            let ghost rem = (seg@.len() - j) as nat;
            let (j2, Ghost(wt)) = self.top_up(seg, j);
            let ghost all2 = self.all@;
            let ghost bl2 = self.buf@.len();
            let (r, Ghost(ws)) = self.settle(events);
            proof {
                lemma_room_settle(
                    l0,
                    events@.len(),
                    events.cap(),
                    st0,
                    self.ctrl,
                    rem,
                    (j2 - j) as nat,
                    self.buf@.len() > 0,
                );
            }
            match r {
                Ok(()) => (Ok(j2), Ghost(wt + ws)),
                Err(e) => {
                    let ghost t = seg@.skip(j2 as int);
                    self.all = Ghost(all2 + t);
                    proof {
                        assert(old(self).all@ + seg@.subrange(j as int, j2 as int) + t =~= old(self).all@
                            + seg@.skip(j as int));
                        assert forall|u: Seq<u8>, f: bool| #[trigger]
                            rfc_uni_stream(self.all@ + u, f, self.seen0@) == (self.emitted@, Some(e)) by {
                            assert(all2 + (t + u) =~= self.all@ + u);
                            assert(rfc_uni_stream(all2 + (t + u), f, self.seen0@) == (self.emitted@, Some(e)));
                        }
                    }
                    (Err(e), Ghost(wt + ws))
                },
            }
        }
    }

    /// Consumes the frame the held bytes complete, if any: they hold at most one frame (`at_most_one`).
    fn settle(&mut self, events: &mut CapVec<UniEvent>) -> (r: (Result<(), u64>, Ghost<nat>))
        requires
            live_s(*old(self)),
            old(self).kind is Control,
            old(self).skip == 0,
            at_most_one(old(self).buf@),
            old(events).wf(),
            old(events)@.len() < old(events).cap(),
        ensures
            same_id(*old(self), *final(self)),
            grew(*old(self), *final(self), old(events)@, final(events)@),
            final(self).all@ == old(self).all@,
            final(self).buf.wf(),
            final(events).wf(),
            final(events).cap() == old(events).cap(),
            final(events)@.len() <= old(events)@.len() + 1,
            final(events)@.len() > old(events)@.len() ==> final(self).buf@.len() == 0 && tok(final(self).ctrl)
                == 0,
            tok(final(self).ctrl) <= tok(old(self).ctrl),
            match r.0 {
                Ok(()) => {
                    &&& wf_live(*final(self))
                    &&& r.1@ + c_uni_frame() * final(self).buf@.len() <= c_uni_frame() * old(self).buf@.len()
                        + c_set()
                    &&& 2 * ev_pairs(views(final(events)@.skip(old(events)@.len() as int))) + final(self).buf@.len() <= old(self).buf@.len()
                },
                Err(e) => {
                    &&& dead_with(*final(self), e)
                    &&& r.1@ <= c_uni_frame() * old(self).buf@.len() + c_set()
                    &&& 2 * ev_pairs(views(final(events)@.skip(old(events)@.len() as int))) <= old(self).buf@.len()
                },
            },
    {
        let ghost ev0 = events@;
        let ghost b = self.buf@;
        let ghost st1 = self.ctrl;
        let ghost e1 = self.emitted@;
        let (res, Ghost(wc)) = control_frame(self.buf.as_slice(), &mut self.ctrl, events);
        let ghost mine = views(events@.skip(ev0.len() as int));
        self.emitted = Ghost(e1 + mine);
        match res {
            Err(e) => {
                proof {
                    assert(events@.skip(ev0.len() as int) =~= Seq::<UniEvent>::empty());
                    assert(views(Seq::<UniEvent>::empty()) =~= Seq::<SpecUniEvent>::empty());
                    lemma_settle_err(self.all@, self.seen0@, e1, st1, b, mine, e);
                }
                (Err(e), Ghost(wc + 1))
            },
            Ok((k, s)) => {
                proof {
                    if k == 0 || s > 0 {
                        assert(events@.skip(ev0.len() as int) =~= Seq::<UniEvent>::empty());
                        assert(views(Seq::<UniEvent>::empty()) =~= Seq::<SpecUniEvent>::empty());
                    }
                    lemma_settle_one(self.all@, self.seen0@, e1, st1, b, mine, self.ctrl, k as nat, s);
                }
                let Ghost(wd) = self.buf.drop_front(k);
                self.skip = s;
                proof {
                    assert(self.buf@ == b.skip(k as int));
                }
                (Ok(()), Ghost(wc + wd + 1))
            },
        }
    }

    /// Discards the next bytes of `seg` that belong to a skipped unknown payload.
    fn discard(&mut self, seg: &[u8], j: usize) -> (r: (usize, Ghost<nat>))
        requires
            live_s(*old(self)),
            old(self).kind is Control,
            old(self).skip > 0,
            j < seg@.len(),
        ensures
            same_id(*old(self), *final(self)),
            final(self).emitted@ == old(self).emitted@,
            final(self).buf == old(self).buf,
            final(self).ctrl == old(self).ctrl,
            j < r.0 <= seg@.len(),
            final(self).all@ == old(self).all@ + seg@.subrange(j as int, r.0 as int),
            live_s(*final(self)),
            r.1@ <= 1,
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
        (j + d, Ghost(1))
    }

    /// With nothing held, parses frames straight from `seg[j..]` and keeps only its incomplete tail.
    fn parse_direct(&mut self, seg: &[u8], j: usize, events: &mut CapVec<UniEvent>) -> (r: (
        Result<(), u64>,
        Ghost<nat>,
    ))
        requires
            live_s(*old(self)),
            old(self).kind is Control,
            old(self).skip == 0,
            old(self).buf@.len() == 0,
            j < seg@.len(),
            old(events).wf(),
            old(events)@.len() + ((seg@.len() - j) as nat + tok(old(self).ctrl)) / 3 <= old(events).cap(),
        ensures
            same_id(*old(self), *final(self)),
            grew(*old(self), *final(self), old(events)@, final(events)@),
            final(self).all@ == old(self).all@ + seg@.skip(j as int),
            final(self).buf.wf(),
            final(events).wf(),
            final(events).cap() == old(events).cap(),
            match r.0 {
                Ok(()) => {
                    &&& wf_live(*final(self))
                    &&& r.1@ + c_uni_frame() * final(self).buf@.len() <= c_stp() * (seg@.len() - j)
                    &&& 2 * ev_pairs(views(final(events)@.skip(old(events)@.len() as int))) + final(self).buf@.len() <= seg@.len() - j
                },
                Err(e) => {
                    &&& dead_with(*final(self), e)
                    &&& r.1@ <= c_stp() * (seg@.len() - j)
                    &&& 2 * ev_pairs(views(final(events)@.skip(old(events)@.len() as int))) <= seg@.len() - j
                },
            },
    {
        hide(rfc_uni_stream);
        hide(rfc_control);
        hide(rfc_frame_header);
        let s = slice_subrange(seg, j, seg.len());
        let ghost ev0 = events@;
        let ghost all1 = self.all@;
        let ghost buf1 = self.buf@;
        let ghost st1 = self.ctrl;
        let ghost e1 = self.emitted@;
        proof {
            assert(s@ =~= seg@.skip(j as int));
        }
        let (res, Ghost(wc)) = control_frames(s, &mut self.ctrl, events);
        self.emitted = Ghost(e1 + views(events@.skip(ev0.len() as int)));
        self.all = Ghost(self.all@ + s@);
        let ghost mine = views(events@.skip(ev0.len() as int));
        proof {
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
            Err(e) => (Err(e), Ghost(wc + 1)),
            Ok((n, sk)) => {
                let tail = slice_subrange(s, n, s.len());
                let Ghost(wp) = self.buf.push_slice(tail);
                self.skip = sk;
                proof {
                    assert(tail@ =~= s@.skip(n as int));
                    assert(self.buf@ =~= s@.skip(n as int));
                    assert forall|t: Seq<u8>, f: bool| #[trigger]
                        rfc_uni_stream(self.all@ + t, f, self.seen0@) == prepend(
                            self.emitted@,
                            tail_of(self.kind, self.ctrl, self.skip, self.buf@ + t, f),
                        ) by {
                        let x = skipping(sk, self.ctrl, self.buf@ + t, f);
                        assert(e1 + (mine + x.0) =~= self.emitted@ + x.0);
                    }
                }
                (Ok(()), Ghost(wc + wp + 1))
            },
        }
    }

    /// Moves just enough of `seg[j..]` into `buf` to complete its frame: one byte while the header is incomplete, then
    /// the rest of the frame. The header is parsed from `buf`'s first 16 bytes at most (N5).
    fn top_up(&mut self, seg: &[u8], j: usize) -> (r: (usize, Ghost<nat>))
        requires
            live_s(*old(self)),
            old(self).kind is Control,
            old(self).skip == 0,
            old(self).buf@.len() > 0,
            one_frame(old(self).buf@),
            j < seg@.len(),
        ensures
            same_id(*old(self), *final(self)),
            final(self).emitted@ == old(self).emitted@,
            final(self).ctrl == old(self).ctrl,
            final(self).skip == old(self).skip,
            j < r.0 <= seg@.len(),
            final(self).all@ == old(self).all@ + seg@.subrange(j as int, r.0 as int),
            final(self).buf@ == old(self).buf@ + seg@.subrange(j as int, r.0 as int),
            live_s(*final(self)),
            at_most_one(final(self).buf@),
            r.1@ <= 7 * (r.0 - j) + 21,
    {
        let bl = self.buf.len();
        let q = self.buf.as_slice();
        let m = if bl < 16 {
            bl
        } else {
            16
        };
        let hp = slice_subrange(q, 0, m);
        proof {
            assert(hp@ =~= q@.take(m as int));
            crate::request::lemma_header_take(q@, m as int);
            lemma_frame_header_bounds(q@);
        }
        // The header parse's proved cost: at most c_fhdr() (17).
        let (fh, Ghost(ch)) = parse_frame_header_w(hp);
        let need: usize = match fh {
            FrameHeader::Incomplete => 1,
            FrameHeader::Complete { len, hdr_len, .. } => hdr_len + len as usize - bl,
        };
        let avail = seg.len() - j;
        let k = if avail < need {
            avail
        } else {
            need
        };
        let piece = slice_subrange(seg, j, j + k);
        let ghost all1 = self.all@;
        let ghost buf1 = self.buf@;
        proof {
            lemma_top_up_shape(buf1, piece@);
        }
        let Ghost(wp) = self.buf.push_slice(piece);
        self.all = Ghost(self.all@ + piece@);
        proof {
            lemma_split_append(all1, self.seen0@, self.emitted@, self.kind, self.ctrl, self.skip, buf1, piece@);
        }
        (j + k, Ghost(wp + ch))
    }

    /// QPACK streams emit no events, so only `buf` and the result change. While an instruction is held, one byte at a
    /// time completes it (at most 11 held); then the rest is scanned in place and only its incomplete tail is kept.
    fn consume_qpack(&mut self, seg: &[u8], fin: bool) -> (r: (Result<(), u64>, Ghost<nat>))
        requires
            wf_live(*old(self)),
            old(self).kind is QpackEncoder || old(self).kind is QpackDecoder,
        ensures
            final(self).all@ == old(self).all@ + seg@,
            final(self).seen0@ == old(self).seen0@,
            final(self).kind == old(self).kind,
            final(self).done == old(self).done,
            final(self).emitted@ == old(self).emitted@,
            final(self).ctrl == old(self).ctrl,
            final(self).skip == old(self).skip,
            final(self).buf.wf(),
            rfc_uni_stream(final(self).all@, fin, final(self).seen0@) == (
                final(self).emitted@,
                err_of(r.0),
            ),
            r.0 is Ok ==> !fin && wf_live(*final(self)),
            r.1@ <= c_csm() * (seg@.len() + 1),
    {
        let ghost all0 = self.all@;
        let ghost mut work: nat = 0;
        let mut j: usize = 0;
        proof {
            assert(all0 + seg@.take(0) =~= all0);
        }
        while j < seg.len() && self.buf.len() > 0
            invariant
                j <= seg@.len(),
                all0 == old(self).all@,
                self.kind == old(self).kind,
                self.seen0@ == old(self).seen0@,
                self.done == old(self).done,
                self.emitted@ == old(self).emitted@,
                self.ctrl == old(self).ctrl,
                self.skip == old(self).skip,
                self.kind is QpackEncoder || self.kind is QpackDecoder,
                self.all@ == all0 + seg@.take(j as int),
                wf_live(*self),
                // per byte held: a 1-byte push (11), a scan of at most 12 bytes (13 * 13), `drop_front` (2) and 1
                work <= 183 * j,
            decreases seg@.len() - j,
        {
            let piece = slice_subrange(seg, j, j + 1);
            let ghost all1 = self.all@;
            let ghost b0 = self.buf@;
            let Ghost(wp) = self.buf.push_slice(piece);
            self.all = Ghost(all1 + piece@);
            let ghost b = self.buf@;
            proof {
                lemma_split_append(all1, self.seen0@, self.emitted@, self.kind, self.ctrl, self.skip, b0, piece@);
                assert(piece@ =~= seg@.subrange(j as int, j + 1));
                assert(all0 + seg@.take(j as int) + seg@.subrange(j as int, j + 1) =~= all0 + seg@.take(j + 1));
            }
            let (scanned, Ghost(cs)) = if let UniKind::QpackEncoder = self.kind {
                process_encoder_stream(self.buf.as_slice())
            } else {
                process_decoder_stream(self.buf.as_slice())
            };
            proof {
                // this iteration's charge, before the exits after it (rca-early-return-cost)
                work = work + wp + cs + 1;
            }
            match scanned {
                Ok(n) => {
                    proof {
                        lemma_qpack_keep(self.all@, self.seen0@, self.emitted@, self.kind, self.ctrl, b, n as nat);
                    }
                    let Ghost(wd) = self.buf.drop_front(n);
                    proof {
                        work = work + wd;
                    }
                    j = j + 1;
                },
                Err(e) => {
                    let ghost t = seg@.skip(j + 1);
                    self.all = Ghost(all0 + seg@);
                    proof {
                        assert(all1 + piece@ + t =~= all0 + seg@);
                        lemma_qpack_dead(all1 + piece@, self.seen0@, self.emitted@, self.kind, self.ctrl, b, e, t);
                    }
                    return (Err(e), Ghost(work));
                },
            }
        }
        if j < seg.len() {
            // Nothing held: scan the rest in place and keep only its incomplete tail.
            let s = slice_subrange(seg, j, seg.len());
            let ghost all1 = self.all@;
            proof {
                assert(s@ =~= seg@.skip(j as int));
                assert(all1 + s@ =~= all0 + seg@);
                lemma_split_append(all1, self.seen0@, self.emitted@, self.kind, self.ctrl, self.skip, self.buf@, s@);
                assert(self.buf@ + s@ =~= s@);
            }
            self.all = Ghost(all0 + seg@);
            let (scanned, Ghost(cs)) = if let UniKind::QpackEncoder = self.kind {
                process_encoder_stream(s)
            } else {
                process_decoder_stream(s)
            };
            match scanned {
                Ok(n) => {
                    proof {
                        lemma_qpack_keep(self.all@, self.seen0@, self.emitted@, self.kind, self.ctrl, s@, n as nat);
                    }
                    let tail = slice_subrange(s, n, s.len());
                    let Ghost(wp) = self.buf.push_slice(tail);
                    proof {
                        assert(self.buf@ =~= s@.skip(n as int));
                        work = work + cs + wp + 1;
                    }
                },
                Err(e) => {
                    proof {
                        assert(self.all@ + Seq::<u8>::empty() =~= self.all@);
                        lemma_qpack_dead(self.all@, self.seen0@, self.emitted@, self.kind, self.ctrl, s@, e, Seq::empty());
                    }
                    return (Err(e), Ghost(work + cs + 1));
                },
            }
        } else {
            proof {
                assert(seg@.take(j as int) =~= seg@);
            }
        }
        proof {
            lemma_qpack_end(*self, fin);
        }
        if fin {
            return (Err(H3_CLOSED_CRITICAL_STREAM), Ghost(work + 1));
        }
        (Ok(()), Ghost(work + 1))
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

/// What `determine` guarantees, from `s0` (shared `seen0`) to `s1` (`seen1`), having read `data`.
spec fn determined(
    s0: UniStream,
    s1: UniStream,
    data: Seq<u8>,
    seen0: SeenUni,
    seen1: SeenUni,
    r: Result<Option<usize>, u64>,
    w: nat,
) -> bool {
    &&& s1.buf.wf()
    &&& s1.seen0@ == seen0
    &&& seen1 == seen_after(seen0, s0.all@ + data)
    &&& s1.done == s0.done
    &&& s1.emitted@ == s0.emitted@
    &&& s1.kind == kind_of_bytes(s0.all@ + data)
    &&& w <= 80
    &&& match r {
        Err(e) => {
            &&& s1.all@ == s0.all@ + data
            &&& forall|f: bool| #[trigger] rfc_uni_stream(s1.all@, f, s1.seen0@) == (s1.emitted@, Some(e))
        },
        Ok(None) => {
            &&& s1.all@ == s0.all@ + data
            &&& s1.buf@.len() < 8
            &&& s1.kind is Undetermined || s1.kind is Ignored
            &&& wf_live(s1)
            &&& forall|f: bool| #[trigger] rfc_uni_stream(s1.all@, f, s1.seen0@) == (s1.emitted@, None::<u64>)
        },
        Ok(Some(i)) => {
            &&& i <= data.len()
            &&& s1.all@ == s0.all@ + data.take(i as int)
            &&& s1.kind is Control || s1.kind is QpackEncoder || s1.kind is QpackDecoder
            &&& live_s(s1)
            &&& s1.buf@.len() == 0
        },
    }
}

/// What every path of `determine` starts from: `s0` holds part of a type varint, and `head`, the first `i` bytes of
/// `data` (as many as fill 8 with it), is pushed after it.
spec fn det_start(s0: UniStream, data: Seq<u8>, i: nat, head: Seq<u8>) -> bool {
    &&& s0.kind is Undetermined
    &&& s0.kind == kind_of_bytes(s0.all@)
    &&& wf_live(s0)
    &&& i <= data.len()
    &&& (i == data.len() || s0.buf@.len() + i == 8)
    &&& head == data.subrange(0, i as int)
}

/// The fields `determine` leaves alone, and the new `seen0`.
spec fn det_frame(s0: UniStream, s1: UniStream, seen0: SeenUni) -> bool {
    &&& s1.buf.wf()
    &&& s1.seen0@ == seen0
    &&& s1.emitted@ == s0.emitted@
    &&& s1.ctrl == s0.ctrl
    &&& s1.skip == s0.skip
    &&& s1.done == s0.done
}

/// A decoded type varint of `n` bytes from `b = s0.buf + head`: what it says about all of `s0.all + data`.
proof fn lemma_det_decoded(s0: UniStream, data: Seq<u8>, i: nat, head: Seq<u8>, b: Seq<u8>, n: nat, ty: u64)
    requires
        det_start(s0, data, i, head),
        b == s0.buf@ + head,
        rfc_varint_decode(b) == Some((n, ty)),
    ensures
        s0.buf@.len() < n <= b.len(),
        rfc_varint_decode(s0.all@ + data) == Some((n, ty)),
        kind_of_bytes(s0.all@ + data) == rfc_kind_of(ty),
        forall|x: SeenUni| #[trigger] seen_after(x, s0.all@ + data) == seen_mark(x, ty),
        b.take(n as int) == s0.all@ + data.take(n - s0.buf@.len()),
        forall|t: Seq<u8>| #[trigger] rfc_varint_decode(b.take(n as int) + t) == Some((n, ty)),
        b + data.skip(i as int) == s0.all@ + data,
{
    lemma_undetermined_def(s0);
    let bl = s0.buf@.len();
    assert(b.take(bl as int) =~= s0.buf@);
    lemma_decode_take(b, n, ty, bl);
    assert(b + data.skip(i as int) =~= s0.all@ + data);
    lemma_decode_prefix(b, data.skip(i as int));
    assert(b.take(n as int) =~= s0.all@ + data.take(n - bl));
}

proof fn lemma_det_none(s0: UniStream, s1: UniStream, data: Seq<u8>, i: nat, head: Seq<u8>, seen0: SeenUni, w: nat)
    requires
        det_start(s0, data, i, head),
        det_frame(s0, s1, seen0),
        s1.kind == s0.kind,
        s1.buf@ == s0.buf@ + head,
        rfc_varint_decode(s1.buf@) is None,
        s1.all@ == s0.all@ + data,
        w <= 80,
    ensures
        determined(s0, s1, data, seen0, seen0, Ok(None), w),
{
    lemma_undetermined_def(s0);
    lemma_undetermined_def(s1);
    lemma_decode_none_short(s1.buf@);
    assert(data.subrange(0, i as int) =~= data);
    lemma_undetermined(s1.buf@, seen0);
    lemma_empty_events(s0.emitted@);
}

proof fn lemma_det_err(
    s0: UniStream,
    s1: UniStream,
    data: Seq<u8>,
    i: nat,
    head: Seq<u8>,
    n: nat,
    ty: u64,
    seen0: SeenUni,
    w: nat,
)
    requires
        det_start(s0, data, i, head),
        det_frame(s0, s1, seen0),
        rfc_varint_decode(s0.buf@ + head) == Some((n, ty)),
        s1.kind == rfc_kind_of(ty),
        ty == STREAM_PUSH || rfc_duplicate(seen0, ty),
        s1.all@ == s0.all@ + data,
        w <= 80,
    ensures
        determined(s0, s1, data, seen0, seen0, Err(H3_STREAM_CREATION_ERROR), w),
{
    lemma_det_decoded(s0, data, i, head, s0.buf@ + head, n, ty);
    assert(seen_mark(seen0, ty) == seen0);
    lemma_creation_err(s0.all@ + data, n, ty, seen0);
    lemma_undetermined_def(s0);
    lemma_empty_events(s0.emitted@);
}

proof fn lemma_det_ignored(
    s0: UniStream,
    s1: UniStream,
    data: Seq<u8>,
    i: nat,
    head: Seq<u8>,
    b: Seq<u8>,
    n: nat,
    ty: u64,
    seen0: SeenUni,
    seen1: SeenUni,
    w: nat,
)
    requires
        det_start(s0, data, i, head),
        det_frame(s0, s1, seen0),
        b == s0.buf@ + head,
        rfc_varint_decode(b) == Some((n, ty)),
        s1.kind == rfc_kind_of(ty),
        s1.kind is Ignored,
        ty != STREAM_PUSH,
        !rfc_duplicate(seen0, ty),
        seen1 == seen_mark(seen0, ty),
        s1.buf@.len() == 0,
        s1.all@ == s0.all@ + data,
        w <= 80,
    ensures
        determined(s0, s1, data, seen0, seen1, Ok(None), w),
{
    lemma_det_decoded(s0, data, i, head, b, n, ty);
    lemma_undetermined_def(s0);
    lemma_empty_events(s0.emitted@);
    lemma_empty_bytes(s1.buf@);
    lemma_determined_ignored(b, n, ty, seen0, data.skip(i as int));
    lemma_ignored_def(s1);
}

proof fn lemma_det_some(
    s0: UniStream,
    s1: UniStream,
    data: Seq<u8>,
    i: nat,
    head: Seq<u8>,
    b: Seq<u8>,
    n: nat,
    ty: u64,
    seen0: SeenUni,
    seen1: SeenUni,
    w: nat,
)
    requires
        det_start(s0, data, i, head),
        det_frame(s0, s1, seen0),
        b == s0.buf@ + head,
        rfc_varint_decode(b) == Some((n, ty)),
        s1.kind == rfc_kind_of(ty),
        !(s1.kind is Ignored),
        ty != STREAM_PUSH,
        !rfc_duplicate(seen0, ty),
        seen1 == seen_mark(seen0, ty),
        s1.buf@.len() == 0,
        n >= s0.buf@.len(),
        s1.all@ == s0.all@ + data.take(n - s0.buf@.len()),
        w <= 80,
    ensures
        n - s0.buf@.len() <= i,
        determined(s0, s1, data, seen0, seen1, Ok(Some((n - s0.buf@.len()) as usize)), w),
{
    lemma_det_decoded(s0, data, i, head, b, n, ty);
    lemma_undetermined_def(s0);
    lemma_empty_events(s0.emitted@);
    lemma_determined_live(s1, b.take(n as int), n, ty);
}

/// What `UniStream::on_data` guarantees, from `s0` (events `e0`, shared `seen0`) to `s1` (`e1`, `seen1`), having fed
/// `data` and returned `r` at `cost`.
pub open spec fn fed(
    s0: UniStream,
    s1: UniStream,
    data: Seq<u8>,
    fin: bool,
    seen0: SeenUni,
    seen1: SeenUni,
    e0: CapVec<UniEvent>,
    e1: CapVec<UniEvent>,
    r: Result<(), u64>,
    cost: nat,
) -> bool {
    &&& s1.wf()
    &&& s1.all() == s0.all() + data
    &&& s1.done() == (r is Err || fin)
    &&& !s1.done() ==> s1.buffered() < UNI_BUF_CAP
    &&& e1.wf()
    &&& e1.cap() == e0.cap()
    &&& e1@.len() >= e0@.len()
    &&& e1@.take(e0@.len() as int) == e0@
    &&& s1.emitted() == s0.emitted() + views(e1@.skip(e0@.len() as int))
    &&& rfc_uni_stream(s1.all(), fin, s1.seen_before()) == (s1.emitted(), err_of(r))
    &&& kind_of_bytes(s0.all()) is Undetermined ==> s1.seen_before() == seen0 && seen1 == seen_after(seen0, s1.all())
    &&& !(kind_of_bytes(s0.all()) is Undetermined) ==> s1.seen_before() == s0.seen_before() && seen1 == seen0
    &&& cost <= c_uni() * (data.len() + 16) + c_uni_frame() * s0.buffered()
    &&& 2 * ev_pairs(views(e1@.skip(e0@.len() as int))) <= data.len() + s0.buffered()
}

/// `wf` with its parts named (for callers that hide them).
proof fn lemma_wf_unfold(s: UniStream)
    requires
        s.wf(),
    ensures
        s.buf.wf(),
        s.kind == kind_of_bytes(s.all@),
        !s.done ==> wf_live(s),
        s.kind is Undetermined <==> rfc_varint_decode(s.all@) is None,
{
}

/// A stream whose type has not arrived, marked done for the call: still `wf_live` (split out of `on_data`).
proof fn lemma_undetermined_done(s0: UniStream, s: UniStream)
    requires
        s0.wf(),
        !s0.done,
        s0.kind is Undetermined,
        s == (UniStream { done: true, ..s0 }),
    ensures
        wf_live(s),
        s.kind == kind_of_bytes(s.all@),
{
}

/// `on_data` on an ignored stream.
proof fn lemma_fed_ignored(s0: UniStream, s1: UniStream, data: Seq<u8>, fin: bool, seen0: SeenUni, e0: CapVec<UniEvent>)
    requires
        s0.wf(),
        !s0.done,
        s0.kind is Ignored,
        s1 == (UniStream { all: Ghost(s0.all@ + data), done: fin, ..s0 }),
        e0.wf(),
    ensures
        fed(s0, s1, data, fin, seen0, seen0, e0, e0, Ok(()), 1),
{
    lemma_ignored_data(s0.all@, s0.seen0@, s0.emitted@, s0.ctrl, s0.skip, s0.buf@, data, fin);
    lemma_pairs_none(e0@);
    assert(e0@.take(e0@.len() as int) =~= e0@);
    assert(views(e0@.skip(e0@.len() as int)) =~= Seq::<SpecUniEvent>::empty());
    assert(s0.emitted@ + Seq::<SpecUniEvent>::empty() =~= s0.emitted@);
}

/// `on_data` when the type varint is a push stream or a second critical stream.
proof fn lemma_fed_det_err(
    s0: UniStream,
    s1: UniStream,
    data: Seq<u8>,
    fin: bool,
    seen0: SeenUni,
    seen1: SeenUni,
    e0: CapVec<UniEvent>,
    e: u64,
    w: nat,
)
    requires
        s0.wf(),
        !s0.done,
        s0.kind is Undetermined,
        s1.done,
        s1.buf.wf(),
        s1.seen0@ == seen0,
        seen1 == seen_after(seen0, s0.all@ + data),
        s1.emitted@ == s0.emitted@,
        s1.kind == kind_of_bytes(s0.all@ + data),
        s1.all@ == s0.all@ + data,
        forall|f: bool| #[trigger] rfc_uni_stream(s1.all@, f, s1.seen0@) == (s1.emitted@, Some(e)),
        w <= 80,
        e0.wf(),
    ensures
        fed(s0, s1, data, fin, seen0, seen1, e0, e0, Err(e), w + 1),
{
    lemma_pairs_none(e0@);
    assert(e0@.take(e0@.len() as int) =~= e0@);
    assert(views(e0@.skip(e0@.len() as int)) =~= Seq::<SpecUniEvent>::empty());
    assert(s0.emitted@ + Seq::<SpecUniEvent>::empty() =~= s0.emitted@);
    assert(rfc_uni_stream(s1.all@, fin, s1.seen0@) == (s1.emitted@, Some(e)));
}

/// `on_data` when the type has not arrived or is unknown: all of `data` consumed, no event.
proof fn lemma_fed_det_none(
    s0: UniStream,
    s1: UniStream,
    s2: UniStream,
    data: Seq<u8>,
    fin: bool,
    seen0: SeenUni,
    seen1: SeenUni,
    e0: CapVec<UniEvent>,
    w: nat,
)
    requires
        s0.wf(),
        !s0.done,
        s0.kind is Undetermined,
        s1.buf.wf(),
        s1.seen0@ == seen0,
        seen1 == seen_after(seen0, s0.all@ + data),
        s1.emitted@ == s0.emitted@,
        s1.kind == kind_of_bytes(s0.all@ + data),
        s1.all@ == s0.all@ + data,
        s1.buf@.len() < 8,
        wf_live(s1),
        forall|f: bool| #[trigger] rfc_uni_stream(s1.all@, f, s1.seen0@) == (s1.emitted@, None::<u64>),
        s2 == (UniStream { done: fin, ..s1 }),
        w <= 80,
        e0.wf(),
    ensures
        fed(s0, s2, data, fin, seen0, seen1, e0, e0, Ok(()), w + 1),
{
    lemma_set_done(s1, fin);
    lemma_pairs_none(e0@);
    assert(e0@.take(e0@.len() as int) =~= e0@);
    assert(views(e0@.skip(e0@.len() as int)) =~= Seq::<SpecUniEvent>::empty());
    assert(s0.emitted@ + Seq::<SpecUniEvent>::empty() =~= s0.emitted@);
    assert(rfc_uni_stream(s1.all@, fin, s1.seen0@) == (s1.emitted@, None::<u64>));
}

/// `on_data` once the type is known: `consume` fed `data[i..]` from `sm` to `sc`; `s1` is `sc`, live again on `Ok`.
proof fn lemma_fed_consume(
    s0: UniStream,
    sm: UniStream,
    sc: UniStream,
    s1: UniStream,
    data: Seq<u8>,
    i: nat,
    rest: Seq<u8>,
    fin: bool,
    seen0: SeenUni,
    seen1: SeenUni,
    e0: CapVec<UniEvent>,
    e1: CapVec<UniEvent>,
    r: Result<(), u64>,
    wd: nat,
    wc: nat,
)
    requires
        s0.wf(),
        !s0.done,
        !(s0.kind is Ignored),
        i <= data.len(),
        sm.all@ == s0.all@ + data.take(i as int),
        s0.kind is Undetermined ==> {
            &&& sm.seen0@ == seen0
            &&& seen1 == seen_after(seen0, s0.all@ + data)
            &&& sm.emitted@ == s0.emitted@
            &&& sm.kind == kind_of_bytes(s0.all@ + data)
            &&& sm.buf@.len() == 0
            &&& wd <= 80
        },
        !(s0.kind is Undetermined) ==> sm == (UniStream { done: true, ..s0 }) && i == 0 && seen1 == seen0 && wd == 0,
        rest == data.subrange(i as int, data.len() as int),
        consumed(sm, sc, rest, e0@, e1@, fin, r),
        wc <= c_uni_frame() * sm.buf@.len() + c_csm() * ((data.len() - i) as nat + 1),
        2 * ev_pairs(views(e1@.skip(e0@.len() as int))) <= sm.buf@.len() + (data.len() - i),
        e1.wf(),
        e1.cap() == e0.cap(),
        sm.done,
        s1 == (if r is Ok {
            UniStream { done: false, ..sc }
        } else {
            sc
        }),
    ensures
        fed(s0, s1, data, fin, seen0, seen1, e0, e1, r, wd + wc + 1),
{
    hide(rfc_uni_stream);
    hide(tail_of);
    assert(data.take(i as int) + rest =~= data);
    assert(sm.all@ + rest =~= s0.all@ + data);
    if !(s0.kind is Undetermined) {
        assert(data.take(0) =~= Seq::<u8>::empty());
        assert(s0.all@ + Seq::<u8>::empty() =~= s0.all@);
        lemma_decode_prefix(s0.all@, data);
    }
    if r is Ok {
        lemma_set_done(sc, false);
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
    &&& s1.buf.wf()
    &&& e1.len() >= e0.len()
    &&& e1.take(e0.len() as int) == e0
    &&& s1.emitted@ == s0.emitted@ + views(e1.skip(e0.len() as int))
    &&& rfc_uni_stream(s1.all@, fin, s1.seen0@) == (s1.emitted@, err_of(r))
    &&& r is Ok ==> !fin && wf_live(s1) && s1.buf@.len() < UNI_BUF_CAP
}

/// The part of `wf` that holds while the stream takes data: a control stream holds at most one incomplete frame, a
/// QPACK stream at most one incomplete instruction.
spec fn wf_live(s: UniStream) -> bool {
    &&& s.buf.wf()
    &&& match s.kind {
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
        UniKind::Control => ready(s) && one_frame(s.buf@),
        _ => ready(s) && s.buf@.len() <= 1 + PREFIX_INT_MAX_CONT,
    }
}

spec fn live_s(s: UniStream) -> bool {
    &&& s.buf.wf()
    &&& live(s.all@, s.seen0@, s.emitted@, s.kind, s.ctrl, s.skip, s.buf@)
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
    hide(rfc_uni_stream);
    hide(rfc_control);
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

/// `wf_live` and the buffer bound do not read `done` (for callers that hide `ready`).
proof fn lemma_set_done(s: UniStream, d: bool)
    ensures
        wf_live(s) == wf_live(UniStream { done: d, ..s }),
{
}

/// A held frame or instruction gone: a live critical stream with nothing held is ready (split out for the rlimit).
proof fn lemma_live_empty(s: UniStream)
    requires
        live_s(s),
        s.buf@.len() == 0,
        s.kind is Control || s.kind is QpackEncoder || s.kind is QpackDecoder,
    ensures
        wf_live(s),
{
    lemma_frame_header_bounds(s.buf@);
    assert(s.buf@ =~= Seq::<u8>::empty());
    if s.kind is Control {
        lemma_settled_empty(s.ctrl, s.skip);
    } else {
        assert(rfc_encoder_stream(Seq::<u8>::empty()) == Ok::<nat, u64>(0));
        assert(rfc_decoder_stream(Seq::<u8>::empty()) == Ok::<nat, u64>(0));
    }
}

/// A call's event capacity covers the control stream's room at its start.
proof fn lemma_room_start(held: bool, st: CtrlState, rem: nat)
    ensures
        ev_room(held, st, rem) <= rem / 3 + 1,
{
}

/// A top-up of `k` bytes and the settle after it keep the room: the held frame's event uses its one, and a frame
/// completed leaves `tok` spent.
proof fn lemma_room_settle(
    l0: nat,
    l1: nat,
    cap: nat,
    st0: CtrlState,
    st1: CtrlState,
    rem: nat,
    k: nat,
    held1: bool,
)
    requires
        l0 + ev_room(true, st0, rem) <= cap,
        1 <= k <= rem,
        l1 <= l0 + 1,
        l1 > l0 ==> !held1 && tok(st1) == 0,
        tok(st1) <= tok(st0),
    ensures
        l1 + ev_room(held1, st1, (rem - k) as nat) <= cap,
{
}

/// One `control_frame` over the held bytes, which hold at most one frame: what it consumed is all of them or none,
/// and `split_ok` moves past it (split out of `settle` for the rlimit).
proof fn lemma_settle_one(
    all: Seq<u8>,
    seen0: SeenUni,
    e1: Seq<SpecUniEvent>,
    st1: CtrlState,
    b: Seq<u8>,
    mine: Seq<SpecUniEvent>,
    st2: CtrlState,
    k: nat,
    s: u64,
)
    requires
        split_ok(all, seen0, e1, UniKind::Control, st1, 0, b),
        at_most_one(b),
        k <= b.len(),
        k == 0 ==> {
            &&& s == 0
            &&& mine == Seq::<SpecUniEvent>::empty()
            &&& st2 == st1
            &&& one_frame(b)
            &&& b.len() < UNI_BUF_CAP
            &&& forall|f: bool| #[trigger] rfc_control(b, st1, f) == (Seq::<SpecUniEvent>::empty(), fin_err(f))
        },
        k > 0 && s == 0 ==> ctrl_split(b, st1, mine, b.skip(k as int), st2),
        k > 0 && s == 0 ==> (rfc_frame_header(b) matches Some((h, _, len)) && k == h + len),
        s > 0 ==> {
            &&& k == b.len()
            &&& mine == Seq::<SpecUniEvent>::empty()
            &&& st2 == st1
            &&& forall|t: Seq<u8>, f: bool| #[trigger] rfc_control(b + t, st1, f) == skipping(s, st1, t, f)
        },
    ensures
        k > 0 ==> k == b.len(),
        split_ok(all, seen0, e1 + mine, UniKind::Control, st2, s, b.skip(k as int)),
        settled(UniKind::Control, st2, s, b.skip(k as int)),
        one_frame(b.skip(k as int)),
        b.skip(k as int).len() < UNI_BUF_CAP,
        s > 0 ==> b.skip(k as int).len() == 0,
{
    assert forall|t: Seq<u8>, f: bool| #[trigger]
        rfc_control(b + t, st1, f) == prepend(mine, skipping(s, st2, b.skip(k as int) + t, f)) by {
        if k == 0 {
            assert(b.skip(0) =~= b);
            lemma_skipping_zero(st1, b + t, f);
            let x = rfc_control(b + t, st1, f);
            assert(Seq::<SpecUniEvent>::empty() + x.0 =~= x.0);
        } else if s == 0 {
            lemma_skipping_zero(st2, b.skip(k as int) + t, f);
        } else {
            assert(b.skip(k as int) + t =~= t);
            let x = skipping(s, st1, t, f);
            assert(Seq::<SpecUniEvent>::empty() + x.0 =~= x.0);
        }
    }
    lemma_settle(all, seen0, e1, st1, b, mine, st2, s, k);
    if k == 0 {
        assert(b.skip(0) =~= b);
        assert forall|f: bool| #[trigger]
            tail_of(UniKind::Control, st2, s, b.skip(k as int), f) == (Seq::<SpecUniEvent>::empty(), fin_err(f)) by {
            lemma_skipping_zero(st2, b, f);
        }
    } else {
        assert(b.skip(k as int) =~= Seq::<u8>::empty());
        lemma_settled_empty(st2, s);
        lemma_frame_header_bounds(Seq::<u8>::empty());
    }
}

/// A top-up keeps at most one frame held: one byte onto an incomplete header ends any header it completes, and the
/// rest of a frame ends it (split out of `top_up` for the rlimit).
proof fn lemma_top_up_shape(b: Seq<u8>, p: Seq<u8>)
    requires
        one_frame(b),
        b.len() > 0,
        p.len() >= 1,
        rfc_frame_header(b) is None ==> p.len() == 1,
        rfc_frame_header(b) matches Some((h, _, len)) ==> b.len() + p.len() <= h + len,
    ensures
        at_most_one(b + p),
        (b + p).len() <= UNI_BUF_CAP,
{
    lemma_frame_header_bounds(b);
    let c = b + p;
    if rfc_frame_header(b) is Some {
        lemma_frame_header_prefix(b, p);
    } else {
        lemma_frame_header_bounds(c);
        if let Some((h, _, _)) = rfc_frame_header(c) {
            if h <= b.len() {
                crate::request::lemma_header_cover(c, b.len() as int);
                assert(c.take(b.len() as int) =~= b);
            }
        }
    }
}

/// A QPACK scan of the held bytes `b` that consumed `n`: `split_ok` moves past the complete instructions, and at most
/// one incomplete one (11 bytes) stays held.
proof fn lemma_qpack_keep(
    all: Seq<u8>,
    seen0: SeenUni,
    em: Seq<SpecUniEvent>,
    k: UniKind,
    st: CtrlState,
    b: Seq<u8>,
    n: nat,
)
    requires
        split_ok(all, seen0, em, k, st, 0, b),
        k is QpackEncoder || k is QpackDecoder,
        k is QpackEncoder ==> rfc_encoder_stream(b) == Ok::<nat, u64>(n),
        k is QpackDecoder ==> rfc_decoder_stream(b) == Ok::<nat, u64>(n),
    ensures
        n <= b.len(),
        b.len() - n <= 1 + PREFIX_INT_MAX_CONT,
        split_ok(all, seen0, em, k, st, 0, b.skip(n as int)),
        settled(k, st, 0, b.skip(n as int)),
{
    lemma_qpack_split(k, st, b, n);
    assert forall|t: Seq<u8>, f: bool| #[trigger]
        rfc_uni_stream(all + t, f, seen0) == prepend(em, tail_of(k, st, 0, b.skip(n as int) + t, f)) by {
        assert(rfc_uni_stream(all + t, f, seen0) == prepend(em, tail_of(k, st, 0, b + t, f)));
    }
}

/// A QPACK scan of the held bytes `b` that failed: the stream fails with that error whatever follows (split out of
/// `consume_qpack` for the rlimit).
proof fn lemma_qpack_dead(
    all: Seq<u8>,
    seen0: SeenUni,
    em: Seq<SpecUniEvent>,
    k: UniKind,
    st: CtrlState,
    b: Seq<u8>,
    e: u64,
    t: Seq<u8>,
)
    requires
        split_ok(all, seen0, em, k, st, 0, b),
        k is QpackEncoder || k is QpackDecoder,
        k is QpackEncoder ==> rfc_encoder_stream(b) == Err::<nat, u64>(e),
        k is QpackDecoder ==> rfc_decoder_stream(b) == Err::<nat, u64>(e),
    ensures
        forall|f: bool| #[trigger] rfc_uni_stream(all + t, f, seen0) == (em, Some(e)),
{
    if k is QpackEncoder {
        lemma_encoder_stream_err(b, t);
    } else {
        lemma_decoder_stream_err(b, t);
    }
    assert forall|f: bool| #[trigger] rfc_uni_stream(all + t, f, seen0) == (em, Some(e)) by {
        assert(rfc_uni_stream(all + t, f, seen0) == prepend(em, tail_of(k, st, 0, b + t, f)));
        assert(em + Seq::<SpecUniEvent>::empty() =~= em);
    }
}

/// A ready stream's bytes so far: its events, and the error a FIN gives.
proof fn lemma_qpack_end(s: UniStream, fin: bool)
    requires
        ready(s),
    ensures
        rfc_uni_stream(s.all@, fin, s.seen0@) == (s.emitted@, fin_err(fin)),
{
    assert(s.all@ + Seq::<u8>::empty() =~= s.all@);
    assert(s.buf@ + Seq::<u8>::empty() =~= s.buf@);
    assert(rfc_uni_stream(s.all@ + Seq::empty(), fin, s.seen0@) == prepend(
        s.emitted@,
        tail_of(s.kind, s.ctrl, s.skip, s.buf@ + Seq::empty(), fin),
    ));
    assert(s.emitted@ + Seq::<SpecUniEvent>::empty() =~= s.emitted@);
}

} // verus!
