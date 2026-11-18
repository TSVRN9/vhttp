//! Client request streams (RFC 9114 §4.1): an RFC-transcribed spec over every byte a request
//! stream has delivered, and an incremental machine proven to agree with it after every call,
//! however the bytes are split into chunks.
//!
//! Proof shape (as in `h3::uni`): the machine keeps the unconsumed bytes `buf`, a `Mode` for a
//! payload still arriving (skipped, or passed on as content), and the invariant `split_ok`: for
//! every future suffix `t`, the spec of `all + t` is the spec of `buf + t` resumed from the
//! machine's state, with the events emitted so far (body chunks concatenated) as accumulator.
use byteq::capvec::CapVec;
use byteq::queue::ByteQueue;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

use crate::codes::*;
use crate::frame::*;
use crate::limits::*;
use crate::message::*;
use crate::qpack::field_section::*;

verus! {

pub enum ReqEvent {
    Head(RequestHead),
    /// Request content as it arrives; never empty.
    Body(Vec<u8>),
    Trailers(Vec<FieldLine>),
    End,
}

pub enum SpecReqEvent {
    Head(SpecRequestHead),
    /// In `rfc_request_stream`, all content so far; in `views` of exec events, one chunk.
    BodyBytes(Seq<u8>),
    Trailers(Seq<(Seq<u8>, Seq<u8>)>),
    End,
}

impl View for ReqEvent {
    type V = SpecReqEvent;

    open spec fn view(&self) -> SpecReqEvent {
        match self {
            ReqEvent::Head(h) => SpecReqEvent::Head(h@),
            ReqEvent::Body(v) => SpecReqEvent::BodyBytes(v@),
            ReqEvent::Trailers(v) => SpecReqEvent::Trailers(fields_view(v@)),
            ReqEvent::End => SpecReqEvent::End,
        }
    }
}

/// A connection error or a stream error, with its code.
#[derive(Debug, PartialEq, Eq)]
pub enum ReqError {
    Connection(u64),
    Stream(u64),
}

/// `ReqError` holds only codes, so it is its own spec value.
pub type SpecReqError = ReqError;

/// Where the message is: before its header section, in its content, or after its trailer
/// section. `cl_left`: the content-length bytes still expected, when one was given.
pub enum Phase {
    AwaitHeaders,
    Body { cl_left: Option<u64> },
    Trailers { cl_left: Option<u64> },
}

pub open spec fn views(s: Seq<ReqEvent>) -> Seq<SpecReqEvent> {
    s.map_values(|e: ReqEvent| e@)
}

/// Appends content: extends a trailing `BodyBytes`, or starts one. Empty content is no event.
pub open spec fn add_body(acc: Seq<SpecReqEvent>, x: Seq<u8>) -> Seq<SpecReqEvent> {
    if x.len() == 0 {
        acc
    } else if acc.len() > 0 && acc.last() is BodyBytes {
        acc.drop_last().push(SpecReqEvent::BodyBytes(acc.last()->BodyBytes_0 + x))
    } else {
        acc.push(SpecReqEvent::BodyBytes(x))
    }
}

pub open spec fn add_event(acc: Seq<SpecReqEvent>, e: SpecReqEvent) -> Seq<SpecReqEvent> {
    match e {
        SpecReqEvent::BodyBytes(x) => add_body(acc, x),
        _ => acc.push(e),
    }
}

pub open spec fn push_all(acc: Seq<SpecReqEvent>, s: Seq<SpecReqEvent>) -> Seq<SpecReqEvent>
    decreases s.len(),
{
    if s.len() == 0 {
        acc
    } else {
        add_event(push_all(acc, s.drop_last()), s.last())
    }
}

/// The events with consecutive body chunks concatenated (and empty ones dropped): the form
/// `rfc_request_stream` reports.
pub open spec fn concat_bodies(s: Seq<SpecReqEvent>) -> Seq<SpecReqEvent> {
    push_all(Seq::empty(), s)
}

/// A `Body` event carries at least one byte.
pub open spec fn body_nonempty(e: ReqEvent) -> bool {
    match e {
        ReqEvent::Body(b) => b@.len() > 0,
        _ => true,
    }
}

/// Every event of `s` from index `a` on satisfies `body_nonempty`.
pub open spec fn bodies_from(s: Seq<ReqEvent>, a: int) -> bool {
    forall|i: int| a <= i < s.len() ==> body_nonempty(#[trigger] s[i])
}

pub open spec fn err_of(r: Result<(), ReqError>) -> Option<ReqError> {
    match r {
        Ok(_) => None,
        Err(e) => Some(e),
    }
}

// =============================================================================
// RFC 9114 §4.1 transcription
// =============================================================================

//= https://www.rfc-editor.org/rfc/rfc9114#section-7.1
//# When a stream terminates cleanly, if the last frame on the stream was
//# truncated, this MUST be treated as a connection error of type
//# H3_FRAME_ERROR.
/// A FIN inside a frame (its header or its payload incomplete).
pub open spec fn cut(fin: bool) -> Option<ReqError> {
    if fin {
        Some(ReqError::Connection(H3_FRAME_ERROR))
    } else {
        None
    }
}

pub open spec fn cl_of(ph: Phase) -> Option<u64> {
    match ph {
        Phase::AwaitHeaders => None,
        Phase::Body { cl_left } => cl_left,
        Phase::Trailers { cl_left } => cl_left,
    }
}

//= https://www.rfc-editor.org/rfc/rfc9114#section-4.1
//# When a stream is closed, this indicates the end of the final HTTP
//# message.
//= https://www.rfc-editor.org/rfc/rfc9114#section-4.1
//# If a client-initiated
//# stream terminates without enough of the HTTP message to provide a
//# complete response, the server SHOULD abort its response stream with
//# the error code H3_REQUEST_INCOMPLETE.
//= https://www.rfc-editor.org/rfc/rfc9114#section-4.1.2
//# A request or response that is defined as having content when it
//# contains a Content-Length header field (Section 8.6 of [HTTP]) is
//# malformed if the value of the Content-Length header field does not
//# equal the sum of the DATA frame lengths received.
/// A FIN at a frame boundary.
pub open spec fn rfc_end(ph: Phase, acc: Seq<SpecReqEvent>) -> (
    Seq<SpecReqEvent>,
    Option<ReqError>,
) {
    if ph is AwaitHeaders {
        (acc, Some(ReqError::Stream(H3_REQUEST_INCOMPLETE)))
    } else if cl_of(ph) is Some && cl_of(ph)->0 != 0 {
        (acc, Some(ReqError::Stream(H3_MESSAGE_ERROR)))
    } else {
        (acc.push(SpecReqEvent::End), None)
    }
}

//= https://www.rfc-editor.org/rfc/rfc9114#section-4.1
//# Receipt of an invalid sequence of frames MUST be treated as a
//# connection error of type H3_FRAME_UNEXPECTED.  In particular, a DATA
//# frame before any HEADERS frame, or a HEADERS or DATA frame after the
//# trailing HEADERS frame, is considered invalid.
//= https://www.rfc-editor.org/rfc/rfc9114#section-7.2.3
//# Receiving a
//# CANCEL_PUSH frame on a stream other than the control stream MUST be
//# treated as a connection error of type H3_FRAME_UNEXPECTED.
//= https://www.rfc-editor.org/rfc/rfc9114#section-7.2.4
//# If an endpoint receives a SETTINGS frame on a different
//# stream, the endpoint MUST respond with a connection error of type
//# H3_FRAME_UNEXPECTED.
//= https://www.rfc-editor.org/rfc/rfc9114#section-7.2.5
//# A server MUST treat the
//# receipt of a PUSH_PROMISE frame as a connection error of type
//# H3_FRAME_UNEXPECTED.
//= https://www.rfc-editor.org/rfc/rfc9114#section-7.2.7
//# Receipt
//# of a MAX_PUSH_ID frame on any other stream MUST be treated as a
//# connection error of type H3_FRAME_UNEXPECTED.
//= https://www.rfc-editor.org/rfc/rfc9114#section-7.2.8
//# These frame
//# types MUST NOT be sent, and their receipt MUST be treated as a
//# connection error of type H3_FRAME_UNEXPECTED.
//= https://www.rfc-editor.org/rfc/rfc9114#section-4.2.2
//# An HTTP/3 implementation MAY impose a limit on the maximum size of
//# the message header it will accept on an individual HTTP message.
/// The error a request-stream frame earns from its header alone. A GOAWAY is a control-stream
/// frame, so on a request stream it is an invalid sequence of frames. A HEADERS payload over
/// our MAX_FIELD_SECTION_SIZE is refused before it is buffered. Unknown frames have no limit.
pub open spec fn rfc_req_header_error(ph: Phase, ty: u64, len: u64) -> Option<ReqError> {
    if ty == FRAME_SETTINGS || ty == FRAME_CANCEL_PUSH || ty == FRAME_GOAWAY || ty
        == FRAME_MAX_PUSH_ID || ty == FRAME_PUSH_PROMISE || is_h2_reserved_frame_spec(ty) {
        Some(ReqError::Connection(H3_FRAME_UNEXPECTED))
    } else if (ty == FRAME_DATA && ph is AwaitHeaders) || ((ty == FRAME_DATA || ty
        == FRAME_HEADERS) && ph is Trailers) {
        Some(ReqError::Connection(H3_FRAME_UNEXPECTED))
    } else if ty == FRAME_HEADERS && len > MAX_FIELD_SECTION_SIZE {
        Some(ReqError::Stream(H3_EXCESSIVE_LOAD))
    } else {
        None
    }
}

//= https://www.rfc-editor.org/rfc/rfc9114#section-7.2.2
//# The HEADERS frame (type=0x01) is used to carry an HTTP field section
//# that is encoded using QPACK.
//= https://www.rfc-editor.org/rfc/rfc9114#section-4.1.2
//# Malformed requests or responses that are
//# detected MUST be treated as a stream error of type H3_MESSAGE_ERROR.
/// A complete HEADERS payload in phase `ph`: the header section, then the trailer section.
/// QPACK errors are connection errors (Phase 2a ruling); a decoded size over the budget is
/// H3_EXCESSIVE_LOAD.
pub open spec fn rfc_headers(ph: Phase, p: Seq<u8>) -> Result<(SpecReqEvent, Phase), ReqError> {
    match rfc_decode_field_section_bounded(p, MAX_FIELD_SECTION_SIZE) {
        Err(BoundedError::Qpack(c)) => Err(ReqError::Connection(c)),
        Err(BoundedError::OverBudget) => Err(ReqError::Stream(H3_EXCESSIVE_LOAD)),
        Ok(f) => match ph {
            Phase::AwaitHeaders => match rfc_validate_request(f) {
                Ok(h) => Ok(
                    (SpecReqEvent::Head(h), Phase::Body { cl_left: rfc_content_length(f) }),
                ),
                Err(_) => Err(ReqError::Stream(H3_MESSAGE_ERROR)),
            },
            Phase::Body { cl_left } => if rfc_validate_trailers(f) {
                Ok((SpecReqEvent::Trailers(f), Phase::Trailers { cl_left }))
            } else {
                Err(ReqError::Stream(H3_MESSAGE_ERROR))
            },
            Phase::Trailers { .. } => Err(ReqError::Connection(H3_FRAME_UNEXPECTED)),
        },
    }
}

/// `ph` after `n` more content bytes.
pub open spec fn sub_cl(ph: Phase, n: u64) -> Phase {
    match ph {
        Phase::Body { cl_left: Some(r) } => Phase::Body { cl_left: Some((r - n) as u64) },
        _ => ph,
    }
}

/// `d` content bytes arriving exceed the content-length bytes still expected.
pub open spec fn data_over(ph: Phase, d: int) -> bool {
    cl_of(ph) is Some && d > cl_of(ph)->0
}

/// The bytes of an `n`-byte payload present in `p`.
pub open spec fn min_len(n: u64, p: Seq<u8>) -> int {
    if n < p.len() {
        n as int
    } else {
        p.len() as int
    }
}

#[verifier::decreases_by]
proof fn req_decreases(b: Seq<u8>, ph: Phase, acc: Seq<SpecReqEvent>, fin: bool) {
    lemma_frame_header_bounds(b);
}

//= https://www.rfc-editor.org/rfc/rfc9114#section-4.1
//# An HTTP message (request or response) consists of:
//= https://www.rfc-editor.org/rfc/rfc9114#section-7.2.1
//# DATA frames (type=0x00) convey arbitrary, variable-length sequences
//# of bytes associated with HTTP request or response content.
//= https://www.rfc-editor.org/rfc/rfc9114#section-4.1
//# Because some messages are large or unbounded, endpoints
//# SHOULD begin processing partial HTTP messages once enough of the
//# message has been received to make progress.
//= https://www.rfc-editor.org/rfc/rfc9114#section-4.1
//# Frames of unknown types (Section 9), including reserved frames
//# (Section 7.2.8) MAY be sent on a request or push stream before,
//# after, or interleaved with other frames described in this section.
//= https://www.rfc-editor.org/rfc/rfc9114#section-9
//# Implementations MUST ignore unknown or unsupported values in all
//# extensible protocol elements.
/// The stream from `b` on, in phase `ph`, after events `acc`: the events up to the first error,
/// and that error. Content is passed on as it arrives, so a partial DATA payload counts; content
/// past the content-length is H3_MESSAGE_ERROR as soon as it arrives, after the bytes that fit.
/// Unknown frames are skipped in every phase.
pub open spec fn rfc_req(b: Seq<u8>, ph: Phase, acc: Seq<SpecReqEvent>, fin: bool) -> (
    Seq<SpecReqEvent>,
    Option<ReqError>,
)
    decreases b.len(),
    via req_decreases
{
    match rfc_frame_header(b) {
        None => if fin && b.len() == 0 {
            rfc_end(ph, acc)
        } else {
            (acc, cut(fin))
        },
        Some((h, ty, len)) => {
            let p = b.skip(h as int);
            if rfc_req_header_error(ph, ty, len) is Some {
                (acc, rfc_req_header_error(ph, ty, len))
            } else if ty == FRAME_DATA {
                if data_over(ph, min_len(len, p)) {
                    (
                        add_body(acc, p.take(cl_of(ph)->0 as int)),
                        Some(ReqError::Stream(H3_MESSAGE_ERROR)),
                    )
                } else if p.len() < len {
                    (add_body(acc, p), cut(fin))
                } else {
                    rfc_req(
                        p.skip(len as int),
                        sub_cl(ph, len),
                        add_body(acc, p.take(len as int)),
                        fin,
                    )
                }
            } else if p.len() < len {
                (acc, cut(fin))
            } else if ty == FRAME_HEADERS {
                match rfc_headers(ph, p.take(len as int)) {
                    Err(e) => (acc, Some(e)),
                    Ok((ev, ph2)) => rfc_req(p.skip(len as int), ph2, acc.push(ev), fin),
                }
            } else {
                rfc_req(p.skip(len as int), ph, acc, fin)
            }
        },
    }
}

/// Events (content concatenated) and error for the `bytes` a request stream has delivered so
/// far (`fin`: they are all of it).
pub open spec fn rfc_request_stream(bytes: Seq<u8>, fin: bool) -> (
    Seq<SpecReqEvent>,
    Option<SpecReqError>,
) {
    rfc_req(bytes, Phase::AwaitHeaders, Seq::empty(), fin)
}

// =============================================================================
// Machine invariants and lemmas
// =============================================================================

/// Bound on a live stream's unconsumed bytes: a frame header (at most 16 bytes) plus a HEADERS
/// payload of at most MAX_FIELD_SECTION_SIZE; DATA and unknown payloads are never buffered.
/// Equal to `16 + MAX_FIELD_SECTION_SIZE`; the bound proof fails if that limit outgrows it.
pub const REQ_BUF_CAP: usize = 65552;

/// What the bytes after `buf` belong to: frames, or the rest of a payload that is skipped
/// (unknown frame) or passed on as content (DATA).
enum Mode {
    Frames,
    Unknown(u64),
    Data(u64),
}

/// The stream after `n` more bytes of an unknown payload are skipped.
spec fn rfc_skip(p: Seq<u8>, n: u64, ph: Phase, acc: Seq<SpecReqEvent>, fin: bool) -> (
    Seq<SpecReqEvent>,
    Option<ReqError>,
) {
    if p.len() < n {
        (acc, cut(fin))
    } else {
        rfc_req(p.skip(n as int), ph, acc, fin)
    }
}

/// The stream after `n` more bytes of a DATA payload (`rfc_req`'s DATA case).
spec fn rfc_data(p: Seq<u8>, n: u64, ph: Phase, acc: Seq<SpecReqEvent>, fin: bool) -> (
    Seq<SpecReqEvent>,
    Option<ReqError>,
) {
    if data_over(ph, min_len(n, p)) {
        (add_body(acc, p.take(cl_of(ph)->0 as int)), Some(ReqError::Stream(H3_MESSAGE_ERROR)))
    } else if p.len() < n {
        (add_body(acc, p), cut(fin))
    } else {
        rfc_req(p.skip(n as int), sub_cl(ph, n), add_body(acc, p.take(n as int)), fin)
    }
}

/// The stream from `b` on, as the machine tracks it.
spec fn rest(m: Mode, ph: Phase, acc: Seq<SpecReqEvent>, b: Seq<u8>, f: bool) -> (
    Seq<SpecReqEvent>,
    Option<ReqError>,
) {
    match m {
        Mode::Frames => rfc_req(b, ph, acc, f),
        Mode::Unknown(n) => rfc_skip(b, n, ph, acc, f),
        Mode::Data(n) => rfc_data(b, n, ph, acc, f),
    }
}

/// The result when `blen` unconsumed bytes complete nothing.
spec fn finish(m: Mode, ph: Phase, acc: Seq<SpecReqEvent>, blen: nat, f: bool) -> (
    Seq<SpecReqEvent>,
    Option<ReqError>,
) {
    if f && m is Frames && blen == 0 {
        rfc_end(ph, acc)
    } else {
        (acc, cut(f))
    }
}

/// `b` completes nothing: without more bytes, only a FIN could still change the result.
spec fn settled(m: Mode, ph: Phase, acc: Seq<SpecReqEvent>, b: Seq<u8>) -> bool {
    forall|f: bool| #[trigger] rest(m, ph, acc, b, f) == finish(m, ph, acc, b.len(), f)
}

spec fn mode_ok(m: Mode, ph: Phase) -> bool {
    match m {
        Mode::Frames => true,
        Mode::Unknown(n) => n > 0,
        Mode::Data(n) => n > 0 && ph is Body,
    }
}

/// What `buf` may hold: part of a frame header, or one HEADERS frame (within our limit) whose
/// payload is incomplete.
spec fn buf_shape(b: Seq<u8>) -> bool {
    match rfc_frame_header(b) {
        None => true,
        Some((h, ty, len)) => ty == FRAME_HEADERS && len <= MAX_FIELD_SECTION_SIZE && b.len() < h
            + len,
    }
}

/// For every suffix `t`, the spec of `all + t` resumes from the machine's state on `buf + t`, `acc` the events so
/// far with content concatenated (content not yet returned included).
spec fn split_ok(all: Seq<u8>, acc: Seq<SpecReqEvent>, m: Mode, ph: Phase, buf: Seq<u8>) -> bool {
    forall|t: Seq<u8>, f: bool| #[trigger] rfc_request_stream(all + t, f) == rest(m, ph, acc, buf + t, f)
}

/// What `run` guarantees from `(m0, ph0, acc0)` on `s` to `(m1, ph1, acc1)`.
spec fn ran(
    s: Seq<u8>,
    m0: Mode,
    ph0: Phase,
    acc0: Seq<SpecReqEvent>,
    m1: Mode,
    ph1: Phase,
    acc1: Seq<SpecReqEvent>,
    r: Result<usize, ReqError>,
) -> bool {
    match r {
        Ok(n) => {
            &&& n <= s.len()
            &&& mode_ok(m1, ph1)
            &&& n < s.len() ==> m1 is Frames
            &&& buf_shape(s.skip(n as int))
            &&& forall|t: Seq<u8>, f: bool| #[trigger]
                rest(m0, ph0, acc0, s + t, f) == rest(m1, ph1, acc1, s.skip(n as int) + t, f)
            &&& settled(m1, ph1, acc1, s.skip(n as int))
        },
        Err(e) => forall|t: Seq<u8>, f: bool| #[trigger]
            rest(m0, ph0, acc0, s + t, f) == (acc1, Some(e)),
    }
}

proof fn lemma_views_push(s: Seq<ReqEvent>, k: int, x: ReqEvent)
    requires
        0 <= k <= s.len(),
    ensures
        views(s.push(x).skip(k)) == views(s.skip(k)).push(x@),
        s.push(x).take(k) == s.take(k),
{
    assert(views(s.push(x).skip(k)) =~= views(s.skip(k)).push(x@));
    assert(s.push(x).take(k) =~= s.take(k));
}

proof fn lemma_bodies_trans(a: int, e1: Seq<ReqEvent>, e2: Seq<ReqEvent>)
    requires
        0 <= a <= e1.len() <= e2.len(),
        e2.take(e1.len() as int) == e1,
        bodies_from(e1, a),
        bodies_from(e2, e1.len() as int),
    ensures
        bodies_from(e2, a),
{
    assert forall|i: int| a <= i < e2.len() implies body_nonempty(#[trigger] e2[i]) by {
        if i < e1.len() {
            assert(e2.take(e1.len() as int)[i] == e2[i]);
        }
    }
}

proof fn lemma_push_all_push(acc: Seq<SpecReqEvent>, s: Seq<SpecReqEvent>, x: SpecReqEvent)
    ensures
        push_all(acc, s.push(x)) == add_event(push_all(acc, s), x),
{
    assert(s.push(x).drop_last() =~= s);
}

proof fn lemma_push_all_append(acc: Seq<SpecReqEvent>, s1: Seq<SpecReqEvent>, s2: Seq<SpecReqEvent>)
    ensures
        push_all(acc, s1 + s2) == push_all(push_all(acc, s1), s2),
    decreases s2.len(),
{
    if s2.len() == 0 {
        assert(s1 + s2 =~= s1);
    } else {
        lemma_push_all_append(acc, s1, s2.drop_last());
        assert((s1 + s2).drop_last() =~= s1 + s2.drop_last());
        assert((s1 + s2).last() == s2.last());
    }
}

proof fn lemma_add_body_assoc(a: Seq<SpecReqEvent>, x: Seq<u8>, y: Seq<u8>)
    ensures
        add_body(add_body(a, x), y) == add_body(a, x + y),
{
    if x.len() == 0 {
        assert(x + y =~= y);
    } else if y.len() == 0 {
        assert(x + y =~= x);
    } else if a.len() > 0 && a.last() is BodyBytes {
        let w = a.last()->BodyBytes_0;
        let ax = add_body(a, x);
        assert(ax.drop_last() =~= a.drop_last());
        assert((w + x) + y =~= w + (x + y));
    } else {
        let ax = add_body(a, x);
        assert(ax.drop_last() =~= a);
    }
}

/// One request-stream frame whose header is complete, followed by anything.
#[verifier::spinoff_prover]
proof fn lemma_frame_at(
    b: Seq<u8>,
    ph: Phase,
    acc: Seq<SpecReqEvent>,
    h: nat,
    ty: u64,
    len: u64,
    t: Seq<u8>,
    f: bool,
)
    requires
        rfc_frame_header(b) == Some((h, ty, len)),
    ensures
        rfc_req_header_error(ph, ty, len) is Some ==> rfc_req(b + t, ph, acc, f) == (
            acc,
            rfc_req_header_error(ph, ty, len),
        ),
        rfc_req_header_error(ph, ty, len) is None && ty == FRAME_DATA ==> rfc_req(b + t, ph, acc, f)
            == rfc_data(b.skip(h as int) + t, len, ph, acc, f),
        rfc_req_header_error(ph, ty, len) is None && ty != FRAME_DATA && ty != FRAME_HEADERS
            ==> rfc_req(b + t, ph, acc, f) == rfc_skip(b.skip(h as int) + t, len, ph, acc, f),
        rfc_req_header_error(ph, ty, len) is None && ty == FRAME_HEADERS && h + len <= b.len()
            ==> rfc_req(b + t, ph, acc, f) == match rfc_headers(
            ph,
            b.subrange(h as int, h + len),
        ) {
            Err(e) => (acc, Some(e)),
            Ok((ev, ph2)) => rfc_req(b.skip(h + len) + t, ph2, acc.push(ev), f),
        },
{
    hide(rfc_headers);
    hide(rfc_end);
    lemma_frame_header_prefix(b, t);
    lemma_frame_header_bounds(b);
    let p = (b + t).skip(h as int);
    assert(p =~= b.skip(h as int) + t);
    if h + len <= b.len() {
        assert(p.take(len as int) =~= b.subrange(h as int, h + len));
        assert(p.skip(len as int) =~= b.skip(h + len) + t);
    }
}

/// Skipping `d` bytes of a pending unknown payload.
proof fn lemma_skip_discard(
    p: Seq<u8>,
    n: u64,
    ph: Phase,
    acc: Seq<SpecReqEvent>,
    d: nat,
    t: Seq<u8>,
    f: bool,
)
    requires
        d <= n,
        d <= p.len(),
    ensures
        rfc_skip(p + t, n, ph, acc, f) == rfc_skip(p.skip(d as int) + t, (n - d) as u64, ph, acc, f),
{
    let r = p.skip(d as int) + t;
    if (p + t).len() >= n {
        assert((p + t).skip(n as int) =~= r.skip(n - d));
    }
}

proof fn lemma_skip_zero(b: Seq<u8>, ph: Phase, acc: Seq<SpecReqEvent>, f: bool)
    ensures
        rfc_skip(b, 0, ph, acc, f) == rfc_req(b, ph, acc, f),
{
    assert(b.skip(0) =~= b);
}

/// Passing on `d` bytes of a pending DATA payload that the content-length still allows.
proof fn lemma_data_discard(
    p: Seq<u8>,
    n: u64,
    ph: Phase,
    acc: Seq<SpecReqEvent>,
    d: nat,
    t: Seq<u8>,
    f: bool,
)
    requires
        ph is Body,
        d <= n,
        d <= p.len(),
        !data_over(ph, d as int),
    ensures
        rfc_data(p + t, n, ph, acc, f) == rfc_data(
            p.skip(d as int) + t,
            (n - d) as u64,
            sub_cl(ph, d as u64),
            add_body(acc, p.take(d as int)),
            f,
        ),
{
    let q = p + t;
    let q2 = p.skip(d as int) + t;
    let x = p.take(d as int);
    let n2 = (n - d) as u64;
    let ph2 = sub_cl(ph, d as u64);
    assert(x + q2 =~= q);
    assert(min_len(n2, q2) == min_len(n, q) - d);
    if cl_of(ph) is Some {
        let r = cl_of(ph)->0;
        assert(cl_of(ph2) == Some((r - d) as u64));
        if min_len(n, q) > r {
            assert(q.take(r as int) =~= x + q2.take(r - d));
            lemma_add_body_assoc(acc, x, q2.take(r - d));
        }
    } else {
        assert(cl_of(ph2) is None);
    }
    if q.len() < n {
        lemma_add_body_assoc(acc, x, q2);
    } else {
        assert(q2.skip(n2 as int) =~= q.skip(n as int));
        assert(q.take(n as int) =~= x + q2.take(n2 as int));
        lemma_add_body_assoc(acc, x, q2.take(n2 as int));
        assert(sub_cl(ph2, n2) == sub_cl(ph, n));
    }
}

/// Content past the content-length: an error once it is present, whatever follows.
proof fn lemma_data_over(p: Seq<u8>, n: u64, ph: Phase, acc: Seq<SpecReqEvent>, t: Seq<u8>, f: bool)
    requires
        data_over(ph, min_len(n, p)),
    ensures
        rfc_data(p + t, n, ph, acc, f) == (
            add_body(acc, p.take(cl_of(ph)->0 as int)),
            Some(ReqError::Stream(H3_MESSAGE_ERROR)),
        ),
{
    let r = cl_of(ph)->0;
    assert(min_len(n, p + t) >= min_len(n, p));
    assert((p + t).take(r as int) =~= p.take(r as int));
}

proof fn lemma_data_zero(b: Seq<u8>, ph: Phase, acc: Seq<SpecReqEvent>, f: bool)
    requires
        ph is Body,
    ensures
        rfc_data(b, 0, ph, acc, f) == rfc_req(b, ph, acc, f),
{
    assert(b.skip(0) =~= b);
    assert(b.take(0) =~= Seq::<u8>::empty());
    assert(sub_cl(ph, 0) == ph);
}

proof fn lemma_settled_empty(m: Mode, ph: Phase, acc: Seq<SpecReqEvent>)
    requires
        mode_ok(m, ph),
    ensures
        settled(m, ph, acc, Seq::empty()),
        buf_shape(Seq::empty()),
{
    lemma_frame_header_bounds(Seq::<u8>::empty());
    assert forall|f: bool| #[trigger]
        rest(m, ph, acc, Seq::empty(), f) == finish(m, ph, acc, 0, f) by {
        if let Mode::Data(n) = m {
            assert(min_len(n, Seq::<u8>::empty()) == 0);
        }
    }
}

proof fn lemma_buf_bound(b: Seq<u8>)
    requires
        buf_shape(b),
    ensures
        b.len() < REQ_BUF_CAP,
{
    lemma_frame_header_bounds(b);
}

/// Appending `p` to both the received bytes and the buffer preserves `split_ok`.
proof fn lemma_split_append(
    all: Seq<u8>,
    acc: Seq<SpecReqEvent>,
    m: Mode,
    ph: Phase,
    buf: Seq<u8>,
    p: Seq<u8>,
)
    requires
        split_ok(all, acc, m, ph, buf),
    ensures
        split_ok(all + p, acc, m, ph, buf + p),
{
    assert forall|t: Seq<u8>, f: bool| #[trigger]
        rfc_request_stream((all + p) + t, f) == rest(m, ph, acc, (buf + p) + t, f) by {
        assert(all + (p + t) =~= (all + p) + t);
        assert(buf + (p + t) =~= (buf + p) + t);
        assert(rfc_request_stream(all + (p + t), f) == rest(m, ph, acc, buf + (p + t), f));
    }
}

/// `run` on the whole buffer moves `split_ok` past what it consumed.
proof fn lemma_run_ok(
    all: Seq<u8>,
    a0: Seq<SpecReqEvent>,
    m0: Mode,
    ph0: Phase,
    b: Seq<u8>,
    m1: Mode,
    ph1: Phase,
    a1: Seq<SpecReqEvent>,
    n: usize,
)
    requires
        split_ok(all, a0, m0, ph0, b),
        ran(b, m0, ph0, a0, m1, ph1, a1, Ok(n)),
    ensures
        split_ok(all, a1, m1, ph1, b.skip(n as int)),
        settled(m1, ph1, a1, b.skip(n as int)),
{
    assert forall|t: Seq<u8>, f: bool| #[trigger]
        rfc_request_stream(all + t, f) == rest(m1, ph1, a1, b.skip(n as int) + t, f) by {
        assert(rest(m0, ph0, a0, b + t, f) == rest(m1, ph1, a1, b.skip(n as int) + t, f));
    }
}

proof fn lemma_run_err(all: Seq<u8>, a0: Seq<SpecReqEvent>, m0: Mode, ph0: Phase, b: Seq<u8>, a1: Seq<SpecReqEvent>, e: ReqError)
    requires
        split_ok(all, a0, m0, ph0, b),
        forall|t: Seq<u8>, f: bool| #[trigger] rest(m0, ph0, a0, b + t, f) == (a1, Some(e)),
    ensures
        forall|t: Seq<u8>, f: bool| #[trigger] rfc_request_stream(all + t, f) == (a1, Some(e)),
{
    assert forall|t: Seq<u8>, f: bool| #[trigger] rfc_request_stream(all + t, f) == (a1, Some(e)) by {
        assert(rest(m0, ph0, a0, b + t, f) == (a1, Some(e)));
    }
}

// =============================================================================
// Executable machine
// =============================================================================

/// At most this many events per `on_data` call: Head, one Body, Trailers, End (spec D6).
pub const MAX_REQ_EVENTS: usize = 4;

/// The cost constant of `headers_frame`: the decode (`c_sec`), then `validate_request` and `content_length` (or
/// `validate_trailers`) and the free of the decoded lines, over at most 77 decoded bytes and lines per encoded byte
/// (`lemma_section_expansion`): 264 + 77·(500 + 20 + 2) = 40,458, rounded up with the constants.
#[verifier::inline]
spec fn c_hf() -> nat {
    41000
}

/// The cost constant of one step (`step_cost`): a HEADERS frame's `c_hf`, its header parse (at most 16 bytes, 17) and
/// the Body it returns first.
#[verifier::inline]
spec fn c_st() -> nat {
    41020
}

/// The cost constant of `run`: a step and its loop iteration.
#[verifier::inline]
spec fn c_run() -> nat {
    41021
}

/// The cost constant of `advance`, per byte of `data` it moves: `2·c_run() + 34` (`run` on the bytes, the rescan of the
/// partial frame header it keeps, `top_up`'s or the tail's push).
#[verifier::inline]
spec fn c_it() -> nat {
    82076
}

/// `on_data`'s cost per byte given: `advance` and its loop iteration (`c_it() + 1`), rounded up.
#[verifier::inline]
pub open spec fn c_req() -> nat {
    82080
}

/// `on_data`'s cost per byte held before the call (the `F` term): the frame a call completes from `buf` is run once.
#[verifier::inline]
pub open spec fn c_frame() -> nat {
    41021
}

/// A step's cost: `c_st` per byte consumed, `c_st` for a step that consumes nothing, `c_st` per byte of `r` (plus one)
/// for one that fails.
spec fn step_cost(res: Result<Option<usize>, ReqError>, w: nat, len: nat) -> bool {
    match res {
        Ok(Some(k)) => w <= c_st() * (k as nat),
        Ok(None) => w <= c_st(),
        Err(_) => w <= c_st() * (len + 1),
    }
}

/// The content this call has passed on and not yet returned as a `Body` event.
spec fn pend(b: Option<CapVec<u8>>) -> Seq<u8> {
    match b {
        Some(v) => v@,
        None => Seq::empty(),
    }
}

/// The pending content can take `n` more bytes below its capacity.
spec fn room(b: Option<CapVec<u8>>, n: nat) -> bool {
    match b {
        Some(v) => v.wf() && v@.len() + n <= v.cap(),
        None => true,
    }
}

/// `len - base` events returned in this call, leaving room for what phase `ph` still allows: in `Body`, a Body,
/// Trailers and End; in `Trailers`, End. Content is pending only in `Body`.
spec fn ev_ok(len: nat, base: nat, cap: nat, ph: Phase, b: Option<CapVec<u8>>) -> bool {
    &&& base <= len
    &&& base + MAX_REQ_EVENTS <= cap
    &&& match ph {
        Phase::AwaitHeaders => len == base && b is None,
        Phase::Body { .. } => len <= base + 1,
        Phase::Trailers { .. } => len <= base + 3 && b is None,
    }
}

/// A frame header is read whole from `r`'s first `m` bytes once they cover it (N5).
proof fn lemma_header_cover(r: Seq<u8>, m: int)
    requires
        rfc_frame_header(r) matches Some((h, _, _)) && h <= m <= r.len(),
    ensures
        rfc_frame_header(r.take(m)) == rfc_frame_header(r),
{
    let q = r.take(m);
    lemma_decode_len_bounds(r);
    let n1 = rfc_varint_decode(r).unwrap().0;
    assert(q[0] == r[0]);
    assert(q.subrange(1, n1 as int) =~= r.subrange(1, n1 as int));
    assert(rfc_varint_decode(q) == rfc_varint_decode(r));
    let r2 = r.skip(n1 as int);
    let q2 = q.skip(n1 as int);
    lemma_decode_len_bounds(r2);
    let n2 = rfc_varint_decode(r2).unwrap().0;
    assert(q2[0] == r2[0]);
    assert(q2.subrange(1, n2 as int) =~= r2.subrange(1, n2 as int));
    assert(rfc_varint_decode(q2) == rfc_varint_decode(r2));
}

/// The header of `r` equals that of its first `min(16, len)` bytes: a header is at most 16 bytes (N5).
proof fn lemma_header_take(r: Seq<u8>, m: int)
    requires
        0 <= m <= r.len(),
        m >= 16 || m == r.len(),
    ensures
        rfc_frame_header(r.take(m)) == rfc_frame_header(r),
{
    lemma_frame_header_bounds(r);
    if rfc_frame_header(r) is Some {
        lemma_header_cover(r, m);
    } else {
        assert(r.take(m) =~= r);
    }
}

/// When `r`'s first `lo` bytes are a buffer `buf_shape` allows, `r`'s first frame header ends after them, or it is a
/// HEADERS frame whose payload does: no content byte of `r` lies in its first `lo`.
proof fn lemma_header_lo(r: Seq<u8>, lo: int)
    requires
        0 <= lo <= r.len(),
        buf_shape(r.take(lo)),
    ensures
        rfc_frame_header(r) matches Some((h, ty, len)) ==> lo < h || (ty == FRAME_HEADERS && lo < h + len),
{
    if let Some((h, _, _)) = rfc_frame_header(r) {
        if h <= lo {
            lemma_header_cover(r, lo);
        }
    }
}

/// Returning the pending content `p` as one `Body` event after `e0` gives what `add_body` says: adjacent content
/// concatenates, so one Body per call reports what one Body per DATA frame did.
proof fn lemma_concat_merge(a: Seq<SpecReqEvent>, e0: Seq<ReqEvent>, e1: Seq<ReqEvent>, k: int, p: Seq<u8>)
    requires
        0 <= k <= e0.len(),
        p.len() == 0 ==> e1 == e0,
        p.len() > 0 ==> e1 == e0.push(e1.last()) && e1.last()@ == SpecReqEvent::BodyBytes(p) && body_nonempty(
            e1.last(),
        ),
    ensures
        push_all(a, views(e1.skip(k))) == add_body(push_all(a, views(e0.skip(k))), p),
        e1.len() >= e0.len(),
        e1.take(e0.len() as int) == e0,
        bodies_from(e1, e0.len() as int),
{
    assert(e0.take(e0.len() as int) =~= e0);
    if p.len() > 0 {
        lemma_views_push(e0, k, e1.last());
        lemma_views_push(e0, e0.len() as int, e1.last());
        lemma_push_all_push(a, views(e0.skip(k)), e1.last()@);
    }
}

/// After `lemma_concat_merge`'s Body (if content was pending), one Head or Trailers: the events `add_body(a, p)` then
/// it.
proof fn lemma_flush_push(a: Seq<SpecReqEvent>, e0: Seq<ReqEvent>, e1: Seq<ReqEvent>, e2: Seq<ReqEvent>, p: Seq<u8>)
    requires
        push_all(a, views(e1.skip(e0.len() as int))) == add_body(push_all(a, views(e0.skip(e0.len() as int))), p),
        e1.len() >= e0.len(),
        e1.take(e0.len() as int) == e0,
        bodies_from(e1, e0.len() as int),
        e2 == e1.push(e2.last()),
        !(e2.last()@ is BodyBytes),
    ensures
        push_all(a, views(e2.skip(e0.len() as int))) == add_body(a, p).push(e2.last()@),
        e2.len() >= e0.len(),
        e2.take(e0.len() as int) == e0,
        bodies_from(e2, e0.len() as int),
{
    let x = e2.last();
    lemma_no_event(e0, a);
    lemma_views_push(e1, e0.len() as int, x);
    lemma_push_all_push(a, views(e1.skip(e0.len() as int)), x@);
    assert forall|i: int| e0.len() <= i < e2.len() implies body_nonempty(#[trigger] e2[i]) by {
        if i < e1.len() {
            assert(e2[i] == e1[i]);
            assert(body_nonempty(e1[i]));
        }
    }
}

/// A complete HEADERS frame at the front of `r` with no error from its header: the stream ends with the payload's
/// error, or resumes after the frame with its event pushed.
proof fn lemma_headers_rest(
    r: Seq<u8>,
    ph0: Phase,
    a0: Seq<SpecReqEvent>,
    h: nat,
    len: u64,
    res: Result<(SpecReqEvent, Phase), ReqError>,
)
    requires
        rfc_frame_header(r) == Some((h, FRAME_HEADERS, len)),
        rfc_req_header_error(ph0, FRAME_HEADERS, len) is None,
        h + len <= r.len(),
        res == rfc_headers(ph0, r.subrange(h as int, h + len)),
    ensures
        forall|t: Seq<u8>, f: bool| #[trigger]
            rest(Mode::Frames, ph0, a0, r + t, f) == match res {
                Err(e) => (a0, Some(e)),
                Ok((ev, ph1)) => rest(Mode::Frames, ph1, a0.push(ev), r.skip(h + len) + t, f),
            },
{
    assert forall|t: Seq<u8>, f: bool| #[trigger]
        rest(Mode::Frames, ph0, a0, r + t, f) == match res {
            Err(e) => (a0, Some(e)),
            Ok((ev, ph1)) => rest(Mode::Frames, ph1, a0.push(ev), r.skip(h + len) + t, f),
        } by {
        lemma_frame_at(r, ph0, a0, h, FRAME_HEADERS, len, t, f);
    }
}

fn req_header_error(ph: &Phase, ty: u64, len: u64) -> (r: Option<ReqError>)
    ensures
        r == rfc_req_header_error(*ph, ty, len),
{
    let await_headers = match ph {
        Phase::AwaitHeaders => true,
        _ => false,
    };
    let after_trailers = match ph {
        Phase::Trailers { .. } => true,
        _ => false,
    };
    if ty == FRAME_SETTINGS || ty == FRAME_CANCEL_PUSH || ty == FRAME_GOAWAY || ty
        == FRAME_MAX_PUSH_ID || ty == FRAME_PUSH_PROMISE || is_h2_reserved_frame(ty) {
        Some(ReqError::Connection(H3_FRAME_UNEXPECTED))
    } else if (ty == FRAME_DATA && await_headers) || ((ty == FRAME_DATA || ty == FRAME_HEADERS)
        && after_trailers) {
        Some(ReqError::Connection(H3_FRAME_UNEXPECTED))
    } else if ty == FRAME_HEADERS && len > MAX_FIELD_SECTION_SIZE {
        Some(ReqError::Stream(H3_EXCESSIVE_LOAD))
    } else {
        None
    }
}

/// Decodes and validates a complete HEADERS payload; on success pushes one Head or Trailers.
fn headers_frame(p: &[u8], ph: &mut Phase, events: &mut CapVec<ReqEvent>) -> (r: (Result<(), ReqError>, Ghost<nat>))
    requires
        p@.len() <= MAX_FIELD_SECTION_SIZE,
        old(events).wf(),
        old(events)@.len() < old(events).cap(),
    ensures
        final(events).wf(),
        final(events).cap() == old(events).cap(),
        match r.0 {
            Ok(()) => {
                &&& final(events)@ == old(events)@.push(final(events)@.last())
                &&& rfc_headers(*old(ph), p@) == Ok::<(SpecReqEvent, Phase), ReqError>(
                    (final(events)@.last()@, *final(ph)),
                )
                &&& *old(ph) is AwaitHeaders ==> *final(ph) is Body
                &&& *old(ph) is Body ==> *final(ph) is Trailers
                &&& !(final(events)@.last()@ is BodyBytes)
            },
            Err(e) => {
                &&& final(events)@ == old(events)@
                &&& rfc_headers(*old(ph), p@) == Err::<(SpecReqEvent, Phase), ReqError>(e)
            },
        },
        r.1@ <= c_hf() * (p@.len() + 1),
{
    let (dec, Ghost(cd)) = decode_field_section_bounded(p, MAX_FIELD_SECTION_SIZE);
    let fields = match dec {
        Ok(f) => f,
        Err(BoundedError::Qpack(c)) => return (Err(ReqError::Connection(c)), Ghost(cd)),
        Err(BoundedError::OverBudget) => return (Err(ReqError::Stream(H3_EXCESSIVE_LOAD)), Ghost(cd)),
    };
    proof {
        lemma_section_size(p@, MAX_FIELD_SECTION_SIZE);
        lemma_section_expansion(p@, MAX_FIELD_SECTION_SIZE);
    }
    // The decoded lines' bytes and count, at most 77 per encoded byte; freeing the lines costs 2n + 1.
    let ghost x: nat = fields_bytes(fields_view(fields@)) + fields@.len() + 1;
    match *ph {
        Phase::AwaitHeaders => {
            let (vr, Ghost(cv)) = validate_request(fields.as_slice());
            match vr {
                Ok(h) => {
                    let (cl, Ghost(cc)) = content_length(fields.as_slice());
                    events.push(ReqEvent::Head(h));
                    *ph = Phase::Body { cl_left: cl };
                    (Ok(()), Ghost(cd + cv + cc + 2 * x))
                },
                Err(_) => (Err(ReqError::Stream(H3_MESSAGE_ERROR)), Ghost(cd + cv + 2 * x)),
            }
        },
        Phase::Body { cl_left } => {
            let (vt, Ghost(ct)) = validate_trailers(fields.as_slice());
            if vt {
                events.push(ReqEvent::Trailers(fields));
                *ph = Phase::Trailers { cl_left };
                (Ok(()), Ghost(cd + ct + 1))
            } else {
                (Err(ReqError::Stream(H3_MESSAGE_ERROR)), Ghost(cd + ct + 2 * x))
            }
        },
        Phase::Trailers { .. } => (Err(ReqError::Connection(H3_FRAME_UNEXPECTED)), Ghost(cd + 2 * x)),
    }
}

/// Returns the pending content, if any, as one `Body` event.
fn flush(events: &mut CapVec<ReqEvent>, body: &mut Option<CapVec<u8>>) -> (r: Ghost<nat>)
    requires
        old(events).wf(),
        pend(*old(body)).len() > 0 ==> old(events)@.len() < old(events).cap(),
    ensures
        *final(body) is None,
        final(events).wf(),
        final(events).cap() == old(events).cap(),
        pend(*old(body)).len() == 0 ==> final(events)@ == old(events)@,
        pend(*old(body)).len() > 0 ==> final(events)@ == old(events)@.push(final(events)@.last())
            && final(events)@.last()@ == SpecReqEvent::BodyBytes(pend(*old(body))) && body_nonempty(
            final(events)@.last(),
        ),
        r@ <= 1,
{
    let mut cur: Option<CapVec<u8>> = None;
    core::mem::swap(&mut cur, body);
    match cur {
        Some(b) => {
            if b.len() > 0 {
                events.push(ReqEvent::Body(b.into_vec()));
            }
            Ghost(1)
        },
        None => Ghost(0),
    }
}

/// What one step on `r` (non-empty) guarantees: `Ok(Some(k))`, it consumed `k` bytes;
/// `Ok(None)`, `r` is a partial frame header or HEADERS frame and nothing changed.
spec fn stepped(
    r: Seq<u8>,
    m0: Mode,
    ph0: Phase,
    acc0: Seq<SpecReqEvent>,
    m1: Mode,
    ph1: Phase,
    acc1: Seq<SpecReqEvent>,
    res: Result<Option<usize>, ReqError>,
) -> bool {
    match res {
        Ok(Some(k)) => {
            &&& 0 < k <= r.len()
            &&& mode_ok(m1, ph1)
            &&& forall|t: Seq<u8>, f: bool| #[trigger]
                rest(m0, ph0, acc0, r + t, f) == rest(m1, ph1, acc1, r.skip(k as int) + t, f)
        },
        Ok(None) => {
            &&& m1 == m0
            &&& ph1 == ph0
            &&& acc1 == acc0
            &&& m0 is Frames
            &&& buf_shape(r)
            &&& settled(m0, ph0, acc0, r)
        },
        Err(e) => forall|t: Seq<u8>, f: bool| #[trigger]
            rest(m0, ph0, acc0, r + t, f) == (acc1, Some(e)),
    }
}

proof fn lemma_no_event(e0: Seq<ReqEvent>, acc: Seq<SpecReqEvent>)
    ensures
        push_all(acc, views(e0.skip(e0.len() as int))) == acc,
        e0.take(e0.len() as int) == e0,
{
    assert(e0.skip(e0.len() as int) =~= Seq::<ReqEvent>::empty());
    assert(views(Seq::<ReqEvent>::empty()) =~= Seq::<SpecReqEvent>::empty());
    assert(e0.take(e0.len() as int) =~= e0);
}

/// Skips the next bytes of an unknown payload.
fn step_skip(r: &[u8], Ghost(ph): Ghost<Phase>, mode: &mut Mode, Ghost(acc): Ghost<Seq<SpecReqEvent>>) -> (res: (
    Result<Option<usize>, ReqError>,
    Ghost<nat>,
))
    requires
        mode_ok(*old(mode), ph),
        *old(mode) is Unknown,
        r@.len() > 0,
    ensures
        stepped(r@, *old(mode), ph, acc, *final(mode), ph, acc, res.0),
        res.0 is Ok && res.0->Ok_0 is Some,
        step_cost(res.0, res.1@, r@.len()),
{
    let n = match *mode {
        Mode::Unknown(n) => n,
        _ => 0,
    };
    let d: usize = if n < r.len() as u64 {
        n as usize
    } else {
        r.len()
    };
    *mode = if n == d as u64 {
        Mode::Frames
    } else {
        Mode::Unknown(n - d as u64)
    };
    proof {
        assert forall|t: Seq<u8>, f: bool| #[trigger]
            rest(Mode::Unknown(n), ph, acc, r@ + t, f) == rest(*mode, ph, acc, r@.skip(d as int) + t, f) by {
            lemma_skip_discard(r@, n, ph, acc, d as nat, t, f);
            if n == d as u64 {
                lemma_skip_zero(r@.skip(d as int) + t, ph, acc, f);
            }
        }
    }
    (Ok(Some(d)), Ghost(1))
}

/// Passes on the next bytes of a DATA payload, or the bytes the content-length still allows and then
/// H3_MESSAGE_ERROR, into the call's one pending `body`, made at its first byte with room for the `r.len() + more`
/// bytes this call has not consumed.
fn step_data(
    r: &[u8],
    ph: &mut Phase,
    mode: &mut Mode,
    body: &mut Option<CapVec<u8>>,
    more: usize,
    Ghost(acc): Ghost<Seq<SpecReqEvent>>,
) -> (res: (Result<Option<usize>, ReqError>, Ghost<nat>))
    requires
        mode_ok(*old(mode), *old(ph)),
        *old(mode) is Data,
        r@.len() > 0,
        r@.len() + more <= usize::MAX,
        room(*old(body), (r@.len() + more) as nat),
    ensures
        stepped(
            r@,
            *old(mode),
            *old(ph),
            add_body(acc, pend(*old(body))),
            *final(mode),
            *final(ph),
            add_body(acc, pend(*final(body))),
            res.0,
        ),
        !(res.0 matches Ok(None)),
        *final(ph) is Body,
        res.0 matches Ok(Some(k)) ==> room(*final(body), (r@.len() - k + more) as nat),
        room(*final(body), 0),
        step_cost(res.0, res.1@, r@.len()),
{
    let ghost ph0 = *ph;
    let ghost m0 = *mode;
    let ghost p0 = pend(*body);
    let ghost a0 = add_body(acc, p0);
    let n = match *mode {
        Mode::Data(n) => n,
        _ => 0,
    };
    let d: usize = if n < r.len() as u64 {
        n as usize
    } else {
        r.len()
    };
    let over: Option<u64> = match *ph {
        Phase::Body { cl_left: Some(c) } => if d as u64 > c {
            Some(c)
        } else {
            None
        },
        _ => None,
    };
    // The bytes passed on: those the content-length still allows when the payload's exceed it.
    let c: usize = match over {
        Some(c) => c as usize,
        None => d,
    };
    let ghost mut work: nat = 1;
    if c > 0 {
        let mut cur: Option<CapVec<u8>> = None;
        core::mem::swap(&mut cur, body);
        let mut b = match cur {
            Some(b) => b,
            None => {
                proof {
                    work = work + 1;
                }
                CapVec::new(r.len() + more)
            },
        };
        let Ghost(wp) = b.push_slice(slice_subrange(r, 0, c));
        proof {
            work = work + wp;
        }
        *body = Some(b);
    }
    proof {
        assert(pend(*body) =~= p0 + r@.take(c as int));
        lemma_add_body_assoc(acc, p0, r@.take(c as int));
    }
    if over.is_some() {
        proof {
            assert forall|t: Seq<u8>, f: bool| #[trigger]
                rest(m0, ph0, a0, r@ + t, f) == (add_body(acc, pend(*body)), Some(ReqError::Stream(H3_MESSAGE_ERROR))) by {
                lemma_data_over(r@, n, ph0, a0, t, f);
            }
        }
        return (Err(ReqError::Stream(H3_MESSAGE_ERROR)), Ghost(work));
    }
    if let Phase::Body { cl_left: Some(c) } = *ph {
        *ph = Phase::Body { cl_left: Some(c - d as u64) };
    }
    *mode = if n == d as u64 {
        Mode::Frames
    } else {
        Mode::Data(n - d as u64)
    };
    proof {
        let a1 = add_body(acc, pend(*body));
        assert(*ph == sub_cl(ph0, d as u64));
        assert forall|t: Seq<u8>, f: bool| #[trigger]
            rest(m0, ph0, a0, r@ + t, f) == rest(*mode, *ph, a1, r@.skip(d as int) + t, f) by {
            lemma_data_discard(r@, n, ph0, a0, d as nat, t, f);
            if n == d as u64 {
                lemma_data_zero(r@.skip(d as int) + t, *ph, a1, f);
            }
        }
    }
    (Ok(Some(d)), Ghost(work))
}

/// The frame at the front of `r`, dispatched on its type before any payload is touched: an
/// error from the header alone, a DATA or unknown header (its payload follows in a `Mode`), a
/// complete HEADERS frame (the pending content returned first), or `Ok(None)` for a partial header or partial HEADERS
/// frame. The header is parsed from `r`'s first 16 bytes at most (N5). `lo`: `r`'s first `lo` bytes are a buffer
/// `buf_shape` allows, so a step that consumes ends after them.
fn step_frame(
    r: &[u8],
    ph: &mut Phase,
    mode: &mut Mode,
    events: &mut CapVec<ReqEvent>,
    body: &mut Option<CapVec<u8>>,
    Ghost(acc): Ghost<Seq<SpecReqEvent>>,
    Ghost(base): Ghost<nat>,
    Ghost(lo): Ghost<int>,
) -> (res: (Result<Option<usize>, ReqError>, Ghost<nat>))
    requires
        *old(mode) is Frames,
        r@.len() > 0,
        old(events).wf(),
        ev_ok(old(events)@.len(), base, old(events).cap(), *old(ph), *old(body)),
        room(*old(body), 0),
        0 <= lo <= r@.len(),
        buf_shape(r@.take(lo)),
    ensures
        final(events).wf(),
        final(events).cap() == old(events).cap(),
        final(events)@.len() >= old(events)@.len(),
        final(events)@.take(old(events)@.len() as int) == old(events)@,
        stepped(
            r@,
            *old(mode),
            *old(ph),
            add_body(acc, pend(*old(body))),
            *final(mode),
            *final(ph),
            add_body(push_all(acc, views(final(events)@.skip(old(events)@.len() as int))), pend(*final(body))),
            res.0,
        ),
        bodies_from(final(events)@, old(events)@.len() as int),
        *final(body) == *old(body) || *final(body) is None,
        res.0 is Ok ==> ev_ok(final(events)@.len(), base, final(events).cap(), *final(ph), *final(body)),
        res.0 is Err ==> final(events)@.len() <= base + 3,
        res.0 matches Ok(Some(k)) ==> lo < k,
        step_cost(res.0, res.1@, r@.len()),
{
    hide(rfc_headers);
    hide(push_all);
    hide(rfc_frame_header);
    let ghost ph0 = *ph;
    let ghost ev0 = events@;
    let ghost p0 = pend(*body);
    let ghost a0 = add_body(acc, p0);
    proof {
        lemma_no_event(ev0, acc);
    }
    let m = if r.len() < 16 {
        r.len()
    } else {
        16
    };
    let hp = slice_subrange(r, 0, m);
    proof {
        assert(hp@ =~= r@.take(m as int));
        lemma_header_take(r@, m as int);
    }
    // The header parse reads at most 16 bytes: a constant charge on the MIR bound (expected-cost.txt:2).
    let (ty, len, hdr_len) = match parse_frame_header(hp) {
        FrameHeader::Incomplete => {
            proof {
                assert forall|f: bool| #[trigger]
                    rest(*mode, *ph, a0, r@, f) == finish(*mode, *ph, a0, r@.len(), f) by {}
            }
            return (Ok(None), Ghost(17));
        },
        FrameHeader::Complete { ty, len, hdr_len } => (ty, len, hdr_len),
    };
    proof {
        lemma_frame_header_bounds(r@);
        lemma_header_lo(r@, lo);
    }
    if let Some(e) = req_header_error(ph, ty, len) {
        proof {
            assert forall|t: Seq<u8>, f: bool| #[trigger]
                rest(*mode, ph0, a0, r@ + t, f) == (a0, Some(e)) by {
                lemma_frame_at(r@, ph0, a0, hdr_len as nat, ty, len, t, f);
            }
        }
        return (Err(e), Ghost(18));
    }
    if ty == FRAME_HEADERS {
        let avail = r.len() - hdr_len;
        if len > avail as u64 {
            proof {
                assert forall|f: bool| #[trigger]
                    rest(*mode, *ph, a0, r@, f) == finish(*mode, *ph, a0, r@.len(), f) by {
                    assert(r@.skip(hdr_len as int).len() < len);
                }
            }
            return (Ok(None), Ghost(18));
        }
        let end = hdr_len + len as usize;
        let payload = slice_subrange(r, hdr_len, end);
        let Ghost(wf) = flush(events, body);
        let ghost ev1 = events@;
        proof {
            lemma_concat_merge(acc, ev0, ev1, ev0.len() as int, p0);
            lemma_headers_rest(r@, ph0, a0, hdr_len as nat, len, rfc_headers(ph0, payload@));
        }
        let (hr, Ghost(wh)) = headers_frame(payload, ph, events);
        proof {
            if hr is Ok {
                lemma_flush_push(acc, ev0, ev1, events@, p0);
            }
        }
        return match hr {
            Err(e) => (Err(e), Ghost(wf + wh + 18)),
            Ok(()) => (Ok(Some(end)), Ghost(wf + wh + 18)),
        };
    }
    let ghost m0 = *mode;
    *mode = if len == 0 {
        Mode::Frames
    } else if ty == FRAME_DATA {
        Mode::Data(len)
    } else {
        Mode::Unknown(len)
    };
    proof {
        assert forall|t: Seq<u8>, f: bool| #[trigger]
            rest(m0, ph0, a0, r@ + t, f) == rest(*mode, *ph, a0, r@.skip(hdr_len as int) + t, f) by {
            lemma_frame_at(r@, ph0, a0, hdr_len as nat, ty, len, t, f);
            if len == 0 {
                if ty == FRAME_DATA {
                    lemma_data_zero(r@.skip(hdr_len as int) + t, *ph, a0, f);
                } else {
                    lemma_skip_zero(r@.skip(hdr_len as int) + t, *ph, a0, f);
                }
            }
        }
    }
    (Ok(Some(hdr_len)), Ghost(18))
}

/// Consumes `s` from `(mode, ph)`: payload bytes are skipped or passed on straight from `s` into the call's one
/// pending `body`, complete frames are processed, and it stops at a partial frame header or a partial HEADERS frame,
/// returning where. `more`: the bytes of this call after `s`. `lo`: `s`'s first `lo` bytes are the buffer the call
/// began with, never content.
fn run(
    s: &[u8],
    ph: &mut Phase,
    mode: &mut Mode,
    events: &mut CapVec<ReqEvent>,
    body: &mut Option<CapVec<u8>>,
    more: usize,
    Ghost(acc0): Ghost<Seq<SpecReqEvent>>,
    Ghost(base): Ghost<nat>,
    Ghost(lo): Ghost<int>,
) -> (r: (Result<usize, ReqError>, Ghost<nat>))
    requires
        mode_ok(*old(mode), *old(ph)),
        old(events).wf(),
        ev_ok(old(events)@.len(), base, old(events).cap(), *old(ph), *old(body)),
        0 <= lo <= s@.len(),
        buf_shape(s@.take(lo)),
        lo > 0 ==> *old(mode) is Frames,
        s@.len() - lo + more <= usize::MAX,
        room(*old(body), (s@.len() - lo + more) as nat),
    ensures
        final(events).wf(),
        final(events).cap() == old(events).cap(),
        final(events)@.len() >= old(events)@.len(),
        final(events)@.take(old(events)@.len() as int) == old(events)@,
        ran(
            s@,
            *old(mode),
            *old(ph),
            add_body(acc0, pend(*old(body))),
            *final(mode),
            *final(ph),
            add_body(push_all(acc0, views(final(events)@.skip(old(events)@.len() as int))), pend(*final(body))),
            r.0,
        ),
        bodies_from(final(events)@, old(events)@.len() as int),
        room(*final(body), 0),
        match r.0 {
            Ok(n) => {
                &&& ev_ok(final(events)@.len(), base, final(events).cap(), *final(ph), *final(body))
                &&& room(*final(body), more as nat)
                &&& r.1@ <= c_run() * (n + 1)
            },
            Err(_) => {
                &&& final(events)@.len() <= base + 3
                &&& r.1@ <= c_run() * (s@.len() + 1)
            },
        },
{
    let ghost m0 = *mode;
    let ghost ph0 = *ph;
    let ghost ev0 = events@;
    let ghost p0 = pend(*body);
    let ghost mut acc = acc0;
    let ghost mut work: nat = 0;
    let mut pos: usize = 0;
    proof {
        assert(s@.skip(0) =~= s@);
        lemma_no_event(ev0, acc0);
    }
    while pos < s.len()
        invariant
            ev0 == old(events)@,
            m0 == *old(mode),
            ph0 == *old(ph),
            p0 == pend(*old(body)),
            pos <= s@.len(),
            mode_ok(*mode, *ph),
            events.wf(),
            events.cap() == old(events).cap(),
            events@.len() >= ev0.len(),
            events@.take(ev0.len() as int) == ev0,
            acc == push_all(acc0, views(events@.skip(ev0.len() as int))),
            bodies_from(events@, ev0.len() as int),
            ev_ok(events@.len(), base, events.cap(), *ph, *body),
            0 <= lo <= s@.len(),
            buf_shape(s@.take(lo)),
            pos < lo ==> pos == 0 && *mode is Frames,
            s@.len() - lo + more <= usize::MAX,
            room(*body, (s@.len() - (if pos < lo { lo } else { pos as int }) + more) as nat),
            work <= c_run() * pos,
            forall|t: Seq<u8>, f: bool| #[trigger]
                rest(m0, ph0, add_body(acc0, p0), s@ + t, f) == rest(
                    *mode,
                    *ph,
                    add_body(acc, pend(*body)),
                    s@.skip(pos as int) + t,
                    f,
                ),
        decreases s@.len() - pos,
    {
        let r = slice_subrange(s, pos, s.len());
        let ghost m1 = *mode;
        let ghost ph1 = *ph;
        let ghost acc1 = acc;
        let ghost ev1 = events@;
        let ghost b1 = *body;
        proof {
            assert(r@ =~= s@.skip(pos as int));
        }
        let (res, Ghost(w)) = match *mode {
            Mode::Frames => {
                let ghost l: int = if pos < lo {
                    lo
                } else {
                    0
                };
                proof {
                    if pos < lo {
                        assert(r@ =~= s@);
                    } else {
                        assert(r@.take(0) =~= Seq::<u8>::empty());
                    }
                }
                step_frame(r, ph, mode, events, body, Ghost(acc), Ghost(base), Ghost(l))
            },
            Mode::Unknown(_) => step_skip(r, Ghost(*ph), mode, Ghost(add_body(acc, pend(*body)))),
            Mode::Data(_) => step_data(r, ph, mode, body, more, Ghost(acc)),
        };
        proof {
            if !(m1 is Frames) {
                lemma_no_event(ev1, acc1);
                assert(events@ == ev1);
            }
            lemma_views_split(ev1, events@, ev0.len() as int);
            lemma_bodies_trans(ev0.len() as int, ev1, events@);
            lemma_push_all_append(
                acc0,
                views(ev1.skip(ev0.len() as int)),
                views(events@.skip(ev1.len() as int)),
            );
            acc = push_all(acc1, views(events@.skip(ev1.len() as int)));
            work = work + w + 1;
        }
        match res {
            Err(e) => {
                return (Err(e), Ghost(work));
            },
            Ok(None) => {
                return (Ok(pos), Ghost(work));
            },
            Ok(Some(k)) => {
                proof {
                    assert(r@.skip(k as int) =~= s@.skip(pos + k));
                    assert forall|t: Seq<u8>, f: bool| #[trigger]
                        rest(m0, ph0, add_body(acc0, p0), s@ + t, f) == rest(
                            *mode,
                            *ph,
                            add_body(acc, pend(*body)),
                            s@.skip(pos + k) + t,
                            f,
                        ) by {
                        assert(rest(m1, ph1, add_body(acc1, pend(b1)), r@ + t, f) == rest(
                            *mode,
                            *ph,
                            add_body(acc, pend(*body)),
                            r@.skip(k as int) + t,
                            f,
                        ));
                    }
                }
                pos = pos + k;
            },
        }
    }
    proof {
        assert(s@.skip(pos as int) =~= Seq::<u8>::empty());
        lemma_settled_empty(*mode, *ph, add_body(acc, pend(*body)));
    }
    (Ok(pos), Ghost(work))
}

/// One client request stream.
pub struct RequestStream {
    phase: Phase,
    mode: Mode,
    /// Received bytes not yet consumed: part of a frame header, or one HEADERS frame whose
    /// payload is incomplete. Under REQ_BUF_CAP (proven).
    buf: ByteQueue,
    done: bool,
    all: Ghost<Seq<u8>>,
    emitted: Ghost<Seq<SpecReqEvent>>,
}

/// A live stream with `acc` its events (content concatenated, pending content included): invariant, settled, bounded,
/// and with `buf` empty while a payload is pending.
spec fn ready(s: RequestStream, acc: Seq<SpecReqEvent>) -> bool {
    &&& s.buf.wf()
    &&& mode_ok(s.mode, s.phase)
    &&& split_ok(s.all@, acc, s.mode, s.phase, s.buf@)
    &&& settled(s.mode, s.phase, acc, s.buf@)
    &&& !(s.mode is Frames) ==> s.buf@.len() == 0
    &&& buf_shape(s.buf@)
    &&& s.buf@.len() < REQ_BUF_CAP
}

/// The events `s` has returned, content concatenated, then the content `p` it holds for this call.
spec fn acc_of(s: RequestStream, p: Seq<u8>) -> Seq<SpecReqEvent> {
    add_body(concat_bodies(s.emitted@), p)
}

/// What a ready stream's call reports when its bytes end here: only a FIN could still change it.
proof fn lemma_ready_end(s: RequestStream, acc: Seq<SpecReqEvent>, fin: bool)
    requires
        ready(s, acc),
    ensures
        rfc_request_stream(s.all@, fin) == finish(s.mode, s.phase, acc, s.buf@.len(), fin),
        s.buf@.len() < REQ_BUF_CAP,
        s.buf.wf(),
        !(s.mode is Frames) ==> s.buf@.len() == 0,
{
    assert(s.all@ + Seq::<u8>::empty() =~= s.all@);
    assert(s.buf@ + Seq::<u8>::empty() =~= s.buf@);
    assert(rfc_request_stream(s.all@ + Seq::empty(), fin) == rest(s.mode, s.phase, acc, s.buf@ + Seq::empty(), fin));
    assert(rest(s.mode, s.phase, acc, s.buf@, fin) == finish(s.mode, s.phase, acc, s.buf@.len(), fin));
}

/// `e1` extends `e0`, and `s1` records exactly the added events.
spec fn grew(s0: RequestStream, s1: RequestStream, e0: Seq<ReqEvent>, e1: Seq<ReqEvent>) -> bool {
    &&& e1.len() >= e0.len()
    &&& e1.take(e0.len() as int) == e0
    &&& s1.emitted@ == s0.emitted@ + views(e1.skip(e0.len() as int))
}

proof fn lemma_views_split(s1: Seq<ReqEvent>, s2: Seq<ReqEvent>, a: int)
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

proof fn lemma_grew_trans(
    s0: RequestStream,
    s1: RequestStream,
    s2: RequestStream,
    e0: Seq<ReqEvent>,
    e1: Seq<ReqEvent>,
    e2: Seq<ReqEvent>,
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

impl RequestStream {
    /// Every byte received on this stream.
    pub closed spec fn all(&self) -> Seq<u8> {
        self.all@
    }

    /// Every event this stream has returned, body chunks as returned.
    pub closed spec fn emitted(&self) -> Seq<SpecReqEvent> {
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
        &&& !self.done ==> ready(*self, concat_bodies(self.emitted@))
    }

    pub fn new() -> (r: Self)
        ensures
            r.wf(),
            r.all() == Seq::<u8>::empty(),
            r.emitted() == Seq::<SpecReqEvent>::empty(),
            !r.done(),
    {
        let r = RequestStream {
            phase: Phase::AwaitHeaders,
            mode: Mode::Frames,
            buf: ByteQueue::new(),
            done: false,
            all: Ghost(Seq::empty()),
            emitted: Ghost(Seq::empty()),
        };
        proof {
            assert(concat_bodies(Seq::empty()) == Seq::<SpecReqEvent>::empty());
            assert forall|t: Seq<u8>, f: bool| #[trigger]
                rfc_request_stream(r.all@ + t, f) == rest(
                    r.mode,
                    r.phase,
                    concat_bodies(r.emitted@),
                    r.buf@ + t,
                    f,
                ) by {
                assert(r.all@ + t =~= t);
                assert(r.buf@ + t =~= t);
            }
            lemma_settled_empty(r.mode, r.phase, Seq::empty());
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

    /// Feeds the next `data` (`fin`: the stream ends after it). Afterwards the cumulative events,
    /// with body chunks concatenated, and the error are exactly `rfc_request_stream` of every
    /// byte received, so they don't depend on how the bytes were chunked. A call returns at most
    /// MAX_REQ_EVENTS events, its content in one Body, and costs at most `c_req()` per byte given plus `c_frame()` per
    /// byte held before it (the frame it may complete from them).
    pub fn on_data(&mut self, data: &[u8], fin: bool, events: &mut CapVec<ReqEvent>) -> (r: (
        Result<(), ReqError>,
        Ghost<nat>,
    ))
        requires
            old(self).wf(),
            !old(self).done(),
            old(events).wf(),
            old(events)@.len() + MAX_REQ_EVENTS <= old(events).cap(),
        ensures
            final(self).wf(),
            final(self).all() == old(self).all() + data@,
            final(self).done() == (r.0 is Err || fin),
            !final(self).done() ==> final(self).buffered() < REQ_BUF_CAP,
            final(events).wf(),
            final(events).cap() == old(events).cap(),
            final(events)@.len() >= old(events)@.len(),
            final(events)@.len() <= old(events)@.len() + MAX_REQ_EVENTS,
            final(events)@.take(old(events)@.len() as int) == old(events)@,
            final(self).emitted() == old(self).emitted() + views(
                final(events)@.skip(old(events)@.len() as int),
            ),
            bodies_from(final(events)@, old(events)@.len() as int),
            rfc_request_stream(final(self).all(), fin) == (
                concat_bodies(final(self).emitted()),
                err_of(r.0),
            ),
            r.1@ <= c_req() * (data@.len() + 16) + c_frame() * old(self).buffered(),
    {
        hide(rfc_req);
        hide(rfc_skip);
        hide(rfc_data);
        hide(rfc_headers);
        hide(ready);
        hide(push_all);
        let ghost all0 = self.all@;
        let ghost ev0 = events@;
        let ghost base = ev0.len();
        let ghost b0 = self.buf@.len();
        let mut body: Option<CapVec<u8>> = None;
        let ghost mut work: nat = 0;
        let mut j: usize = 0;
        proof {
            assert(events@.take(ev0.len() as int) =~= ev0);
            assert(events@.skip(ev0.len() as int) =~= Seq::<ReqEvent>::empty());
            assert(views(Seq::<ReqEvent>::empty()) =~= Seq::<SpecReqEvent>::empty());
            assert(self.emitted@ + Seq::<SpecReqEvent>::empty() =~= self.emitted@);
            assert(all0 + data@.take(0) =~= all0);
        }
        while j < data.len()
            invariant
                j <= data@.len(),
                !self.done,
                ready(*self, acc_of(*self, pend(body))),
                all0 == old(self).all@,
                ev0 == old(events)@,
                base == ev0.len(),
                b0 == old(self).buf@.len(),
                self.all@ == all0 + data@.take(j as int),
                grew(*old(self), *self, ev0, events@),
                bodies_from(events@, ev0.len() as int),
                events.wf(),
                events.cap() == old(events).cap(),
                ev_ok(events@.len(), base, events.cap(), self.phase, body),
                room(body, (data@.len() - j) as nat),
                work + c_run() * self.buf@.len() <= c_run() * b0 + c_it() * j + j,
            decreases data@.len() - j,
        {
            let ghost s1 = *self;
            let ghost e1 = events@;
            let (res, Ghost(w)) = self.advance(data, j, events, &mut body, Ghost(base));
            proof {
                lemma_bodies_trans(ev0.len() as int, e1, events@);
                lemma_grew_trans(*old(self), s1, *self, ev0, e1, events@);
            }
            match res {
                Err(e) => {
                    proof {
                        assert(all0 + data@.take(j as int) + data@.skip(j as int) =~= all0 + data@);
                    }
                    let ghost s2 = *self;
                    let ghost e2 = events@;
                    let Ghost(wb) = self.emit_body(events, &mut body);
                    proof {
                        lemma_grew_trans(*old(self), s2, *self, ev0, e2, events@);
                        lemma_bodies_trans(ev0.len() as int, e2, events@);
                    }
                    self.done = true;
                    return (Err(e), Ghost(work + w + wb + 1));
                },
                Ok(j2) => {
                    proof {
                        assert(all0 + data@.take(j as int) + data@.subrange(j as int, j2 as int)
                            =~= all0 + data@.take(j2 as int));
                        work = work + w + 1;
                    }
                    j = j2;
                },
            }
        }
        let ghost e2 = events@;
        let ghost s2 = *self;
        let Ghost(wb) = self.emit_body(events, &mut body);
        proof {
            lemma_grew_trans(*old(self), s2, *self, ev0, e2, events@);
            lemma_bodies_trans(ev0.len() as int, e2, events@);
            work = work + wb;
        }
        let ghost acc = concat_bodies(self.emitted@);
        proof {
            assert(data@.take(j as int) =~= data@);
            lemma_ready_end(*self, acc, fin);
        }
        if !fin {
            return (Ok(()), Ghost(work));
        }
        self.done = true;
        let frames = match self.mode {
            Mode::Frames => true,
            _ => false,
        };
        if !frames || self.buf.len() > 0 {
            return (Err(ReqError::Connection(H3_FRAME_ERROR)), Ghost(work + 1));
        }
        let cl = match self.phase {
            Phase::AwaitHeaders => return (Err(ReqError::Stream(H3_REQUEST_INCOMPLETE)), Ghost(work + 1)),
            Phase::Body { cl_left } => cl_left,
            Phase::Trailers { cl_left } => cl_left,
        };
        if let Some(left) = cl {
            if left != 0 {
                return (Err(ReqError::Stream(H3_MESSAGE_ERROR)), Ghost(work + 1));
            }
        }
        let ghost e3 = events@;
        events.push(ReqEvent::End);
        proof {
            lemma_views_push(e3, ev0.len() as int, ReqEvent::End);
            lemma_push_all_push(Seq::empty(), self.emitted@, SpecReqEvent::End);
            assert(old(self).emitted@ + views(e3.skip(ev0.len() as int)).push(SpecReqEvent::End)
                =~= self.emitted@.push(SpecReqEvent::End));
        }
        self.emitted = Ghost(self.emitted@.push(SpecReqEvent::End));
        (Ok(()), Ghost(work + 2))
    }

    /// Returns the pending content, if any, as one `Body` event, recorded in `emitted`.
    fn emit_body(&mut self, events: &mut CapVec<ReqEvent>, body: &mut Option<CapVec<u8>>) -> (r: Ghost<nat>)
        requires
            old(events).wf(),
            pend(*old(body)).len() > 0 ==> old(events)@.len() < old(events).cap(),
        ensures
            *final(body) is None,
            final(events).wf(),
            final(events).cap() == old(events).cap(),
            final(events)@.len() <= old(events)@.len() + 1,
            pend(*old(body)).len() == 0 ==> final(events)@.len() == old(events)@.len(),
            grew(*old(self), *final(self), old(events)@, final(events)@),
            bodies_from(final(events)@, old(events)@.len() as int),
            concat_bodies(final(self).emitted@) == acc_of(*old(self), pend(*old(body))),
            ready(*old(self), acc_of(*old(self), pend(*old(body)))) ==> ready(
                *final(self),
                concat_bodies(final(self).emitted@),
            ),
            final(self).all == old(self).all,
            final(self).buf == old(self).buf,
            final(self).phase == old(self).phase,
            final(self).mode == old(self).mode,
            final(self).done == old(self).done,
            r@ <= 1,
    {
        let ghost e0 = events@;
        let ghost p = pend(*body);
        let ghost a = concat_bodies(self.emitted@);
        let Ghost(w) = flush(events, body);
        let ghost v = views(events@.skip(e0.len() as int));
        proof {
            lemma_concat_merge(a, e0, events@, e0.len() as int, p);
            lemma_no_event(e0, a);
            lemma_push_all_append(Seq::empty(), self.emitted@, v);
        }
        self.emitted = Ghost(self.emitted@ + v);
        Ghost(w)
    }

    /// One step through `data[j..]`: with `buf` empty, runs straight over `data[j..]` and keeps
    /// its unconsumed tail; otherwise moves just enough of `data` into `buf` to complete its
    /// frame header or HEADERS frame, then runs over `buf` and drops what it consumed.
    fn advance(
        &mut self,
        data: &[u8],
        j: usize,
        events: &mut CapVec<ReqEvent>,
        body: &mut Option<CapVec<u8>>,
        Ghost(base): Ghost<nat>,
    ) -> (r: (Result<usize, ReqError>, Ghost<nat>))
        requires
            ready(*old(self), acc_of(*old(self), pend(*old(body)))),
            !old(self).done,
            j < data@.len(),
            old(events).wf(),
            ev_ok(old(events)@.len(), base, old(events).cap(), old(self).phase, *old(body)),
            room(*old(body), (data@.len() - j) as nat),
        ensures
            grew(*old(self), *final(self), old(events)@, final(events)@),
            bodies_from(final(events)@, old(events)@.len() as int),
            !final(self).done,
            final(self).buf.wf(),
            final(events).wf(),
            final(events).cap() == old(events).cap(),
            room(*final(body), 0),
            match r.0 {
                Ok(j2) => {
                    &&& j < j2 <= data@.len()
                    &&& final(self).all@ == old(self).all@ + data@.subrange(j as int, j2 as int)
                    &&& ready(*final(self), acc_of(*final(self), pend(*final(body))))
                    &&& ev_ok(final(events)@.len(), base, final(events).cap(), final(self).phase, *final(body))
                    &&& room(*final(body), (data@.len() - j2) as nat)
                    &&& r.1@ + c_run() * final(self).buf@.len() <= c_run() * old(self).buf@.len() + c_it() * (j2
                        - j)
                },
                Err(e) => {
                    &&& final(self).all@ == old(self).all@ + data@.skip(j as int)
                    &&& forall|f: bool| #[trigger]
                        rfc_request_stream(final(self).all@, f) == (
                            acc_of(*final(self), pend(*final(body))),
                            Some(e),
                        )
                    &&& base <= final(events)@.len() <= base + 3
                    &&& base + MAX_REQ_EVENTS <= final(events).cap()
                    &&& r.1@ <= c_run() * old(self).buf@.len() + c_it() * (data@.len() - j)
                },
            },
    {
        let ghost em1 = self.emitted@;
        let ghost ev1 = events@;
        let ghost acc = concat_bodies(em1);
        let ghost m1 = self.mode;
        let ghost ph1 = self.phase;
        let ghost a1 = add_body(acc, pend(*body));
        if self.buf.len() == 0 {
            let s = slice_subrange(data, j, data.len());
            let ghost all1 = self.all@;
            proof {
                lemma_split_append(all1, a1, m1, ph1, self.buf@, s@);
                assert(self.buf@ + s@ =~= s@);
                assert(s@ =~= data@.subrange(j as int, data@.len() as int));
                assert(s@.take(0) =~= Seq::<u8>::empty());
            }
            let (res, Ghost(wr)) = run(
                s,
                &mut self.phase,
                &mut self.mode,
                events,
                body,
                0,
                Ghost(acc),
                Ghost(base),
                Ghost(0),
            );
            let ghost v = views(events@.skip(ev1.len() as int));
            let ghost a2 = add_body(push_all(acc, v), pend(*body));
            self.emitted = Ghost(em1 + v);
            self.all = Ghost(all1 + s@);
            proof {
                lemma_push_all_append(Seq::empty(), em1, v);
                assert(acc_of(*self, pend(*body)) == a2);
            }
            match res {
                Err(e) => {
                    proof {
                        lemma_run_err(all1 + s@, a1, m1, ph1, s@, a2, e);
                        assert(self.all@ + Seq::<u8>::empty() =~= self.all@);
                        assert forall|f: bool| #[trigger] rfc_request_stream(self.all@, f) == (a2, Some(e)) by {
                            assert(rfc_request_stream(self.all@ + Seq::empty(), f) == (a2, Some(e)));
                        }
                    }
                    (Err(e), Ghost(wr + 1))
                },
                Ok(n) => {
                    let tail = slice_subrange(s, n, s.len());
                    proof {
                        assert(tail@ =~= s@.skip(n as int));
                        lemma_buf_bound(tail@);
                    }
                    let Ghost(wp) = self.buf.push_slice(tail);
                    proof {
                        assert(self.buf@ =~= s@.skip(n as int));
                        lemma_run_ok(all1 + s@, a1, m1, ph1, s@, self.mode, self.phase, a2, n);
                    }
                    (Ok(data.len()), Ghost(wr + wp + 1))
                },
            }
        } else {
            let ghost b0 = self.buf@;
            let ghost all0 = self.all@;
            let (k, Ghost(wt)) = self.top_up(data, j);
            let ghost all2 = self.all@;
            let ghost b = self.buf@;
            proof {
                lemma_split_append(all0, a1, m1, ph1, b0, data@.subrange(j as int, j + k));
                assert(b.take(b0.len() as int) =~= b0);
            }
            let more = data.len() - (j + k);
            let (res, Ghost(wr)) = run(
                self.buf.as_slice(),
                &mut self.phase,
                &mut self.mode,
                events,
                body,
                more,
                Ghost(acc),
                Ghost(base),
                Ghost(b0.len() as int),
            );
            let ghost v = views(events@.skip(ev1.len() as int));
            let ghost a2 = add_body(push_all(acc, v), pend(*body));
            self.emitted = Ghost(em1 + v);
            proof {
                lemma_push_all_append(Seq::empty(), em1, v);
                assert(acc_of(*self, pend(*body)) == a2);
            }
            match res {
                Err(e) => {
                    let ghost t = data@.skip(j + k);
                    self.all = Ghost(all2 + t);
                    proof {
                        lemma_run_err(all2, a1, m1, ph1, b, a2, e);
                        assert(all2 + t =~= old(self).all@ + data@.skip(j as int));
                        assert forall|f: bool| #[trigger] rfc_request_stream(all2 + t, f) == (a2, Some(e)) by {}
                    }
                    (Err(e), Ghost(wt + wr + 1))
                },
                Ok(n) => {
                    let Ghost(wd) = self.buf.drop_front(n);
                    proof {
                        lemma_run_ok(all2, a1, m1, ph1, b, self.mode, self.phase, a2, n);
                        lemma_buf_bound(self.buf@);
                    }
                    (Ok(j + k), Ghost(wt + wr + wd + 1))
                },
            }
        }
    }

    /// Appends `data[j..j + k]` to a non-empty `buf`, with `k` just enough to complete its frame
    /// header (at most 16 bytes in all) or its HEADERS frame (at most REQ_BUF_CAP bytes in all). The header is parsed
    /// from `buf`'s first 16 bytes at most (N5).
    fn top_up(&mut self, data: &[u8], j: usize) -> (r: (usize, Ghost<nat>))
        requires
            old(self).buf.wf(),
            buf_shape(old(self).buf@),
            old(self).buf@.len() > 0,
            j < data@.len(),
        ensures
            0 < r.0 <= data@.len() - j,
            final(self).buf.wf(),
            final(self).buf@ == old(self).buf@ + data@.subrange(j as int, j + r.0),
            final(self).all@ == old(self).all@ + data@.subrange(j as int, j + r.0),
            final(self).buf@.len() <= REQ_BUF_CAP,
            final(self).phase == old(self).phase,
            final(self).mode == old(self).mode,
            final(self).emitted@ == old(self).emitted@,
            final(self).done == old(self).done,
            r.1@ <= 7 * r.0 + 24,
    {
        proof {
            lemma_frame_header_bounds(self.buf@);
            lemma_buf_bound(self.buf@);
        }
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
            lemma_header_take(q@, m as int);
        }
        // The header parse reads at most 16 bytes: a constant charge on the MIR bound (expected-cost.txt:2).
        let need: usize = match parse_frame_header(hp) {
            FrameHeader::Incomplete => 16 - bl,
            FrameHeader::Complete { len, hdr_len, .. } => hdr_len + len as usize - bl,
        };
        let avail = data.len() - j;
        let k = if avail < need {
            avail
        } else {
            need
        };
        let piece = slice_subrange(data, j, j + k);
        let Ghost(wp) = self.buf.push_slice(piece);
        self.all = Ghost(self.all@ + piece@);
        (k, Ghost(wp + 17))
    }
}

} // verus!
