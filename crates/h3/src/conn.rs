//! The HTTP/3 server connection (RFC 9114): dispatch by stream ID to the verified stream machines
//! (`h3::request`, `h3::uni`), our control stream (one SETTINGS frame, then GOAWAYs), responses,
//! and the connection-error latch. Sans-IO: QUIC stream events in, `Output`s out.
//!
//! Contract with the QUIC layer: stream IDs follow RFC 9000 §2.1, and no data is delivered on a
//! stream after its FIN or the peer's reset. Data that was in flight when we sent STOP_SENDING
//! may still arrive; it is ignored until the stream's FIN or reset.
//!
//! Caller obligations (Phase 3c; stated here, not proven by this module):
//! - **Bounded streams.** The tracked streams grow with every peer stream, and nothing here caps
//!   them. The QUIC layer advertises bounded `initial_max_streams_bidi`/`_uni` and re-credits a
//!   stream (MAX_STREAMS) only once `H3Conn` has forgotten it (`!req_known` / `!uni_known`).
//! - **`start()` first.** Call `start` as soon as the transport can send, before delivering any
//!   stream event or calling `send_response`, so SETTINGS opens our control stream before any
//!   response is written (RFC 9114 §6.2.1, §7.2.4.2). Nothing else here calls it, except
//!   `shutdown`.
//! - **At least 3 peer uni streams.** Encode `initial_max_streams_uni >= MIN_PEER_UNI_STREAMS`
//!   (3) in our transport parameters (RFC 9114 §6.2); the constant alone enforces nothing.
//! - **Aborted requests.** A peer reset of a request whose response was already sent (or whose
//!   sending part the peer stopped), i.e. `send_open` is false, outputs nothing. The caller
//!   knows it delivered `on_stream_reset`, and tells the application that any `RequestBody`
//!   stream for that request has been aborted.
use vstd::prelude::*;
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;
use vstd::slice::slice_to_vec;
use wire::varint::VARINT_MAX;
#[allow(unused_imports)]
use wire::varint::*;

use crate::codes::*;
use crate::frame::*;
pub use crate::limits::*;
use crate::message::*;
use crate::qpack::field_section::*;
use crate::request::{ReqError, ReqEvent, RequestStream, SpecReqEvent, MAX_REQ_EVENTS};
use byteq::avl::{first, get_le, join, join2, pop_min, split, Tree};
// Its spec fns and lemmas, used only in ghost code, which a plain `cargo build` erases.
#[allow(unused_imports)]
use byteq::avl::*;
use byteq::capvec::CapVec;
use crate::uni::{SeenUni, SpecUniEvent, UniEvent, UniKind, UniStream};
// Used only in ghost code, which a plain `cargo build` erases.
#[allow(unused_imports)]
use crate::qpack::int::*;
#[allow(unused_imports)]
use crate::qpack::static_table::*;
#[allow(unused_imports)]
use crate::{request, uni};

verus! {

type Fields = Seq<(Seq<u8>, Seq<u8>)>;

/// What the connection asks of the QUIC layer and the application.
pub enum Output {
    StreamWrite { stream_id: u64, data: Vec<u8>, fin: bool },
    ResetStream { stream_id: u64, code: u64 },
    StopSending { stream_id: u64, code: u64 },
    CloseConnection { code: u64 },
    Request { stream_id: u64, head: Request },
    /// Request content as it arrives; never empty.
    RequestBody { stream_id: u64, data: Vec<u8> },
    RequestEnd { stream_id: u64, trailers: Vec<FieldLine> },
}

pub enum SpecOutput {
    StreamWrite { stream_id: u64, data: Seq<u8>, fin: bool },
    ResetStream { stream_id: u64, code: u64 },
    StopSending { stream_id: u64, code: u64 },
    CloseConnection { code: u64 },
    Request { stream_id: u64, head: SpecRequest },
    RequestBody { stream_id: u64, data: Seq<u8> },
    RequestEnd { stream_id: u64, trailers: Fields },
}

impl View for Output {
    type V = SpecOutput;

    open spec fn view(&self) -> SpecOutput {
        match self {
            Output::StreamWrite { stream_id, data, fin } => SpecOutput::StreamWrite {
                stream_id: *stream_id,
                data: data@,
                fin: *fin,
            },
            Output::ResetStream { stream_id, code } => SpecOutput::ResetStream {
                stream_id: *stream_id,
                code: *code,
            },
            Output::StopSending { stream_id, code } => SpecOutput::StopSending {
                stream_id: *stream_id,
                code: *code,
            },
            Output::CloseConnection { code } => SpecOutput::CloseConnection { code: *code },
            Output::Request { stream_id, head } => SpecOutput::Request {
                stream_id: *stream_id,
                head: head@,
            },
            Output::RequestBody { stream_id, data } => SpecOutput::RequestBody {
                stream_id: *stream_id,
                data: data@,
            },
            Output::RequestEnd { stream_id, trailers } => SpecOutput::RequestEnd {
                stream_id: *stream_id,
                trailers: fields_view(trailers@),
            },
        }
    }
}

pub open spec fn outs_view(s: Seq<Output>) -> Seq<SpecOutput> {
    s.map_values(|o: Output| o@)
}

/// `o1` is `o0` with outputs appended.
pub open spec fn extends(o0: Seq<Output>, o1: Seq<Output>) -> bool {
    o0.len() <= o1.len() && o1.take(o0.len() as int) == o0
}

/// The outputs appended to `o0`.
pub open spec fn added(o0: Seq<Output>, o1: Seq<Output>) -> Seq<SpecOutput> {
    outs_view(o1.skip(o0.len() as int))
}

// =============================================================================
// Specs: our control stream
// =============================================================================

pub open spec fn our_settings() -> Seq<(u64, u64)> {
    seq![(SETTINGS_MAX_FIELD_SECTION_SIZE, MAX_FIELD_SECTION_SIZE), (0x21u64, 0u64)]
}

//= https://www.rfc-editor.org/rfc/rfc9114#section-3.2
//# After the QUIC connection is
//# established, a SETTINGS frame MUST be sent by each endpoint as the
//# initial frame of their respective HTTP control stream.
//= https://www.rfc-editor.org/rfc/rfc9114#section-6.2.1
//# Each side MUST initiate a single control stream at the beginning of
//# the connection and send its SETTINGS frame as the first frame on this
//# stream.
/// The start of our control stream (server uni stream 3): its type, then our SETTINGS frame:
/// MAX_FIELD_SECTION_SIZE and one grease setting.
pub open spec fn ctrl_preamble() -> Seq<u8> {
    seq![0u8] + spec_frame_bytes(FRAME_SETTINGS, spec_pairs_bytes(our_settings()))
}

pub open spec fn goaway_frames(g: Seq<u64>) -> Seq<u8>
    decreases g.len(),
{
    if g.len() == 0 {
        Seq::empty()
    } else {
        goaway_frames(g.drop_last()) + spec_frame_bytes(FRAME_GOAWAY, spec_varint(g.last()))
    }
}

//= https://www.rfc-editor.org/rfc/rfc9114#section-5.2
//# An endpoint MAY send multiple GOAWAY frames indicating different
//# identifiers, but the identifier in each frame MUST NOT be greater
//# than the identifier in any previous frame, since clients might
//# already have retried unprocessed requests on another HTTP connection.
pub open spec fn nonincreasing(g: Seq<u64>) -> bool {
    forall|i: int, j: int| 0 <= i < j < g.len() ==> g[j] <= g[i]
}

/// The bytes the outputs write on stream `id`, in order.
pub open spec fn writes_on(o: Seq<SpecOutput>, id: u64) -> Seq<u8>
    decreases o.len(),
{
    if o.len() == 0 {
        Seq::empty()
    } else {
        writes_on(o.drop_last(), id) + match o.last() {
            SpecOutput::StreamWrite { stream_id, data, .. } => if stream_id == id {
                data
            } else {
                Seq::empty()
            },
            _ => Seq::empty(),
        }
    }
}

/// Our control stream as received: the type varint is 0x00, and its first frame is one SETTINGS
/// frame carrying exactly `our_settings()`.
pub proof fn theorem_ctrl_preamble()
    ensures
        rfc_varint_decode(ctrl_preamble()) == Some((1nat, STREAM_CONTROL)),
        ({
            let p = ctrl_preamble().skip(1);
            let h = spec_frame_header_bytes(
                FRAME_SETTINGS,
                spec_pairs_bytes(our_settings()).len() as u64,
            ).len();
            &&& rfc_frame_header(p) == Some(
                (h, FRAME_SETTINGS, spec_pairs_bytes(our_settings()).len() as u64),
            )
            &&& h + spec_pairs_bytes(our_settings()).len() == p.len()
            &&& rfc_frame_payload(FRAME_SETTINGS, p.skip(h as int)) == Ok::<SpecFrame, u64>(
                SpecFrame::Settings(our_settings()),
            )
        }),
{
    let pl = spec_pairs_bytes(our_settings());
    let body = spec_frame_bytes(FRAME_SETTINGS, pl);
    lemma_settings_bounds();
    lemma_decode_zero();
    lemma_decode_prefix(seq![0u8], body);
    assert(ctrl_preamble() =~= seq![0u8] + body);
    assert(ctrl_preamble().skip(1) =~= body);
    lemma_frame_bytes_roundtrip(FRAME_SETTINGS, pl, Seq::empty());
    assert(body + Seq::<u8>::empty() =~= body);
    let h = spec_frame_header_bytes(FRAME_SETTINGS, pl.len() as u64).len();
    assert(body.skip(h as int) =~= body.subrange(h as int, (h + pl.len()) as int));
    theorem_settings_roundtrip(our_settings());
}

proof fn lemma_settings_bounds()
    ensures
        rfc_settings_valid(our_settings()),
        forall|i: int|
            0 <= i < our_settings().len() ==> (#[trigger] our_settings()[i]).0 <= VARINT_MAX
                && our_settings()[i].1 <= VARINT_MAX,
        spec_pairs_bytes(our_settings()).len() <= VARINT_MAX,
{
    let s = our_settings();
    assert(s.skip(1).skip(1) =~= Seq::<(u64, u64)>::empty());
    reveal_with_fuel(spec_pairs_bytes, 3);
    lemma_varint_len(s[0].0);
    lemma_varint_len(s[0].1);
    lemma_varint_len(s[1].0);
    lemma_varint_len(s[1].1);
}

proof fn lemma_varint_len(v: u64)
    requires
        v <= VARINT_MAX,
    ensures
        spec_varint(v).len() <= 8,
{
    theorem_serialize_matches_rfc(v);
    lemma_frame_header_bounds(spec_varint(v) + spec_varint(0));
    theorem_header_roundtrip(v, 0);
}

// =============================================================================
// Specs: responses
// =============================================================================

/// ":status"
pub open spec fn lit_status() -> Seq<u8> {
    seq![58u8, 115u8, 116u8, 97u8, 116u8, 117u8, 115u8]
}

pub open spec fn status_digits(s: u16) -> Seq<u8> {
    seq![(48 + s / 100) as u8, (48 + (s / 10) % 10) as u8, (48 + s % 10) as u8]
}

//= https://www.rfc-editor.org/rfc/rfc9114#section-4.3.2
//# This pseudo-
//# header field MUST be included in all responses; otherwise, the
//# response is malformed (see Section 4.1.2).
/// The field section we encode for `r`: `:status` first, then `r.headers` (which
/// `valid_response` keeps free of pseudo-headers).
pub open spec fn resp_fields(r: SpecResponse) -> Fields {
    seq![(lit_status(), status_digits(r.status))] + r.headers
}

pub open spec fn body_frames(b: Seq<u8>) -> Seq<u8> {
    if b.len() == 0 {
        Seq::empty()
    } else {
        spec_frame_bytes(FRAME_DATA, b)
    }
}

/// `data` carries `r`: a HEADERS frame whose payload decodes back to `resp_fields(r)`, then the
/// body as one DATA frame (none if empty).
pub open spec fn response_wire(data: Seq<u8>, r: SpecResponse) -> bool {
    match rfc_frame_header(data) {
        Some((h, ty, len)) => {
            &&& ty == FRAME_HEADERS
            &&& h + len <= data.len()
            &&& rfc_decode_field_section(data.subrange(h as int, h + len)) == Ok::<Fields, u64>(
                resp_fields(r),
            )
            &&& data.skip(h + len) == body_frames(r.body)
        },
        None => false,
    }
}

/// Σ(name + value + 32) over the lines (RFC 9114 §4.2.2).
pub open spec fn fields_size(f: Fields) -> int
    decreases f.len(),
{
    if f.len() == 0 {
        0
    } else {
        fields_size(f.drop_last()) + field_line_size(f.last())
    }
}

//= https://www.rfc-editor.org/rfc/rfc9114#section-4.2.2
//# An implementation that
//# has received this parameter SHOULD NOT send an HTTP message header
//# that exceeds the indicated size, as the peer will likely refuse to
//# process it.
pub open spec fn fits_peer(peer: Option<u64>, n: int) -> bool {
    match peer {
        None => true,
        Some(l) => n <= l,
    }
}

/// One `StreamWrite` of `r` on `id`, with FIN.
pub open spec fn one_response(o: Seq<SpecOutput>, id: u64, r: SpecResponse) -> bool {
    o.len() == 1 && match o[0] {
        SpecOutput::StreamWrite { stream_id, data, fin } => stream_id == id && fin && response_wire(
            data,
            r,
        ),
        _ => false,
    }
}

pub open spec fn empty_response(status: u16) -> SpecResponse {
    SpecResponse { status, headers: Seq::empty(), body: Seq::empty() }
}

// =============================================================================
// Specs: request-stream delegation
// =============================================================================

/// What a request-stream call's outputs depend on besides the events: the FIN flag, the peer's
/// SETTINGS_MAX_FIELD_SECTION_SIZE, and whether our sending part is still open.
pub struct Ctx {
    pub fin: bool,
    pub peer: Option<u64>,
    pub send_open: bool,
}

/// STOP_SENDING with `code`, unless the peer's sending part has ended.
pub open spec fn stop_outs(id: u64, code: u64, fin: bool) -> Seq<SpecOutput> {
    if fin {
        Seq::empty()
    } else {
        seq![SpecOutput::StopSending { stream_id: id, code }]
    }
}

//= https://www.rfc-editor.org/rfc/rfc9114#section-4.1.2
//# Malformed requests or responses that are
//# detected MUST be treated as a stream error of type H3_MESSAGE_ERROR.
//= https://www.rfc-editor.org/rfc/rfc9114#section-4.1.1
//# Implementations SHOULD cancel requests by abruptly terminating any
//# directions of a stream that are still open.
/// The outputs for the request machine's error: a connection error closes the connection; a
/// stream error resets our sending part (if still open) and aborts reading (unless the peer's
/// sending part has ended), with that code.
pub open spec fn err_outs(id: u64, e: Option<ReqError>, cx: Ctx) -> Seq<SpecOutput> {
    match e {
        None => Seq::empty(),
        Some(ReqError::Connection(c)) => seq![SpecOutput::CloseConnection { code: c }],
        Some(ReqError::Stream(c)) => (if cx.send_open {
            seq![SpecOutput::ResetStream { stream_id: id, code: c }]
        } else {
            Seq::empty()
        }) + stop_outs(id, c, cx.fin),
    }
}

//= https://www.rfc-editor.org/rfc/rfc9114#section-4.1
//# When the server does
//# not need to receive the remainder of the request, it MAY abort
//# reading the request stream, send a complete response, and cleanly
//# close the sending part of the stream.  The error code H3_NO_ERROR
//# SHOULD be used when requesting that the client stop sending on the
//# request stream.
/// A request the connection answers itself with `status` (no headers, no body), never passed to
/// the application: the response with FIN, then STOP_SENDING(H3_NO_ERROR) unless the request has
/// ended. If the peer's field-section limit doesn't admit it, the request is rejected instead;
/// if our sending part is already closed (peer STOP_SENDING), only reading is aborted.
pub open spec fn answered_outs(id: u64, status: u16, cx: Ctx, o: Seq<SpecOutput>) -> bool {
    let stop = stop_outs(id, H3_NO_ERROR, cx.fin);
    if !cx.send_open {
        o == stop
    } else if fits_peer(cx.peer, fields_size(resp_fields(empty_response(status)))) {
        o.len() == 1 + stop.len() && one_response(o.take(1), id, empty_response(status)) && o.skip(1)
            == stop
    } else {
        o == rejected_outs(id, cx.fin)
    }
}

//= https://www.rfc-editor.org/rfc/rfc9114#section-4.1.1
//# When the server cancels a request without performing any application
//# processing, the request is considered "rejected".  The server SHOULD
//# abort its response stream with the error code H3_REQUEST_REJECTED.
//= https://www.rfc-editor.org/rfc/rfc9114#section-4.1.1
//# Servers MUST NOT use the H3_REQUEST_REJECTED error code for requests
//# that were partially or fully processed.
/// A request rejected without any of it reaching the application (the only uses: a new stream
/// at or above our GOAWAY ID, and a 501/421 the peer's limit doesn't admit).
pub open spec fn rejected_outs(id: u64, fin: bool) -> Seq<SpecOutput> {
    seq![SpecOutput::ResetStream { stream_id: id, code: H3_REQUEST_REJECTED }] + stop_outs(
        id,
        H3_REQUEST_REJECTED,
        fin,
    )
}

/// The head of a request the connection answers itself.
pub open spec fn internal_head(e: SpecReqEvent) -> bool {
    match e {
        SpecReqEvent::Head(SpecRequestHead::Connect { .. }) => true,
        SpecReqEvent::Head(SpecRequestHead::Request(r)) => !http_scheme(r.scheme),
        _ => false,
    }
}

pub open spec fn no_internal(s: Seq<SpecReqEvent>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> !internal_head(#[trigger] s[i])
}

pub open spec fn has_request(o: Seq<SpecOutput>) -> bool {
    exists|i: int| 0 <= i < o.len() && (#[trigger] o[i]) is Request
}

/// "HEAD"
pub open spec fn lit_head_method() -> Seq<u8> {
    seq![72u8, 69u8, 65u8, 68u8]
}

pub open spec fn is_head_request(o: SpecOutput) -> bool {
    match o {
        SpecOutput::Request { head, .. } => head.method == lit_head_method(),
        _ => false,
    }
}

/// `o` delivers a request whose method is HEAD.
pub open spec fn head_req(o: Seq<SpecOutput>) -> bool {
    exists|i: int| 0 <= i < o.len() && is_head_request(#[trigger] o[i])
}

/// `o` is what the connection outputs for new request-machine events `evs` on stream `id`,
/// given the trailer section `tr` held from earlier calls, the machine's error `err` and the
/// call's context `cx`. A CONNECT is answered 501 (RFC 9110 §9.1: an unimplemented method) and a
/// scheme other than http/https 421 (RFC 9110 §15.5.20: Misdirected Request); either ends the
/// stream's processing, so later events and the error are not output. Trailers are held until
/// the end.
pub open spec fn req_outs(
    id: u64,
    evs: Seq<SpecReqEvent>,
    tr: Fields,
    err: Option<ReqError>,
    cx: Ctx,
    o: Seq<SpecOutput>,
) -> bool
    decreases evs.len(),
{
    if evs.len() == 0 {
        o == err_outs(id, err, cx)
    } else {
        match evs[0] {
            SpecReqEvent::Head(SpecRequestHead::Connect { .. }) => answered_outs(id, 501, cx, o),
            SpecReqEvent::Head(SpecRequestHead::Request(r)) => if !http_scheme(r.scheme) {
                answered_outs(id, 421, cx, o)
            } else {
                o.len() > 0 && o[0] == SpecOutput::Request { stream_id: id, head: r } && req_outs(
                    id,
                    evs.skip(1),
                    tr,
                    err,
                    cx,
                    o.skip(1),
                )
            },
            SpecReqEvent::BodyBytes(d) => o.len() > 0 && o[0] == SpecOutput::RequestBody {
                stream_id: id,
                data: d,
            } && req_outs(id, evs.skip(1), tr, err, cx, o.skip(1)),
            SpecReqEvent::Trailers(t) => req_outs(id, evs.skip(1), t, err, cx, o),
            SpecReqEvent::End => o.len() > 0 && o[0] == SpecOutput::RequestEnd {
                stream_id: id,
                trailers: tr,
            } && req_outs(id, evs.skip(1), Seq::empty(), err, cx, o.skip(1)),
        }
    }
}

pub open spec fn uni_err_outs(e: Option<u64>) -> Seq<SpecOutput> {
    match e {
        None => Seq::empty(),
        Some(c) => seq![SpecOutput::CloseConnection { code: c }],
    }
}

// =============================================================================
// Specs: what every call guarantees
// =============================================================================

/// STOP_SENDING and RESET_STREAM only on request streams.
pub open spec fn stop_ok(o: SpecOutput) -> bool {
    match o {
        SpecOutput::StopSending { stream_id, .. } => stream_id % 4 == 0,
        SpecOutput::ResetStream { stream_id, .. } => stream_id % 4 == 0,
        _ => true,
    }
}

pub open spec fn ctrl_free(o: SpecOutput) -> bool {
    match o {
        SpecOutput::StreamWrite { stream_id, .. } => stream_id != 3,
        _ => true,
    }
}

pub open spec fn ctrl_open(o: SpecOutput) -> bool {
    match o {
        SpecOutput::StreamWrite { stream_id, fin, .. } => stream_id == 3 ==> !fin,
        _ => true,
    }
}

pub open spec fn body_ok(o: SpecOutput) -> bool {
    match o {
        SpecOutput::RequestBody { data, .. } => data.len() > 0,
        _ => true,
    }
}

pub open spec fn no_close(o: Seq<SpecOutput>) -> bool {
    forall|i: int| 0 <= i < o.len() ==> !((#[trigger] o[i]) is CloseConnection)
}

//= https://www.rfc-editor.org/rfc/rfc9114#section-6.2.1
//# The
//# sender MUST NOT close the control stream, and the receiver MUST NOT
//# request that the sender close the control stream.
//= https://www.rfc-editor.org/rfc/rfc9204#section-4.2
//# The sender MUST NOT close either of these streams, and the receiver
//# MUST NOT request that the sender close either of these streams.
/// The shape of one call's outputs: STOP_SENDING only on request streams (never on the peer's
/// control or QPACK streams), our control stream never FIN-ed nor reset (RESET_STREAM only on
/// request streams), no empty RequestBody, and a CloseConnection, if any, is the last output
/// and only when `closing`.
pub open spec fn outs_ok(o: Seq<SpecOutput>, closing: bool) -> bool {
    &&& forall|i: int| 0 <= i < o.len() ==> stop_ok(#[trigger] o[i]) && ctrl_open(o[i]) && body_ok(o[i])
    &&& forall|i: int|
        0 <= i < o.len() && (#[trigger] o[i]) is CloseConnection ==> closing && i == o.len() - 1
    &&& closing ==> o.len() > 0 && o.last() is CloseConnection
}

/// Outputs on request streams only: no control-stream write, STOP_SENDING and RESET_STREAM only
/// on request streams, no empty RequestBody.
pub open spec fn req_only(o: Seq<SpecOutput>) -> bool {
    forall|i: int| 0 <= i < o.len() ==> ctrl_free(#[trigger] o[i]) && stop_ok(o[i]) && body_ok(o[i])
}

// =============================================================================
// Executable helpers
// =============================================================================

proof fn lemma_added_refl(o: Seq<Output>)
    ensures
        extends(o, o),
        added(o, o) == Seq::<SpecOutput>::empty(),
{
    assert(o.take(o.len() as int) =~= o);
    assert(added(o, o) =~= Seq::<SpecOutput>::empty());
}

proof fn lemma_added_push(o0: Seq<Output>, o1: Seq<Output>, x: Output)
    requires
        extends(o0, o1),
    ensures
        extends(o0, o1.push(x)),
        added(o0, o1.push(x)) == added(o0, o1).push(x@),
{
    assert(o1.push(x).take(o0.len() as int) =~= o1.take(o0.len() as int));
    assert(added(o0, o1.push(x)) =~= added(o0, o1).push(x@));
}

proof fn lemma_added_trans(o0: Seq<Output>, o1: Seq<Output>, o2: Seq<Output>)
    requires
        extends(o0, o1),
        extends(o1, o2),
    ensures
        extends(o0, o2),
        added(o0, o2) == added(o0, o1) + added(o1, o2),
{
    assert(o2.take(o0.len() as int) =~= o2.take(o1.len() as int).take(o0.len() as int));
    assert forall|i: int| 0 <= i < o1.len() - o0.len() implies o2.skip(o0.len() as int)[i]
        == o1.skip(o0.len() as int)[i] by {
        assert(o2.take(o1.len() as int)[o0.len() + i] == o2[o0.len() + i]);
    }
    assert(added(o0, o2) =~= added(o0, o1) + added(o1, o2));
}

proof fn lemma_writes_append(a: Seq<SpecOutput>, b: Seq<SpecOutput>, id: u64)
    ensures
        writes_on(a + b, id) == writes_on(a, id) + writes_on(b, id),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
        assert(writes_on(a, id) + Seq::empty() =~= writes_on(a, id));
    } else {
        lemma_writes_append(a, b.drop_last(), id);
        assert((a + b).drop_last() =~= a + b.drop_last());
        assert((a + b).last() == b.last());
        let w = writes_on(a, id);
        let wb = writes_on(b.drop_last(), id);
        let t = writes_on(b, id).skip(wb.len() as int);
        assert(w + wb + t =~= w + (wb + t));
        assert(writes_on(b, id) =~= wb + t);
    }
}

proof fn lemma_writes_none(o: Seq<SpecOutput>, id: u64)
    requires
        forall|i: int| 0 <= i < o.len() ==> ctrl_free(#[trigger] o[i]),
        id == 3,
    ensures
        writes_on(o, id) == Seq::<u8>::empty(),
    decreases o.len(),
{
    if o.len() > 0 {
        assert(ctrl_free(o[o.len() - 1]));
        assert forall|i: int| 0 <= i < o.drop_last().len() implies ctrl_free(
            #[trigger] o.drop_last()[i],
        ) by {
            assert(o.drop_last()[i] == o[i]);
        }
        lemma_writes_none(o.drop_last(), id);
    }
}

proof fn lemma_writes_one(x: SpecOutput, id: u64)
    ensures
        writes_on(seq![x], id) == match x {
            SpecOutput::StreamWrite { stream_id, data, .. } => if stream_id == id {
                data
            } else {
                Seq::empty()
            },
            _ => Seq::empty(),
        },
{
    reveal_with_fuel(writes_on, 2);
    assert(seq![x].drop_last() =~= Seq::<SpecOutput>::empty());
    assert(seq![x].last() == x);
    assert(writes_on(Seq::<SpecOutput>::empty(), id) == Seq::<u8>::empty());
    match x {
        SpecOutput::StreamWrite { data, .. } => {
            assert(Seq::<u8>::empty() + data =~= data);
            assert(Seq::<u8>::empty() + Seq::<u8>::empty() =~= Seq::<u8>::empty());
        },
        _ => {
            assert(Seq::<u8>::empty() + Seq::<u8>::empty() =~= Seq::<u8>::empty());
        },
    }
}

/// Moves `v` into reverse order in an exact buffer, so popping yields its elements first to last: one allocation, the
/// free of `v`, one unit per element moved.
fn rev<T>(v: Vec<T>) -> (r: (Vec<T>, Ghost<nat>))
    ensures
        r.0@.len() == v@.len(),
        forall|i: int| 0 <= i < v@.len() ==> r.0@[i] == v@[v@.len() - 1 - i],
        r.1@ <= v@.len() + 2,
{
    let ghost v0 = v@;
    let mut v = v;
    let mut r: CapVec<T> = CapVec::new(v.len());
    let ghost mut work: nat = 2;
    while v.len() > 0
        invariant
            v@.len() + r@.len() == v0.len(),
            v@ == v0.take(v@.len() as int),
            forall|i: int| 0 <= i < r@.len() ==> r@[i] == v0[v0.len() - 1 - i],
            r.wf(),
            r.cap() == v0.len(),
            work == r@.len() + 2,
        decreases v@.len(),
    {
        let ghost n = v@.len();
        match v.pop() {
            Some(x) => {
                proof {
                    assert(x == v0[n - 1]);
                    assert(v@ =~= v0.take(v@.len() as int));
                }
                r.push(x);
                proof {
                    work = work + 1;
                }
            },
            None => {},
        }
    }
    (r.into_vec(), Ghost(work))
}

fn status_line(status: u16) -> (f: FieldLine)
    requires
        100 <= status <= 599,
    ensures
        f@ == (lit_status(), status_digits(status)),
{
    let mut name: Vec<u8> = Vec::new();
    name.push(58);
    name.push(115);
    name.push(116);
    name.push(97);
    name.push(116);
    name.push(117);
    name.push(115);
    let mut value: Vec<u8> = Vec::new();
    value.push((48 + status / 100) as u8);
    value.push((48 + (status / 10) % 10) as u8);
    value.push((48 + status % 10) as u8);
    proof {
        assert(name@ =~= lit_status());
        assert(value@ =~= status_digits(status));
    }
    FieldLine { name, value }
}

/// Appends copies of `h`.
fn copy_fields(h: &[FieldLine], out: &mut Vec<FieldLine>)
    ensures
        fields_view(final(out)@) == fields_view(old(out)@) + fields_view(h@),
{
    let ghost o0 = fields_view(out@);
    let mut i: usize = 0;
    while i < h.len()
        invariant
            i <= h@.len(),
            fields_view(out@) == o0 + fields_view(h@.take(i as int)),
        decreases h@.len() - i,
    {
        let f = FieldLine { name: slice_to_vec(h[i].name.as_slice()), value: slice_to_vec(h[i].value.as_slice()) };
        let ghost before = out@;
        out.push(f);
        proof {
            assert(fields_view(h@.take(i + 1)) =~= fields_view(h@.take(i as int)).push(h@[i as int]@));
            assert(fields_view(out@) =~= fields_view(before).push(f@));
        }
        i += 1;
    }
    proof {
        assert(h@.take(h@.len() as int) =~= h@);
    }
}

proof fn lemma_fields_size_prefix(f: Fields, k: int)
    requires
        0 <= k <= f.len(),
    ensures
        fields_size(f) >= fields_size(f.take(k)),
    decreases f.len(),
{
    if k < f.len() {
        assert(f.drop_last().take(k) =~= f.take(k));
        lemma_fields_size_prefix(f.drop_last(), k);
    } else {
        assert(f.take(k) =~= f);
    }
}

/// Whether the lines' Σ(name + value + 32) fits the peer's limit; computed without overflow.
fn fits_peer_x(fields: &[FieldLine], peer: Option<u64>) -> (r: bool)
    ensures
        r == fits_peer(peer, fields_size(fields_view(fields@))),
{
    let l = match peer {
        None => return true,
        Some(l) => l,
    };
    let ghost fv = fields_view(fields@);
    let mut acc: u64 = 0;
    let mut i: usize = 0;
    while i < fields.len()
        invariant
            i <= fields@.len(),
            fv == fields_view(fields@),
            peer == Some(l),
            acc <= l,
            acc == fields_size(fv.take(i as int)),
        decreases fields@.len() - i,
    {
        let n = fields[i].name.len() as u64;
        let v = fields[i].value.len() as u64;
        proof {
            assert(fv.take(i + 1).drop_last() =~= fv.take(i as int));
            assert(fv.take(i + 1).last() == fields@[i as int]@);
            assert(fields_size(fv.take(i + 1)) == acc + n + v + 32);
        }
        if !(n <= l - acc && v <= l - acc - n && 32 <= l - acc - n - v) {
            proof {
                assert(acc + n + v + 32 > l);
                assert(fields_size(fv.take(i + 1)) > l);
                lemma_fields_size_prefix(fv, i + 1);
                assert(fields_size(fv) > l);
            }
            return false;
        }
        acc = acc + n + v + 32;
        i += 1;
    }
    proof {
        assert(fv.take(fields@.len() as int) =~= fv);
    }
    true
}

/// `write_response`'s bytes: a HEADERS frame of `enc` then the body frames carry `r`.
proof fn lemma_write_wire(enc: Seq<u8>, data: Seq<u8>, r: SpecResponse)
    requires
        enc.len() <= VARINT_MAX,
        rfc_decode_field_section(enc) == Ok::<Fields, u64>(resp_fields(r)),
        data == spec_frame_bytes(FRAME_HEADERS, enc) + body_frames(r.body),
    ensures
        response_wire(data, r),
{
    hide(rfc_decode_field_section);
    hide(body_frames);
    let b = body_frames(r.body);
    lemma_frame_bytes_roundtrip(FRAME_HEADERS, enc, b);
    let h = spec_frame_header_bytes(FRAME_HEADERS, enc.len() as u64).len();
    assert(data.skip((h + enc.len()) as int) =~= b);
}

/// `write_response`'s one output.
proof fn lemma_one_write(o0: Seq<Output>, out: Seq<Output>, w: Output, id: u64, r: SpecResponse)
    requires
        out == o0.push(w),
        match w@ {
            SpecOutput::StreamWrite { stream_id, data, fin } => stream_id == id && fin && response_wire(data, r),
            _ => false,
        },
    ensures
        extends(o0, out),
        one_response(added(o0, out), id, r),
{
    hide(response_wire);
    lemma_added_refl(o0);
    lemma_added_push(o0, o0, w);
    assert(added(o0, out) =~= seq![w@]);
}

/// The input path's 421 (D10): HEADERS, the section prefix `00 00`, then `:status 421` as an indexed line of static
/// entry 69 (`FF 06`).
const ANSWER_421: [u8; 6] = [0x01, 0x04, 0x00, 0x00, 0xFF, 0x06];
/// The input path's 501 (D10): HEADERS, `00 00`, then a literal line naming static entry 24 (`:status`, `5F 09`) with
/// the raw 3-byte value "501".
const ANSWER_501: [u8; 10] = [0x01, 0x08, 0x00, 0x00, 0x5F, 0x09, 0x03, 0x35, 0x30, 0x31];

/// A zero first byte is the prefix integer 0 in one byte.
#[verifier::spinoff_prover]
proof fn lemma_zero_prefix(n: u8, b: Seq<u8>)
    requires
        7 <= n <= 8,
        b.len() > 0,
        b[0] == 0u8,
    ensures
        rfc_prefix_int(n, b) == (PrefixIntSpec::Value { value: 0, consumed: 1 }),
{
    lemma2_to64();
}

/// The prefix `00 00` (Required Insert Count 0, Base 0) then one line `l` of `:status` decodes to an empty response's
/// fields.
#[verifier::spinoff_prover]
proof fn lemma_one_line_section(l: Seq<u8>, status: u16)
    requires
        l.len() > 0,
        rfc_field_line(l) == Some(((lit_status(), status_digits(status)), l.len())),
    ensures
        rfc_decode_field_section(seq![0u8, 0u8] + l) == Ok::<Fields, u64>(resp_fields(empty_response(status))),
{
    hide(rfc_field_line);
    hide(rfc_prefix_int);
    let f = (lit_status(), status_digits(status));
    let b = seq![0u8, 0u8] + l;
    let rest = b.skip(1);
    assert(b[0] == 0u8);
    assert(rest[0] == 0u8);
    assert(rest.skip(1) =~= l);
    lemma_zero_prefix(8, b);
    lemma_zero_prefix(7, rest);
    assert(0u8 & 0x80u8 == 0u8) by (bit_vector);
    assert(l.skip(l.len() as int) =~= Seq::<u8>::empty());
    reveal_with_fuel(rfc_field_lines, 2);
    assert(rfc_field_lines(l) == Some(seq![f] + Seq::<(Seq<u8>, Seq<u8>)>::empty()));
    assert(seq![f] + Seq::<(Seq<u8>, Seq<u8>)>::empty() =~= resp_fields(empty_response(status)));
}

/// An empty response's section, `:status` and its 3 digits, is 7 + 3 + 32 = 42 bytes.
#[verifier::spinoff_prover]
proof fn lemma_status_size(status: u16)
    ensures
        fields_size(resp_fields(empty_response(status))) == 42,
{
    let r = resp_fields(empty_response(status));
    assert(r =~= seq![(lit_status(), status_digits(status))]);
    assert(r.drop_last() =~= Seq::<(Seq<u8>, Seq<u8>)>::empty());
    reveal_with_fuel(fields_size, 2);
}

/// The indexed line of static entry 69.
spec fn line_421() -> Seq<u8> {
    seq![0xFFu8, 0x06u8]
}

/// The literal line naming static entry 24 with the raw value "501".
spec fn line_501() -> Seq<u8> {
    seq![0x5Fu8, 0x09u8, 0x03u8, 0x35u8, 0x30u8, 0x31u8]
}

/// `ANSWER_421` and `ANSWER_501` are HEADERS frames (type 1, a one-byte length) of the prefix `00 00` and the line.
#[verifier::spinoff_prover]
proof fn lemma_answer_bytes()
    ensures
        ANSWER_421@ == seq![1u8, 4u8] + (seq![0u8, 0u8] + line_421()),
        ANSWER_501@ == seq![1u8, 8u8] + (seq![0u8, 0u8] + line_501()),
{
    assert(ANSWER_421@ =~= seq![1u8, 4u8] + (seq![0u8, 0u8] + line_421()));
    assert(ANSWER_501@ =~= seq![1u8, 8u8] + (seq![0u8, 0u8] + line_501()));
}

/// Static entry 69 is `:status 421`.
#[verifier::spinoff_prover]
proof fn lemma_entry_69()
    ensures
        spec_static_entry(69) == Some((lit_status(), status_digits(421))),
{
    assert(spec_static_entry(69) == Some((lit_status(), status_digits(421)))) by (compute_only);
}

/// Static entry 24 is `:status 103`, so a name reference to it names `:status`.
#[verifier::spinoff_prover]
proof fn lemma_entry_24()
    ensures
        spec_static_entry(24) == Some((lit_status(), seq![49u8, 48u8, 51u8])),
{
    assert(spec_static_entry(24) == Some((lit_status(), seq![49u8, 48u8, 51u8]))) by (compute_only);
}

/// The indexed line `FF 06` (static entry 69: 63 in the 6-bit prefix, then the continuation 6) decodes to
/// `:status 421` (RFC 9204 §4.5.2).
#[verifier::spinoff_prover]
proof fn lemma_line_421()
    ensures
        line_421().len() == 2,
        rfc_field_line(line_421()) == Some(((lit_status(), status_digits(421)), line_421().len())),
{
    hide(spec_static_entry);
    hide(rfc_prefix_int);
    lemma2_to64();
    lemma_entry_69();
    assert(0xffu8 >> 2u8 == 63u8) by (bit_vector);
    assert(0xc0u8 | 63u8 == 0xFFu8) by (bit_vector);
    assert(spec_prefix_int_bytes(6, 0xc0, 69) =~= line_421());
    theorem_prefix_int_roundtrip(6, 0xc0, 69);
    assert(0xFFu8 & 0x80u8 != 0u8) by (bit_vector);
    assert(0xFFu8 & 0x40u8 != 0u8) by (bit_vector);
}

/// The raw string `03 '501'` (length 3 in the 7-bit prefix, no Huffman) decodes to "501" (RFC 9204 §4.1.2).
#[verifier::spinoff_prover]
proof fn lemma_value_501()
    ensures
        spec_prefix_int_bytes(7, 0x00, 3) + status_digits(501) == seq![0x03u8, 0x35u8, 0x30u8, 0x31u8],
        rfc_string(7, seq![0x03u8, 0x35u8, 0x30u8, 0x31u8]) == Some((status_digits(501), 4nat)),
{
    hide(rfc_prefix_int);
    lemma2_to64();
    let v = status_digits(501);
    assert(v =~= seq![53u8, 48u8, 49u8]);
    assert(0xffu8 >> 1u8 == 127u8) by (bit_vector);
    assert(0x00u8 | 3u8 == 0x03u8) by (bit_vector);
    let q = spec_prefix_int_bytes(7, 0x00, 3) + v;
    assert(q =~= seq![0x03u8, 0x35u8, 0x30u8, 0x31u8]);
    theorem_prefix_int_roundtrip(7, 0x00, 3);
    lemma_prefix_int_append(7, spec_prefix_int_bytes(7, 0x00, 3), v);
    assert(q.subrange(1, 4) =~= v);
    assert((3u8 >> 7u8) & 1u8 == 0u8) by (bit_vector);
}

/// The literal line `5F 09 03 '501'` (a name reference to static entry 24: 15 in the 4-bit prefix, then the
/// continuation 9; then the value) decodes to `:status 501` (RFC 9204 §4.5.4).
#[verifier::spinoff_prover]
proof fn lemma_line_501()
    ensures
        line_501().len() == 6,
        rfc_field_line(line_501()) == Some(((lit_status(), status_digits(501)), line_501().len())),
{
    hide(spec_static_entry);
    hide(rfc_prefix_int);
    hide(rfc_string);
    lemma2_to64();
    lemma_entry_24();
    lemma_value_501();
    assert(0xffu8 >> 4u8 == 15u8) by (bit_vector);
    assert(0x50u8 | 15u8 == 0x5Fu8) by (bit_vector);
    let p = spec_prefix_int_bytes(4, 0x50, 24);
    let q = seq![0x03u8, 0x35u8, 0x30u8, 0x31u8];
    assert(p =~= seq![0x5Fu8, 0x09u8]);
    let l = p + q;
    theorem_prefix_int_roundtrip(4, 0x50, 24);
    lemma_prefix_int_append(4, p, q);
    assert(l[0] == 0x5Fu8);
    assert(l.skip(2) =~= q);
    assert(0x5Fu8 & 0x80u8 == 0u8) by (bit_vector);
    assert(0x5Fu8 & 0x40u8 != 0u8) by (bit_vector);
    assert(0x5Fu8 & 0x10u8 != 0u8) by (bit_vector);
    assert(l =~= line_501());
}

/// A HEADERS frame (type 1, a one-byte length `n`) of the prefix `00 00` and one `:status` line `l`, and no DATA: its
/// header parses to `(2, HEADERS, n)`, its section decodes (RFC 9204) to that one line, and it carries the empty
/// response (`response_wire`).
#[verifier::spinoff_prover]
proof fn lemma_short_wire(l: Seq<u8>, n: u8, data: Seq<u8>, status: u16)
    requires
        l.len() > 0,
        rfc_field_line(l) == Some(((lit_status(), status_digits(status)), l.len())),
        l.len() + 2 == n <= 63,
        data == seq![1u8, n] + (seq![0u8, 0u8] + l),
    ensures
        data.len() == 2 + n,
        rfc_frame_header(data) == Some((2nat, FRAME_HEADERS, n as u64)),
        rfc_decode_field_section(data.subrange(2, 2 + n)) == Ok::<Fields, u64>(
            seq![(lit_status(), status_digits(status))],
        ),
        response_wire(data, empty_response(status)),
{
    hide(rfc_field_line);
    hide(rfc_decode_field_section);
    hide(response_wire);
    let enc = seq![0u8, 0u8] + l;
    lemma_one_line_section(l, status);
    lemma_serialize_bytes::<true>(FRAME_HEADERS);
    lemma_serialize_bytes::<true>(n as u64);
    assert(spec_frame_bytes(FRAME_HEADERS, enc) + body_frames(Seq::empty()) =~= data);
    lemma_frame_bytes_roundtrip(FRAME_HEADERS, enc, Seq::empty());
    assert(spec_frame_bytes(FRAME_HEADERS, enc).add(Seq::empty()) =~= data);
    assert(data.subrange(2, 2 + n) =~= enc);
    assert(resp_fields(empty_response(status)) =~= seq![(lit_status(), status_digits(status))]);
    lemma_write_wire(enc, data, empty_response(status));
}

/// What a peer receives as `ANSWER_421`: a HEADERS frame (header `01 04`) whose 4-byte field section decodes, by the
/// RFC 9204 model, to exactly `[(":status", "421")]`, and no DATA, so it carries the empty 421 (`response_wire`).
#[verifier::spinoff_prover]
proof fn lemma_answer_421()
    ensures
        ANSWER_421@.len() == 6,
        rfc_frame_header(ANSWER_421@) == Some((2nat, FRAME_HEADERS, 4u64)),
        rfc_decode_field_section(ANSWER_421@.subrange(2, 6)) == Ok::<Fields, u64>(
            seq![(lit_status(), seq![0x34u8, 0x32u8, 0x31u8])],
        ),
        response_wire(ANSWER_421@, empty_response(421)),
{
    hide(rfc_field_line);
    hide(rfc_decode_field_section);
    hide(rfc_frame_header);
    hide(response_wire);
    hide(line_421);
    lemma_line_421();
    lemma_answer_bytes();
    lemma_short_wire(line_421(), 4, ANSWER_421@, 421);
    assert(status_digits(421) =~= seq![0x34u8, 0x32u8, 0x31u8]);
}

/// What a peer receives as `ANSWER_501`: a HEADERS frame (header `01 08`) whose 8-byte field section decodes, by the
/// RFC 9204 model, to exactly `[(":status", "501")]`, and no DATA, so it carries the empty 501 (`response_wire`).
#[verifier::spinoff_prover]
proof fn lemma_answer_501()
    ensures
        ANSWER_501@.len() == 10,
        rfc_frame_header(ANSWER_501@) == Some((2nat, FRAME_HEADERS, 8u64)),
        rfc_decode_field_section(ANSWER_501@.subrange(2, 10)) == Ok::<Fields, u64>(
            seq![(lit_status(), seq![0x35u8, 0x30u8, 0x31u8])],
        ),
        response_wire(ANSWER_501@, empty_response(501)),
{
    hide(rfc_field_line);
    hide(rfc_decode_field_section);
    hide(rfc_frame_header);
    hide(response_wire);
    hide(line_501);
    lemma_line_501();
    lemma_answer_bytes();
    lemma_short_wire(line_501(), 8, ANSWER_501@, 501);
    assert(status_digits(501) =~= seq![0x35u8, 0x30u8, 0x31u8]);
}

/// Writes `r` on `id` with FIN, `:status` first. `false` (nothing written): the field section
/// exceeds the peer's limit, or a frame would be too long to encode.
#[verifier::spinoff_prover]
fn write_response(id: u64, r: &Response, peer: Option<u64>, out: &mut Vec<Output>) -> (ok: bool)
    requires
        valid_response(r@, false) || valid_response(r@, true),
    ensures
        extends(old(out)@, final(out)@),
        ok ==> fits_peer(peer, fields_size(resp_fields(r@))) && one_response(
            added(old(out)@, final(out)@),
            id,
            r@,
        ),
        !ok ==> final(out)@ == old(out)@,
        !ok && r@.headers.len() == 0 && r@.body.len() == 0 ==> !fits_peer(
            peer,
            fields_size(resp_fields(r@)),
        ),
{
    hide(response_wire);
    hide(one_response);
    hide(rfc_decode_field_section);
    hide(rfc_frame_header);
    hide(spec_frame_bytes);
    hide(spec_varint);
    let mut fields: Vec<FieldLine> = Vec::new();
    fields.push(status_line(r.status));
    proof {
        assert(fields_view(fields@) =~= seq![(lit_status(), status_digits(r.status))]);
    }
    copy_fields(r.headers.as_slice(), &mut fields);
    proof {
        assert(fields_view(fields@) == resp_fields(r@));
    }
    if !fits_peer_x(fields.as_slice(), peer) {
        proof {
            lemma_added_refl(out@);
        }
        return false;
    }
    proof {
        assert forall|i: int| 0 <= i < fields@.len() implies #[trigger] fields@[i].name@.len()
            <= PREFIX_INT_MAX && fields@[i].value@.len() <= PREFIX_INT_MAX by {
            assert(fields_view(fields@)[i] == fields@[i]@);
            if i > 0 {
                assert(resp_fields(r@)[i] == r@.headers[i - 1]);
                assert(resp_header_ok(r@.headers[i - 1]));
            }
        }
    }
    let mut enc: Vec<u8> = Vec::new();
    encode_field_section(fields.as_slice(), &mut enc);
    if enc.len() as u64 > VARINT_MAX || r.body.len() as u64 > VARINT_MAX {
        proof {
            lemma_added_refl(out@);
            if r@.headers.len() == 0 {
                assert(fields_view(fields@).len() == 1);
                assert(fields_view(fields@)[0] == fields@[0]@);
                assert(enc@.len() <= 262);
            }
        }
        return false;
    }
    let mut data: Vec<u8> = Vec::new();
    put_frame(FRAME_HEADERS, &enc, &mut data);
    if r.body.len() > 0 {
        put_frame(FRAME_DATA, &r.body, &mut data);
    }
    proof {
        assert(enc@.skip(0) =~= enc@);
        assert(data@ =~= spec_frame_bytes(FRAME_HEADERS, enc@) + body_frames(r.body@));
        lemma_write_wire(enc@, data@, r@);
    }
    let ghost o0 = out@;
    let w = Output::StreamWrite { stream_id: id, data, fin: true };
    out.push(w);
    proof {
        lemma_one_write(o0, out@, w, id, r@);
    }
    true
}

// =============================================================================
// Per-stream state
// =============================================================================

struct ReqEntry {
    id: u64,
    stream: RequestStream,
    /// Request bytes are still processed: no FIN, error or internal answer yet.
    rx_open: bool,
    /// The peer's sending part has ended (FIN seen).
    fin_seen: bool,
    /// The request head was delivered to the application.
    head: bool,
    /// The delivered request's method is HEAD (its response carries no content).
    is_head: bool,
    /// Our sending part is open: no response, reset, or peer STOP_SENDING yet.
    send_open: bool,
    /// A trailer section received, held until the request ends.
    trailers: Vec<FieldLine>,
}

spec fn req_entry_ok(e: ReqEntry) -> bool {
    &&& e.id % 4 == 0
    &&& e.stream.wf()
    &&& e.rx_open ==> !e.stream.done() && !e.fin_seen
}

spec fn req_hist_of(e: ReqEntry) -> (Seq<u8>, Seq<SpecReqEvent>, Fields) {
    (e.stream.all(), e.stream.emitted(), fields_view(e.trailers@))
}

struct UniEntry {
    id: u64,
    stream: UniStream,
}

spec fn uni_hist_of(e: UniEntry) -> (Seq<u8>, SeenUni, Seq<SpecUniEvent>) {
    (e.stream.all(), e.stream.seen_before(), e.stream.emitted())
}

/// A request stream's state as `req_state` reports it.
pub struct ReqState {
    /// Request bytes are still processed: no FIN, error or internal answer yet.
    pub receiving: bool,
    /// The request head was delivered to the application.
    pub head: bool,
    /// Our sending part is open.
    pub send_open: bool,
    /// The peer's sending part has ended (FIN seen).
    pub fin_seen: bool,
    /// The delivered request's method is HEAD.
    pub is_head: bool,
}

spec fn state_of(e: ReqEntry) -> ReqState {
    ReqState {
        receiving: e.rx_open,
        head: e.head,
        send_open: e.send_open,
        fin_seen: e.fin_seen,
        is_head: e.is_head,
    }
}

type RHist = (Seq<u8>, Seq<SpecReqEvent>, Fields);

type UHist = (Seq<u8>, SeenUni, Seq<SpecUniEvent>);

/// The request table's view: each entry under its own ID, valid, with its history in `h`.
#[verifier::opaque]
spec fn reqs_ok(m: Map<u64, Box<ReqEntry>>, h: Map<u64, RHist>) -> bool {
    forall|id: u64|
        #[trigger] m.contains_key(id) ==> m[id].id == id && req_entry_ok(*m[id]) && h.contains_key(id) && h[id]
            == req_hist_of(*m[id])
}

/// The uni table's view: each entry under its own ID (a client uni stream), live, with its history in `h`.
#[verifier::opaque]
spec fn unis_ok(m: Map<u64, Box<UniEntry>>, h: Map<u64, UHist>) -> bool {
    forall|id: u64|
        #[trigger] m.contains_key(id) ==> m[id].id == id && id % 4 == 2 && m[id].stream.wf() && !m[id].stream.done()
            && h.contains_key(id) && h[id] == uni_hist_of(*m[id])
}

/// `st` mirrors the request table: its keys, each with its entry's state.
#[verifier::opaque]
spec fn req_dom(m: Map<u64, Box<ReqEntry>>, st: Map<u64, ReqState>) -> bool {
    &&& st.dom() == m.dom()
    &&& forall|id: u64| #[trigger] st.contains_key(id) ==> st[id] == state_of(*m[id])
}

/// `us` is the uni table's key set.
#[verifier::opaque]
spec fn uni_dom(m: Map<u64, Box<UniEntry>>, us: Set<u64>) -> bool {
    us == m.dom()
}

/// Putting `k` back after taking it out is setting it.
proof fn lemma_map_put<K, V>(m: Map<K, V>, k: K, v: V)
    ensures
        m.remove(k).insert(k, v) == m.insert(k, v),
{
    assert(m.remove(k).insert(k, v) =~= m.insert(k, v));
}

/// Removing an absent key changes nothing.
proof fn lemma_map_absent<K, V>(m: Map<K, V>, k: K)
    ensures
        !m.contains_key(k) ==> m.remove(k) == m,
{
    if !m.contains_key(k) {
        assert(m.remove(k) =~= m);
    }
}

/// A request table lookup: the entry, its state and its history, or neither entry nor state.
proof fn lemma_req_get(m: Map<u64, Box<ReqEntry>>, h: Map<u64, RHist>, st: Map<u64, ReqState>, id: u64)
    requires
        reqs_ok(m, h),
        req_dom(m, st),
    ensures
        st.contains_key(id) == m.contains_key(id),
        m.contains_key(id) ==> m[id].id == id && req_entry_ok(*m[id]) && h.contains_key(id) && h[id]
            == req_hist_of(*m[id]) && st[id] == state_of(*m[id]),
{
    reveal(reqs_ok);
    reveal(req_dom);
    assert(st.dom().contains(id) == m.dom().contains(id));
}

/// Setting a request entry keeps the view's invariant, with its history and state set.
proof fn lemma_req_set(m: Map<u64, Box<ReqEntry>>, h: Map<u64, RHist>, st: Map<u64, ReqState>, e: Box<ReqEntry>)
    requires
        reqs_ok(m, h),
        req_dom(m, st),
        req_entry_ok(*e),
    ensures
        reqs_ok(m.insert(e.id, e), h.insert(e.id, req_hist_of(*e))),
        req_dom(m.insert(e.id, e), st.insert(e.id, state_of(*e))),
{
    reveal(reqs_ok);
    reveal(req_dom);
    assert(st.insert(e.id, state_of(*e)).dom() =~= m.insert(e.id, e).dom());
}

/// Removing request entry `id` keeps the view's invariant, under any history `h2` that agrees off `id`.
proof fn lemma_req_del(
    m: Map<u64, Box<ReqEntry>>,
    h: Map<u64, RHist>,
    h2: Map<u64, RHist>,
    st: Map<u64, ReqState>,
    id: u64,
)
    requires
        reqs_ok(m, h),
        req_dom(m, st),
        forall|x: u64|
            #![trigger h2.contains_key(x)]
            #![trigger h2[x]]
            x != id && h.contains_key(x) ==> h2.contains_key(x) && h2[x] == h[x],
    ensures
        reqs_ok(m.remove(id), h2),
        req_dom(m.remove(id), st.remove(id)),
{
    reveal(reqs_ok);
    reveal(req_dom);
    assert(st.remove(id).dom() =~= m.remove(id).dom());
}

/// A uni table lookup: the entry and its history, or no entry.
proof fn lemma_uni_get(m: Map<u64, Box<UniEntry>>, h: Map<u64, UHist>, us: Set<u64>, id: u64)
    requires
        unis_ok(m, h),
        uni_dom(m, us),
    ensures
        us.contains(id) == m.contains_key(id),
        m.contains_key(id) ==> m[id].id == id && id % 4 == 2 && m[id].stream.wf() && !m[id].stream.done()
            && h.contains_key(id) && h[id] == uni_hist_of(*m[id]),
{
    reveal(unis_ok);
    reveal(uni_dom);
}

/// Setting a uni entry keeps the view's invariant, with its history set and its ID tracked.
proof fn lemma_uni_set(m: Map<u64, Box<UniEntry>>, h: Map<u64, UHist>, us: Set<u64>, e: Box<UniEntry>)
    requires
        unis_ok(m, h),
        uni_dom(m, us),
        e.id % 4 == 2,
        e.stream.wf(),
        !e.stream.done(),
    ensures
        unis_ok(m.insert(e.id, e), h.insert(e.id, uni_hist_of(*e))),
        uni_dom(m.insert(e.id, e), us.insert(e.id)),
{
    reveal(unis_ok);
    reveal(uni_dom);
    assert(us.insert(e.id) =~= m.insert(e.id, e).dom());
}

/// Removing uni entry `id` keeps the view's invariant, under any history `h2` that agrees off `id`.
proof fn lemma_uni_del(m: Map<u64, Box<UniEntry>>, h: Map<u64, UHist>, h2: Map<u64, UHist>, us: Set<u64>, id: u64)
    requires
        unis_ok(m, h),
        uni_dom(m, us),
        forall|x: u64|
            #![trigger h2.contains_key(x)]
            #![trigger h2[x]]
            x != id && h.contains_key(x) ==> h2.contains_key(x) && h2[x] == h[x],
    ensures
        unis_ok(m.remove(id), h2),
        uni_dom(m.remove(id), us.remove(id)),
{
    reveal(unis_ok);
    reveal(uni_dom);
    assert(us.remove(id) =~= m.remove(id).dom());
}

/// The buffers a dropped request entry frees beside its box: its queue's (at most two), its trailer list and each
/// trailer line's two.
spec fn req_frees(e: ReqEntry) -> nat {
    3 + 2 * e.trailers@.len()
}

/// The buffers a dropped uni entry frees beside its box: its queue's (at most two).
spec fn uni_frees() -> nat {
    2
}

// =============================================================================
// The stream tables: avl trees keyed by stream ID, viewed as maps
// =============================================================================

/// The map view of a table's entries, the later of two entries with one key winning (a search tree has none).
spec fn mview<V>(s: Seq<(u64, V)>) -> Map<u64, V>
    decreases s.len(),
{
    if s.len() == 0 {
        Map::empty()
    } else {
        mview(s.drop_last()).insert(s.last().0, s.last().1)
    }
}

/// A table's map view.
spec fn tv<V>(t: Tree<V>) -> Map<u64, V> {
    mview(seq(t))
}

/// A table: a search tree whose keys are all `r` mod 4 (a stream ID's type bits). So it holds at most `2^62` entries
/// (`lemma_keys_len`), within the `pow2(63)` that avl's `split`, `pop_min` and `join` require.
spec fn tbl<V>(t: Tree<V>, r: u64) -> bool {
    &&& wf(t)
    &&& keys_mod(t, r)
}

/// Every key of `t` is `r` mod 4 (opaque: revealed only by the table's lemmas).
#[verifier::opaque]
spec fn keys_mod<V>(t: Tree<V>, r: u64) -> bool {
    forall|i: int| 0 <= i < seq(t).len() ==> (#[trigger] seq(t)[i]).0 % 4 == r
}

proof fn lemma_mview_one<V>(k: u64, v: V)
    ensures
        mview(seq![(k, v)]) == Map::<u64, V>::empty().insert(k, v),
{
    let e = seq![(k, v)];
    assert(e.drop_last() =~= Seq::<(u64, V)>::empty());
    assert(mview(Seq::<(u64, V)>::empty()) == Map::<u64, V>::empty());
    assert(e.last() == (k, v));
}

proof fn lemma_mview_app<V>(x: Seq<(u64, V)>, y: Seq<(u64, V)>)
    ensures
        mview(x + y) == mview(x).union_prefer_right(mview(y)),
    decreases y.len(),
{
    if y.len() == 0 {
        assert(x + y =~= x);
        assert(mview(x).union_prefer_right(mview(y)) =~= mview(x));
    } else {
        assert((x + y).drop_last() =~= x + y.drop_last());
        lemma_mview_app(x, y.drop_last());
        assert(mview(x + y) =~= mview(x).union_prefer_right(mview(y)));
    }
}

proof fn lemma_mview_has<V>(s: Seq<(u64, V)>, k: u64)
    ensures
        mview(s).contains_key(k) <==> exists|i: int| 0 <= i < s.len() && (#[trigger] s[i]).0 == k,
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_mview_has(s.drop_last(), k);
        if exists|i: int| 0 <= i < s.drop_last().len() && (#[trigger] s.drop_last()[i]).0 == k {
            let i = choose|i: int| 0 <= i < s.drop_last().len() && (#[trigger] s.drop_last()[i]).0 == k;
            assert(s[i] == s.drop_last()[i]);
        }
        if exists|i: int| 0 <= i < s.len() && (#[trigger] s[i]).0 == k {
            let i = choose|i: int| 0 <= i < s.len() && (#[trigger] s[i]).0 == k;
            if i < s.len() - 1 {
                assert(s.drop_last()[i] == s[i]);
            }
        }
    }
}

/// In a sorted sequence, the map view holds each entry under its key.
proof fn lemma_mview_at<V>(s: Seq<(u64, V)>, i: int)
    requires
        sorted(s),
        0 <= i < s.len(),
    ensures
        mview(s).contains_key(s[i].0),
        mview(s)[s[i].0] == s[i].1,
    decreases s.len(),
{
    if i < s.len() - 1 {
        let d = s.drop_last();
        assert(d[i] == s[i]);
        assert(s[i].0 < s[s.len() - 1].0);
        assert(sorted(d)) by {
            assert forall|a: int, b: int| 0 <= a < b < d.len() implies #[trigger] d[a].0 < #[trigger] d[b].0 by {
                assert(d[a] == s[a] && d[b] == s[b]);
            }
        }
        lemma_mview_at(d, i);
    }
}

/// A sorted sequence whose keys are all `r` mod 4 has at most `2^62` entries: key `i` is at least `4·i`.
proof fn lemma_keys_len<V>(s: Seq<(u64, V)>, r: u64)
    requires
        sorted(s),
        forall|i: int| 0 <= i < s.len() ==> (#[trigger] s[i]).0 % 4 == r,
    ensures
        s.len() <= pow2(62),
        s.len() < pow2(63),
{
    lemma2_to64();
    lemma2_to64_rest();
    if s.len() > 0 {
        lemma_key_ge(s, r, s.len() - 1);
    }
}

proof fn lemma_key_ge<V>(s: Seq<(u64, V)>, r: u64, i: int)
    requires
        sorted(s),
        forall|i: int| 0 <= i < s.len() ==> (#[trigger] s[i]).0 % 4 == r,
        0 <= i < s.len(),
    ensures
        s[i].0 >= 4 * i,
    decreases i,
{
    if i > 0 {
        lemma_key_ge(s, r, i - 1);
        assert(s[i - 1].0 < s[i].0);
        assert(s[i - 1].0 % 4 == r && s[i].0 % 4 == r);
    }
}

/// A table holds fewer than `2^63` entries.
proof fn lemma_tbl_len<V>(t: Tree<V>, r: u64)
    requires
        tbl(t, r),
    ensures
        seq(t).len() <= pow2(62),
        seq(t).len() < pow2(63),
{
    reveal(keys_mod);
    lemma_wf_sorted(t);
    lemma_keys_len(seq(t), r);
}

/// A table split at `k`: two tables whose views make up `t`'s, `k` in neither unless at the front of the upper one.
proof fn lemma_split_tbl<V>(t: Tree<V>, a: Tree<V>, b: Tree<V>, k: u64, r: u64)
    requires
        tbl(t, r),
        wf(a),
        wf(b),
        seq(a) + seq(b) == seq(t),
        keys_lt(a, k),
        keys_ge(b, k),
    ensures
        tbl(a, r),
        tbl(b, r),
        tv(a).union_prefer_right(tv(b)) == tv(t),
        !tv(a).contains_key(k),
        !tv(t).contains_key(k) ==> keys_gt(b, k),
{
    reveal(keys_mod);
    let (sa, sb) = (seq(a), seq(b));
    assert forall|i: int| 0 <= i < sa.len() implies (#[trigger] sa[i]).0 % 4 == r by {
        assert(seq(t)[i] == sa[i]);
    }
    assert forall|i: int| 0 <= i < sb.len() implies (#[trigger] sb[i]).0 % 4 == r by {
        assert(seq(t)[sa.len() + i] == sb[i]);
    }
    lemma_mview_app(sa, sb);
    lemma_mview_has(sa, k);
    lemma_mview_has(seq(t), k);
    if !tv(t).contains_key(k) {
        assert forall|j: int| 0 <= j < sb.len() implies #[trigger] sb[j].0 > k by {
            assert(seq(t)[sa.len() + j] == sb[j]);
        }
    }
}

/// A sorted sequence's map view has one key per entry.
proof fn lemma_mview_len<V>(s: Seq<(u64, V)>)
    requires
        sorted(s),
    ensures
        mview(s).dom().len() == s.len(),
    decreases s.len(),
{
    if s.len() > 0 {
        let d = s.drop_last();
        assert(sorted(d)) by {
            assert forall|a: int, b: int| 0 <= a < b < d.len() implies #[trigger] d[a].0 < #[trigger] d[b].0 by {
                assert(d[a] == s[a] && d[b] == s[b]);
            }
        }
        lemma_mview_len(d);
        lemma_mview_has(d, s.last().0);
        assert(!mview(d).contains_key(s.last().0)) by {
            if mview(d).contains_key(s.last().0) {
                let i = choose|i: int| 0 <= i < d.len() && (#[trigger] d[i]).0 == s.last().0;
                assert(d[i] == s[i]);
                assert(s[i].0 < s[s.len() - 1].0);
            }
        }
        assert(mview(s).dom() == mview(d).dom().insert(s.last().0));
    }
}

/// A table's map view has one key per entry.
proof fn lemma_tv_len<V>(t: Tree<V>)
    requires
        wf(t),
    ensures
        tv(t).dom().len() == seq(t).len(),
{
    lemma_wf_sorted(t);
    lemma_mview_len(seq(t));
}

/// The entry under key `k`, if any: `get_le`, then its key compared.
fn tbl_get<V>(t: &Tree<V>, k: u64) -> (r: (Option<&V>, Ghost<nat>))
    requires
        wf(*t),
    ensures
        (r.0 is Some) == tv(*t).contains_key(k),
        r.0 matches Some(v) ==> *v == tv(*t)[k],
        r.1@ <= c_get() * (ht(*t) + 1) + 1,
{
    let ghost mut work: nat = 1;
    let (g, Ghost(c)) = get_le(t, k);
    proof {
        work = work + c;
        lemma_wf_sorted(*t);
        lemma_mview_has(seq(*t), k);
    }
    match g {
        Some((key, v)) => {
            let ghost i = choose|i: int| #[trigger] last_le(seq(*t), k, i, key, *v);
            if key == k {
                proof {
                    lemma_mview_at(seq(*t), i);
                }
                (Some(v), Ghost(work))
            } else {
                proof {
                    let s = seq(*t);
                    assert forall|j: int| 0 <= j < s.len() implies (#[trigger] s[j]).0 != k by {
                        if j < i {
                            assert(s[j].0 < s[i].0);
                        }
                    }
                }
                (None, Ghost(work))
            }
        },
        None => {
            proof {
                let s = seq(*t);
                assert forall|j: int| 0 <= j < s.len() implies (#[trigger] s[j]).0 != k by {
                    assert(s[j].0 > k);
                }
            }
            (None, Ghost(work))
        },
    }
}

/// `take`'s view: `t`'s first entry `(k, v)` popped from `b` (keys at least `k`), `k` in `t`, splits `t`'s view.
proof fn lemma_take<V>(t: Tree<V>, a: Tree<V>, b: Tree<V>, b2: Tree<V>, k: u64, k2: u64, v: V, r: u64)
    requires
        tbl(t, r),
        tv(t).contains_key(k),
        tbl(a, r),
        tbl(b, r),
        keys_lt(a, k),
        keys_ge(b, k),
        tv(a).union_prefer_right(tv(b)) == tv(t),
        !tv(a).contains_key(k),
        wf(b2),
        seq![(k2, v)] + seq(b2) == seq(b),
        keys_gt(b2, k2),
        keys_ge(b, k2),
    ensures
        k2 == k,
        v == tv(t)[k],
        tbl(b2, r),
        keys_gt(b2, k),
        tv(a).union_prefer_right(tv(b2)) == tv(t).remove(k),
{
    reveal(keys_mod);
    let (sb, sb2) = (seq(b), seq(b2));
    lemma_mview_app(seq![(k2, v)], sb2);
    lemma_mview_one(k2, v);
    assert(tv(b).contains_key(k));
    lemma_mview_has(sb, k);
    let i = choose|i: int| 0 <= i < sb.len() && (#[trigger] sb[i]).0 == k;
    assert(sb[0] == (k2, v));
    assert(sb[0].0 >= k);
    assert(sb[i].0 >= k2);
    assert forall|j: int| 0 <= j < sb2.len() implies (#[trigger] sb2[j]).0 % 4 == r by {
        assert(sb[j + 1] == sb2[j]);
    }
    lemma_mview_has(sb2, k);
    assert(!tv(b2).contains_key(k));
    assert(tv(a).union_prefer_right(tv(b2)) =~= tv(t).remove(k));
}

/// `put`'s view: `join(a, k, v, b)` of two tables around `k`, `k` being `r` mod 4.
proof fn lemma_put<V>(a: Tree<V>, k: u64, v: V, b: Tree<V>, j: Tree<V>, r: u64)
    requires
        tbl(a, r),
        tbl(b, r),
        keys_lt(a, k),
        keys_gt(b, k),
        k % 4 == r,
        seq(j) == seq(a) + seq![(k, v)] + seq(b),
    ensures
        forall|i: int| 0 <= i < seq(j).len() ==> (#[trigger] seq(j)[i]).0 % 4 == r,
        tv(j) == tv(a).union_prefer_right(tv(b)).insert(k, v),
{
    reveal(keys_mod);
    let (sa, sb, s) = (seq(a), seq(b), seq(j));
    assert forall|i: int| 0 <= i < s.len() implies (#[trigger] s[i]).0 % 4 == r by {
        if i < sa.len() {
            assert(s[i] == sa[i]);
        } else if i > sa.len() {
            assert(s[i] == sb[i - sa.len() - 1]);
        }
    }
    lemma_mview_app(sa + seq![(k, v)], sb);
    lemma_mview_app(sa, seq![(k, v)]);
    lemma_mview_one(k, v);
    lemma_mview_has(sb, k);
    assert(!tv(b).contains_key(k)) by {
        if tv(b).contains_key(k) {
            let i = choose|i: int| 0 <= i < sb.len() && (#[trigger] sb[i]).0 == k;
        }
    }
    assert(tv(j) =~= tv(a).union_prefer_right(tv(b)).insert(k, v));
}

/// `put`'s size precondition: two tables around `k` (`r` mod 4) hold fewer than `2^63` entries with it.
proof fn lemma_put_len<V>(a: Tree<V>, k: u64, v: V, b: Tree<V>, r: u64)
    requires
        tbl(a, r),
        tbl(b, r),
        keys_lt(a, k),
        keys_gt(b, k),
        k % 4 == r,
    ensures
        seq(a).len() + seq(b).len() + 1 < pow2(63),
{
    reveal(keys_mod);
    lemma_wf_sorted(a);
    lemma_wf_sorted(b);
    let s = seq(a) + seq![(k, v)] + seq(b);
    lemma_sorted_concat(seq(a), (k, v), seq(b));
    assert forall|i: int| 0 <= i < s.len() implies (#[trigger] s[i]).0 % 4 == r by {
        if i < seq(a).len() {
            assert(s[i] == seq(a)[i]);
        } else if i > seq(a).len() {
            assert(s[i] == seq(b)[i - seq(a).len() - 1]);
        }
    }
    lemma_keys_len(s, r);
}

/// The cost constant of `req_take_w` and `uni_take_w`: `split` (`c_split6()`), `first` and `pop_min`.
#[verifier::inline]
spec fn c_take() -> nat {
    44
}

/// `take`'s split and first-key check: `b`'s first key is `k` exactly when `t` holds `k`.
proof fn lemma_take_hit<V>(t: Tree<V>, a: Tree<V>, b: Tree<V>, k: u64, r: u64, hit: bool)
    requires
        tbl(t, r),
        tbl(b, r),
        keys_ge(b, k),
        tv(a).union_prefer_right(tv(b)) == tv(t),
        !tv(a).contains_key(k),
        hit == (seq(b).len() > 0 && seq(b)[0].0 == k),
    ensures
        hit == tv(t).contains_key(k),
        tv(b).contains_key(k) == tv(t).contains_key(k),
{
    lemma_mview_has(seq(b), k);
    lemma_wf_sorted(b);
    if tv(b).contains_key(k) {
        let i = choose|i: int| 0 <= i < seq(b).len() && (#[trigger] seq(b)[i]).0 == k;
        if i > 0 {
            assert(seq(b)[0].0 < seq(b)[i].0);
        }
    }
    if hit {
        assert(seq(b)[0].0 == k);
    }
}

/// Takes request stream `id`'s entry, if any, out of the table: the entries below it, the entry, and the entries above
/// it (`split`, then `pop_min` of the upper part when its first key is `id`).
// The popped key `k2` is read only by the proof.
#[allow(unused_variables)]
fn req_take_w(t: Tree<Box<ReqEntry>>, id: u64) -> (r: (Tree<Box<ReqEntry>>, Option<Box<ReqEntry>>, Tree<Box<ReqEntry>>, Ghost<nat>))
    requires
        tbl(t, 0),
    ensures
        tbl(r.0, 0),
        tbl(r.2, 0),
        keys_lt(r.0, id),
        keys_gt(r.2, id),
        ht(r.0) <= ht(t),
        ht(r.2) <= ht(t),
        (r.1 is Some) == tv(t).contains_key(id),
        r.1 matches Some(e) ==> e == tv(t)[id],
        tv(r.0).union_prefer_right(tv(r.2)) == tv(t).remove(id),
        r.3@ <= c_take() * (ht(t) + 1),
{
    let ghost t0 = t;
    let ghost mut work: nat = 0;
    proof {
        lemma_tbl_len(t0, 0);
        assert(c_split6() == 37 && c_first() == 1 && c_pop() == 6);
    }
    let (a, b, Ghost(c1)) = split(t, id);
    proof {
        lemma_split_cost(t0, a, b, c1);
        lemma_split_tbl(t0, a, b, id, 0);
        work = work + c1;
    }
    let (f, Ghost(c2)) = first(&b);
    let hit = match f {
        Some((k, _)) => k == id,
        None => false,
    };
    proof {
        work = work + c2;
        lemma_take_hit(t0, a, b, id, 0, hit);
    }
    if hit {
        let ghost b0 = b;
        let (b2, k2, e, Ghost(c3)) = pop_min(b);
        proof {
            lemma_take(t0, a, b0, b2, id, k2, e, 0);
            work = work + c3;
        }
        (a, Some(e), b2, Ghost(work))
    } else {
        proof {
            assert(tv(t0).remove(id) =~= tv(t0));
            lemma_split_tbl(t0, a, b, id, 0);
        }
        (a, None, b, Ghost(work))
    }
}

/// Puts request entry `e` back between the tables `lo` and `hi` (`join`), `h` bounding their heights.
fn req_put_w(lo: Tree<Box<ReqEntry>>, e: Box<ReqEntry>, hi: Tree<Box<ReqEntry>>, Ghost(h): Ghost<nat>) -> (r: (
    Tree<Box<ReqEntry>>,
    Ghost<nat>,
))
    requires
        tbl(lo, 0),
        tbl(hi, 0),
        keys_lt(lo, e.id),
        keys_gt(hi, e.id),
        e.id % 4 == 0,
        ht(lo) <= h,
        ht(hi) <= h,
    ensures
        tbl(r.0, 0),
        tv(r.0) == tv(lo).union_prefer_right(tv(hi)).insert(e.id, e),
        r.1@ <= c_join() * (h + 1),
{
    let ghost (a, b) = (lo, hi);
    let k = e.id;
    proof {
        lemma_put_len(a, k, e, b, 0);
    }
    let ghost ev = e;
    let (j, Ghost(c)) = join(lo, k, e, hi);
    proof {
        reveal(keys_mod);
        lemma_put(a, k, ev, b, j, 0);
    }
    (j, Ghost(c))
}

/// `uni`'s `req_take_w`.
// The popped key `k2` is read only by the proof.
#[allow(unused_variables)]
fn uni_take_w(t: Tree<Box<UniEntry>>, id: u64) -> (r: (Tree<Box<UniEntry>>, Option<Box<UniEntry>>, Tree<Box<UniEntry>>, Ghost<nat>))
    requires
        tbl(t, 2),
    ensures
        tbl(r.0, 2),
        tbl(r.2, 2),
        keys_lt(r.0, id),
        keys_gt(r.2, id),
        ht(r.0) <= ht(t),
        ht(r.2) <= ht(t),
        (r.1 is Some) == tv(t).contains_key(id),
        r.1 matches Some(e) ==> e == tv(t)[id],
        tv(r.0).union_prefer_right(tv(r.2)) == tv(t).remove(id),
        r.3@ <= c_take() * (ht(t) + 1),
{
    let ghost t0 = t;
    let ghost mut work: nat = 0;
    proof {
        lemma_tbl_len(t0, 2);
        assert(c_split6() == 37 && c_first() == 1 && c_pop() == 6);
    }
    let (a, b, Ghost(c1)) = split(t, id);
    proof {
        lemma_split_cost(t0, a, b, c1);
        lemma_split_tbl(t0, a, b, id, 2);
        work = work + c1;
    }
    let (f, Ghost(c2)) = first(&b);
    let hit = match f {
        Some((k, _)) => k == id,
        None => false,
    };
    proof {
        work = work + c2;
        lemma_take_hit(t0, a, b, id, 2, hit);
    }
    if hit {
        let ghost b0 = b;
        let (b2, k2, e, Ghost(c3)) = pop_min(b);
        proof {
            lemma_take(t0, a, b0, b2, id, k2, e, 2);
            work = work + c3;
        }
        (a, Some(e), b2, Ghost(work))
    } else {
        proof {
            assert(tv(t0).remove(id) =~= tv(t0));
            lemma_split_tbl(t0, a, b, id, 2);
        }
        (a, None, b, Ghost(work))
    }
}

/// `uni`'s `req_put_w`.
fn uni_put_w(lo: Tree<Box<UniEntry>>, e: Box<UniEntry>, hi: Tree<Box<UniEntry>>, Ghost(h): Ghost<nat>) -> (r: (
    Tree<Box<UniEntry>>,
    Ghost<nat>,
))
    requires
        tbl(lo, 2),
        tbl(hi, 2),
        keys_lt(lo, e.id),
        keys_gt(hi, e.id),
        e.id % 4 == 2,
        ht(lo) <= h,
        ht(hi) <= h,
    ensures
        tbl(r.0, 2),
        tv(r.0) == tv(lo).union_prefer_right(tv(hi)).insert(e.id, e),
        r.1@ <= c_join() * (h + 1),
{
    let ghost (a, b) = (lo, hi);
    let k = e.id;
    proof {
        lemma_put_len(a, k, e, b, 2);
    }
    let ghost ev = e;
    let (j, Ghost(c)) = join(lo, k, e, hi);
    proof {
        reveal(keys_mod);
        lemma_put(a, k, ev, b, j, 2);
    }
    (j, Ghost(c))
}

/// The two tables around a taken entry, joined again without it (`join2`), `h` bounding their heights.
fn tbl_join<V>(lo: Tree<V>, hi: Tree<V>, Ghost(k): Ghost<u64>, Ghost(r): Ghost<u64>, Ghost(h): Ghost<nat>) -> (res: (
    Tree<V>,
    Ghost<nat>,
))
    requires
        tbl(lo, r),
        tbl(hi, r),
        keys_lt(lo, k),
        keys_gt(hi, k),
        k % 4 == r,
        ht(lo) <= h,
        ht(hi) <= h,
    ensures
        tbl(res.0, r),
        tv(res.0) == tv(lo).union_prefer_right(tv(hi)),
        res.1@ <= c_join2() * (h + 1),
{
    proof {
        reveal(keys_mod);
    }
    let ghost (a, b) = (lo, hi);
    proof {
        lemma_put_len(a, k, arbitrary(), b, r);
        assert forall|i: int, j: int| 0 <= i < seq(a).len() && 0 <= j < seq(b).len() implies #[trigger] seq(a)[i].0
            < #[trigger] seq(b)[j].0 by {
            assert(seq(a)[i].0 < k && seq(b)[j].0 > k);
        }
    }
    let (j, Ghost(c)) = join2(lo, hi);
    proof {
        let s = seq(j);
        assert forall|i: int| 0 <= i < s.len() implies (#[trigger] s[i]).0 % 4 == r by {
            if i < seq(a).len() {
                assert(s[i] == seq(a)[i]);
            } else {
                assert(s[i] == seq(b)[i - seq(a).len()]);
            }
        }
        lemma_mview_app(seq(a), seq(b));
    }
    (j, Ghost(c))
}

/// The outputs one input call (`on_stream_data`, `on_stream_reset`, `on_stop_sending`) adds at most: on a request
/// stream, one per event (at most `MAX_REQ_EVENTS`), then an answer's write and STOP_SENDING in place of its event, or
/// a stream error's reset and STOP_SENDING (`feed_req`); a close or a reset elsewhere is one. `MAX_REQ_EVENTS + 2`,
/// proved sufficient by the entry points' ensures (5 fails `feed_req`'s).
pub const MAX_OUTS: usize = 6;

/// The answer frame for `status`, `ANSWER_421` or `ANSWER_501`, copied into an exact buffer: one allocation and its
/// at most 10 bytes.
fn answer_frame(status: u16) -> (r: (Vec<u8>, Ghost<nat>))
    requires
        status == 501 || status == 421,
    ensures
        response_wire(r.0@, empty_response(status)),
        r.1@ <= 11,
{
    if status == 421 {
        let mut d: CapVec<u8> = CapVec::new(6);
        let Ghost(c) = d.push_slice(&ANSWER_421);
        proof {
            lemma_answer_421();
        }
        (d.into_vec(), Ghost(1 + c))
    } else {
        let mut d: CapVec<u8> = CapVec::new(10);
        let Ghost(c) = d.push_slice(&ANSWER_501);
        proof {
            lemma_answer_501();
        }
        (d.into_vec(), Ghost(1 + c))
    }
}

/// Answers the request on `e` itself with an empty `status` response (rejecting it if the
/// peer's limit doesn't admit that) and stops processing it.
fn answer(e: &mut ReqEntry, status: u16, fin: bool, peer: Option<u64>, out: &mut CapVec<Output>) -> (r: Ghost<nat>)
    requires
        old(e).id % 4 == 0,
        old(e).stream.wf(),
        status == 501 || status == 421,
        old(out).wf(),
        old(out)@.len() + 2 <= old(out).cap(),
    ensures
        final(out).wf(),
        final(out).cap() == old(out).cap(),
        final(out)@.len() <= old(out)@.len() + 2,
        r@ <= c_ans(),
        extends(old(out)@, final(out)@),
        answered_outs(
            old(e).id,
            status,
            Ctx { fin, peer, send_open: old(e).send_open },
            added(old(out)@, final(out)@),
        ),
        final(e).id == old(e).id,
        final(e).stream == old(e).stream,
        final(e).trailers == old(e).trailers,
        final(e).head == old(e).head,
        final(e).is_head == old(e).is_head,
        !final(e).rx_open && !final(e).send_open,
        final(e).fin_seen == (old(e).fin_seen || fin),
{
    hide(response_wire);
    let ghost o0 = out@;
    // One unit per output pushed (at most 2), and the limit comparison.
    let ghost mut work: nat = 3;
    proof {
        lemma_added_refl(o0);
        lemma_status_size(status);
    }
    if e.send_open {
        //= https://www.rfc-editor.org/rfc/rfc9114#section-4.2.2
        //# An implementation that
        //# has received this parameter SHOULD NOT send an HTTP message header
        //# that exceeds the indicated size, as the peer will likely refuse to
        //# process it.
        // The section is `:status` and 3 digits: 7 + 3 + 32 = 42 (`lemma_status_size`).
        let fits = match peer {
            None => true,
            Some(l) => 42 <= l,
        };
        if fits {
            let (data, Ghost(cf)) = answer_frame(status);
            proof {
                work = work + cf;
            }
            let w = Output::StreamWrite { stream_id: e.id, data, fin: true };
            out.push(w);
            proof {
                lemma_one_write(o0, out@, w, e.id, empty_response(status));
            }
            let ghost o1 = out@;
            stop(e.id, H3_NO_ERROR, fin, out);
            proof {
                lemma_added_trans(o0, o1, out@);
                assert(added(o0, out@).take(1) =~= added(o0, o1));
                assert(added(o0, out@).skip(1) =~= added(o1, out@));
            }
        } else {
            reject(e.id, fin, out);
        }
    } else {
        stop(e.id, H3_NO_ERROR, fin, out);
    }
    e.rx_open = false;
    e.send_open = false;
    e.fin_seen = e.fin_seen || fin;
    Ghost(work)
}

/// `answer`'s cost: the limit comparison, at most 2 outputs, and `answer_frame`'s buffer, one allocation and its at
/// most 10 bytes.
#[verifier::inline]
spec fn c_ans() -> nat {
    14
}

/// STOP_SENDING with `code` unless `fin`.
fn stop(id: u64, code: u64, fin: bool, out: &mut CapVec<Output>)
    requires
        old(out).wf(),
        old(out)@.len() + 1 <= old(out).cap(),
    ensures
        final(out).wf(),
        final(out).cap() == old(out).cap(),
        final(out)@.len() <= old(out)@.len() + 1,
        extends(old(out)@, final(out)@),
        added(old(out)@, final(out)@) == stop_outs(id, code, fin),
{
    let ghost o0 = out@;
    proof {
        lemma_added_refl(o0);
    }
    if !fin {
        let b = Output::StopSending { stream_id: id, code };
        out.push(b);
        proof {
            lemma_added_push(o0, o0, b);
            assert(added(o0, out@) =~= stop_outs(id, code, fin));
        }
    }
}

fn reject(id: u64, fin: bool, out: &mut CapVec<Output>)
    requires
        old(out).wf(),
        old(out)@.len() + 2 <= old(out).cap(),
    ensures
        final(out).wf(),
        final(out).cap() == old(out).cap(),
        final(out)@.len() <= old(out)@.len() + 2,
        extends(old(out)@, final(out)@),
        added(old(out)@, final(out)@) == rejected_outs(id, fin),
{
    let ghost o0 = out@;
    proof {
        lemma_added_refl(o0);
    }
    let a = Output::ResetStream { stream_id: id, code: H3_REQUEST_REJECTED };
    out.push(a);
    proof {
        lemma_added_push(o0, o0, a);
    }
    let ghost o1 = out@;
    stop(id, H3_REQUEST_REJECTED, fin, out);
    proof {
        lemma_added_trans(o0, o1, out@);
        assert(added(o0, o1) =~= seq![a@]);
    }
}

proof fn lemma_answered_shape(id: u64, status: u16, cx: Ctx, o: Seq<SpecOutput>)
    requires
        answered_outs(id, status, cx, o),
        id % 4 == 0,
    ensures
        req_only(o),
        no_close(o),
        !has_request(o),
{
    if cx.send_open && fits_peer(cx.peer, fields_size(resp_fields(empty_response(status)))) {
        assert(o.take(1)[0] == o[0]);
        if !cx.fin {
            assert(o.skip(1)[0] == o[1]);
        }
    } else if cx.send_open && !cx.fin {
        assert(o[1] == o.skip(1)[0]);
    }
    assert(!has_request(o)) by {
        if has_request(o) {
            let i = choose|i: int| 0 <= i < o.len() && (#[trigger] o[i]) is Request;
            if i > 0 {
                assert(o[i] == o.skip(1)[i - 1]);
            }
        }
    }
}

proof fn lemma_head_req_push(a: Seq<SpecOutput>, x: SpecOutput)
    ensures
        head_req(a.push(x)) == (head_req(a) || is_head_request(x)),
{
    if head_req(a) {
        let i = choose|i: int| 0 <= i < a.len() && is_head_request(#[trigger] a[i]);
        assert(a.push(x)[i] == a[i]);
    }
    if is_head_request(x) {
        assert(a.push(x)[a.len() as int] == x);
    }
    if head_req(a.push(x)) {
        let i = choose|i: int| 0 <= i < a.push(x).len() && is_head_request(#[trigger] a.push(x)[i]);
        if i < a.len() {
            assert(a.push(x)[i] == a[i]);
        }
    }
}

/// `b` adds no Request output.
proof fn lemma_head_req_concat(a: Seq<SpecOutput>, b: Seq<SpecOutput>)
    requires
        !has_request(b),
    ensures
        head_req(a + b) == head_req(a),
{
    if head_req(a) {
        let i = choose|i: int| 0 <= i < a.len() && is_head_request(#[trigger] a[i]);
        assert((a + b)[i] == a[i]);
    }
    if head_req(a + b) {
        let i = choose|i: int| 0 <= i < (a + b).len() && is_head_request(#[trigger] (a + b)[i]);
        if i >= a.len() {
            assert((a + b)[i] == b[i - a.len()]);
            assert(b[i - a.len()] is Request);
        } else {
            assert((a + b)[i] == a[i]);
        }
    }
}

proof fn lemma_has_request_push(a: Seq<SpecOutput>, x: SpecOutput)
    ensures
        has_request(a.push(x)) == (has_request(a) || x is Request),
{
    if has_request(a) {
        let i = choose|i: int| 0 <= i < a.len() && (#[trigger] a[i]) is Request;
        assert(a.push(x)[i] == a[i]);
    }
    if x is Request {
        assert(a.push(x)[a.len() as int] == x);
    }
    if has_request(a.push(x)) {
        let i = choose|i: int| 0 <= i < a.push(x).len() && (#[trigger] a.push(x)[i]) is Request;
        if i < a.len() {
            assert(a.push(x)[i] == a[i]);
        }
    }
}

/// `b` adds no Request output.
proof fn lemma_has_request_concat(a: Seq<SpecOutput>, b: Seq<SpecOutput>)
    requires
        !has_request(b),
    ensures
        has_request(a + b) == has_request(a),
{
    if has_request(a) {
        let i = choose|i: int| 0 <= i < a.len() && (#[trigger] a[i]) is Request;
        assert((a + b)[i] == a[i]);
    }
    if has_request(a + b) {
        let i = choose|i: int| 0 <= i < (a + b).len() && (#[trigger] (a + b)[i]) is Request;
        if i < a.len() {
            assert((a + b)[i] == a[i]);
        } else {
            assert((a + b)[i] == b[i - a.len()]);
        }
    }
}

/// Concatenating request-stream outputs: `b` may end with a CloseConnection.
proof fn lemma_req_concat(a: Seq<SpecOutput>, b: Seq<SpecOutput>, closing: bool)
    requires
        req_only(a),
        no_close(a),
        req_only(b),
        outs_ok(b, closing),
    ensures
        req_only(a + b),
        outs_ok(a + b, closing),
{
    let c = a + b;
    assert forall|i: int| 0 <= i < c.len() implies ctrl_free(#[trigger] c[i]) && stop_ok(c[i])
        && ctrl_open(c[i]) && body_ok(c[i]) by {
        if i < a.len() {
            assert(c[i] == a[i]);
        } else {
            assert(c[i] == b[i - a.len()]);
        }
    }
    assert forall|i: int| 0 <= i < c.len() && (#[trigger] c[i]) is CloseConnection implies closing
        && i == c.len() - 1 by {
        if i < a.len() {
            assert(c[i] == a[i]);
        } else {
            assert(c[i] == b[i - a.len()]);
        }
    }
    if closing {
        assert(c.last() == b.last());
    }
}

proof fn lemma_err_outs_shape(id: u64, e: Option<ReqError>, cx: Ctx)
    requires
        id % 4 == 0,
    ensures
        req_only(err_outs(id, e, cx)),
        outs_ok(err_outs(id, e, cx), e matches Some(ReqError::Connection(_))),
{
    if let Some(ReqError::Stream(c)) = e {
        let a = if cx.send_open {
            seq![SpecOutput::ResetStream { stream_id: id, code: c }]
        } else {
            Seq::<SpecOutput>::empty()
        };
        let b = stop_outs(id, c, cx.fin);
        assert forall|i: int| 0 <= i < (a + b).len() implies !((#[trigger] (a + b)[i]) is CloseConnection) && ctrl_free((a + b)[i]) && stop_ok((a + b)[i]) && ctrl_open((a + b)[i]) && body_ok((a + b)[i]) by {
            if i < a.len() {
                assert((a + b)[i] == a[i]);
            } else {
                assert((a + b)[i] == b[i - a.len()]);
            }
        }
    }
}

/// The `k`-th new event, delivered as `w`, moves the loop invariant past it.
proof fn lemma_deliver(
    id: u64,
    ev: Seq<SpecReqEvent>,
    k: int,
    tr: Fields,
    tr2: Fields,
    tr0: Fields,
    err: Option<ReqError>,
    cx: Ctx,
    o0: Seq<Output>,
    o1: Seq<Output>,
    w: Output,
)
    requires
        0 <= k < ev.len(),
        extends(o0, o1),
        forall|x: Seq<SpecOutput>| #[trigger]
            req_outs(id, ev.skip(k), tr, err, cx, x) ==> req_outs(
                id,
                ev,
                tr0,
                err,
                cx,
                added(o0, o1) + x,
            ),
        match ev[k] {
            SpecReqEvent::Head(SpecRequestHead::Request(r)) => http_scheme(r.scheme) && w@
                == SpecOutput::Request { stream_id: id, head: r } && tr2 == tr,
            SpecReqEvent::BodyBytes(d) => w@ == SpecOutput::RequestBody { stream_id: id, data: d }
                && tr2 == tr,
            SpecReqEvent::End => w@ == SpecOutput::RequestEnd { stream_id: id, trailers: tr } && tr2
                == Seq::<(Seq<u8>, Seq<u8>)>::empty(),
            _ => false,
        },
    ensures
        extends(o0, o1.push(w)),
        added(o0, o1.push(w)) == added(o0, o1).push(w@),
        forall|x: Seq<SpecOutput>| #[trigger]
            req_outs(id, ev.skip(k + 1), tr2, err, cx, x) ==> req_outs(
                id,
                ev,
                tr0,
                err,
                cx,
                added(o0, o1.push(w)) + x,
            ),
{
    lemma_added_push(o0, o1, w);
    let s = ev.skip(k);
    assert(s.skip(1) =~= ev.skip(k + 1));
    assert(s[0] == ev[k]);
    assert forall|x: Seq<SpecOutput>| #[trigger]
        req_outs(id, ev.skip(k + 1), tr2, err, cx, x) implies req_outs(
        id,
        ev,
        tr0,
        err,
        cx,
        added(o0, o1.push(w)) + x,
    ) by {
        let y = seq![w@] + x;
        assert(y[0] == w@);
        assert(y.skip(1) =~= x);
        assert(req_outs(id, s, tr, err, cx, y));
        assert(added(o0, o1) + y =~= added(o0, o1.push(w)) + x);
    }
}

/// The `k`-th new event is answered by the connection: the outputs are complete.
proof fn lemma_answer_done(
    id: u64,
    ev: Seq<SpecReqEvent>,
    k: int,
    tr: Fields,
    tr0: Fields,
    err: Option<ReqError>,
    cx: Ctx,
    status: u16,
    o0: Seq<Output>,
    o1: Seq<Output>,
    o2: Seq<Output>,
)
    requires
        0 <= k < ev.len(),
        extends(o0, o1),
        extends(o1, o2),
        forall|x: Seq<SpecOutput>| #[trigger]
            req_outs(id, ev.skip(k), tr, err, cx, x) ==> req_outs(
                id,
                ev,
                tr0,
                err,
                cx,
                added(o0, o1) + x,
            ),
        answered_outs(id, status, cx, added(o1, o2)),
        match ev[k] {
            SpecReqEvent::Head(SpecRequestHead::Connect { .. }) => status == 501,
            SpecReqEvent::Head(SpecRequestHead::Request(r)) => !http_scheme(r.scheme) && status
                == 421,
            _ => false,
        },
    ensures
        extends(o0, o2),
        added(o0, o2) == added(o0, o1) + added(o1, o2),
        req_outs(id, ev, tr0, err, cx, added(o0, o2)),
{
    lemma_added_trans(o0, o1, o2);
    let s = ev.skip(k);
    assert(s[0] == ev[k]);
    assert(req_outs(id, s, tr, err, cx, added(o1, o2)));
}

/// `deliver`'s answered return at event `k`: the outputs are complete and keep `deliver`'s output shape, and the head
/// flags see nothing new (an answer is never a `Request`).
proof fn lemma_answered_ret(
    id: u64,
    ev: Seq<SpecReqEvent>,
    k: int,
    tr: Fields,
    tr0: Fields,
    err: Option<ReqError>,
    cx: Ctx,
    status: u16,
    o0: Seq<Output>,
    o1: Seq<Output>,
    o2: Seq<Output>,
)
    requires
        0 <= k < ev.len(),
        id % 4 == 0,
        extends(o0, o1),
        extends(o1, o2),
        req_only(added(o0, o1)),
        no_close(added(o0, o1)),
        forall|x: Seq<SpecOutput>| #[trigger]
            req_outs(id, ev.skip(k), tr, err, cx, x) ==> req_outs(
                id,
                ev,
                tr0,
                err,
                cx,
                added(o0, o1) + x,
            ),
        answered_outs(id, status, cx, added(o1, o2)),
        match ev[k] {
            SpecReqEvent::Head(SpecRequestHead::Connect { .. }) => status == 501,
            SpecReqEvent::Head(SpecRequestHead::Request(r)) => !http_scheme(r.scheme) && status
                == 421,
            _ => false,
        },
    ensures
        extends(o0, o2),
        req_only(added(o0, o2)),
        no_close(added(o0, o2)),
        req_outs(id, ev, tr0, err, cx, added(o0, o2)),
        has_request(added(o0, o2)) == has_request(added(o0, o1)),
        head_req(added(o0, o2)) == head_req(added(o0, o1)),
        !no_internal(ev),
{
    lemma_answer_done(id, ev, k, tr, tr0, err, cx, status, o0, o1, o2);
    lemma_answered_shape(id, status, cx, added(o1, o2));
    lemma_req_concat(added(o0, o1), added(o1, o2), false);
    lemma_has_request_concat(added(o0, o1), added(o1, o2));
    lemma_head_req_concat(added(o0, o1), added(o1, o2));
    assert(internal_head(ev[k]));
}

/// The buffers an event's value frees when it is dropped: a request head's four strings, its field list and each
/// line's two; a CONNECT's authority; a body; a trailer list and each line's two.
spec fn ev_frees(e: SpecReqEvent) -> nat {
    match e {
        SpecReqEvent::Head(SpecRequestHead::Request(r)) => 5 + 2 * r.headers.len(),
        SpecReqEvent::Head(SpecRequestHead::Connect { .. }) => 1,
        SpecReqEvent::BodyBytes(_) => 1,
        SpecReqEvent::Trailers(t) => 1 + 2 * t.len(),
        SpecReqEvent::End => 0,
    }
}

/// The buffers events free when they are dropped.
spec fn frees(s: Seq<SpecReqEvent>) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        frees(s.drop_last()) + ev_frees(s.last())
    }
}

/// Events free at most 5 buffers each and 2 per field line they carry.
proof fn lemma_frees(s: Seq<SpecReqEvent>)
    ensures
        frees(s) <= 5 * s.len() + 2 * request::ev_lines(s),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_frees(s.drop_last());
    }
}

/// The events from `k` on carry at most the lines all of them do.
proof fn lemma_lines_suffix(s: Seq<SpecReqEvent>, k: int)
    requires
        0 <= k <= s.len(),
    ensures
        request::ev_lines(s.skip(k)) <= request::ev_lines(s),
{
    request::lemma_tally_append(s.take(k), s.skip(k));
    assert(s.take(k) + s.skip(k) =~= s);
}

/// `deliver`'s cost on an answered return at event `k`: the work so far, `extra` (the event's step, the scheme check,
/// the answer and the reversed buffer's free) and the events it drops stay within its bound. The lower bound on
/// `extra` is the catch for an early return that drops its iteration's step or a free (RCA 2026-11-21-early-return-cost).
proof fn lemma_answered_cost(ev: Seq<SpecReqEvent>, k: int, work: nat, extra: nat)
    requires
        0 <= k < ev.len(),
        work <= ev.len() + 2 + 31 * k,
        c_step() + 1 <= extra <= c_step() + 20 + c_ans() + 1,
    ensures
        work + extra + frees(ev.skip(k)) <= c_dlv() * (ev.len() + 1) + 2 * request::ev_lines(ev),
{
    lemma_frees(ev.skip(k));
    lemma_lines_suffix(ev, k);
}

/// The events before `k` carry at most the lines all of them do.
proof fn lemma_lines_prefix(s: Seq<SpecReqEvent>, k: int)
    requires
        0 <= k <= s.len(),
    ensures
        request::ev_lines(s.take(k)) <= request::ev_lines(s),
{
    request::lemma_tally_append(s.take(k), s.skip(k));
    assert(s.take(k) + s.skip(k) =~= s);
}

/// The events before `k + 1` carry the lines of those before `k` and event `k`'s.
proof fn lemma_lines_step(s: Seq<SpecReqEvent>, k: int)
    requires
        0 <= k < s.len(),
    ensures
        request::ev_lines(s.take(k + 1)) == request::ev_lines(s.take(k)) + request::ev_line(s[k]),
{
    assert(s.take(k + 1).drop_last() =~= s.take(k));
    assert(s.take(k + 1).last() == s[k]);
}

/// One more output that is request-only and no close keeps `req_only` and `no_close`.
proof fn lemma_added_kept(a0: Seq<SpecOutput>, a1: Seq<SpecOutput>)
    requires
        req_only(a0),
        no_close(a0),
        a1 == a0 || (a1 == a0.push(a1.last()) && ctrl_free(a1.last()) && stop_ok(a1.last()) && body_ok(a1.last())
            && !(a1.last() is CloseConnection)),
    ensures
        req_only(a1),
        no_close(a1),
{
    if a1 != a0 {
        assert forall|i: int| 0 <= i < a1.len() implies ctrl_free(#[trigger] a1[i]) && stop_ok(a1[i]) && body_ok(
            a1[i],
        ) && !(a1[i] is CloseConnection) by {
            if i < a1.len() - 1 {
                assert(a1[i] == a0[i]);
            }
        }
    }
}

/// Outputs what the request machine's new events `evs` mean, in order; stops at a request the
/// connection answers itself (`true`). Otherwise (`false`) the outputs followed by the error's
/// outputs are `req_outs`.
fn deliver(
    e: &mut ReqEntry,
    evs: CapVec<ReqEvent>,
    fin: bool,
    peer: Option<u64>,
    Ghost(ev): Ghost<Seq<SpecReqEvent>>,
    Ghost(err): Ghost<Option<ReqError>>,
    Ghost(cx): Ghost<Ctx>,
    out: &mut CapVec<Output>,
) -> (r: (bool, Ghost<nat>))
    requires
        old(out).wf(),
        old(out)@.len() + ev.len() + 1 <= old(out).cap(),
        ev == request::views(evs@),
        cx == (Ctx { fin, peer, send_open: old(e).send_open }),
        request::bodies_from(evs@, 0),
        old(e).id % 4 == 0,
        old(e).stream.wf(),
        old(e).rx_open,
    ensures
        final(e).id == old(e).id,
        final(e).stream == old(e).stream,
        extends(old(out)@, final(out)@),
        req_only(added(old(out)@, final(out)@)),
        no_close(added(old(out)@, final(out)@)),
        r.0 ==> req_outs(
            old(e).id,
            ev,
            fields_view(old(e).trailers@),
            err,
            cx,
            added(old(out)@, final(out)@),
        ),
        !r.0 ==> req_outs(
            old(e).id,
            ev,
            fields_view(old(e).trailers@),
            err,
            cx,
            added(old(out)@, final(out)@) + err_outs(old(e).id, err, cx),
        ),
        r.0 == !no_internal(ev),
        final(e).head == (old(e).head || has_request(added(old(out)@, final(out)@))),
        final(e).is_head == (old(e).is_head || head_req(added(old(out)@, final(out)@))),
        r.0 ==> !final(e).rx_open && !final(e).send_open && final(e).fin_seen == (old(
            e,
        ).fin_seen || fin),
        !r.0 ==> final(e).rx_open && final(e).send_open == old(e).send_open
            && final(e).fin_seen == old(e).fin_seen,
        r.1@ <= c_dlv() * (ev.len() + 1) + 2 * request::ev_lines(ev),
        final(e).trailers@.len() <= old(e).trailers@.len() + request::ev_lines(ev),
        final(out).wf(),
        final(out).cap() == old(out).cap(),
        final(out)@.len() <= old(out)@.len() + ev.len() + (if r.0 { 1nat } else { 0nat }),
{
    let ghost id = e.id;
    let ghost o0 = out@;
    let ghost tr0 = fields_view(e.trailers@);
    let n = evs.len();
    let ghost evs0 = evs@;
    let (rv0, Ghost(wr)) = rev(evs.into_vec());
    let mut rv = rv0;
    let ghost mut work: nat = wr;
    let mut k: usize = 0;
    proof {
        assert forall|i: int| 0 <= i < rv@.len() implies request::body_nonempty(#[trigger] rv@[i]) by {
            assert(rv@[i] == evs0[n - 1 - i]);
        }
        lemma_added_refl(o0);
        assert(ev.skip(0) =~= ev);
        assert forall|x: Seq<SpecOutput>| #[trigger]
            req_outs(id, ev.skip(0), tr0, err, cx, x) implies req_outs(
            id,
            ev,
            tr0,
            err,
            cx,
            added(o0, out@) + x,
        ) by {
            assert(added(o0, out@) + x =~= x);
        }
    }
    while k < n
        invariant
            k <= n,
            n == ev.len(),
            rv@.len() + k == n,
            forall|i: int| 0 <= i < rv@.len() ==> (#[trigger] rv@[i])@ == ev[n - 1 - i],
            forall|i: int| 0 <= i < rv@.len() ==> request::body_nonempty(#[trigger] rv@[i]),
            extends(o0, out@),
            forall|x: Seq<SpecOutput>| #[trigger]
                req_outs(id, ev.skip(k as int), fields_view(e.trailers@), err, cx, x) ==> req_outs(
                    id,
                    ev,
                    tr0,
                    err,
                    cx,
                    added(o0, out@) + x,
                ),
            req_only(added(o0, out@)),
            no_close(added(o0, out@)),
            o0 == old(out)@,
            tr0 == fields_view(old(e).trailers@),
            id == old(e).id,
            e.id == id,
            id % 4 == 0,
            e.stream == old(e).stream,
            old(e).stream.wf(),
            e.rx_open,
            e.fin_seen == old(e).fin_seen,
            e.send_open == old(e).send_open,
            cx == (Ctx { fin, peer, send_open: old(e).send_open }),
            forall|i: int| 0 <= i < k ==> !internal_head(#[trigger] ev[i]),
            e.head == (old(e).head || has_request(added(o0, out@))),
            e.is_head == (old(e).is_head || head_req(added(o0, out@))),
            work <= n + 2 + 31 * k,
            e.trailers@.len() <= old(e).trailers@.len() + request::ev_lines(ev.take(k as int)),
            ev.len() == n,
            out.wf(),
            out.cap() == old(out).cap(),
            out@.len() <= o0.len() + k,
            o0.len() + n + 1 <= out.cap(),
        decreases n - k,
    {
        let ghost tr = fields_view(e.trailers@);
        let ghost o1 = out@;
        let x = match rv.pop() {
            Some(x) => x,
            None => {
                proof {
                    assert(false);
                }
                return (false, Ghost(work));
            },
        };
        proof {
            assert(x@ == ev[k as int]);
            assert(request::body_nonempty(x));
        }
        // The status the connection answers this event with itself (D10), 0 for none: 501 for a CONNECT, which we do
        // not implement, and 421 for a scheme other than http/https, for which we are not an origin.
        //= https://www.rfc-editor.org/rfc/rfc9110#section-9.1
        //# An origin server that receives a
        //# request method that is unrecognized or not implemented SHOULD respond
        //# with the 501 (Not Implemented) status code.
        //= https://www.rfc-editor.org/rfc/rfc9110#section-15.5.20
        //# An origin server (or
        //# gateway acting on behalf of the origin server) sends 421 to reject a
        //# target URI that does not match an origin for which the server has
        //# been configured (Section 4.3.1) or does not match the connection
        //# context over which the request was received (Section 7.4).
        //= https://www.rfc-editor.org/rfc/rfc9110#section-7.4
        //# Unless the connection is from a trusted gateway, an origin server
        //# MUST reject a request if any scheme-specific requirements for the
        //# target URI are not met.
        let ghost mut cs: nat = 0;
        let status: u16 = match &x {
            ReqEvent::Head(RequestHead::Connect { .. }) => 501,
            ReqEvent::Head(RequestHead::Request(req)) => {
                let (http, Ghost(c)) = is_http_scheme(req.scheme.as_slice());
                proof {
                    cs = c;
                }
                if http {
                    0
                } else {
                    421
                }
            },
            _ => 0,
        };
        if status != 0 {
            let Ghost(ca) = answer(e, status, fin, peer, out);
            // This event's step, as at the loop's end, its scheme check and answer, and the reversed buffer's free (1);
            // `lemma_answered_cost` requires the step and the free to be in it. The answered event and those after it
            // are dropped here.
            let ghost extra: nat = c_step() + cs + ca + 1;
            proof {
                lemma_answered_ret(id, ev, k as int, tr, tr0, err, cx, status, o0, o1, out@);
                lemma_answered_cost(ev, k as int, work, extra);
                lemma_lines_prefix(ev, k as int);
            }
            return (true, Ghost(work + extra + frees(ev.skip(k as int))));
        }
        match x {
            ReqEvent::Head(RequestHead::Connect { .. }) => {
                proof {
                    assert(false);
                }
                return (false, Ghost(work));
            },
            ReqEvent::Head(RequestHead::Request(req)) => {
                e.head = true;
                let head_method: [u8; 4] = [72u8, 69u8, 65u8, 68u8];
                proof {
                    assert(head_method@ =~= lit_head_method());
                }
                let (is_hm, Ghost(ch)) = eq_bytes_w(req.method.as_slice(), &head_method);
                proof {
                    // at most c_eq·(4 + 1) = 5, against the 4-byte literal
                    assert(ch <= 5);
                    work = work + cs + ch;
                }
                e.is_head = e.is_head || is_hm;
                let w = Output::Request { stream_id: e.id, head: req };
                proof {
                    lemma_deliver(id, ev, k as int, tr, tr, tr0, err, cx, o0, o1, w);
                    lemma_has_request_push(added(o0, o1), w@);
                    lemma_head_req_push(added(o0, o1), w@);
                }
                out.push(w);
            },
            ReqEvent::Body(d) => {
                let w = Output::RequestBody { stream_id: e.id, data: d };
                proof {
                    lemma_deliver(id, ev, k as int, tr, tr, tr0, err, cx, o0, o1, w);
                    lemma_has_request_push(added(o0, o1), w@);
                    lemma_head_req_push(added(o0, o1), w@);
                }
                out.push(w);
            },
            ReqEvent::Trailers(t) => {
                e.trailers = t;
                proof {
                    let s = ev.skip(k as int);
                    assert(s[0] == ev[k as int]);
                    assert(s.skip(1) =~= ev.skip(k + 1));
                    assert forall|x: Seq<SpecOutput>| #[trigger]
                        req_outs(id, ev.skip(k + 1), fields_view(e.trailers@), err, cx, x) implies req_outs(
                        id,
                        ev,
                        tr0,
                        err,
                        cx,
                        added(o0, out@) + x,
                    ) by {
                        assert(req_outs(id, s, tr, err, cx, x));
                    }
                }
            },
            ReqEvent::End => {
                let mut t: Vec<FieldLine> = Vec::new();
                core::mem::swap(&mut t, &mut e.trailers);
                let w = Output::RequestEnd { stream_id: e.id, trailers: t };
                proof {
                    assert(fields_view(e.trailers@) =~= Seq::<(Seq<u8>, Seq<u8>)>::empty());
                    lemma_deliver(id, ev, k as int, tr, Seq::empty(), tr0, err, cx, o0, o1, w);
                    lemma_has_request_push(added(o0, o1), w@);
                    lemma_head_req_push(added(o0, o1), w@);
                }
                out.push(w);
            },
        }
        proof {
            lemma_added_kept(added(o0, o1), added(o0, out@));
            lemma_lines_step(ev, k as int);
        }
        k += 1;
        proof {
            // a request head's scheme and method checks are charged above, at most 20 + 5
            work = work + c_step();
        }
    }
    proof {
        assert(ev.skip(n as int) =~= Seq::<SpecReqEvent>::empty());
        assert(req_outs(id, ev.skip(n as int), fields_view(e.trailers@), err, cx, err_outs(id, err, cx)));
        assert(ev.take(n as int) =~= ev);
    }
    (false, Ghost(work + 1))
}

/// The cost constant of `deliver`, per event: at most 31 (an `http` scheme check 20, a HEAD method check 5, the step
/// `c_step` 6) and one for the reversal; the reversal's allocation and the two frees fit the constant term. On an
/// answered return the dropped events (`frees`, at most 5 each plus 2 per field line) add `2·ev_lines(ev)` to the bound.
#[verifier::inline]
spec fn c_dlv() -> nat {
    32
}

/// `deliver`'s step per event, wherever the event's iteration ends (the loop's end or an answered return): the pop,
/// the output push and the event's move. One name for both paths, so an early return cannot drop part of it.
#[verifier::inline]
spec fn c_step() -> nat {
    6
}

/// Outputs what the request machine's error means (`err_outs`); `true` for a connection error.
fn push_err(
    id: u64,
    res: &Result<(), ReqError>,
    send_open: bool,
    fin: bool,
    Ghost(cx): Ghost<Ctx>,
    out: &mut CapVec<Output>,
) -> (closing: bool)
    requires
        cx.send_open == send_open,
        cx.fin == fin,
        old(out).wf(),
        old(out)@.len() + 2 <= old(out).cap(),
    ensures
        final(out).wf(),
        final(out).cap() == old(out).cap(),
        final(out)@.len() <= old(out)@.len() + 2,
        extends(old(out)@, final(out)@),
        added(old(out)@, final(out)@) == err_outs(id, request::err_of(*res), cx),
        closing == (*res matches Err(ReqError::Connection(_))),
{
    let ghost o0 = out@;
    proof {
        lemma_added_refl(o0);
    }
    match res {
        Err(ReqError::Connection(c)) => {
            let w = Output::CloseConnection { code: *c };
            out.push(w);
            proof {
                lemma_added_push(o0, o0, w);
                assert(added(o0, out@) =~= err_outs(id, request::err_of(*res), cx));
            }
            true
        },
        Err(ReqError::Stream(c)) => {
            if send_open {
                let a = Output::ResetStream { stream_id: id, code: *c };
                out.push(a);
                proof {
                    lemma_added_push(o0, o0, a);
                    assert(added(o0, out@) =~= seq![a@]);
                }
            }
            let ghost o1 = out@;
            stop(id, *c, fin, out);
            proof {
                lemma_added_trans(o0, o1, out@);
                assert(added(o0, out@) =~= err_outs(id, request::err_of(*res), cx));
            }
            false
        },
        Ok(()) => false,
    }
}

/// The request-machine error of a call, from the stream's bytes.
pub open spec fn req_err(all: Seq<u8>, fin: bool) -> Option<ReqError> {
    request::rfc_request_stream(all, fin).1
}

/// `feed_req`'s cost per byte of `d + 16`: `on_data`'s `c_req()`, `deliver`'s 2 per field line (at most 77 per byte),
/// and the constant terms (the event buffer, `c_dlv()` for each of at most 5 events, and the error's 2 outputs: 163, at
/// most 11 per byte of the 16).
#[verifier::inline]
spec fn c_fr() -> nat {
    82245
}

/// `feed_req`'s cost per byte held before the call: `on_data`'s `request::c_frame()` and `deliver`'s 2 per field line.
#[verifier::inline]
spec fn c_frb() -> nat {
    41175
}

/// What `feed_req` ensures of the entry (`e0` to `e1`) and the outputs (`o0` to `o1`), its cost aside: the machine fed
/// `data`, and the outputs what its new events and error mean (`closing`: the connection must close).
#[verifier::opaque]
spec fn fed_ok(
    e0: ReqEntry,
    e1: ReqEntry,
    o0: CapVec<Output>,
    o1: CapVec<Output>,
    data: Seq<u8>,
    fin: bool,
    peer: Option<u64>,
    closing: bool,
) -> bool {
    let ne = e1.stream.emitted().skip(e0.stream.emitted().len() as int);
    let err = req_err(e1.stream.all(), fin);
    &&& o1.wf()
    &&& o1.cap() == o0.cap()
    &&& o1@.len() <= o0@.len() + MAX_OUTS
    &&& extends(o0@, o1@)
    &&& e1.stream.all() == e0.stream.all() + data
    &&& e1.stream.emitted().len() >= e0.stream.emitted().len()
    &&& e1.stream.emitted().take(e0.stream.emitted().len() as int) == e0.stream.emitted()
    &&& request::concat_bodies(e1.stream.emitted()) == request::rfc_request_stream(e1.stream.all(), fin).0
    &&& req_outs(e0.id, ne, fields_view(e0.trailers@), err, Ctx { fin, peer, send_open: e0.send_open }, added(o0@, o1@))
    &&& outs_ok(added(o0@, o1@), closing)
    &&& req_only(added(o0@, o1@))
    &&& e1.fin_seen == fin
    &&& e1.rx_open == (err is None && !fin && no_internal(ne))
    &&& !closing ==> e1.send_open == (e0.send_open && err is None && no_internal(ne))
    &&& e1.head == (e0.head || has_request(added(o0@, o1@)))
    &&& e1.is_head == (e0.is_head || head_req(added(o0@, o1@)))
}

/// `fed_ok` from its parts.
proof fn lemma_fed_ok(
    e0: ReqEntry,
    e1: ReqEntry,
    o0: CapVec<Output>,
    o1: CapVec<Output>,
    data: Seq<u8>,
    fin: bool,
    peer: Option<u64>,
    closing: bool,
)
    requires
        o1.wf(),
        o1.cap() == o0.cap(),
        o1@.len() <= o0@.len() + MAX_OUTS,
        extends(o0@, o1@),
        e1.stream.all() == e0.stream.all() + data,
        e1.stream.emitted().len() >= e0.stream.emitted().len(),
        e1.stream.emitted().take(e0.stream.emitted().len() as int) == e0.stream.emitted(),
        request::concat_bodies(e1.stream.emitted()) == request::rfc_request_stream(e1.stream.all(), fin).0,
        req_outs(
            e0.id,
            e1.stream.emitted().skip(e0.stream.emitted().len() as int),
            fields_view(e0.trailers@),
            req_err(e1.stream.all(), fin),
            Ctx { fin, peer, send_open: e0.send_open },
            added(o0@, o1@),
        ),
        outs_ok(added(o0@, o1@), closing),
        req_only(added(o0@, o1@)),
        e1.fin_seen == fin,
        e1.rx_open == (req_err(e1.stream.all(), fin) is None && !fin && no_internal(
            e1.stream.emitted().skip(e0.stream.emitted().len() as int),
        )),
        !closing ==> e1.send_open == (e0.send_open && req_err(e1.stream.all(), fin) is None && no_internal(
            e1.stream.emitted().skip(e0.stream.emitted().len() as int),
        )),
        e1.head == (e0.head || has_request(added(o0@, o1@))),
        e1.is_head == (e0.is_head || head_req(added(o0@, o1@))),
    ensures
        fed_ok(e0, e1, o0, o1, data, fin, peer, closing),
{
    hide(req_outs);
    reveal(fed_ok);
}

/// `uni_data`'s cost: the take (`ct`), `on_data` (`cu`), at most `2·d + b + 13·(h + 1) + 9` for the settings, the put
/// or the join, the boxes, the output and the dropped stream's buffers, and the `n` events' frees (`n <= d / 3 + 1`).
proof fn lemma_uni_cost(work: nat, ct: nat, cu: nat, h: nat, d: nat, b: nat, n: nat)
    requires
        ct <= c_take() * (h + 1),
        cu <= uni::c_uni() * (d + 16) + uni::c_uni_frame() * b,
        n <= d / 3 + 1,
        work <= ct + cu + 2 * d + b + 13 * (h + 1) + 9 + n,
    ensures
        work <= c_ud() * (d + 16) + uni::c_uni_frame() * b + b + c_take() * (h + 1) + 13 * (h + 1),
{
}

/// What `uni_data` reads of `UniStream::on_data`'s ensures (`uni::fed`), the events buffer `e0` empty before.
proof fn lemma_fed_facts(
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
)
    requires
        uni::fed(s0, s1, data, fin, seen0, seen1, e0, e1, r, cost),
        e0@ == Seq::<UniEvent>::empty(),
    ensures
        s1.wf(),
        s1.done() == (r is Err || fin),
        e1.wf(),
        e1.cap() == e0.cap(),
        cost <= uni::c_uni() * (data.len() + 16) + uni::c_uni_frame() * s0.buffered(),
        2 * uni::ev_pairs(uni::views(e1@)) <= data.len() + s0.buffered(),
{
    assert(e1@.skip(0) =~= e1@);
}

/// What `uni_data` ensures, its cost aside.
#[verifier::opaque]
spec fn uni_done(c0: H3Conn, c1: H3Conn, o0: CapVec<Output>, o1: CapVec<Output>, id: u64, data: Seq<u8>, fin: bool) -> bool {
    &&& o1.wf()
    &&& o1.cap() == o0.cap()
    &&& o1@.len() <= o0@.len() + 1
    &&& step(c0, c1, o0@, o1@)
    &&& c1.goaways() == c0.goaways()
    &&& frame(c0, c1, Some(id))
    &&& uni_fed(c0, c1, id, data, fin, added(o0@, o1@))
    &&& c1.highest == c0.highest
}

/// `uni_data`'s ensures, its cost aside: uni stream `id`'s entry `e0` (or a fresh one) fed into `e` (`uni::fed`, its
/// events `ev1`) and its history recorded; on an error the connection closed with the error's code, else the settings
/// applied and the tables updated: `e` kept, or forgotten at its FIN.
proof fn lemma_uni_done(
    c0: H3Conn,
    c1: H3Conn,
    o0: CapVec<Output>,
    o1: CapVec<Output>,
    id: u64,
    data: Seq<u8>,
    fin: bool,
    e0: UniEntry,
    e: UniEntry,
    ev0: CapVec<UniEvent>,
    ev1: CapVec<UniEvent>,
    r: Result<(), u64>,
    cu: nat,
)
    requires
        c0.wf(),
        !c0.closed,
        id % 4 == 2,
        c0.uni_known(id) ==> c0.uhist@[id] == uni_hist_of(e0),
        !c0.uni_known(id) ==> e0.stream.all() == Seq::<u8>::empty() && e0.stream.emitted() == Seq::<
            SpecUniEvent,
        >::empty(),
        ev0@ == Seq::<UniEvent>::empty(),
        uni::fed(e0.stream, e.stream, data, fin, c0.seen, c1.seen, ev0, ev1, r, cu),
        c1.uhist@ == c0.uhist@.insert(id, uni_hist_of(e)),
        c1.ctrl == c0.ctrl,
        c1.goaways == c0.goaways,
        c1.highest == c0.highest,
        c1.goaway == c0.goaway,
        c1.started == c0.started,
        c1.rhist == c0.rhist,
        c1.rstate == c0.rstate,
        o1.wf(),
        o1.cap() == o0.cap(),
        r is Err ==> c1.closed && c1.wf() && extends(o0@, o1@) && added(o0@, o1@) == seq![
            SpecOutput::CloseConnection { code: r->Err_0 },
        ] && c1.peer_max == c0.peer_max && c1.uset == c0.uset,
        r is Ok ==> !c1.closed && o1 == o0 && c1.peer_max == events_fs(uni::views(ev1@), c0.peer_max) && c1.uset@
            == (if fin {
            c0.uset@.remove(id)
        } else {
            c0.uset@.insert(id)
        }) && tables_ok(c1.reqs, c1.unis, c1.rhist@, c1.uhist@, c1.rstate@, c1.uset@),
    ensures
        uni_done(c0, c1, o0, o1, id, data, fin),
{
    hide(uni::rfc_uni_stream);
    reveal(uni_done);
    assert(ev1@.skip(0) =~= ev1@);
    assert(Seq::<u8>::empty() + data =~= data);
    let em0 = e0.stream.emitted();
    assert(e.stream.emitted().take(em0.len() as int) =~= em0);
    assert(e.stream.emitted().skip(em0.len() as int) =~= uni::views(ev1@));
    assert(c0.ctrl@ + Seq::<u8>::empty() =~= c0.ctrl@);
    assert(c0.goaways@.take(c0.goaways@.len() as int) =~= c0.goaways@);
    if r is Err {
        lemma_writes_one(SpecOutput::CloseConnection { code: r->Err_0 }, 3);
    } else {
        lemma_added_refl(o0@);
    }
}

/// `lemma_feed_cost` when the entry is put back (`cx`: the put and the new box): nothing is freed beyond a constant.
proof fn lemma_feed_cost_put(ct: nat, cf: nat, cx: nat, h: nat, d: nat, b: nat)
    requires
        ct <= c_take() * (h + 1),
        cf <= c_fr() * (d + 16) + c_frb() * b,
        cx <= 6 * (h + 1) + 1,
    ensures
        ct + 1 + cf + cx <= c_fr() * (d + 16) + 154 * (d + 16) + c_held() * b + c_take() * (h + 1) + 13 * (h + 1) + 4,
{
}

/// A fed request entry's cost when it is dropped: the take (`ct`), the box freed, `feed_req` (`cf`), and the put or the drop (`cx`: at
/// most a join of the two halves and the frees of the entry, whose `t1` trailer lines `feed_req` bounds by the `t0` it
/// held and the call's bytes).
proof fn lemma_feed_cost(ct: nat, cf: nat, cx: nat, h: nat, d: nat, b: nat, t0: nat, t1: nat)
    requires
        ct <= c_take() * (h + 1),
        cf <= c_fr() * (d + 16) + c_frb() * b,
        t1 <= t0 + 77 * (d + 16 + b),
        cx <= 13 * (h + 1) + 3 + 2 * t1,
    ensures
        ct + 1 + cf + cx <= c_fr() * (d + 16) + 154 * (d + 16) + c_held() * b + c_take() * (h + 1) + 13 * (h + 1) + 4
            + 2 * t0,
{
    assert(2 * t1 <= 2 * t0 + 154 * (d + 16) + 154 * b) by (nonlinear_arith)
        requires
            t1 <= t0 + 77 * (d + 16 + b),
    ;
}

/// `feed_req` with its ensures bundled (`fed_ok`), for callers that only pass them on.
fn feed_req_ok(e: &mut ReqEntry, data: &[u8], fin: bool, peer: Option<u64>, out: &mut CapVec<Output>) -> (r: (
    bool,
    Ghost<nat>,
))
    requires
        req_entry_ok(*old(e)),
        old(e).rx_open,
        old(out).wf(),
        old(out)@.len() + MAX_OUTS <= old(out).cap(),
    ensures
        fed_ok(*old(e), *final(e), *old(out), *final(out), data@, fin, peer, r.0),
        final(e).id == old(e).id,
        req_entry_ok(*final(e)),
        final(e).trailers@.len() <= old(e).trailers@.len() + 77 * (data@.len() + 16 + old(e).stream.buffered()),
        r.1@ <= c_fr() * (data@.len() + 16) + c_frb() * old(e).stream.buffered(),
{
    let (closing, Ghost(c)) = feed_req(e, data, fin, peer, out);
    proof {
        lemma_fed_ok(*old(e), *e, *old(out), *out, data@, fin, peer, closing);
    }
    (closing, Ghost(c))
}

/// A request-stream call's `step` and `frame`: its outputs are request-only (none on stream 3), it closes exactly when
/// it closed the connection, and the request state and history change only at `id`.
proof fn lemma_req_step(c0: H3Conn, c1: H3Conn, o0: CapVec<Output>, o1: CapVec<Output>, id: u64)
    requires
        c0.wf(),
        !c0.closed,
        c1.wf(),
        extends(o0@, o1@),
        outs_ok(added(o0@, o1@), c1.closed),
        req_only(added(o0@, o1@)),
        c1.ctrl == c0.ctrl,
        c1.goaways == c0.goaways,
        c1.uset == c0.uset,
        c1.uhist == c0.uhist,
        c1.rstate@.remove(id) == c0.rstate@.remove(id),
        c1.rhist@.remove(id) == c0.rhist@.remove(id),
    ensures
        step(c0, c1, o0@, o1@),
        frame(c0, c1, Some(id)),
{
    lemma_writes_none(added(o0@, o1@), 3);
    assert(c0.ctrl@ + Seq::<u8>::empty() =~= c0.ctrl@);
    assert(c0.goaways@.take(c0.goaways@.len() as int) =~= c0.goaways@);
    assert forall|y: u64| y != id implies #[trigger] c1.rstate@.contains_key(y) == c0.rstate@.contains_key(y)
        && (c0.rstate@.contains_key(y) ==> c1.rstate@[y] == c0.rstate@[y]) && c1.rhist@[y] == c0.rhist@[y] by {
        assert(c1.rstate@.remove(id).contains_key(y) == c1.rstate@.contains_key(y));
        assert(c0.rstate@.remove(id).contains_key(y) == c0.rstate@.contains_key(y));
        if c0.rstate@.contains_key(y) {
            assert(c1.rstate@.remove(id)[y] == c1.rstate@[y]);
            assert(c0.rstate@.remove(id)[y] == c0.rstate@[y]);
        }
        if c0.rhist@.contains_key(y) {
            assert(c0.rhist@.remove(id)[y] == c0.rhist@[y]);
        }
        assert(c1.rhist@.remove(id).contains_key(y) == c1.rhist@.contains_key(y));
        assert(c0.rhist@.remove(id).contains_key(y) == c0.rhist@.contains_key(y));
        if c1.rhist@.contains_key(y) {
            assert(c1.rhist@.remove(id)[y] == c1.rhist@[y]);
            assert(c0.rhist@.remove(id)[y] == c0.rhist@[y]);
        }
    }
}

/// `request_feed`'s ensures, its cost aside: request stream `id`'s entry `e0` fed into `e` (`fed_ok`), its history
/// recorded, and, unless the connection closed, the tables updated: `e` kept, or dropped once the request has ended both
/// ways.
proof fn lemma_feed_done(
    c0: H3Conn,
    c1: H3Conn,
    o0: CapVec<Output>,
    o1: CapVec<Output>,
    id: u64,
    data: Seq<u8>,
    fin: bool,
    e0: ReqEntry,
    e: ReqEntry,
    closing: bool,
)
    requires
        c0.wf(),
        !c0.closed,
        id % 4 == 0,
        c0.req_receiving(id),
        e0.id == id,
        c0.rstate@[id] == state_of(e0),
        c0.rhist@[id] == req_hist_of(e0),
        fed_ok(e0, e, o0, o1, data, fin, c0.peer_max, closing),
        c1 == (H3Conn {
            reqs: c1.reqs,
            closed: closing,
            rhist: Ghost(c0.rhist@.insert(id, req_hist_of(e))),
            rstate: c1.rstate,
            ..c0
        }),
        closing ==> c1.rstate == c0.rstate,
        !closing ==> c1.rstate@ == if e.fin_seen && !e.send_open {
            c0.rstate@.remove(id)
        } else {
            c0.rstate@.insert(id, state_of(e))
        },
        !closing ==> tables_ok(c1.reqs, c1.unis, c1.rhist@, c1.uhist@, c1.rstate@, c1.uset@),
    ensures
        req_done(c0, c1, o0, o1, id, data, fin),
{
    reveal(fed_ok);
    reveal(req_done);
    assert(c1.rstate@.remove(id) =~= c0.rstate@.remove(id));
    assert(c1.rhist@.remove(id) =~= c0.rhist@.remove(id));
    lemma_req_step(c0, c1, o0, o1, id);
}

/// `request_data_new`'s ensures on a stream it accepts, its cost aside: a fresh entry `e0` for request stream `id` fed
/// into `e` (`fed_ok`), its history recorded, `id` accepted, and, unless the connection closed, the tables updated: `e`
/// kept, or dropped if the request has already ended both ways.
proof fn lemma_new_done(
    c0: H3Conn,
    c1: H3Conn,
    o0: CapVec<Output>,
    o1: CapVec<Output>,
    id: u64,
    data: Seq<u8>,
    fin: bool,
    e0: ReqEntry,
    e: ReqEntry,
    closing: bool,
)
    requires
        c0.wf(),
        !c0.closed,
        id % 4 == 0,
        !c0.req_known(id),
        !rejected_id(c0, id),
        e0 == (ReqEntry {
            id,
            stream: e0.stream,
            rx_open: true,
            fin_seen: false,
            head: false,
            is_head: false,
            send_open: true,
            trailers: e0.trailers,
        }),
        e0.stream.all() == Seq::<u8>::empty(),
        e0.stream.emitted() == Seq::<SpecReqEvent>::empty(),
        e0.trailers@ == Seq::<FieldLine>::empty(),
        fed_ok(e0, e, o0, o1, data, fin, c0.peer_max, closing),
        c1 == (H3Conn {
            reqs: c1.reqs,
            closed: closing,
            highest: bump(c0.highest, id),
            rhist: Ghost(c0.rhist@.insert(id, req_hist_of(e))),
            rstate: c1.rstate,
            ..c0
        }),
        closing ==> c1.rstate == c0.rstate,
        !closing ==> c1.rstate@ == if e.fin_seen && !e.send_open {
            c0.rstate@
        } else {
            c0.rstate@.insert(id, state_of(e))
        },
        !closing ==> tables_ok(c1.reqs, c1.unis, c1.rhist@, c1.uhist@, c1.rstate@, c1.uset@),
    ensures
        req_done(c0, c1, o0, o1, id, data, fin),
{
    reveal(fed_ok);
    reveal(req_done);
    assert(c1.rstate@.remove(id) =~= c0.rstate@.remove(id));
    assert(c1.rhist@.remove(id) =~= c0.rhist@.remove(id));
    lemma_req_step(c0, c1, o0, o1, id);
    assert(Seq::<u8>::empty() + data =~= data);
    assert(fields_view(e0.trailers@) =~= Seq::<(Seq<u8>, Seq<u8>)>::empty());
}

/// Feeds `data` to the request machine of `e` and outputs what its events and error mean.
/// Returns whether the connection must close (the last output is then CloseConnection).
fn feed_req(e: &mut ReqEntry, data: &[u8], fin: bool, peer: Option<u64>, out: &mut CapVec<Output>) -> (r: (bool, Ghost<nat>))
    requires
        req_entry_ok(*old(e)),
        old(e).rx_open,
        old(out).wf(),
        old(out)@.len() + MAX_OUTS <= old(out).cap(),
    ensures
        final(out).wf(),
        final(out).cap() == old(out).cap(),
        final(out)@.len() <= old(out)@.len() + MAX_OUTS,
        extends(old(out)@, final(out)@),
        final(e).stream.all() == old(e).stream.all() + data@,
        final(e).stream.emitted().len() >= old(e).stream.emitted().len(),
        final(e).stream.emitted().take(old(e).stream.emitted().len() as int) == old(e).stream.emitted(),
        request::concat_bodies(final(e).stream.emitted()) == request::rfc_request_stream(
            final(e).stream.all(),
            fin,
        ).0,
        req_outs(
            old(e).id,
            final(e).stream.emitted().skip(old(e).stream.emitted().len() as int),
            fields_view(old(e).trailers@),
            req_err(final(e).stream.all(), fin),
            Ctx { fin, peer, send_open: old(e).send_open },
            added(old(out)@, final(out)@),
        ),
        outs_ok(added(old(out)@, final(out)@), r.0),
        req_only(added(old(out)@, final(out)@)),
        final(e).fin_seen == fin,
        final(e).rx_open == (req_err(final(e).stream.all(), fin) is None && !fin && no_internal(
            final(e).stream.emitted().skip(old(e).stream.emitted().len() as int),
        )),
        !r.0 ==> final(e).send_open == (old(e).send_open && req_err(final(e).stream.all(), fin)
            is None && no_internal(final(e).stream.emitted().skip(old(e).stream.emitted().len() as int))),
        final(e).head == (old(e).head || has_request(added(old(out)@, final(out)@))),
        final(e).is_head == (old(e).is_head || head_req(added(old(out)@, final(out)@))),
        final(e).id == old(e).id,
        req_entry_ok(*final(e)),
        final(e).trailers@.len() <= old(e).trailers@.len() + 77 * (data@.len() + 16 + old(e).stream.buffered()),
        r.1@ <= c_fr() * (data@.len() + 16) + c_frb() * old(e).stream.buffered(),
{
    hide(request::rfc_req);
    let ghost id = e.id;
    let ghost o0 = out@;
    let ghost em0 = e.stream.emitted();
    let ghost so = e.send_open;
    let ghost b0 = e.stream.buffered();
    // The event buffer's allocation.
    let ghost mut work: nat = 1;
    let mut evs: CapVec<ReqEvent> = CapVec::new(MAX_REQ_EVENTS);
    let (res, Ghost(cr)) = e.stream.on_data(data, fin, &mut evs);
    proof {
        work = work + cr;
        assert(evs@.skip(0) =~= evs@);
        assert(e.stream.emitted().skip(em0.len() as int) =~= request::views(evs@));
        assert(e.stream.emitted().take(em0.len() as int) =~= em0);
    }
    let ghost err = request::err_of(res);
    let ghost cx = Ctx { fin, peer, send_open: e.send_open };
    let ghost evv = request::views(evs@);
    let (answered, Ghost(cd)) = deliver(e, evs, fin, peer, Ghost(evv), Ghost(err), Ghost(cx), out);
    proof {
        work = work + cd;
        assert(c_dlv() * (evv.len() + 1) <= 160);
    }
    if answered {
        proof {
            lemma_added_refl(out@);
            lemma_req_concat(added(o0, out@), Seq::empty(), false);
            assert(added(o0, out@) + Seq::<SpecOutput>::empty() =~= added(o0, out@));
        }
        return (false, Ghost(work));
    }
    let ghost o2 = out@;
    let closing = push_err(e.id, &res, e.send_open, fin, Ghost(cx), out);
    proof {
        // `push_err`'s outputs, at most 2.
        work = work + 2;
    }
    match res {
        Err(_) => {
            e.rx_open = false;
            e.send_open = false;
        },
        Ok(()) => {
            if fin {
                e.rx_open = false;
            }
        },
    }
    e.fin_seen = fin;
    proof {
        lemma_added_trans(o0, o2, out@);
        lemma_err_outs_shape(id, err, cx);
        lemma_req_concat(added(o0, o2), added(o2, out@), closing);
        assert(!has_request(added(o2, out@))) by {
            if has_request(added(o2, out@)) {
                let i = choose|i: int| 0 <= i < added(o2, out@).len() && (#[trigger] added(o2, out@)[i]) is Request;
                if let Some(ReqError::Stream(c)) = err {
                    let a = if cx.send_open { seq![SpecOutput::ResetStream { stream_id: id, code: c }] } else { Seq::<SpecOutput>::empty() };
                    let b = stop_outs(id, c, fin);
                    if i < a.len() { assert((a + b)[i] == a[i]); } else { assert((a + b)[i] == b[i - a.len()]); }
                }
            }
        }
        lemma_has_request_concat(added(o0, o2), added(o2, out@));
        lemma_head_req_concat(added(o0, o2), added(o2, out@));
    }
    (closing, Ghost(work))
}

/// The stream tables' part of `H3Conn::wf`, opaque: revealed only by the fns that read or change a table.
#[verifier::opaque]
spec fn tables_ok(
    reqs: Tree<Box<ReqEntry>>,
    unis: Tree<Box<UniEntry>>,
    rhist: Map<u64, RHist>,
    uhist: Map<u64, UHist>,
    rstate: Map<u64, ReqState>,
    uset: Set<u64>,
) -> bool {
    &&& tbl(reqs, 0)
    &&& tbl(unis, 2)
    &&& reqs_ok(tv(reqs), rhist)
    &&& unis_ok(tv(unis), uhist)
    &&& req_dom(tv(reqs), rstate)
    &&& uni_dom(tv(unis), uset)
}

/// `tables_ok`'s parts.
proof fn lemma_tables_open(
    reqs: Tree<Box<ReqEntry>>,
    unis: Tree<Box<UniEntry>>,
    rhist: Map<u64, RHist>,
    uhist: Map<u64, UHist>,
    rstate: Map<u64, ReqState>,
    uset: Set<u64>,
)
    requires
        tables_ok(reqs, unis, rhist, uhist, rstate, uset),
    ensures
        tbl(reqs, 0),
        tbl(unis, 2),
        reqs_ok(tv(reqs), rhist),
        unis_ok(tv(unis), uhist),
        req_dom(tv(reqs), rstate),
        uni_dom(tv(unis), uset),
{
    reveal(tables_ok);
}

/// `tables_ok` from its parts.
proof fn lemma_tables_close(
    reqs: Tree<Box<ReqEntry>>,
    unis: Tree<Box<UniEntry>>,
    rhist: Map<u64, RHist>,
    uhist: Map<u64, UHist>,
    rstate: Map<u64, ReqState>,
    uset: Set<u64>,
)
    requires
        tbl(reqs, 0),
        tbl(unis, 2),
        reqs_ok(tv(reqs), rhist),
        unis_ok(tv(unis), uhist),
        req_dom(tv(reqs), rstate),
        uni_dom(tv(unis), uset),
    ensures
        tables_ok(reqs, unis, rhist, uhist, rstate, uset),
{
    reveal(tables_ok);
}

/// The entry points' cost per byte given, and their constant: the request path's, the costliest. `feed_req` and the
/// frees of the trailer lines it may leave on an entry it drops (2 per line, at most 77 lines per byte) cost
/// `c_fr() + 154` per byte of `d + 16`, which is at most 16 times `d + 1`; the lookup's comparison, a box and the
/// dropped entry's other buffers add 5.
#[verifier::inline]
pub open spec fn c_in() -> nat {
    1318389
}

/// The entry points' cost per level of the stream's table: the lookup (`c_get()`), a take (`c_take()`), and a put
/// (`c_join()`) or the two halves' join (`c_join2()`).
#[verifier::inline]
pub open spec fn c_map() -> nat {
    58
}

/// The entry points' cost per byte the stream held before the call (the frame it may complete from them):
/// `request::c_frame()` + 308. On a request stream, `feed_req`'s `c_frb()` and the frees of the trailer lines that frame
/// may leave on an entry the call drops (2 per line, at most 77 lines per byte). A uni stream's (`c_uni_frame() + 1`)
/// is less.
#[verifier::inline]
pub open spec fn c_held() -> nat {
    41329
}

/// `uni_data`'s cost per byte of `d + 16`: `on_data`'s `c_uni()`, `apply_settings`' 2 per byte, the frees of the
/// events (at most one per 3 bytes), and the constant terms (the event buffer, the boxes, the output and the dropped
/// stream's buffers: at most 1 per byte of the 16).
#[verifier::inline]
spec fn c_ud() -> nat {
    860
}

/// Two per trailer line held by request stream `id`'s entry in `c0` if the call from `c0` to `c1` removed that entry,
/// else 0: the buffers the removal frees beyond a constant. Not bounded by the call's input: N6, the teardown class,
/// owned by carryover `cat-C15-teardown` (9b4).
pub closed spec fn removed_fields(c0: H3Conn, c1: H3Conn, id: u64) -> nat {
    if id % 4 == 0 && tv(c0.reqs).contains_key(id) && !c1.rstate@.contains_key(id) {
        2 * tv(c0.reqs)[id].trailers@.len()
    } else {
        0
    }
}

/// The height of the table stream `id` is looked up in.
pub closed spec fn ht_of(c: H3Conn, id: u64) -> nat {
    if id % 4 == 2 {
        ht(c.unis)
    } else {
        ht(c.reqs)
    }
}

/// The streams the connection tracks in the table stream `id` is looked up in: its uni streams for a client uni ID, else
/// its request streams.
pub closed spec fn tracked_of(c: H3Conn, id: u64) -> nat {
    if id % 4 == 2 {
        c.uset@.len()
    } else {
        c.rstate@.dom().len()
    }
}

/// The table height the entry points charge for (`ht_of`) is logarithmic in the streams the table holds: avl's
/// `lemma_height` over the map view, whose keys the mirrors `rstate` and `uset` are. So `c_map()·(ht_of + 1)` is the
/// spec's `L(n)`: `ht_of <= 2·log2(n + 1) + 1`.
pub proof fn lemma_ht_of(c: H3Conn, id: u64)
    requires
        c.wf(),
        !c.closed(),
    ensures
        pow2(ht_of(c, id) / 2) <= tracked_of(c, id) + 1,
{
    lemma_tables_open(c.reqs, c.unis, c.rhist@, c.uhist@, c.rstate@, c.uset@);
    reveal(req_dom);
    reveal(uni_dom);
    lemma_tv_len(c.reqs);
    lemma_tv_len(c.unis);
    lemma_height(c.reqs);
    lemma_height(c.unis);
    assert(c.rstate@.dom() == tv(c.reqs).dom());
}

/// What `request_data` and its parts ensure, their costs aside.
#[verifier::opaque]
spec fn req_done(c0: H3Conn, c1: H3Conn, o0: CapVec<Output>, o1: CapVec<Output>, id: u64, data: Seq<u8>, fin: bool) -> bool {
    &&& o1.wf()
    &&& o1.cap() == o0.cap()
    &&& o1@.len() <= o0@.len() + MAX_OUTS
    &&& step(c0, c1, o0@, o1@)
    &&& c1.goaways() == c0.goaways()
    &&& c1.peer_max == c0.peer_max
    &&& frame(c0, c1, Some(id))
    &&& req_call(c0, c1, id, data, fin, added(o0@, o1@))
    &&& c1.seen == c0.seen
}

// =============================================================================
// The connection
// =============================================================================

pub struct H3Conn {
    closed: bool,
    started: bool,
    seen: SeenUni,
    /// The tracked request streams, keyed by ID (boxed: a tree node stays small, so an update's node rebuilds stay
    /// within an input call's allocation budget).
    reqs: Tree<Box<ReqEntry>>,
    /// The tracked peer uni streams, keyed by ID.
    unis: Tree<Box<UniEntry>>,
    /// The highest client bidirectional stream ID accepted (processed, not rejected).
    highest: Option<u64>,
    /// The last GOAWAY ID we sent.
    goaway: Option<u64>,
    /// The peer's SETTINGS_MAX_FIELD_SECTION_SIZE, once received.
    peer_max: Option<u64>,
    /// Every byte we have written on our control stream.
    ctrl: Ghost<Seq<u8>>,
    goaways: Ghost<Seq<u64>>,
    /// Per request stream: bytes fed to its machine, its events, the held trailer section.
    rhist: Ghost<Map<u64, RHist>>,
    /// Per peer uni stream: bytes fed to its machine, its `seen_before`, its events.
    uhist: Ghost<Map<u64, UHist>>,
    /// The tracked request streams and their states (mirrors `reqs`).
    rstate: Ghost<Map<u64, ReqState>>,
    /// The tracked peer uni streams (mirrors `unis`).
    uset: Ghost<Set<u64>>,
}

/// What every call guarantees: the invariant, outputs only appended, nothing at all once
/// closed, a CloseConnection only as the closing call's last output, our control-stream bytes
/// extended by exactly what this call wrote on stream 3, and GOAWAYs only appended.
pub open spec fn step(c0: H3Conn, c1: H3Conn, o0: Seq<Output>, o1: Seq<Output>) -> bool {
    &&& c1.wf()
    &&& extends(o0, o1)
    &&& c0.closed() ==> c1.closed() && o1 == o0
    &&& outs_ok(added(o0, o1), c1.closed() && !c0.closed())
    &&& c1.ctrl_bytes() == c0.ctrl_bytes() + writes_on(added(o0, o1), 3)
    &&& c1.goaways().len() >= c0.goaways().len()
    &&& c1.goaways().take(c0.goaways().len() as int) == c0.goaways()
}

pub open spec fn rejected_id(c: H3Conn, id: u64) -> bool {
    c.goaways().len() > 0 && id >= c.goaways().last()
}

/// Every tracked stream other than `x` is unchanged: its state, and the history its machine was
/// fed. (With `x == None`, every stream.)
pub open spec fn frame(c0: H3Conn, c1: H3Conn, x: Option<u64>) -> bool {
    forall|y: u64|
        #![trigger c1.req_state(y)]
        #![trigger c1.uni_known(y)]
        #![trigger c1.req_hist(y)]
        #![trigger c1.uni_hist(y)]
        x != Some(y) ==> c1.req_state(y) == c0.req_state(y) && c1.uni_known(y) == c0.uni_known(y)
            && c1.req_hist(y) == c0.req_hist(y) && c1.uni_hist(y) == c0.uni_hist(y)
}

/// The state a request stream starts in.
pub open spec fn fresh_state() -> ReqState {
    ReqState { receiving: true, head: false, send_open: true, fin_seen: false, is_head: false }
}

/// The state request stream `id` was fed from: its own if it was being received, else fresh.
pub open spec fn state_before(c0: H3Conn, id: u64) -> ReqState {
    if c0.req_receiving(id) {
        c0.req_state(id)->0
    } else {
        fresh_state()
    }
}

/// A request-stream call that fed the machine.
/// - The stream's bytes (continued if it was being received, else from empty) grew by `data`.
/// - Its cumulative events (body chunks concatenated) are `rfc_request_stream` of those bytes.
/// - The call's outputs `o` are exactly what the new events and the machine's error mean
///   (`req_outs`), with our sending part and the peer's limit as they were.
/// - Unless the connection closed: the stream is still received exactly when there was no
///   FIN, no error and no internal answer, and it is respondable exactly when, besides no error
///   and no internal answer, our sending part was open and a head was delivered (now or before).
///   While still tracked, its whole state is given: in particular `is_head` holds exactly when a
///   delivered request (now or before) had the method HEAD.
pub open spec fn req_fed(c0: H3Conn, c1: H3Conn, id: u64, data: Seq<u8>, fin: bool, o: Seq<SpecOutput>) -> bool {
    let b0 = if c0.req_receiving(id) { c0.req_hist(id).0 } else { Seq::<u8>::empty() };
    let e0 = if c0.req_receiving(id) { c0.req_hist(id).1 } else { Seq::<SpecReqEvent>::empty() };
    let t0 = if c0.req_receiving(id) { c0.req_hist(id).2 } else { Seq::<(Seq<u8>, Seq<u8>)>::empty() };
    let s0 = state_before(c0, id);
    let h = c1.req_hist(id);
    let err = req_err(h.0, fin);
    let ne = h.1.skip(e0.len() as int);
    &&& h.0 == b0 + data
    &&& h.1.len() >= e0.len()
    &&& h.1.take(e0.len() as int) == e0
    &&& request::concat_bodies(h.1) == request::rfc_request_stream(h.0, fin).0
    &&& req_outs(
        id,
        ne,
        t0,
        err,
        Ctx { fin, peer: c0.peer_max_field_section(), send_open: s0.send_open },
        o,
    )
    &&& !c1.closed() ==> c1.req_receiving(id) == (err is None && !fin && no_internal(ne))
    &&& !c1.closed() ==> c1.req_respondable(id) == (err is None && no_internal(ne) && s0.send_open
        && (s0.head || has_request(o)))
    &&& !c1.closed() && c1.req_known(id) ==> c1.req_state(id) == Some(
        ReqState {
            receiving: err is None && !fin && no_internal(ne),
            head: s0.head || has_request(o),
            send_open: s0.send_open && err is None && no_internal(ne),
            fin_seen: fin,
            is_head: s0.is_head || head_req(o),
        },
    )
}

/// The last SETTINGS_MAX_FIELD_SECTION_SIZE in `p`, else `cur`.
pub open spec fn pairs_fs(p: Seq<(u64, u64)>, cur: Option<u64>) -> Option<u64>
    decreases p.len(),
{
    if p.len() == 0 {
        cur
    } else if p.last().0 == SETTINGS_MAX_FIELD_SECTION_SIZE {
        Some(p.last().1)
    } else {
        pairs_fs(p.drop_last(), cur)
    }
}

/// `apply_settings`' cost over a uni call's events is linear in the call: at most `d / 3 + 1` events (the capacity) and
/// at most `(d + buffered) / 2` SETTINGS pairs (`UniStream::on_data`).
proof fn lemma_settings_apply_cost(ca: nat, n: nat, pairs: nat, d: nat, b: nat)
    requires
        ca <= 1 + n + pairs,
        n <= d / 3 + 1,
        2 * pairs <= d + b,
    ensures
        ca <= 2 * d + b + 2,
{
}

/// The peer's MAX_FIELD_SECTION_SIZE after its uni-stream events `e`, starting from `cur`.
pub open spec fn events_fs(e: Seq<SpecUniEvent>, cur: Option<u64>) -> Option<u64>
    decreases e.len(),
{
    if e.len() == 0 {
        cur
    } else {
        match e.last() {
            SpecUniEvent::PeerSettings(p) => pairs_fs(p, events_fs(e.drop_last(), cur)),
            _ => events_fs(e.drop_last(), cur),
        }
    }
}

/// A peer uni stream call: the stream's bytes grew by `data`; its events and error are
/// `rfc_uni_stream` of them; the only output is CloseConnection on that error. Otherwise the
/// stream stays tracked until its FIN, and the peer's MAX_FIELD_SECTION_SIZE is the last one its
/// new events carry. The stream's type is checked against the connection's `uni_seen()` at the
/// call that determined it, and that call records the type there (`seen_after`); so a second
/// control, encoder or decoder stream is H3_STREAM_CREATION_ERROR (RFC 9114 §6.2.1, RFC 9204
/// §4.2).
pub open spec fn uni_fed(c0: H3Conn, c1: H3Conn, id: u64, data: Seq<u8>, fin: bool, o: Seq<SpecOutput>) -> bool {
    let b0 = if c0.uni_known(id) { c0.uni_hist(id).0 } else { Seq::<u8>::empty() };
    let e0 = if c0.uni_known(id) { c0.uni_hist(id).2 } else { Seq::<SpecUniEvent>::empty() };
    let h = c1.uni_hist(id);
    &&& h.0 == b0 + data
    &&& h.2.len() >= e0.len()
    &&& h.2.take(e0.len() as int) == e0
    &&& uni::rfc_uni_stream(h.0, fin, h.1).0 == h.2
    &&& o == uni_err_outs(uni::rfc_uni_stream(h.0, fin, h.1).1)
    &&& if uni::kind_of_bytes(b0) is Undetermined {
        h.1 == c0.uni_seen() && c1.uni_seen() == uni::seen_after(c0.uni_seen(), h.0)
    } else {
        h.1 == c0.uni_hist(id).1 && c1.uni_seen() == c0.uni_seen()
    }
    &&& !c1.closed() ==> c1.uni_known(id) == !fin && c1.peer_max_field_section() == events_fs(
        h.2.skip(e0.len() as int),
        c0.peer_max_field_section(),
    )
}

/// What a peer reset of request stream `id` outputs: our sending part, if still open, is reset
/// (H3_REQUEST_INCOMPLETE if the request never ended, else H3_REQUEST_CANCELLED).
pub open spec fn reset_outs(id: u64, st: Option<ReqState>) -> Seq<SpecOutput> {
    match st {
        Some(s) => if s.send_open {
            seq![
                SpecOutput::ResetStream {
                    stream_id: id,
                    code: if s.fin_seen {
                        H3_REQUEST_CANCELLED
                    } else {
                        H3_REQUEST_INCOMPLETE
                    },
                },
            ]
        } else {
            Seq::empty()
        },
        None => Seq::empty(),
    }
}

/// What a request-stream call does (connection open, `id % 4 == 0`).
/// - A new stream at or above our GOAWAY ID is rejected (`rejected_outs`), never fed; it is
///   kept, neither received nor answerable, until the peer's FIN or reset.
/// - A tracked stream no longer received (finished, or abandoned awaiting the peer's FIN or
///   reset) outputs nothing and is unchanged, except that a FIN may forget it.
/// - Otherwise its machine is fed (`req_fed`).
/// - A new stream that is fed is accepted: `highest_accepted` rises to its ID (`bump`); every
///   other call leaves it unchanged.
pub open spec fn req_call(c0: H3Conn, c1: H3Conn, id: u64, data: Seq<u8>, fin: bool, o: Seq<SpecOutput>) -> bool {
    &&& !c0.req_known(id) && rejected_id(c0, id) ==> o == rejected_outs(id, fin) && !c1.closed()
        && !c1.req_receiving(id) && !c1.req_respondable(id) && (if fin {
        !c1.req_known(id)
    } else {
        c1.req_state(id) == Some(
            ReqState { receiving: false, head: false, send_open: false, fin_seen: false, is_head: false },
        )
    })
    &&& c0.req_known(id) && !c0.req_receiving(id) ==> o == Seq::<SpecOutput>::empty() && !c1.closed()
        && !c1.req_receiving(id) && c1.req_respondable(id) == c0.req_respondable(id) && (
    c1.req_known(id) ==> c1.req_state(id) == Some(
        ReqState { fin_seen: c0.req_state(id)->0.fin_seen || fin, ..c0.req_state(id)->0 },
    ))
    &&& (c0.req_receiving(id) || (!c0.req_known(id) && !rejected_id(c0, id))) ==> req_fed(
        c0,
        c1,
        id,
        data,
        fin,
        o,
    )
    &&& c1.highest_accepted() == if !c0.req_known(id) && !rejected_id(c0, id) {
        bump(c0.highest_accepted(), id)
    } else {
        c0.highest_accepted()
    }
}

pub open spec fn critical(k: UniKind) -> bool {
    k is Control || k is QpackEncoder || k is QpackDecoder
}

/// The ID of the GOAWAY `shutdown` sends: one past the highest accepted request, or 0, and
/// never more than an earlier GOAWAY.
pub open spec fn goaway_id(highest: Option<u64>, sent: Seq<u64>) -> int {
    let t = match highest {
        None => 0int,
        Some(h) => h + 4,
    };
    if sent.len() > 0 && sent.last() < t {
        sent.last() as int
    } else {
        t
    }
}

/// The highest accepted request ID once `id` is accepted.
pub open spec fn bump(h: Option<u64>, id: u64) -> Option<u64> {
    match h {
        Some(x) => if x < id {
            Some(id)
        } else {
            Some(x)
        },
        None => Some(id),
    }
}

/// `start`'s outputs: our control-stream preamble, if the stream isn't open yet.
pub open spec fn start_outs(c: H3Conn) -> Seq<SpecOutput> {
    if !c.closed() && c.ctrl_bytes().len() == 0 {
        seq![SpecOutput::StreamWrite { stream_id: 3, data: ctrl_preamble(), fin: false }]
    } else {
        Seq::empty()
    }
}

/// `shutdown`'s outputs: `start_outs`, then one GOAWAY(`goaway_id`) frame on stream 3 if that ID
/// is encodable (it isn't only when stream 2^62 - 4 was accepted and no GOAWAY was sent yet).
pub open spec fn shutdown_outs(c: H3Conn) -> Seq<SpecOutput> {
    let g = goaway_id(c.highest_accepted(), c.goaways());
    if c.closed() {
        Seq::empty()
    } else if g <= VARINT_MAX {
        start_outs(c).push(
            SpecOutput::StreamWrite {
                stream_id: 3,
                data: spec_frame_bytes(FRAME_GOAWAY, spec_varint(g as u64)),
                fin: false,
            },
        )
    } else {
        start_outs(c)
    }
}

impl H3Conn {
    pub closed spec fn closed(&self) -> bool {
        self.closed
    }

    /// Every byte we have written on our control stream (stream 3).
    pub closed spec fn ctrl_bytes(&self) -> Seq<u8> {
        self.ctrl@
    }

    /// The GOAWAY IDs we have sent, in order.
    pub closed spec fn goaways(&self) -> Seq<u64> {
        self.goaways@
    }

    pub closed spec fn highest_accepted(&self) -> Option<u64> {
        self.highest
    }

    pub closed spec fn peer_max_field_section(&self) -> Option<u64> {
        self.peer_max
    }

    /// The state of request stream `id`, while the connection tracks it.
    pub closed spec fn req_state(&self, id: u64) -> Option<ReqState> {
        if self.rstate@.contains_key(id) {
            Some(self.rstate@[id])
        } else {
            None
        }
    }

    /// The connection tracks request stream `id` (it may be finished or abandoned).
    pub open spec fn req_known(&self, id: u64) -> bool {
        self.req_state(id) is Some
    }

    /// Request stream `id` is still being received and processed.
    pub open spec fn req_receiving(&self, id: u64) -> bool {
        match self.req_state(id) {
            Some(s) => s.receiving,
            None => false,
        }
    }

    /// Request stream `id` had its head delivered and has no response yet.
    pub open spec fn req_respondable(&self, id: u64) -> bool {
        match self.req_state(id) {
            Some(s) => s.head && s.send_open,
            None => false,
        }
    }

    pub closed spec fn req_hist(&self, id: u64) -> (Seq<u8>, Seq<SpecReqEvent>, Fields) {
        self.rhist@[id]
    }

    /// The bytes stream `id`'s machine holds from earlier calls: the frame a call may complete from them is the
    /// entry points' `F` term.
    pub closed spec fn buffered_of(&self, id: u64) -> nat {
        if id % 4 == 0 && tv(self.reqs).contains_key(id) {
            tv(self.reqs)[id].stream.buffered()
        } else if id % 4 == 2 && tv(self.unis).contains_key(id) {
            tv(self.unis)[id].stream.buffered()
        } else {
            0
        }
    }

    /// The connection tracks peer uni stream `id`.
    pub closed spec fn uni_known(&self, id: u64) -> bool {
        self.uset@.contains(id)
    }

    pub closed spec fn uni_hist(&self, id: u64) -> (Seq<u8>, SeenUni, Seq<SpecUniEvent>) {
        self.uhist@[id]
    }

    /// The critical stream types (control, QPACK encoder, QPACK decoder) the peer has opened:
    /// the `SeenUni` every new uni stream's type is checked against (`uni_fed`).
    pub closed spec fn uni_seen(&self) -> SeenUni {
        self.seen
    }

    pub closed spec fn wf(&self) -> bool {
        &&& self.ctrl_inv()
        &&& !self.closed ==> tables_ok(self.reqs, self.unis, self.rhist@, self.uhist@, self.rstate@, self.uset@)
    }

    /// The control-stream and GOAWAY part of the invariant (kept even once closed).
    spec fn ctrl_inv(&self) -> bool {
        &&& nonincreasing(self.goaways@)
        &&& forall|i: int| 0 <= i < self.goaways@.len() ==> #[trigger] self.goaways@[i] <= VARINT_MAX
        &&& self.ctrl@ == if self.started {
            ctrl_preamble() + goaway_frames(self.goaways@)
        } else {
            Seq::empty()
        }
        &&& !self.started ==> self.goaways@.len() == 0
        &&& self.goaway == if self.goaways@.len() == 0 {
            None::<u64>
        } else {
            Some(self.goaways@.last())
        }
        &&& (self.highest is Some && self.goaway is Some) ==> self.highest->0 < self.goaway->0
        &&& self.highest is Some ==> self.highest->0 % 4 == 0
        &&& forall|i: int| 0 <= i < self.goaways@.len() ==> #[trigger] self.goaways@[i] % 4 == 0
    }

    /// What the invariant means for our control stream and GOAWAYs: nothing written yet, or the
    /// stream type and one SETTINGS frame (`theorem_ctrl_preamble`) followed only by GOAWAY
    /// frames with non-increasing client-bidi IDs (RFC 9114 §5.2, §7.2.6), all above the highest
    /// request we accepted (`highest_accepted`, which `on_stream_data` raises to every accepted
    /// stream's ID and nothing else changes).
    pub proof fn theorem_wf(c: H3Conn)
        requires
            c.wf(),
        ensures
            c.ctrl_bytes() == Seq::<u8>::empty() || c.ctrl_bytes() == ctrl_preamble()
                + goaway_frames(c.goaways()),
            c.ctrl_bytes() == Seq::<u8>::empty() ==> c.goaways().len() == 0,
            nonincreasing(c.goaways()),
            c.highest_accepted() is Some && c.goaways().len() > 0 ==> c.highest_accepted()->0
                < c.goaways().last(),
            c.highest_accepted() is Some ==> c.highest_accepted()->0 % 4 == 0,
            forall|i: int| 0 <= i < c.goaways().len() ==> #[trigger] c.goaways()[i] % 4 == 0,
            forall|i: int|
                0 <= i < c.goaways().len() && c.highest_accepted() is Some ==> c.highest_accepted()->0
                    < #[trigger] c.goaways()[i],
    {
        if !c.started {
        } else {
            assert(ctrl_preamble().len() > 0);
        }
        if c.goaways@.len() > 0 {
            assert forall|i: int| 0 <= i < c.goaways().len() && c.highest_accepted() is Some implies c.highest_accepted()->0
                < #[trigger] c.goaways()[i] by {
                assert(c.goaways@[c.goaways@.len() - 1] <= c.goaways@[i]);
            }
        }
    }

    pub fn new() -> (c: Self)
        ensures
            c.wf(),
            !c.closed(),
            c.ctrl_bytes() == Seq::<u8>::empty(),
            c.goaways() == Seq::<u64>::empty(),
            c.highest_accepted() is None,
            c.peer_max_field_section() is None,
            c.uni_seen() == (SeenUni { control: false, encoder: false, decoder: false }),
            forall|id: u64| !c.req_known(id) && !c.uni_known(id),
    {
        proof {
            reveal(tables_ok);
            reveal(reqs_ok);
            reveal(unis_ok);
            reveal(req_dom);
            reveal(uni_dom);
            reveal(keys_mod);
            assert(tv::<Box<ReqEntry>>(None).dom() =~= Set::<u64>::empty());
            assert(tv::<Box<UniEntry>>(None).dom() =~= Set::<u64>::empty());
        }
        H3Conn {
            closed: false,
            started: false,
            seen: SeenUni { control: false, encoder: false, decoder: false },
            reqs: None,
            unis: None,
            highest: None,
            goaway: None,
            peer_max: None,
            ctrl: Ghost(Seq::empty()),
            goaways: Ghost(Seq::empty()),
            rhist: Ghost(Map::empty()),
            uhist: Ghost(Map::empty()),
            rstate: Ghost(Map::empty()),
            uset: Ghost(Set::empty()),
        }
    }

    /// Outputs CloseConnection and latches the connection closed.
    fn close(&mut self, code: u64, out: &mut CapVec<Output>)
        requires
            old(self).ctrl_inv(),
            !old(self).closed,
            old(out).wf(),
            old(out)@.len() + 1 <= old(out).cap(),
        ensures
            final(out).wf(),
            final(out).cap() == old(out).cap(),
            final(self).wf(),
            final(self).closed,
            final(self).ctrl == old(self).ctrl,
            final(self).goaways == old(self).goaways,
            final(self).highest == old(self).highest,
            final(self).seen == old(self).seen,
            final(self).peer_max == old(self).peer_max,
            final(self).reqs == old(self).reqs,
            final(self).rhist == old(self).rhist,
            final(self).uhist == old(self).uhist,
            final(self).rstate == old(self).rstate,
            final(self).uset == old(self).uset,
            extends(old(out)@, final(out)@),
            added(old(out)@, final(out)@) == seq![SpecOutput::CloseConnection { code }],
            step(*old(self), *final(self), old(out)@, final(out)@),
    {
        let ghost o0 = out@;
        let w = Output::CloseConnection { code };
        out.push(w);
        self.closed = true;
        proof {
            lemma_added_refl(o0);
            lemma_added_push(o0, o0, w);
            assert(added(o0, out@) =~= seq![w@]);
            lemma_writes_one(w@, 3);
            assert(self.ctrl@ + Seq::<u8>::empty() =~= self.ctrl@);
            assert(self.goaways@.take(self.goaways@.len() as int) =~= self.goaways@);
        }
    }

    /// Nothing output, nothing changed that `step` sees.
    proof fn lemma_idle(c: H3Conn, o: Seq<Output>)
        requires
            c.wf(),
        ensures
            step(c, c, o, o),
    {
        lemma_added_refl(o);
        assert(c.ctrl@ + Seq::<u8>::empty() =~= c.ctrl@);
        assert(c.goaways@.take(c.goaways@.len() as int) =~= c.goaways@);
        assert(writes_on(Seq::<SpecOutput>::empty(), 3) == Seq::<u8>::empty());
    }

    //= https://www.rfc-editor.org/rfc/rfc9114#section-7.2.4.2
    //# Endpoints MUST NOT require any data to be received from
    //# the peer prior to sending the SETTINGS frame; settings MUST be sent
    //# as soon as the transport is ready to send data.
    /// Opens our control stream: its type byte and our SETTINGS frame, on server uni stream 3.
    /// Needs nothing from the peer; a second call writes nothing.
    pub fn start(&mut self, out: &mut Vec<Output>)
        requires
            old(self).wf(),
        ensures
            step(*old(self), *final(self), old(out)@, final(out)@),
            final(self).closed() == old(self).closed(),
            final(self).goaways() == old(self).goaways(),
            final(self).highest_accepted() == old(self).highest_accepted(),
            frame(*old(self), *final(self), None::<u64>),
            final(self).peer_max_field_section() == old(self).peer_max_field_section(),
            !old(self).closed() ==> final(self).ctrl_bytes().len() > 0,
            !old(self).closed() && old(self).ctrl_bytes().len() == 0 ==> final(self).ctrl_bytes()
                == ctrl_preamble(),
            added(old(out)@, final(out)@) == start_outs(*old(self)),
            final(self).uni_seen() == old(self).uni_seen(),
    {
        if self.closed || self.started {
            proof {
                Self::lemma_idle(*self, out@);
                if self.started {
                    assert(self.ctrl@.len() >= ctrl_preamble().len());
                    assert(ctrl_preamble().len() > 0);
                }
            }
            return;
        }
        let ghost o0 = out@;
        let mut data: Vec<u8> = Vec::new();
        data.push(0u8);
        let mut pairs: Vec<(u64, u64)> = Vec::new();
        pairs.push((SETTINGS_MAX_FIELD_SECTION_SIZE, MAX_FIELD_SECTION_SIZE));
        pairs.push((0x21u64, 0u64));
        proof {
            assert(pairs@ =~= our_settings());
            lemma_settings_bounds();
        }
        serialize_settings(pairs.as_slice(), &mut data);
        proof {
            assert(data@ =~= ctrl_preamble());
        }
        let w = Output::StreamWrite { stream_id: 3, data, fin: false };
        out.push(w);
        self.started = true;
        self.ctrl = Ghost(ctrl_preamble());
        proof {
            lemma_added_refl(o0);
            lemma_added_push(o0, o0, w);
            assert(added(o0, out@) =~= seq![w@]);
            lemma_writes_one(w@, 3);
            assert(goaway_frames(self.goaways@) == Seq::<u8>::empty());
            assert(ctrl_preamble() + Seq::<u8>::empty() =~= ctrl_preamble());
            assert(Seq::<u8>::empty() + ctrl_preamble() =~= ctrl_preamble());
            assert(self.goaways@.take(self.goaways@.len() as int) =~= self.goaways@);
        }
    }

    //= https://www.rfc-editor.org/rfc/rfc9114#section-5.2
    //# Endpoints initiate the graceful shutdown of an HTTP/3 connection by
    //# sending a GOAWAY frame.
    //= https://www.rfc-editor.org/rfc/rfc9114#section-5.2
    //# Requests or pushes with the indicated identifier or greater are
    //# rejected (Section 4.1.1) by the sender of the GOAWAY.  This
    //# identifier MAY be zero if no requests or pushes were processed.
    /// Sends GOAWAY with `goaway_id`: one past the highest request accepted (0 if none), never
    /// more than an earlier GOAWAY. Opens the control stream first if needed, so SETTINGS stays
    /// its first frame.
    pub fn shutdown(&mut self, out: &mut Vec<Output>)
        requires
            old(self).wf(),
        ensures
            step(*old(self), *final(self), old(out)@, final(out)@),
            final(self).closed() == old(self).closed(),
            frame(*old(self), *final(self), None::<u64>),
            final(self).peer_max_field_section() == old(self).peer_max_field_section(),
            !old(self).closed() && goaway_id(old(self).highest_accepted(), old(self).goaways())
                <= VARINT_MAX ==> final(self).goaways() == old(self).goaways().push(
                goaway_id(old(self).highest_accepted(), old(self).goaways()) as u64,
            ),
            !old(self).closed() ==> final(self).ctrl_bytes().len() > 0,
            added(old(out)@, final(out)@) == shutdown_outs(*old(self)),
            final(self).highest_accepted() == old(self).highest_accepted(),
            final(self).uni_seen() == old(self).uni_seen(),
    {
        if self.closed {
            proof {
                Self::lemma_shutdown_closed(*self, out@);
            }
            return;
        }
        let ghost c0 = *self;
        let ghost o0 = out@;
        self.start(out);
        let ghost c1 = *self;
        let ghost o1 = out@;
        proof {
            Self::lemma_started(c0, *self, o0, o1);
        }
        match self.goaway_target() {
            Some(id) => {
                self.send_goaway(id, out);
                proof {
                    Self::lemma_shutdown_sent(c0, c1, *self, o0, o1, out@, id);
                }
            },
            None => {
                proof {
                    Self::lemma_shutdown_none(c0, c1, o0, o1);
                }
            },
        }
    }

    /// The ID `shutdown` sends, `goaway_id`, if it is encodable (split out of `shutdown` for the rlimit).
    fn goaway_target(&self) -> (r: Option<u64>)
        requires
            self.wf(),
            !self.closed,
            self.started,
        ensures
            r matches Some(id) ==> id == goaway_id(self.highest_accepted(), self.goaways()) && id <= VARINT_MAX
                && (self.goaways@.len() > 0 ==> id <= self.goaways@.last()) && (self.highest is Some
                ==> self.highest->0 < id) && id % 4 == 0,
            r is None ==> goaway_id(self.highest_accepted(), self.goaways()) > VARINT_MAX,
    {
        let target: u64 = match self.highest {
            None => 0,
            Some(h) => if h <= VARINT_MAX - 4 {
                h + 4
            } else {
                // Stream 2^62 - 4, the last client stream ID, was accepted: no ID above it is
                // encodable, and no later stream can exist. Repeat the last GOAWAY, if any.
                match self.goaway {
                    Some(g) => g,
                    None => return None,
                }
            },
        };
        let id = match self.goaway {
            Some(g) => if g < target {
                g
            } else {
                target
            },
            None => target,
        };
        proof {
            if self.goaways@.len() > 0 {
                assert(self.goaways@[self.goaways@.len() - 1] <= VARINT_MAX);
                assert(self.goaways@[self.goaways@.len() - 1] % 4 == 0);
            }
        }
        Some(id)
    }

    /// `shutdown`'s ensures once `start` and `send_goaway(id)` ran.
    proof fn lemma_shutdown_sent(c0: H3Conn, c1: H3Conn, c2: H3Conn, o0: Seq<Output>, o1: Seq<Output>, o2: Seq<Output>, id: u64)
        requires
            c0.wf(),
            !c0.closed,
            step(c0, c1, o0, o1),
            c1.closed() == c0.closed(),
            c1.goaways() == c0.goaways(),
            c1.highest_accepted() == c0.highest_accepted(),
            frame(c0, c1, None::<u64>),
            c1.peer_max_field_section() == c0.peer_max_field_section(),
            added(o0, o1) == start_outs(c0),
            c1.uni_seen() == c0.uni_seen(),
            step(c1, c2, o1, o2),
            !c2.closed,
            c2.goaways@ == c1.goaways@.push(id),
            frame(c1, c2, None::<u64>),
            c2.peer_max == c1.peer_max,
            c2.highest == c1.highest,
            c2.seen == c1.seen,
            added(o1, o2) == seq![
                SpecOutput::StreamWrite {
                    stream_id: 3,
                    data: spec_frame_bytes(FRAME_GOAWAY, spec_varint(id)),
                    fin: false,
                },
            ],
            id == goaway_id(c0.highest_accepted(), c0.goaways()),
            id <= VARINT_MAX,
        ensures
            step(c0, c2, o0, o2),
            c2.closed() == c0.closed(),
            frame(c0, c2, None::<u64>),
            c2.peer_max_field_section() == c0.peer_max_field_section(),
            c2.goaways() == c0.goaways().push(goaway_id(c0.highest_accepted(), c0.goaways()) as u64),
            c2.ctrl_bytes().len() > 0,
            added(o0, o2) == shutdown_outs(c0),
            c2.highest_accepted() == c0.highest_accepted(),
            c2.uni_seen() == c0.uni_seen(),
    {
        Self::lemma_step_trans(c0, c1, c2, o0, o1, o2);
        lemma_added_trans(o0, o1, o2);
        assert(added(o0, o2) =~= shutdown_outs(c0));
        assert(c2.ctrl_bytes() == ctrl_preamble() + goaway_frames(c2.goaways()));
        assert(ctrl_preamble().len() > 0);
    }

    /// After `start` on an open connection: the invariant, and our control stream open.
    proof fn lemma_started(c0: H3Conn, c1: H3Conn, o0: Seq<Output>, o1: Seq<Output>)
        requires
            step(c0, c1, o0, o1),
            !c1.closed(),
            c1.ctrl_bytes().len() > 0,
        ensures
            c1.wf(),
            !c1.closed,
            c1.started,
    {
    }

    /// `shutdown`'s ensures on a closed connection.
    proof fn lemma_shutdown_closed(c: H3Conn, o: Seq<Output>)
        requires
            c.wf(),
            c.closed,
        ensures
            step(c, c, o, o),
            frame(c, c, None::<u64>),
            added(o, o) == shutdown_outs(c),
    {
        Self::lemma_idle(c, o);
    }

    /// `shutdown`'s ensures once `start` ran and `goaway_id` is not encodable.
    proof fn lemma_shutdown_none(c0: H3Conn, c1: H3Conn, o0: Seq<Output>, o1: Seq<Output>)
        requires
            c0.wf(),
            !c0.closed,
            step(c0, c1, o0, o1),
            c1.closed() == c0.closed(),
            c1.goaways() == c0.goaways(),
            c1.highest_accepted() == c0.highest_accepted(),
            frame(c0, c1, None::<u64>),
            c1.peer_max_field_section() == c0.peer_max_field_section(),
            c1.ctrl_bytes().len() > 0,
            added(o0, o1) == start_outs(c0),
            c1.uni_seen() == c0.uni_seen(),
            goaway_id(c0.highest_accepted(), c0.goaways()) > VARINT_MAX,
        ensures
            added(o0, o1) == shutdown_outs(c0),
    {
    }

    /// Writes GOAWAY(`id`) on our (open) control stream.
    fn send_goaway(&mut self, id: u64, out: &mut Vec<Output>)
        requires
            old(self).wf(),
            !old(self).closed,
            old(self).started,
            id <= VARINT_MAX,
            old(self).goaways@.len() > 0 ==> id <= old(self).goaways@.last(),
            old(self).highest is Some ==> old(self).highest->0 < id,
            id % 4 == 0,
        ensures
            step(*old(self), *final(self), old(out)@, final(out)@),
            !final(self).closed,
            final(self).goaways@ == old(self).goaways@.push(id),
            frame(*old(self), *final(self), None::<u64>),
            final(self).peer_max == old(self).peer_max,
            final(self).highest == old(self).highest,
            final(self).seen == old(self).seen,
            added(old(out)@, final(out)@) == seq![
                SpecOutput::StreamWrite {
                    stream_id: 3,
                    data: spec_frame_bytes(FRAME_GOAWAY, spec_varint(id)),
                    fin: false,
                },
            ],
    {
        let ghost o0 = out@;
        let mut data: Vec<u8> = Vec::new();
        serialize_goaway(id, &mut data);
        proof {
            assert(data@ =~= spec_frame_bytes(FRAME_GOAWAY, spec_varint(id)));
        }
        let w = Output::StreamWrite { stream_id: 3, data, fin: false };
        out.push(w);
        proof {
            lemma_added_refl(o0);
            lemma_added_push(o0, o0, w);
            assert(added(o0, out@) =~= seq![w@]);
            lemma_writes_one(w@, 3);
            let g0 = self.goaways@;
            let g1 = g0.push(id);
            assert(g1.drop_last() =~= g0);
            assert(goaway_frames(g1) == goaway_frames(g0) + data@);
            assert(ctrl_preamble() + goaway_frames(g0) + data@ =~= ctrl_preamble() + goaway_frames(g1));
            assert forall|i: int, j: int| 0 <= i < j < g1.len() implies g1[j] <= g1[i] by {
                if j < g0.len() {
                    assert(g0[j] <= g0[i]);
                } else if i < g0.len() - 1 {
                    assert(g0[g0.len() - 1] <= g0[i]);
                }
            }
            assert(g1.take(g0.len() as int) =~= g0);
        }
        self.goaway = Some(id);
        self.goaways = Ghost(self.goaways@.push(id));
        self.ctrl = Ghost(self.ctrl@ + data@);
    }

    /// Two calls in a row that leave the connection open compose.
    proof fn lemma_step_trans(c0: H3Conn, c1: H3Conn, c2: H3Conn, o0: Seq<Output>, o1: Seq<Output>, o2: Seq<Output>)
        requires
            step(c0, c1, o0, o1),
            step(c1, c2, o1, o2),
            !c2.closed(),
        ensures
            step(c0, c2, o0, o2),
    {
        lemma_added_trans(o0, o1, o2);
        let a = added(o0, o1);
        let b = added(o1, o2);
        lemma_writes_append(a, b, 3);
        assert(c0.ctrl_bytes() + writes_on(a, 3) + writes_on(b, 3) =~= c0.ctrl_bytes() + (writes_on(a, 3) + writes_on(b, 3)));
        let c = a + b;
        assert forall|i: int| 0 <= i < c.len() implies stop_ok(#[trigger] c[i]) && ctrl_open(c[i]) && body_ok(c[i]) && !(c[i] is CloseConnection) by {
            if i < a.len() {
                assert(c[i] == a[i]);
            } else {
                assert(c[i] == b[i - a.len()]);
            }
        }
        assert(c2.goaways().take(c0.goaways().len() as int) =~= c2.goaways().take(c1.goaways().len() as int).take(c0.goaways().len() as int));
    }

    /// Data on stream `stream_id` (`fin`: the peer's sending part ends after it). Its cost is linear in the bytes given,
    /// logarithmic in the tracked streams of its kind (`ht_of`, avl's `lemma_height`), plus the frame it may complete
    /// from bytes earlier calls buffered (`buffered_of`) and the trailer lines of an entry it removes (`removed_fields`).
    pub fn on_stream_data(&mut self, stream_id: u64, data: &[u8], fin: bool, out: &mut CapVec<Output>) -> (r: Ghost<nat>)
        requires
            old(self).wf(),
            old(out).wf(),
            old(out)@.len() + MAX_OUTS <= old(out).cap(),
        ensures
            final(out).wf(),
            final(out).cap() == old(out).cap(),
            final(out)@.len() <= old(out)@.len() + MAX_OUTS,
            step(*old(self), *final(self), old(out)@, final(out)@),
            final(self).goaways() == old(self).goaways(),
            frame(*old(self), *final(self), Some(stream_id)),
            stream_id % 4 != 2 ==> final(self).peer_max_field_section() == old(
                self,
            ).peer_max_field_section(),
            !old(self).closed() && stream_id % 4 != 0 && stream_id % 4 != 2 ==> added(
                old(out)@,
                final(out)@,
            ) == seq![SpecOutput::CloseConnection { code: H3_STREAM_CREATION_ERROR }],
            !old(self).closed() && stream_id % 4 == 0 ==> req_call(
                *old(self),
                *final(self),
                stream_id,
                data@,
                fin,
                added(old(out)@, final(out)@),
            ),
            !old(self).closed() && stream_id % 4 == 2 ==> uni_fed(
                *old(self),
                *final(self),
                stream_id,
                data@,
                fin,
                added(old(out)@, final(out)@),
            ),
            old(self).closed() || stream_id % 4 != 0 ==> final(self).highest_accepted() == old(
                self,
            ).highest_accepted(),
            old(self).closed() || stream_id % 4 != 2 ==> final(self).uni_seen() == old(
                self,
            ).uni_seen(),
            // `removed_fields` is not bounded by the call's input: N6, owned by carryover cat-C15-teardown (9b4).
            r@ <= c_in() * (data@.len() + 1) + c_map() * (ht_of(*old(self), stream_id) + 1) + c_held()
                * old(self).buffered_of(stream_id) + c_free() * removed_fields(*old(self), *final(self), stream_id),
    {
        if self.closed {
            proof {
                Self::lemma_idle(*self, out@);
            }
            return Ghost(0);
        }
        if stream_id % 4 == 0 {
            let r = self.request_data(stream_id, data, fin, out);
            proof {
                reveal(req_done);
            }
            r
        } else if stream_id % 4 == 2 {
            let r = self.uni_data(stream_id, data, fin, out);
            proof {
                reveal(uni_done);
            }
            r
        } else {
            // Server-initiated IDs: the peer cannot send on them (RFC 9000 §2.1); the QUIC layer
            // normally refuses such data first.
            self.close(H3_STREAM_CREATION_ERROR, out);
            // The close's output.
            Ghost(1)
        }
    }

    /// `on_stream_data` on a request stream: looks its entry up and dispatches on its state.
    fn request_data(&mut self, id: u64, data: &[u8], fin: bool, out: &mut CapVec<Output>) -> (r: Ghost<nat>)
        requires
            old(self).wf(),
            !old(self).closed,
            id % 4 == 0,
            old(out).wf(),
            old(out)@.len() + MAX_OUTS <= old(out).cap(),
        ensures
            req_done(*old(self), *final(self), *old(out), *final(out), id, data@, fin),
            r@ <= c_in() * (data@.len() + 1) + c_map() * (ht(old(self).reqs) + 1) + c_held() * old(
                self,
            ).buffered_of(id) + c_free() * removed_fields(*old(self), *final(self), id),
    {
        let ghost c0 = *self;
        let ghost mut work: nat = 0;
        proof {
            lemma_tables_open(c0.reqs, c0.unis, c0.rhist@, c0.uhist@, c0.rstate@, c0.uset@);
        }
        let (g, Ghost(cg)) = tbl_get(&self.reqs, id);
        let rx = match g {
            Some(e) => Some(e.rx_open),
            None => None,
        };
        proof {
            lemma_req_get(tv(c0.reqs), c0.rhist@, c0.rstate@, id);
            work = work + cg;
            assert(c_get() == 1 && c_free() == 1 && c_join() == 6 && c_join2() == 13);
        }
        match rx {
            Some(true) => {
                let Ghost(c) = self.request_feed(id, data, fin, out);
                proof {
                    work = work + c;
                }
            },
            Some(false) => {
                let Ghost(c) = self.request_idle(id, Ghost(data@), fin, out);
                proof {
                    work = work + c;
                }
            },
            None => {
                let Ghost(c) = self.request_data_new(id, data, fin, out);
                proof {
                    work = work + c;
                }
            },
        }
        Ghost(work)
    }

    /// `request_data` for a stream no longer received (finished, or abandoned awaiting the peer's FIN or reset): nothing
    /// is output, and a FIN may forget it.
    // `out` is in the ensures only: nothing is output.
    #[allow(unused_variables)]
    fn request_idle(&mut self, id: u64, Ghost(data): Ghost<Seq<u8>>, fin: bool, out: &mut CapVec<Output>) -> (r: Ghost<nat>)
        requires
            old(self).wf(),
            !old(self).closed,
            id % 4 == 0,
            old(self).req_known(id),
            !old(self).req_receiving(id),
            old(out).wf(),
            old(out)@.len() + MAX_OUTS <= old(out).cap(),
        ensures
            req_done(*old(self), *final(self), *old(out), *final(out), id, data, fin),
            r@ <= c_take() * (ht(old(self).reqs) + 1) + c_join2() * (ht(old(self).reqs) + 1) + 4 + removed_fields(*old(self), *final(self), id),
    {
        let ghost c0 = *self;
        let ghost m0 = tv(self.reqs);
        let ghost h = ht(self.reqs);
        proof {
            lemma_tables_open(c0.reqs, c0.unis, c0.rhist@, c0.uhist@, c0.rstate@, c0.uset@);
            reveal(req_done);
            lemma_req_get(m0, c0.rhist@, c0.rstate@, id);
            assert(c_join() == 6 && c_join2() == 13);
            Self::lemma_idle(c0, out@);
            assert(c0.goaways@.take(c0.goaways@.len() as int) =~= c0.goaways@);
            assert(c0.ctrl@ + Seq::<u8>::empty() =~= c0.ctrl@);
        }
        if !fin {
            proof {
                let o = out@;
                assert(step(c0, *self, o, o));
                assert(frame(c0, *self, Some(id)));
                assert(added(o, o) == Seq::<SpecOutput>::empty());
                assert(c0.req_state(id) == Some(ReqState { fin_seen: c0.req_state(id)->0.fin_seen || fin, ..c0.req_state(id)->0 }));
                assert(req_call(c0, *self, id, data, fin, added(o, o)));
            }
            return Ghost(0);
        }
        let ghost mut work: nat = 0;
        let t = self.reqs.take();
        let (lo, got, hi, Ghost(ct)) = req_take_w(t, id);
        // The entry's box is freed here.
        let mut e = *got.unwrap();
        proof {
            work = work + ct + 1;
        }
        if e.send_open {
            e.fin_seen = true;
            let b = Box::new(e);
            proof {
                lemma_req_set(m0, c0.rhist@, c0.rstate@, b);
                assert(c0.rhist@.insert(id, req_hist_of(e)) =~= c0.rhist@);
            }
            let (j, Ghost(cp)) = req_put_w(lo, b, hi, Ghost(h));
            self.reqs = j;
            self.rstate = Ghost(self.rstate@.insert(id, state_of(e)));
            proof {
                // The new box.
                work = work + cp + 1;
                lemma_map_put(m0, id, b);
            }
        } else {
            let (j, Ghost(cj)) = tbl_join(lo, hi, Ghost(id), Ghost(0), Ghost(h));
            self.reqs = j;
            self.rstate = Ghost(self.rstate@.remove(id));
            proof {
                lemma_req_del(m0, c0.rhist@, c0.rhist@, c0.rstate@, id);
                // `e` is dropped here.
                work = work + cj + req_frees(e);
                assert(ct <= 44 * (h + 1));
                assert(cj <= 13 * (h + 1));
                assert(h == ht(c0.reqs));
                assert(e == *m0[id]);
                assert(removed_fields(c0, *self, id) == 2 * e.trailers@.len());
            }
        }
        proof {
            lemma_tables_close(self.reqs, self.unis, self.rhist@, self.uhist@, self.rstate@, self.uset@);
            Self::lemma_idle(*self, out@);
        }
        Ghost(work)
    }

    /// `request_data` for a stream still received: its entry is taken out, its machine fed, and the entry put back
    /// unless the request has ended both ways.
    fn request_feed(&mut self, id: u64, data: &[u8], fin: bool, out: &mut CapVec<Output>) -> (r: Ghost<nat>)
        requires
            old(self).wf(),
            !old(self).closed,
            id % 4 == 0,
            old(self).req_receiving(id),
            old(out).wf(),
            old(out)@.len() + MAX_OUTS <= old(out).cap(),
        ensures
            req_done(*old(self), *final(self), *old(out), *final(out), id, data@, fin),
            r@ <= c_fr() * (data@.len() + 16) + 154 * (data@.len() + 16) + c_held() * old(self).buffered_of(id)
                + c_take() * (ht(old(self).reqs) + 1) + c_join2() * (ht(old(self).reqs) + 1) + 4 + removed_fields(
                *old(self),
                *final(self),
                id,
            ),
    {
        let ghost c0 = *self;
        let ghost m0 = tv(self.reqs);
        let ghost h = ht(self.reqs);
        let ghost mut work: nat = 0;
        proof {
            lemma_tables_open(c0.reqs, c0.unis, c0.rhist@, c0.uhist@, c0.rstate@, c0.uset@);
            lemma_req_get(m0, c0.rhist@, c0.rstate@, id);
            assert(c_join() == 6 && c_join2() == 13);
        }
        let t = self.reqs.take();
        let (lo, got, hi, Ghost(ct)) = req_take_w(t, id);
        // The entry's box is freed here.
        let mut e = *got.unwrap();
        let ghost e0 = e;
        proof {
            assert(e0 == *m0[id]);
            assert(c0.buffered_of(id) == e0.stream.buffered());
        }
        let pm = self.peer_max;
        let (closing, Ghost(cf)) = feed_req_ok(&mut e, data, fin, pm, out);
        self.rhist = Ghost(self.rhist@.insert(id, req_hist_of(e)));
        proof {
            work = work + ct + 1 + cf;
        }
        if closing {
            // Put back, so the table's two halves are not dropped here.
            let (j, Ghost(cp)) = req_put_w(lo, Box::new(e), hi, Ghost(h));
            self.reqs = j;
            self.closed = true;
            proof {
                // The new box.
                work = work + cp + 1;
                lemma_feed_cost_put(ct, cf, cp + 1, h, data@.len(), e0.stream.buffered());
                lemma_feed_done(c0, *self, *old(out), *out, id, data@, fin, e0, e, closing);
            }
            return Ghost(work);
        }
        if e.fin_seen && !e.send_open {
            let (j, Ghost(cj)) = tbl_join(lo, hi, Ghost(id), Ghost(0), Ghost(h));
            self.reqs = j;
            self.rstate = Ghost(self.rstate@.remove(id));
            proof {
                lemma_req_del(m0, c0.rhist@, self.rhist@, c0.rstate@, id);
                // `e` is dropped here.
                work = work + cj + req_frees(e);
                lemma_feed_cost(ct, cf, cj + req_frees(e), h, data@.len(), e0.stream.buffered(), e0.trailers@.len(), e.trailers@.len());
                assert(removed_fields(c0, *self, id) == 2 * e0.trailers@.len());
            }
        } else {
            let b = Box::new(e);
            proof {
                lemma_req_set(m0, c0.rhist@, c0.rstate@, b);
            }
            let (j, Ghost(cp)) = req_put_w(lo, b, hi, Ghost(h));
            self.reqs = j;
            self.rstate = Ghost(self.rstate@.insert(id, state_of(e)));
            proof {
                // The new box.
                work = work + cp + 1;
                lemma_map_put(m0, id, b);
                lemma_feed_cost_put(ct, cf, cp + 1, h, data@.len(), e0.stream.buffered());
            }
        }
        proof {
            lemma_tables_close(self.reqs, self.unis, self.rhist@, self.uhist@, self.rstate@, self.uset@);
            lemma_feed_done(c0, *self, *old(out), *out, id, data@, fin, e0, e, closing);
        }
        Ghost(work)
    }

    /// `request_data` for a new stream at or above our GOAWAY ID: rejected, and kept (not received, not answerable)
    /// until the peer's FIN or reset.
    fn request_reject(&mut self, id: u64, Ghost(data): Ghost<Seq<u8>>, fin: bool, out: &mut CapVec<Output>) -> (r: Ghost<nat>)
        requires
            old(self).wf(),
            !old(self).closed,
            id % 4 == 0,
            !old(self).req_known(id),
            rejected_id(*old(self), id),
            old(out).wf(),
            old(out)@.len() + MAX_OUTS <= old(out).cap(),
        ensures
            req_done(*old(self), *final(self), *old(out), *final(out), id, data, fin),
            r@ <= c_take() * (ht(old(self).reqs) + 1) + c_join() * (ht(old(self).reqs) + 1) + 3,
    {
        let ghost c0 = *self;
        let ghost o0 = out@;
        let ghost m0 = tv(self.reqs);
        let ghost h = ht(self.reqs);
        let ghost mut work: nat = 0;
        proof {
            lemma_tables_open(c0.reqs, c0.unis, c0.rhist@, c0.uhist@, c0.rstate@, c0.uset@);
            lemma_added_refl(o0);
            lemma_req_get(m0, c0.rhist@, c0.rstate@, id);
            assert(c_join() == 6);
        }
        //= https://www.rfc-editor.org/rfc/rfc9114#section-5.2
        //# Upon sending a GOAWAY frame, the endpoint
        //# SHOULD explicitly cancel (see Sections 4.1.1 and 7.2.3) any requests
        //# or pushes that have identifiers greater than or equal to the one
        //# indicated, in order to clean up transport state for the affected
        //# streams.
        reject(id, fin, out);
        proof {
            // `reject`'s outputs.
            work = work + 2;
        }
        if !fin {
            // Kept until the peer's FIN or reset, so data in flight is ignored.
            let e = ReqEntry {
                id,
                stream: RequestStream::new(),
                rx_open: false,
                fin_seen: false,
                head: false,
                is_head: false,
                send_open: false,
                trailers: Vec::new(),
            };
            let b = Box::new(e);
            let t = self.reqs.take();
            let (lo, _none, hi, Ghost(ct)) = req_take_w(t, id);
            proof {
                lemma_req_set(m0, c0.rhist@, c0.rstate@, b);
                lemma_map_absent(m0, id);
            }
            let (j, Ghost(cp)) = req_put_w(lo, b, hi, Ghost(h));
            self.reqs = j;
            self.rhist = Ghost(self.rhist@.insert(id, req_hist_of(e)));
            self.rstate = Ghost(self.rstate@.insert(id, state_of(e)));
            proof {
                // The new box.
                work = work + ct + cp + 1;
                lemma_map_put(m0, id, b);
            }
        }
        proof {
            lemma_tables_close(self.reqs, self.unis, self.rhist@, self.uhist@, self.rstate@, self.uset@);
            reveal(req_done);
            assert(rejected_id(c0, id));
            lemma_writes_none(added(o0, out@), 3);
            assert(self.ctrl@ + Seq::<u8>::empty() =~= self.ctrl@);
            assert(self.goaways@.take(self.goaways@.len() as int) =~= self.goaways@);
        }
        Ghost(work)
    }

    /// `request_data` for a stream with no entry yet.
    fn request_data_new(&mut self, id: u64, data: &[u8], fin: bool, out: &mut CapVec<Output>) -> (r: Ghost<nat>)
        requires
            old(self).wf(),
            !old(self).closed,
            id % 4 == 0,
            !old(self).req_known(id),
            old(out).wf(),
            old(out)@.len() + MAX_OUTS <= old(out).cap(),
        ensures
            req_done(*old(self), *final(self), *old(out), *final(out), id, data@, fin),
            r@ <= c_fr() * (data@.len() + 16) + 154 * (data@.len() + 16) + c_take() * (ht(old(self).reqs) + 1) + c_join() * (ht(old(self).reqs) + 1) + 4,
    {
        let ghost c0 = *self;
        let ghost o0 = out@;
        let ghost m0 = tv(self.reqs);
        let ghost h = ht(self.reqs);
        let ghost mut work: nat = 0;
        proof {
            lemma_tables_open(c0.reqs, c0.unis, c0.rhist@, c0.uhist@, c0.rstate@, c0.uset@);
            lemma_added_refl(o0);
            lemma_req_get(m0, c0.rhist@, c0.rstate@, id);
        }
        if let Some(g) = self.goaway {
            if id >= g {
                return self.request_reject(id, Ghost(data@), fin, out);
            }
        }
        proof {
            assert(!rejected_id(c0, id));
        }
        let mut e = ReqEntry {
            id,
            stream: RequestStream::new(),
            rx_open: true,
            fin_seen: false,
            head: false,
            is_head: false,
            send_open: true,
            trailers: Vec::new(),
        };
        let ghost e0 = e;
        self.highest = match self.highest {
            Some(h) => if h < id {
                Some(id)
            } else {
                Some(h)
            },
            None => Some(id),
        };
        let pm = self.peer_max;
        let (closing, Ghost(cf)) = feed_req_ok(&mut e, data, fin, pm, out);
        self.rhist = Ghost(self.rhist@.insert(id, req_hist_of(e)));
        proof {
            work = work + cf;
        }
        if closing {
            proof {
                // `e` is dropped here (it has no box yet).
                work = work + req_frees(e);
            }
            self.closed = true;
            proof {
                lemma_new_done(c0, *self, *old(out), *out, id, data@, fin, e0, e, closing);
            }
            return Ghost(work);
        }
        if !(e.fin_seen && !e.send_open) {
            let b = Box::new(e);
            let t = self.reqs.take();
            let (lo, _none, hi, Ghost(ct)) = req_take_w(t, id);
            proof {
                lemma_req_set(m0, c0.rhist@, c0.rstate@, b);
                lemma_map_absent(m0, id);
            }
            let (j, Ghost(cp)) = req_put_w(lo, b, hi, Ghost(h));
            self.reqs = j;
            self.rstate = Ghost(self.rstate@.insert(id, state_of(e)));
            proof {
                // The new box.
                work = work + ct + cp + 1;
                lemma_map_put(m0, id, b);
            }
        } else {
            proof {
                // `e` is dropped here (it has no box).
                work = work + req_frees(e);
                lemma_req_del(m0, c0.rhist@, self.rhist@, c0.rstate@, id);
                lemma_map_absent(m0, id);
                lemma_map_absent(c0.rstate@, id);
            }
        }
        proof {
            lemma_tables_close(self.reqs, self.unis, self.rhist@, self.uhist@, self.rstate@, self.uset@);
            lemma_new_done(c0, *self, *old(out), *out, id, data@, fin, e0, e, closing);
        }
        Ghost(work)
    }

    /// `on_stream_data` on a peer uni stream: its entry (or a new one) is taken out, its machine fed, and the entry put
    /// back unless the stream ended.
    fn uni_data(&mut self, id: u64, data: &[u8], fin: bool, out: &mut CapVec<Output>) -> (r: Ghost<nat>)
        requires
            old(self).wf(),
            !old(self).closed,
            id % 4 == 2,
            old(out).wf(),
            old(out)@.len() + 1 <= old(out).cap(),
        ensures
            uni_done(*old(self), *final(self), *old(out), *final(out), id, data@, fin),
            r@ <= c_ud() * (data@.len() + 16) + uni::c_uni_frame() * old(self).buffered_of(id) + old(self).buffered_of(id)
                + c_take() * (ht(old(self).unis) + 1) + c_join2() * (ht(old(self).unis) + 1),
    {
        hide(uni::fed);
        let ghost c0 = *self;
        let ghost m0 = tv(self.unis);
        let ghost h = ht(self.unis);
        let ghost mut work: nat = 0;
        proof {
            lemma_tables_open(c0.reqs, c0.unis, c0.rhist@, c0.uhist@, c0.rstate@, c0.uset@);
            lemma_uni_get(m0, c0.uhist@, c0.uset@, id);
            assert(c_join() == 6 && c_join2() == 13);
        }
        let t = self.unis.take();
        let (lo, got, hi, Ghost(ct)) = uni_take_w(t, id);
        let mut e = match got {
            // The entry's box is freed here.
            Some(b) => *b,
            None => UniEntry { id, stream: UniStream::new() },
        };
        let ghost e_old = e;
        proof {
            assert(c0.buffered_of(id) == e_old.stream.buffered());
        }
        let mut evs: CapVec<UniEvent> = CapVec::new(data.len() / 3 + 1);
        let ghost ev0 = evs;
        let (r, Ghost(cu)) = e.stream.on_data(data, fin, &mut self.seen, &mut evs);
        self.uhist = Ghost(self.uhist@.insert(id, uni_hist_of(e)));
        proof {
            lemma_fed_facts(e_old.stream, e.stream, data@, fin, c0.seen, self.seen, ev0, evs, r, cu);
            evs.lemma_wf();
            // The box freed, and the event buffer's allocation.
            work = work + ct + 2 + cu;
        }
        match r {
            Err(c) => {
                // Put back, so the table's two halves are not dropped here.
                let (j, Ghost(cp)) = uni_put_w(lo, Box::new(e), hi, Ghost(h));
                self.unis = j;
                self.close(c, out);
                proof {
                    // The new box, and the close's output.
                    work = work + cp + 2;
                }
            },
            Ok(()) => {
                let Ghost(ca) = self.apply_settings(&evs);
                proof {
                    lemma_settings_apply_cost(
                        ca,
                        evs@.len(),
                        uni::ev_pairs(uni::views(evs@)),
                        data@.len(),
                        e_old.stream.buffered(),
                    );
                    work = work + ca;
                }
                let Ghost(cs) = self.uni_store(e, lo, hi, fin, Ghost(m0), Ghost(c0.uhist@), Ghost(h));
                proof {
                    work = work + cs;
                }
            },
        }
        proof {
            // `evs` is dropped here: its buffer and each event's.
            work = work + 1 + evs@.len();
            lemma_uni_cost(work, ct, cu, h, data@.len(), e_old.stream.buffered(), evs@.len());
            lemma_uni_done(c0, *self, *old(out), *out, id, data@, fin, e_old, e, ev0, evs, r, cu);
        }
        Ghost(work)
    }

    /// `uni_data`'s table update once the stream's call succeeded: `e` put back between `lo` and `hi`, or, at its FIN,
    /// forgotten (only a stream of unknown type ends cleanly): the halves joined and `e` dropped.
    fn uni_store(
        &mut self,
        e: UniEntry,
        lo: Tree<Box<UniEntry>>,
        hi: Tree<Box<UniEntry>>,
        fin: bool,
        Ghost(m0): Ghost<Map<u64, Box<UniEntry>>>,
        Ghost(h0): Ghost<Map<u64, UHist>>,
        Ghost(h): Ghost<nat>,
    ) -> (r: Ghost<nat>)
        requires
            tbl(lo, 2),
            tbl(hi, 2),
            keys_lt(lo, e.id),
            keys_gt(hi, e.id),
            e.id % 4 == 2,
            ht(lo) <= h,
            ht(hi) <= h,
            tv(lo).union_prefer_right(tv(hi)) == m0.remove(e.id),
            unis_ok(m0, h0),
            uni_dom(m0, old(self).uset@),
            old(self).uhist@ == h0.insert(e.id, uni_hist_of(e)),
            !fin ==> e.stream.wf() && !e.stream.done(),
            tbl(old(self).reqs, 0),
            reqs_ok(tv(old(self).reqs), old(self).rhist@),
            req_dom(tv(old(self).reqs), old(self).rstate@),
        ensures
            tables_ok(final(self).reqs, final(self).unis, final(self).rhist@, final(self).uhist@, final(self).rstate@, final(self).uset@),
            *final(self) == (H3Conn { unis: final(self).unis, uset: final(self).uset, ..*old(self) }),
            final(self).uset@ == (if fin {
                old(self).uset@.remove(e.id)
            } else {
                old(self).uset@.insert(e.id)
            }),
            r@ <= c_join2() * (h + 1) + 2,
    {
        let id = e.id;
        let ghost mut work: nat = 0;
        proof {
            assert(c_join() == 6 && c_join2() == 13);
        }
        if !fin {
            let b = Box::new(e);
            proof {
                lemma_uni_set(m0, h0, self.uset@, b);
            }
            let (j, Ghost(cp)) = uni_put_w(lo, b, hi, Ghost(h));
            self.unis = j;
            self.uset = Ghost(self.uset@.insert(id));
            proof {
                // The new box.
                work = work + cp + 1;
                lemma_map_put(m0, id, b);
                lemma_tables_close(self.reqs, self.unis, self.rhist@, self.uhist@, self.rstate@, self.uset@);
            }
        } else {
            let ghost us0 = self.uset@;
            let (j, Ghost(cj)) = tbl_join(lo, hi, Ghost(id), Ghost(2), Ghost(h));
            self.unis = j;
            self.uset = Ghost(self.uset@.remove(id));
            proof {
                lemma_uni_del(m0, h0, self.uhist@, us0, id);
                lemma_tables_close(self.reqs, self.unis, self.rhist@, self.uhist@, self.rstate@, self.uset@);
                // `e` is dropped here: its queue's buffers.
                work = work + cj + uni_frees();
            }
        }
        Ghost(work)
    }

    //= https://www.rfc-editor.org/rfc/rfc9114#section-9
    //# Implementations MUST ignore unknown or unsupported values in all
    //# extensible protocol elements.
    /// Records the peer's SETTINGS_MAX_FIELD_SECTION_SIZE (the last one); every other identifier
    /// is ignored (the QPACK settings don't matter with a dynamic table of capacity 0).
    fn apply_settings(&mut self, evs: &CapVec<UniEvent>) -> (r: Ghost<nat>)
        ensures
            final(self).peer_max == events_fs(uni::views(evs@), old(self).peer_max),
            *final(self) == (H3Conn { peer_max: final(self).peer_max, ..*old(self) }),
            r@ <= 1 + evs@.len() + uni::ev_pairs(uni::views(evs@)),
    {
        let ghost ev = uni::views(evs@);
        let ghost mut work: nat = 1;
        let mut k: usize = 0;
        proof {
            assert(ev.take(0) =~= Seq::<SpecUniEvent>::empty());
        }
        while k < evs.len()
            invariant
                k <= evs@.len(),
                ev == uni::views(evs@),
                *self == (H3Conn { peer_max: self.peer_max, ..*old(self) }),
                self.peer_max == events_fs(ev.take(k as int), old(self).peer_max),
                work <= 1 + k + uni::ev_pairs(ev.take(k as int)),
            decreases evs@.len() - k,
        {
            let ghost before = self.peer_max;
            let ghost w0 = work;
            proof {
                assert(ev.take(k + 1).drop_last() =~= ev.take(k as int));
                assert(ev.take(k + 1).last() == evs@[k as int]@);
            }
            if let UniEvent::PeerSettings(v) = evs.index(k) {
                let mut j: usize = 0;
                proof {
                    assert(v@.take(0) =~= Seq::<(u64, u64)>::empty());
                }
                while j < v.len()
                    invariant
                        j <= v@.len(),
                        *self == (H3Conn { peer_max: self.peer_max, ..*old(self) }),
                        self.peer_max == pairs_fs(v@.take(j as int), before),
                        work == w0 + j,
                    decreases v@.len() - j,
                {
                    let (s, x) = v[j];
                    proof {
                        assert(v@.take(j + 1).drop_last() =~= v@.take(j as int));
                        assert(v@.take(j + 1).last() == v@[j as int]);
                    }
                    if s == SETTINGS_MAX_FIELD_SECTION_SIZE {
                        self.peer_max = Some(x);
                    }
                    j += 1;
                    proof {
                        work = work + 1;
                    }
                }
                proof {
                    assert(v@.take(v@.len() as int) =~= v@);
                }
            }
            k += 1;
            proof {
                work = work + 1;
            }
        }
        proof {
            assert(ev.take(evs@.len() as int) =~= ev);
        }
        Ghost(work)
    }

    /// Closes our sending part of request stream `id`; its entry is dropped if the request has also ended.
    fn end_send(&mut self, id: u64) -> (r: Ghost<nat>)
        requires
            old(self).wf(),
            !old(self).closed,
            old(self).req_known(id),
        ensures
            final(self).wf(),
            *final(self) == (H3Conn { reqs: final(self).reqs, rstate: final(self).rstate, ..*old(self) }),
            frame(*old(self), *final(self), Some(id)),
            !final(self).req_respondable(id),
            final(self).req_receiving(id) == old(self).req_receiving(id),
            final(self).req_known(id) ==> final(self).req_state(id) == Some(
                ReqState { send_open: false, ..old(self).req_state(id)->0 },
            ),
            r@ <= c_take() * (ht(old(self).reqs) + 1) + c_join2() * (ht(old(self).reqs) + 1) + 4 + removed_fields(*old(self), *final(self), id),
    {
        let ghost c0 = *self;
        let ghost m0 = tv(self.reqs);
        let ghost h = ht(self.reqs);
        let ghost mut work: nat = 0;
        proof {
            lemma_tables_open(c0.reqs, c0.unis, c0.rhist@, c0.uhist@, c0.rstate@, c0.uset@);
            lemma_req_get(m0, c0.rhist@, c0.rstate@, id);
            assert(c_join() == 6 && c_join2() == 13);
        }
        let t = self.reqs.take();
        let (lo, got, hi, Ghost(ct)) = req_take_w(t, id);
        // The entry's box is freed here.
        let mut e = *got.unwrap();
        proof {
            work = work + ct + 1;
        }
        e.send_open = false;
        if !e.fin_seen {
            let b = Box::new(e);
            proof {
                lemma_req_set(m0, c0.rhist@, c0.rstate@, b);
                assert(c0.rhist@.insert(id, req_hist_of(e)) =~= c0.rhist@);
            }
            let (j, Ghost(cp)) = req_put_w(lo, b, hi, Ghost(h));
            self.reqs = j;
            self.rstate = Ghost(self.rstate@.insert(id, state_of(e)));
            proof {
                // The new box.
                work = work + cp + 1;
                lemma_map_put(m0, id, b);
            }
        } else {
            let (j, Ghost(cj)) = tbl_join(lo, hi, Ghost(id), Ghost(0), Ghost(h));
            self.reqs = j;
            self.rstate = Ghost(self.rstate@.remove(id));
            proof {
                lemma_req_del(m0, c0.rhist@, c0.rhist@, c0.rstate@, id);
                // `e` is dropped here.
                work = work + cj + req_frees(e);
            }
        }
        proof {
            lemma_tables_close(self.reqs, self.unis, self.rhist@, self.uhist@, self.rstate@, self.uset@);
        }
        Ghost(work)
    }

    //= https://www.rfc-editor.org/rfc/rfc9114#section-6.2.1
    //# If either control
    //# stream is closed at any point, this MUST be treated as a connection
    //# error of type H3_CLOSED_CRITICAL_STREAM.
    //= https://www.rfc-editor.org/rfc/rfc9204#section-4.2
    //# Closure of either unidirectional stream type MUST be treated as a
    //# connection error of type H3_CLOSED_CRITICAL_STREAM.
    //= https://www.rfc-editor.org/rfc/rfc9114#section-6.2
    //# A receiver MUST tolerate unidirectional streams being
    //# closed or reset prior to the reception of the unidirectional stream
    //# header.
    //= https://www.rfc-editor.org/rfc/rfc9114#section-8
    //# Because new error codes can be defined without negotiation (see
    //# Section 9), use of an error code in an unexpected context or receipt
    //# of an unknown error code MUST be treated as equivalent to
    //# H3_NO_ERROR.
    //= https://www.rfc-editor.org/rfc/rfc9114#section-4.1
    //# If a client-initiated
    //# stream terminates without enough of the HTTP message to provide a
    //# complete response, the server SHOULD abort its response stream with
    //# the error code H3_REQUEST_INCOMPLETE.
    /// The peer reset its sending part of `stream_id`. The error code changes nothing: every code
    /// is handled as H3_NO_ERROR would be. A reset peer control or QPACK stream closes the
    /// connection; any other uni stream is forgotten silently. A request stream is forgotten,
    /// and our sending part, if still open, is reset (`reset_outs`).
    pub fn on_stream_reset(&mut self, stream_id: u64, _code: u64, out: &mut CapVec<Output>) -> (r: Ghost<nat>)
        requires
            old(self).wf(),
            old(out).wf(),
            old(out)@.len() + MAX_OUTS <= old(out).cap(),
        ensures
            final(out).wf(),
            final(out).cap() == old(out).cap(),
            final(out)@.len() <= old(out)@.len() + MAX_OUTS,
            step(*old(self), *final(self), old(out)@, final(out)@),
            final(self).goaways() == old(self).goaways(),
            frame(*old(self), *final(self), Some(stream_id)),
            final(self).peer_max_field_section() == old(self).peer_max_field_section(),
            !old(self).closed() && stream_id % 4 == 2 && old(self).uni_known(stream_id) && critical(
                uni::kind_of_bytes(old(self).uni_hist(stream_id).0),
            ) ==> added(old(out)@, final(out)@) == seq![
                SpecOutput::CloseConnection { code: H3_CLOSED_CRITICAL_STREAM },
            ],
            !old(self).closed() && stream_id % 4 == 2 && !(old(self).uni_known(stream_id) && critical(
                uni::kind_of_bytes(old(self).uni_hist(stream_id).0),
            )) ==> added(old(out)@, final(out)@) == Seq::<SpecOutput>::empty() && !final(self).closed()
                && !final(self).uni_known(stream_id),
            !old(self).closed() && stream_id % 4 == 0 ==> added(old(out)@, final(out)@) == reset_outs(
                stream_id,
                old(self).req_state(stream_id),
            ) && !final(self).closed() && !final(self).req_known(stream_id),
            !old(self).closed() && stream_id % 4 != 0 && stream_id % 4 != 2 ==> added(
                old(out)@,
                final(out)@,
            ) == Seq::<SpecOutput>::empty() && !final(self).closed(),
            final(self).highest_accepted() == old(self).highest_accepted(),
            final(self).uni_seen() == old(self).uni_seen(),
            // `removed_fields` is not bounded by the call's input: N6, owned by carryover cat-C15-teardown (9b4).
            r@ <= c_in() + c_map() * (ht_of(*old(self), stream_id) + 1) + c_free() * removed_fields(
                *old(self),
                *final(self),
                stream_id,
            ),
    {
        let ghost c0 = *self;
        let ghost o0 = out@;
        let ghost mut work: nat = 0;
        proof {
            lemma_added_refl(o0);
        }
        if self.closed {
            proof {
                Self::lemma_idle(*self, out@);
            }
            return Ghost(0);
        }
        proof {
            lemma_tables_open(c0.reqs, c0.unis, c0.rhist@, c0.uhist@, c0.rstate@, c0.uset@);
            assert(c_get() == 1 && c_free() == 1 && c_join() == 6 && c_join2() == 13);
        }
        if stream_id % 4 == 2 {
            let ghost m0 = tv(self.unis);
            let ghost h = ht(self.unis);
            let (g, Ghost(cg)) = tbl_get(&self.unis, stream_id);
            proof {
                work = work + cg;
                lemma_uni_get(m0, c0.uhist@, c0.uset@, stream_id);
            }
            let k = match g {
                Some(e) => Some(e.stream.kind()),
                None => None,
            };
            match k {
                Some(UniKind::Control) | Some(UniKind::QpackEncoder) | Some(UniKind::QpackDecoder) => {
                    self.close(H3_CLOSED_CRITICAL_STREAM, out);
                    // The close's output.
                    return Ghost(work + 1);
                },
                Some(_) => {
                    let Ghost(cd) = self.reset_uni(stream_id);
                    proof {
                        work = work + cd;
                    }
                },
                None => {},
            }
        } else if stream_id % 4 == 0 {
            let Ghost(cr) = self.reset_req(stream_id, out);
            proof {
                work = work + cr;
            }
        }
        proof {
            if added(o0, out@).len() == 0 {
                Self::lemma_idle(c0, o0);
            }
            assert(c0.ctrl@ + Seq::<u8>::empty() =~= c0.ctrl@);
            assert(c0.goaways@.take(c0.goaways@.len() as int) =~= c0.goaways@);
        }
        Ghost(work)
    }

    /// `on_stream_reset` on a tracked uni stream of no critical type: it is forgotten (the halves joined, the entry
    /// dropped).
    fn reset_uni(&mut self, id: u64) -> (r: Ghost<nat>)
        requires
            old(self).wf(),
            !old(self).closed,
            id % 4 == 2,
            old(self).uset@.contains(id),
        ensures
            final(self).wf(),
            *final(self) == (H3Conn { unis: final(self).unis, uset: final(self).uset, ..*old(self) }),
            final(self).uset@ == old(self).uset@.remove(id),
            r@ <= c_take() * (ht(old(self).unis) + 1) + c_join2() * (ht(old(self).unis) + 1) + 3,
    {
        let ghost c0 = *self;
        let ghost m0 = tv(self.unis);
        let ghost h = ht(self.unis);
        let ghost mut work: nat = 0;
        proof {
            lemma_tables_open(c0.reqs, c0.unis, c0.rhist@, c0.uhist@, c0.rstate@, c0.uset@);
            lemma_uni_get(m0, c0.uhist@, c0.uset@, id);
            assert(c_join2() == 13);
        }
        let t = self.unis.take();
        let (lo, _e, hi, Ghost(ct)) = uni_take_w(t, id);
        let (j, Ghost(cj)) = tbl_join(lo, hi, Ghost(id), Ghost(2), Ghost(h));
        self.unis = j;
        self.uset = Ghost(self.uset@.remove(id));
        proof {
            lemma_uni_del(m0, c0.uhist@, c0.uhist@, c0.uset@, id);
            lemma_tables_close(self.reqs, self.unis, self.rhist@, self.uhist@, self.rstate@, self.uset@);
            // The entry is dropped here: its box and its queue's buffers.
            work = work + ct + cj + 1 + uni_frees();
        }
        Ghost(work)
    }

    /// `on_stream_reset` on a request stream: it is forgotten, and our sending part, if still open, is reset
    /// (`reset_outs`).
    fn reset_req(&mut self, id: u64, out: &mut CapVec<Output>) -> (r: Ghost<nat>)
        requires
            old(self).wf(),
            !old(self).closed,
            id % 4 == 0,
            old(out).wf(),
            old(out)@.len() + 1 <= old(out).cap(),
        ensures
            final(self).wf(),
            *final(self) == (H3Conn { reqs: final(self).reqs, rstate: final(self).rstate, ..*old(self) }),
            final(self).rstate@ == old(self).rstate@.remove(id),
            final(out).wf(),
            final(out).cap() == old(out).cap(),
            final(out)@.len() <= old(out)@.len() + 1,
            extends(old(out)@, final(out)@),
            added(old(out)@, final(out)@) == reset_outs(id, old(self).req_state(id)),
            outs_ok(added(old(out)@, final(out)@), false),
            writes_on(added(old(out)@, final(out)@), 3) == Seq::<u8>::empty(),
            r@ <= c_take() * (ht(old(self).reqs) + 1) + c_join2() * (ht(old(self).reqs) + 1) + 5 + removed_fields(
                *old(self),
                *final(self),
                id,
            ),
    {
        let ghost c0 = *self;
        let ghost o0 = out@;
        let ghost m0 = tv(self.reqs);
        let ghost h = ht(self.reqs);
        let ghost mut work: nat = 0;
        proof {
            lemma_added_refl(o0);
            lemma_tables_open(c0.reqs, c0.unis, c0.rhist@, c0.uhist@, c0.rstate@, c0.uset@);
            lemma_req_get(m0, c0.rhist@, c0.rstate@, id);
            assert(c_join2() == 13);
        }
        let t = self.reqs.take();
        let (lo, got, hi, Ghost(ct)) = req_take_w(t, id);
        let (j, Ghost(cj)) = tbl_join(lo, hi, Ghost(id), Ghost(0), Ghost(h));
        self.reqs = j;
        proof {
            work = work + ct + cj;
            lemma_map_absent(m0, id);
            lemma_map_absent(c0.rstate@, id);
        }
        if let Some(b) = got {
            let e = *b;
            proof {
                lemma_req_del(m0, c0.rhist@, c0.rhist@, c0.rstate@, id);
            }
            self.rstate = Ghost(self.rstate@.remove(id));
            if e.send_open {
                let code = if e.fin_seen {
                    H3_REQUEST_CANCELLED
                } else {
                    H3_REQUEST_INCOMPLETE
                };
                let w = Output::ResetStream { stream_id: id, code };
                out.push(w);
                proof {
                    lemma_added_push(o0, o0, w);
                    assert(added(o0, out@) =~= seq![w@]);
                    lemma_writes_one(w@, 3);
                    // The output.
                    work = work + 1;
                }
            }
            proof {
                // `e` is dropped here, and its box above.
                work = work + 1 + req_frees(e);
                assert(removed_fields(c0, *self, id) == 2 * e.trailers@.len());
            }
        }
        proof {
            lemma_tables_close(self.reqs, self.unis, self.rhist@, self.uhist@, self.rstate@, self.uset@);
            assert(writes_on(Seq::<SpecOutput>::empty(), 3) == Seq::<u8>::empty());
        }
        Ghost(work)
    }

    //= https://www.rfc-editor.org/rfc/rfc9114#section-6.2.1
    //# The
    //# sender MUST NOT close the control stream, and the receiver MUST NOT
    //# request that the sender close the control stream.
    /// The peer sent STOP_SENDING for our sending part of `stream_id`; the error code changes
    /// nothing (RFC 9114 §8). On our control stream it is a request to close a critical stream:
    /// H3_CLOSED_CRITICAL_STREAM. On a request stream, the pending response is dropped (the QUIC
    /// layer answers with RESET_STREAM, RFC 9000 §3.5); the request is still received.
    pub fn on_stop_sending(&mut self, stream_id: u64, _code: u64, out: &mut CapVec<Output>) -> (r: Ghost<nat>)
        requires
            old(self).wf(),
            old(out).wf(),
            old(out)@.len() + MAX_OUTS <= old(out).cap(),
        ensures
            final(out).wf(),
            final(out).cap() == old(out).cap(),
            final(out)@.len() <= old(out)@.len() + MAX_OUTS,
            step(*old(self), *final(self), old(out)@, final(out)@),
            final(self).goaways() == old(self).goaways(),
            frame(*old(self), *final(self), Some(stream_id)),
            final(self).peer_max_field_section() == old(self).peer_max_field_section(),
            !old(self).closed() && stream_id == 3 ==> added(old(out)@, final(out)@) == seq![
                SpecOutput::CloseConnection { code: H3_CLOSED_CRITICAL_STREAM },
            ],
            !old(self).closed() ==> !final(self).req_respondable(stream_id),
            !old(self).closed() && stream_id != 3 ==> added(old(out)@, final(out)@) == Seq::<
                SpecOutput,
            >::empty() && !final(self).closed() && final(self).req_receiving(stream_id) == old(
                self,
            ).req_receiving(stream_id) && (final(self).req_known(stream_id) ==> old(self).req_known(
                stream_id,
            ) && final(self).req_state(stream_id) == Some(
                ReqState { send_open: false, ..old(self).req_state(stream_id)->0 },
            )),
            final(self).req_hist(stream_id) == old(self).req_hist(stream_id),
            final(self).highest_accepted() == old(self).highest_accepted(),
            final(self).uni_seen() == old(self).uni_seen(),
            // `removed_fields` is not bounded by the call's input: N6, owned by carryover cat-C15-teardown (9b4).
            r@ <= c_in() + c_map() * (ht_of(*old(self), stream_id) + 1) + c_free() * removed_fields(
                *old(self),
                *final(self),
                stream_id,
            ),
    {
        let ghost c0 = *self;
        if self.closed {
            proof {
                Self::lemma_idle(*self, out@);
            }
            return Ghost(0);
        }
        proof {
            lemma_tables_open(c0.reqs, c0.unis, c0.rhist@, c0.uhist@, c0.rstate@, c0.uset@);
            lemma_req_get(tv(c0.reqs), c0.rhist@, c0.rstate@, stream_id);
            lemma_req_get(tv(c0.reqs), c0.rhist@, c0.rstate@, 3);
            assert(c_get() == 1 && c_free() == 1);
        }
        if stream_id == 3 {
            self.close(H3_CLOSED_CRITICAL_STREAM, out);
            // The close's output.
            return Ghost(1);
        }
        if stream_id % 4 != 0 {
            // No request stream: request keys are 0 mod 4 (`tbl(reqs, 0)`).
            proof {
                Self::lemma_idle(*self, out@);
            }
            return Ghost(0);
        }
        let ghost mut work: nat = 0;
        let (g, Ghost(cg)) = tbl_get(&self.reqs, stream_id);
        let known = g.is_some();
        proof {
            work = work + cg;
        }
        if known {
            let Ghost(ce) = self.end_send(stream_id);
            proof {
                work = work + ce;
            }
        }
        proof {
            Self::lemma_idle(*self, out@);
            assert(c0.ctrl@ + Seq::<u8>::empty() =~= c0.ctrl@);
            assert(c0.goaways@.take(c0.goaways@.len() as int) =~= c0.goaways@);
        }
        Ghost(work)
    }

    //= https://www.rfc-editor.org/rfc/rfc9114#section-4.1
    //# After sending a final
    //# response, the server MUST close the stream for sending.
    /// Sends `resp` on request stream `stream_id`: HEADERS (`:status` first), then DATA if the
    /// body is non-empty, then FIN. `Err` with nothing written if the connection is closed,
    /// `resp` would be malformed for this request (`check_response`; a HEAD request, tracked per
    /// stream, takes no content), the stream has no delivered request or
    /// already has a response, or the field section exceeds the peer's limit.
    ///
    /// Caller's obligation (RFC 9110 §8.6 MUST NOT; the transport can't check it): on a response
    /// to HEAD, or a 304, a `content-length` must be the length a GET would have had (a 200).
    #[verifier::spinoff_prover]
    pub fn send_response(&mut self, stream_id: u64, resp: &Response, out: &mut Vec<Output>) -> (r: Result<(), ()>)
        requires
            old(self).wf(),
        ensures
            step(*old(self), *final(self), old(out)@, final(out)@),
            final(self).goaways() == old(self).goaways(),
            final(self).closed() == old(self).closed(),
            final(self).peer_max_field_section() == old(self).peer_max_field_section(),
            frame(*old(self), *final(self), Some(stream_id)),
            final(self).req_hist(stream_id) == old(self).req_hist(stream_id),
            final(self).req_receiving(stream_id) == old(self).req_receiving(stream_id),
            final(self).highest_accepted() == old(self).highest_accepted(),
            final(self).uni_seen() == old(self).uni_seen(),
            r is Ok ==> !old(self).closed() && old(self).req_respondable(stream_id) && valid_response(
                resp@,
                old(self).req_state(stream_id)->0.is_head,
            ) && fits_peer(old(self).peer_max_field_section(), fields_size(resp_fields(resp@)))
                && one_response(added(old(out)@, final(out)@), stream_id, resp@) && !final(self).req_respondable(stream_id)
                && (final(self).req_known(stream_id) ==> final(self).req_state(stream_id) == Some(
                ReqState { send_open: false, ..old(self).req_state(stream_id)->0 },
            )),
            r is Err ==> final(out)@ == old(out)@ && final(self).req_state(stream_id) == old(self).req_state(stream_id),
            old(self).closed() || !old(self).req_respondable(stream_id) || !valid_response(
                resp@,
                old(self).req_state(stream_id)->0.is_head,
            ) ==> r is Err,
    {
        hide(one_response);
        hide(valid_response);
        hide(fits_peer);
        hide(resp_fields);
        hide(ctrl_preamble);
        hide(goaway_frames);
        hide(spec_frame_bytes);
        hide(spec_frame_header_bytes);
        hide(spec_varint);
        hide(spec_pairs_bytes);
        hide(rfc_frame_header);
        hide(response_wire);
        let ghost c0 = *self;
        let ghost o0 = out@;
        proof {
            Self::lemma_idle(*self, out@);
        }
        if self.closed {
            return Err(());
        }
        proof {
            lemma_tables_open(c0.reqs, c0.unis, c0.rhist@, c0.uhist@, c0.rstate@, c0.uset@);
            lemma_req_get(tv(c0.reqs), c0.rhist@, c0.rstate@, stream_id);
        }
        // `send_response` is the outbound side, not an input call: its costs (this lookup, `end_send`) are uncharged,
        // carryover cat-C15-9b4's (sweep H11).
        let (g, Ghost(_cg)) = tbl_get(&self.reqs, stream_id);
        let (head, send_open, is_head) = match g {
            Some(e) => (e.head, e.send_open, e.is_head),
            None => {
                return Err(());
            },
        };
        if !(head && send_open) {
            return Err(());
        }
        if !check_response(resp, is_head) {
            return Err(());
        }
        //= https://www.rfc-editor.org/rfc/rfc9114#section-7.2.4.2
        //# An HTTP implementation MUST NOT send frames or requests that would be
        //# invalid based on its current understanding of the peer's settings.
        if !write_response(stream_id, resp, self.peer_max, out) {
            return Err(());
        }
        let Ghost(_ce) = self.end_send(stream_id);
        proof {
            reveal(one_response);
            let a = added(o0, out@);
            assert(stream_id % 4 == 0);
            assert(a[0] == a.take(1)[0]);
            assert(ctrl_free(a[0]));
            lemma_writes_none(a, 3);
            assert(c0.ctrl@ + Seq::<u8>::empty() =~= c0.ctrl@);
            assert(c0.goaways@.take(c0.goaways@.len() as int) =~= c0.goaways@);
        }
        Ok(())
    }
}

} // verus!
