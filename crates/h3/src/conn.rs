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
use vstd::slice::slice_to_vec;
use wire::varint::VARINT_MAX;
#[allow(unused_imports)]
use wire::varint::*;

use crate::codes::*;
use crate::frame::*;
pub use crate::limits::*;
use crate::message::*;
use crate::qpack::field_section::*;
use crate::request::{ReqError, ReqEvent, RequestStream, SpecReqEvent};
use crate::uni::{SeenUni, SpecUniEvent, UniEvent, UniKind, UniStream};
// Used only in ghost code, which a plain `cargo build` erases.
#[allow(unused_imports)]
use crate::qpack::int::PREFIX_INT_MAX;
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

/// Moves `v` into reverse order, so popping yields its elements first to last.
fn rev<T>(v: Vec<T>) -> (r: Vec<T>)
    ensures
        r@.len() == v@.len(),
        forall|i: int| 0 <= i < v@.len() ==> r@[i] == v@[v@.len() - 1 - i],
{
    let ghost v0 = v@;
    let mut v = v;
    let mut r: Vec<T> = Vec::new();
    while v.len() > 0
        invariant
            v@.len() + r@.len() == v0.len(),
            v@ == v0.take(v@.len() as int),
            forall|i: int| 0 <= i < r@.len() ==> r@[i] == v0[v0.len() - 1 - i],
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
            },
            None => {},
        }
    }
    r
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
        let b = body_frames(r.body@);
        assert(enc@.skip(0) =~= enc@);
        assert(data@ =~= spec_frame_bytes(FRAME_HEADERS, enc@) + b);
        lemma_frame_bytes_roundtrip(FRAME_HEADERS, enc@, b);
        let h = spec_frame_header_bytes(FRAME_HEADERS, enc@.len() as u64).len();
        assert(data@.skip((h + enc@.len()) as int) =~= b);
    }
    let ghost o0 = out@;
    let w = Output::StreamWrite { stream_id: id, data, fin: true };
    out.push(w);
    proof {
        lemma_added_refl(o0);
        lemma_added_push(o0, o0, w);
        assert(added(o0, out@) =~= seq![w@]);
        assert(added(o0, out@).take(1) =~= added(o0, out@));
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

spec fn reqs_ok(s: Seq<ReqEntry>, h: Map<u64, (Seq<u8>, Seq<SpecReqEvent>, Fields)>) -> bool {
    &&& forall|j: int, k: int|
        0 <= j < s.len() && 0 <= k < s.len() && j != k ==> (#[trigger] s[j]).id != (
        #[trigger] s[k]).id
    &&& forall|k: int|
        0 <= k < s.len() ==> req_entry_ok(#[trigger] s[k]) && h.contains_key(s[k].id) && h[s[k].id]
            == req_hist_of(s[k])
}

spec fn unis_ok(s: Seq<UniEntry>, h: Map<u64, (Seq<u8>, SeenUni, Seq<SpecUniEvent>)>) -> bool {
    &&& forall|j: int, k: int|
        0 <= j < s.len() && 0 <= k < s.len() && j != k ==> (#[trigger] s[j]).id != (
        #[trigger] s[k]).id
    &&& forall|k: int|
        0 <= k < s.len() ==> (#[trigger] s[k]).id % 4 == 2 && s[k].stream.wf()
            && !s[k].stream.done() && h.contains_key(s[k].id) && h[s[k].id] == uni_hist_of(s[k])
}

proof fn lemma_reqs_remove(
    s: Seq<ReqEntry>,
    h: Map<u64, (Seq<u8>, Seq<SpecReqEvent>, Fields)>,
    h2: Map<u64, (Seq<u8>, Seq<SpecReqEvent>, Fields)>,
    i: int,
)
    requires
        reqs_ok(s, h),
        0 <= i < s.len(),
        forall|id: u64|
            #![trigger h2.contains_key(id)]
            #![trigger h2[id]]
            id != s[i].id && h.contains_key(id) ==> h2.contains_key(id) && h2[id] == h[id],
    ensures
        reqs_ok(s.remove(i), h2),
        forall|k: int| 0 <= k < s.remove(i).len() ==> (#[trigger] s.remove(i)[k]).id != s[i].id,
{
    let t = s.remove(i);
    assert forall|k: int| 0 <= k < t.len() implies t[k] == s[if k < i { k } else { k + 1 }] by {}
    assert forall|j: int, k: int|
        0 <= j < t.len() && 0 <= k < t.len() && j != k implies (#[trigger] t[j]).id != (
        #[trigger] t[k]).id by {
        let jj = if j < i { j } else { j + 1 };
        let kk = if k < i { k } else { k + 1 };
        assert(t[j] == s[jj] && t[k] == s[kk]);
    }
    assert forall|k: int| 0 <= k < t.len() implies req_entry_ok(#[trigger] t[k]) && h2.contains_key(
        t[k].id,
    ) && h2[t[k].id] == req_hist_of(t[k]) by {
        let kk = if k < i { k } else { k + 1 };
        assert(t[k] == s[kk]);
        assert(s[kk].id != s[i].id);
    }
    assert forall|k: int| 0 <= k < t.len() implies (#[trigger] t[k]).id != s[i].id by {
        let kk = if k < i { k } else { k + 1 };
        assert(t[k] == s[kk]);
    }
}

proof fn lemma_unis_remove(
    s: Seq<UniEntry>,
    h: Map<u64, (Seq<u8>, SeenUni, Seq<SpecUniEvent>)>,
    i: int,
)
    requires
        unis_ok(s, h),
        0 <= i < s.len(),
    ensures
        unis_ok(s.remove(i), h),
        forall|k: int| 0 <= k < s.remove(i).len() ==> (#[trigger] s.remove(i)[k]).id != s[i].id,
{
    let t = s.remove(i);
    assert forall|k: int| 0 <= k < t.len() implies t[k] == s[if k < i { k } else { k + 1 }] by {}
    assert forall|j: int, k: int|
        0 <= j < t.len() && 0 <= k < t.len() && j != k implies (#[trigger] t[j]).id != (
        #[trigger] t[k]).id by {
        let jj = if j < i { j } else { j + 1 };
        let kk = if k < i { k } else { k + 1 };
        assert(t[j] == s[jj] && t[k] == s[kk]);
    }
    assert forall|k: int| 0 <= k < t.len() implies (#[trigger] t[k]).id % 4 == 2 && t[k].stream.wf()
        && !t[k].stream.done() && h.contains_key(t[k].id) && h[t[k].id] == uni_hist_of(t[k]) && t[k].id
        != s[i].id by {
        let kk = if k < i { k } else { k + 1 };
        assert(t[k] == s[kk]);
    }
}

/// The table is unchanged and `id` is not in it: updating `id`'s history keeps the invariant.
proof fn lemma_unis_hist(
    s: Seq<UniEntry>,
    h: Map<u64, (Seq<u8>, SeenUni, Seq<SpecUniEvent>)>,
    h2: Map<u64, (Seq<u8>, SeenUni, Seq<SpecUniEvent>)>,
    id: u64,
)
    requires
        unis_ok(s, h),
        forall|k: int| 0 <= k < s.len() ==> (#[trigger] s[k]).id != id,
        forall|x: u64|
            #![trigger h2.contains_key(x)]
            #![trigger h2[x]]
            x != id && h.contains_key(x) ==> h2.contains_key(x) && h2[x] == h[x],
    ensures
        unis_ok(s, h2),
{
    assert forall|k: int| 0 <= k < s.len() implies (#[trigger] s[k]).id % 4 == 2 && s[k].stream.wf()
        && !s[k].stream.done() && h2.contains_key(s[k].id) && h2[s[k].id] == uni_hist_of(s[k]) by {
        assert(s[k].id != id);
    }
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

/// `st` mirrors the table: exactly its IDs, each with its entry's state.
spec fn req_dom(s: Seq<ReqEntry>, st: Map<u64, ReqState>) -> bool {
    &&& forall|k: int|
        0 <= k < s.len() ==> st.contains_key((#[trigger] s[k]).id) && st[s[k].id] == state_of(s[k])
    &&& forall|id: u64|
        #[trigger] st.contains_key(id) ==> exists|k: int| 0 <= k < s.len() && (#[trigger] s[k]).id
            == id
}

spec fn uni_dom(s: Seq<UniEntry>, us: Set<u64>) -> bool {
    &&& forall|k: int| 0 <= k < s.len() ==> us.contains((#[trigger] s[k]).id)
    &&& forall|id: u64|
        #[trigger] us.contains(id) ==> exists|k: int| 0 <= k < s.len() && (#[trigger] s[k]).id == id
}

proof fn lemma_dom_update(
    s: Seq<ReqEntry>,
    h: Map<u64, (Seq<u8>, Seq<SpecReqEvent>, Fields)>,
    st: Map<u64, ReqState>,
    i: int,
    e: ReqEntry,
)
    requires
        reqs_ok(s, h),
        req_dom(s, st),
        0 <= i < s.len(),
        e.id == s[i].id,
    ensures
        req_dom(s.update(i, e), st.insert(e.id, state_of(e))),
{
    let t = s.update(i, e);
    let st2 = st.insert(e.id, state_of(e));
    assert forall|k: int| 0 <= k < t.len() implies st2.contains_key((#[trigger] t[k]).id) && st2[t[k].id]
        == state_of(t[k]) by {
        if k != i {
            assert(s[k].id != s[i].id);
        }
    }
    assert forall|id: u64| #[trigger] st2.contains_key(id) implies exists|k: int|
        0 <= k < t.len() && (#[trigger] t[k]).id == id by {
        if id == e.id {
            assert(t[i].id == id);
        } else {
            let k = choose|k: int| 0 <= k < s.len() && (#[trigger] s[k]).id == id;
            assert(t[k].id == id);
        }
    }
}

proof fn lemma_dom_push(s: Seq<ReqEntry>, st: Map<u64, ReqState>, e: ReqEntry)
    requires
        req_dom(s, st),
        forall|k: int| 0 <= k < s.len() ==> (#[trigger] s[k]).id != e.id,
    ensures
        req_dom(s.push(e), st.insert(e.id, state_of(e))),
{
    let t = s.push(e);
    let st2 = st.insert(e.id, state_of(e));
    assert forall|k: int| 0 <= k < t.len() implies st2.contains_key((#[trigger] t[k]).id) && st2[t[k].id]
        == state_of(t[k]) by {
        if k < s.len() {
            assert(t[k] == s[k]);
            assert(s[k].id != e.id);
        }
    }
    assert forall|id: u64| #[trigger] st2.contains_key(id) implies exists|k: int|
        0 <= k < t.len() && (#[trigger] t[k]).id == id by {
        if id == e.id {
            assert(t[s.len() as int].id == id);
        } else {
            let k = choose|k: int| 0 <= k < s.len() && (#[trigger] s[k]).id == id;
            assert(t[k].id == id);
        }
    }
}

proof fn lemma_dom_remove(
    s: Seq<ReqEntry>,
    h: Map<u64, (Seq<u8>, Seq<SpecReqEvent>, Fields)>,
    st: Map<u64, ReqState>,
    i: int,
)
    requires
        reqs_ok(s, h),
        req_dom(s, st),
        0 <= i < s.len(),
    ensures
        req_dom(s.remove(i), st.remove(s[i].id)),
{
    let t = s.remove(i);
    let st2 = st.remove(s[i].id);
    assert forall|k: int| 0 <= k < t.len() implies t[k] == s[if k < i { k } else { k + 1 }] by {}
    assert forall|k: int| 0 <= k < t.len() implies st2.contains_key((#[trigger] t[k]).id) && st2[t[k].id]
        == state_of(t[k]) by {
        let kk = if k < i { k } else { k + 1 };
        assert(t[k] == s[kk]);
        assert(s[kk].id != s[i].id);
    }
    assert forall|id: u64| #[trigger] st2.contains_key(id) implies exists|k: int|
        0 <= k < t.len() && (#[trigger] t[k]).id == id by {
        let k = choose|k: int| 0 <= k < s.len() && (#[trigger] s[k]).id == id;
        assert(k != i);
        let kk = if k < i { k } else { k - 1 };
        assert(t[kk] == s[k]);
    }
}

proof fn lemma_udom_push(s: Seq<UniEntry>, us: Set<u64>, e: UniEntry)
    requires
        uni_dom(s, us),
    ensures
        uni_dom(s.push(e), us.insert(e.id)),
{
    let t = s.push(e);
    let u2 = us.insert(e.id);
    assert forall|k: int| 0 <= k < t.len() implies u2.contains((#[trigger] t[k]).id) by {
        if k < s.len() {
            assert(t[k] == s[k]);
        }
    }
    assert forall|id: u64| #[trigger] u2.contains(id) implies exists|k: int|
        0 <= k < t.len() && (#[trigger] t[k]).id == id by {
        if id == e.id {
            assert(t[s.len() as int].id == id);
        } else {
            let k = choose|k: int| 0 <= k < s.len() && (#[trigger] s[k]).id == id;
            assert(t[k].id == id);
        }
    }
}

proof fn lemma_udom_update(s: Seq<UniEntry>, us: Set<u64>, i: int, e: UniEntry)
    requires
        uni_dom(s, us),
        0 <= i < s.len(),
        e.id == s[i].id,
    ensures
        uni_dom(s.update(i, e), us),
{
    let t = s.update(i, e);
    assert forall|k: int| 0 <= k < t.len() implies us.contains((#[trigger] t[k]).id) by {
        if k != i {
            assert(t[k] == s[k]);
        }
    }
    assert forall|id: u64| #[trigger] us.contains(id) implies exists|k: int|
        0 <= k < t.len() && (#[trigger] t[k]).id == id by {
        let k = choose|k: int| 0 <= k < s.len() && (#[trigger] s[k]).id == id;
        assert(t[k].id == id);
    }
}

proof fn lemma_udom_remove(s: Seq<UniEntry>, h: Map<u64, (Seq<u8>, SeenUni, Seq<SpecUniEvent>)>, us: Set<u64>, i: int)
    requires
        unis_ok(s, h),
        uni_dom(s, us),
        0 <= i < s.len(),
    ensures
        uni_dom(s.remove(i), us.remove(s[i].id)),
{
    let t = s.remove(i);
    let u2 = us.remove(s[i].id);
    assert forall|k: int| 0 <= k < t.len() implies t[k] == s[if k < i { k } else { k + 1 }] by {}
    assert forall|k: int| 0 <= k < t.len() implies u2.contains((#[trigger] t[k]).id) by {
        let kk = if k < i { k } else { k + 1 };
        assert(t[k] == s[kk]);
        assert(s[kk].id != s[i].id);
    }
    assert forall|id: u64| #[trigger] u2.contains(id) implies exists|k: int|
        0 <= k < t.len() && (#[trigger] t[k]).id == id by {
        let k = choose|k: int| 0 <= k < s.len() && (#[trigger] s[k]).id == id;
        assert(k != i);
        let kk = if k < i { k } else { k - 1 };
        assert(t[kk] == s[k]);
    }
}

fn find_req(s: &Vec<ReqEntry>, id: u64) -> (r: Option<usize>)
    ensures
        match r {
            Some(i) => i < s@.len() && s@[i as int].id == id,
            None => forall|k: int| 0 <= k < s@.len() ==> (#[trigger] s@[k]).id != id,
        },
{
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s@.len(),
            forall|k: int| 0 <= k < i ==> (#[trigger] s@[k]).id != id,
        decreases s@.len() - i,
    {
        if s[i].id == id {
            return Some(i);
        }
        i += 1;
    }
    None
}

fn find_uni(s: &Vec<UniEntry>, id: u64) -> (r: Option<usize>)
    ensures
        match r {
            Some(i) => i < s@.len() && s@[i as int].id == id,
            None => forall|k: int| 0 <= k < s@.len() ==> (#[trigger] s@[k]).id != id,
        },
{
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s@.len(),
            forall|k: int| 0 <= k < i ==> (#[trigger] s@[k]).id != id,
        decreases s@.len() - i,
    {
        if s[i].id == id {
            return Some(i);
        }
        i += 1;
    }
    None
}

/// Answers the request on `e` itself with an empty `status` response (rejecting it if the
/// peer's limit doesn't admit that) and stops processing it.
fn answer(e: &mut ReqEntry, status: u16, fin: bool, peer: Option<u64>, out: &mut Vec<Output>)
    requires
        old(e).id % 4 == 0,
        old(e).stream.wf(),
        status == 501 || status == 421,
    ensures
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
    let ghost o0 = out@;
    proof {
        lemma_added_refl(o0);
    }
    if e.send_open {
        let r = Response { status, headers: Vec::new(), body: Vec::new() };
        proof {
            assert(fields_view(r.headers@) =~= Seq::<(Seq<u8>, Seq<u8>)>::empty());
            assert(r.body@ =~= Seq::<u8>::empty());
            assert(r@ == empty_response(status));
        }
        if write_response(e.id, &r, peer, out) {
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
}

/// STOP_SENDING with `code` unless `fin`.
fn stop(id: u64, code: u64, fin: bool, out: &mut Vec<Output>)
    ensures
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

fn reject(id: u64, fin: bool, out: &mut Vec<Output>)
    ensures
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

/// Outputs what the request machine's new events `evs` mean, in order; stops at a request the
/// connection answers itself (`true`). Otherwise (`false`) the outputs followed by the error's
/// outputs are `req_outs`.
fn deliver(
    e: &mut ReqEntry,
    evs: Vec<ReqEvent>,
    fin: bool,
    peer: Option<u64>,
    Ghost(ev): Ghost<Seq<SpecReqEvent>>,
    Ghost(err): Ghost<Option<ReqError>>,
    Ghost(cx): Ghost<Ctx>,
    out: &mut Vec<Output>,
) -> (answered: bool)
    requires
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
        answered ==> req_outs(
            old(e).id,
            ev,
            fields_view(old(e).trailers@),
            err,
            cx,
            added(old(out)@, final(out)@),
        ),
        !answered ==> req_outs(
            old(e).id,
            ev,
            fields_view(old(e).trailers@),
            err,
            cx,
            added(old(out)@, final(out)@) + err_outs(old(e).id, err, cx),
        ),
        answered == !no_internal(ev),
        final(e).head == (old(e).head || has_request(added(old(out)@, final(out)@))),
        final(e).is_head == (old(e).is_head || head_req(added(old(out)@, final(out)@))),
        answered ==> !final(e).rx_open && !final(e).send_open && final(e).fin_seen == (old(
            e,
        ).fin_seen || fin),
        !answered ==> final(e).rx_open && final(e).send_open == old(e).send_open
            && final(e).fin_seen == old(e).fin_seen,
{
    let ghost id = e.id;
    let ghost o0 = out@;
    let ghost tr0 = fields_view(e.trailers@);
    let n = evs.len();
    let ghost evs0 = evs@;
    let mut rv = rev(evs);
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
                return false;
            },
        };
        proof {
            assert(x@ == ev[k as int]);
            assert(request::body_nonempty(x));
        }
        match x {
            ReqEvent::Head(RequestHead::Connect { .. }) => {
                answer(e, 501, fin, peer, out);
                proof {
                    lemma_answer_done(id, ev, k as int, tr, tr0, err, cx, 501, o0, o1, out@);
                    lemma_answered_shape(id, 501, cx, added(o1, out@));
                    lemma_req_concat(added(o0, o1), added(o1, out@), false);
                    lemma_has_request_concat(added(o0, o1), added(o1, out@));
                    lemma_head_req_concat(added(o0, o1), added(o1, out@));
                    assert(internal_head(ev[k as int]));
                }
                return true;
            },
            ReqEvent::Head(RequestHead::Request(req)) => {
                if !is_http_scheme(req.scheme.as_slice()) {
                    answer(e, 421, fin, peer, out);
                    proof {
                        lemma_answer_done(id, ev, k as int, tr, tr0, err, cx, 421, o0, o1, out@);
                        lemma_answered_shape(id, 421, cx, added(o1, out@));
                        lemma_req_concat(added(o0, o1), added(o1, out@), false);
                        lemma_has_request_concat(added(o0, o1), added(o1, out@));
                        lemma_head_req_concat(added(o0, o1), added(o1, out@));
                        assert(internal_head(ev[k as int]));
                    }
                    return true;
                }
                e.head = true;
                let head_method: [u8; 4] = [72u8, 69u8, 65u8, 68u8];
                proof {
                    assert(head_method@ =~= lit_head_method());
                }
                e.is_head = e.is_head || eq_bytes(req.method.as_slice(), &head_method);
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
            let a = added(o0, out@);
            if out@.len() > o1.len() {
                assert(a == added(o0, o1).push(a.last()));
                assert forall|i: int| 0 <= i < a.len() implies ctrl_free(#[trigger] a[i]) && stop_ok(
                    a[i],
                ) && body_ok(a[i]) && !(a[i] is CloseConnection) by {
                    if i < a.len() - 1 {
                        assert(a[i] == added(o0, o1)[i]);
                    }
                }
            }
        }
        k += 1;
    }
    proof {
        assert(ev.skip(n as int) =~= Seq::<SpecReqEvent>::empty());
        assert(req_outs(id, ev.skip(n as int), fields_view(e.trailers@), err, cx, err_outs(id, err, cx)));
    }
    false
}

/// Outputs what the request machine's error means (`err_outs`); `true` for a connection error.
fn push_err(
    id: u64,
    res: &Result<(), ReqError>,
    send_open: bool,
    fin: bool,
    Ghost(cx): Ghost<Ctx>,
    out: &mut Vec<Output>,
) -> (closing: bool)
    requires
        cx.send_open == send_open,
        cx.fin == fin,
    ensures
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

/// Feeds `data` to the request machine of `e` and outputs what its events and error mean.
/// Returns whether the connection must close (the last output is then CloseConnection).
fn feed_req(e: &mut ReqEntry, data: &[u8], fin: bool, peer: Option<u64>, out: &mut Vec<Output>) -> (closing: bool)
    requires
        req_entry_ok(*old(e)),
        old(e).rx_open,
    ensures
        final(e).id == old(e).id,
        req_entry_ok(*final(e)),
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
        outs_ok(added(old(out)@, final(out)@), closing),
        req_only(added(old(out)@, final(out)@)),
        final(e).fin_seen == fin,
        final(e).rx_open == (req_err(final(e).stream.all(), fin) is None && !fin && no_internal(
            final(e).stream.emitted().skip(old(e).stream.emitted().len() as int),
        )),
        !closing ==> final(e).send_open == (old(e).send_open && req_err(final(e).stream.all(), fin)
            is None && no_internal(final(e).stream.emitted().skip(old(e).stream.emitted().len() as int))),
        final(e).head == (old(e).head || has_request(added(old(out)@, final(out)@))),
        final(e).is_head == (old(e).is_head || head_req(added(old(out)@, final(out)@))),
{
    hide(request::rfc_req);
    let ghost id = e.id;
    let ghost o0 = out@;
    let ghost em0 = e.stream.emitted();
    let ghost so = e.send_open;
    let mut evs: Vec<ReqEvent> = Vec::new();
    let res = e.stream.on_data(data, fin, &mut evs);
    proof {
        assert(evs@.skip(0) =~= evs@);
        assert(e.stream.emitted().skip(em0.len() as int) =~= request::views(evs@));
    }
    let ghost err = request::err_of(res);
    let ghost cx = Ctx { fin, peer, send_open: e.send_open };
    if deliver(e, evs, fin, peer, Ghost(request::views(evs@)), Ghost(err), Ghost(cx), out) {
        proof {
            lemma_added_refl(out@);
            lemma_req_concat(added(o0, out@), Seq::empty(), false);
            assert(added(o0, out@) + Seq::<SpecOutput>::empty() =~= added(o0, out@));
        }
        return false;
    }
    let ghost o2 = out@;
    let closing = push_err(e.id, &res, e.send_open, fin, Ghost(cx), out);
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
    closing
}

proof fn lemma_reqs_update(
    s: Seq<ReqEntry>,
    h: Map<u64, (Seq<u8>, Seq<SpecReqEvent>, Fields)>,
    i: int,
    e: ReqEntry,
)
    requires
        reqs_ok(s, h),
        0 <= i < s.len(),
        e.id == s[i].id,
        req_entry_ok(e),
    ensures
        reqs_ok(s.update(i, e), h.insert(e.id, req_hist_of(e))),
{
    let t = s.update(i, e);
    let h2 = h.insert(e.id, req_hist_of(e));
    assert forall|j: int, k: int|
        0 <= j < t.len() && 0 <= k < t.len() && j != k implies (#[trigger] t[j]).id != (
        #[trigger] t[k]).id by {
        assert(s[j].id != s[k].id);
    }
    assert forall|k: int| 0 <= k < t.len() implies req_entry_ok(#[trigger] t[k]) && h2.contains_key(
        t[k].id,
    ) && h2[t[k].id] == req_hist_of(t[k]) by {
        if k != i {
            assert(s[k].id != s[i].id);
        }
    }
}

proof fn lemma_reqs_push(s: Seq<ReqEntry>, h: Map<u64, (Seq<u8>, Seq<SpecReqEvent>, Fields)>, e: ReqEntry)
    requires
        reqs_ok(s, h),
        forall|k: int| 0 <= k < s.len() ==> (#[trigger] s[k]).id != e.id,
        req_entry_ok(e),
    ensures
        reqs_ok(s.push(e), h.insert(e.id, req_hist_of(e))),
{
    let t = s.push(e);
    let h2 = h.insert(e.id, req_hist_of(e));
    assert forall|j: int, k: int|
        0 <= j < t.len() && 0 <= k < t.len() && j != k implies (#[trigger] t[j]).id != (
        #[trigger] t[k]).id by {
        if j < s.len() && k < s.len() {
            assert(s[j].id != s[k].id);
        } else if j < s.len() {
            assert(s[j].id != e.id);
        } else {
            assert(s[k].id != e.id);
        }
    }
    assert forall|k: int| 0 <= k < t.len() implies req_entry_ok(#[trigger] t[k]) && h2.contains_key(
        t[k].id,
    ) && h2[t[k].id] == req_hist_of(t[k]) by {
        if k < s.len() {
            assert(s[k].id != e.id);
        }
    }
}

proof fn lemma_unis_update(
    s: Seq<UniEntry>,
    h: Map<u64, (Seq<u8>, SeenUni, Seq<SpecUniEvent>)>,
    i: int,
    e: UniEntry,
)
    requires
        unis_ok(s, h),
        0 <= i < s.len(),
        e.id == s[i].id,
        e.stream.wf(),
        !e.stream.done(),
    ensures
        unis_ok(s.update(i, e), h.insert(e.id, uni_hist_of(e))),
{
    let t = s.update(i, e);
    let h2 = h.insert(e.id, uni_hist_of(e));
    assert forall|j: int, k: int|
        0 <= j < t.len() && 0 <= k < t.len() && j != k implies (#[trigger] t[j]).id != (
        #[trigger] t[k]).id by {
        assert(s[j].id != s[k].id);
    }
    assert forall|k: int| 0 <= k < t.len() implies (#[trigger] t[k]).id % 4 == 2 && t[k].stream.wf()
        && !t[k].stream.done() && h2.contains_key(t[k].id) && h2[t[k].id] == uni_hist_of(t[k]) by {
        if k != i {
            assert(s[k].id != s[i].id);
        }
    }
}

proof fn lemma_unis_push(s: Seq<UniEntry>, h: Map<u64, (Seq<u8>, SeenUni, Seq<SpecUniEvent>)>, e: UniEntry)
    requires
        unis_ok(s, h),
        forall|k: int| 0 <= k < s.len() ==> (#[trigger] s[k]).id != e.id,
        e.id % 4 == 2,
        e.stream.wf(),
        !e.stream.done(),
    ensures
        unis_ok(s.push(e), h.insert(e.id, uni_hist_of(e))),
{
    let t = s.push(e);
    let h2 = h.insert(e.id, uni_hist_of(e));
    assert forall|j: int, k: int|
        0 <= j < t.len() && 0 <= k < t.len() && j != k implies (#[trigger] t[j]).id != (
        #[trigger] t[k]).id by {
        if j < s.len() && k < s.len() {
            assert(s[j].id != s[k].id);
        } else if j < s.len() {
            assert(s[j].id != e.id);
        } else {
            assert(s[k].id != e.id);
        }
    }
    assert forall|k: int| 0 <= k < t.len() implies (#[trigger] t[k]).id % 4 == 2 && t[k].stream.wf()
        && !t[k].stream.done() && h2.contains_key(t[k].id) && h2[t[k].id] == uni_hist_of(t[k]) by {
        if k < s.len() {
            assert(s[k].id != e.id);
        }
    }
}

// =============================================================================
// The connection
// =============================================================================

pub struct H3Conn {
    closed: bool,
    started: bool,
    seen: SeenUni,
    // ponytail: linear lookup over the open streams; bounded by the stream limits Phase 3
    // advertises. Use a map if those limits grow large.
    reqs: Vec<ReqEntry>,
    unis: Vec<UniEntry>,
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
    rhist: Ghost<Map<u64, (Seq<u8>, Seq<SpecReqEvent>, Fields)>>,
    /// Per peer uni stream: bytes fed to its machine, its `seen_before`, its events.
    uhist: Ghost<Map<u64, (Seq<u8>, SeenUni, Seq<SpecUniEvent>)>>,
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
        &&& !self.closed ==> reqs_ok(self.reqs@, self.rhist@) && unis_ok(self.unis@, self.uhist@)
            && req_dom(self.reqs@, self.rstate@) && uni_dom(self.unis@, self.uset@)
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
        H3Conn {
            closed: false,
            started: false,
            seen: SeenUni { control: false, encoder: false, decoder: false },
            reqs: Vec::new(),
            unis: Vec::new(),
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
    fn close(&mut self, code: u64, out: &mut Vec<Output>)
        requires
            old(self).ctrl_inv(),
            !old(self).closed,
        ensures
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
                Self::lemma_idle(*self, out@);
            }
            return;
        }
        let ghost c0 = *self;
        let ghost o0 = out@;
        self.start(out);
        let ghost c1 = *self;
        let ghost o1 = out@;
        let target: u64 = match self.highest {
            None => 0,
            Some(h) => if h <= VARINT_MAX - 4 {
                h + 4
            } else {
                // Stream 2^62 - 4, the last client stream ID, was accepted: no ID above it is
                // encodable, and no later stream can exist. Repeat the last GOAWAY, if any.
                match self.goaway {
                    Some(g) => g,
                    None => return,
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
            assert(c1.goaways@ == c0.goaways@);
            if self.goaways@.len() > 0 {
                assert(self.goaways@[self.goaways@.len() - 1] <= VARINT_MAX);
            }
        }
        self.send_goaway(id, out);
        proof {
            Self::lemma_step_trans(c0, c1, *self, o0, o1, out@);
        }
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

    /// Data on stream `stream_id` (`fin`: the peer's sending part ends after it).
    pub fn on_stream_data(&mut self, stream_id: u64, data: &[u8], fin: bool, out: &mut Vec<Output>)
        requires
            old(self).wf(),
        ensures
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
    {
        if self.closed {
            proof {
                Self::lemma_idle(*self, out@);
            }
            return;
        }
        if stream_id % 4 == 0 {
            self.request_data(stream_id, data, fin, out);
        } else if stream_id % 4 == 2 {
            self.uni_data(stream_id, data, fin, out);
        } else {
            // Server-initiated IDs: the peer cannot send on them (RFC 9000 §2.1); the QUIC layer
            // normally refuses such data first.
            self.close(H3_STREAM_CREATION_ERROR, out);
        }
    }

    #[verifier::spinoff_prover]
    fn request_data(&mut self, id: u64, data: &[u8], fin: bool, out: &mut Vec<Output>)
        requires
            old(self).wf(),
            !old(self).closed,
            id % 4 == 0,
        ensures
            step(*old(self), *final(self), old(out)@, final(out)@),
            final(self).goaways() == old(self).goaways(),
            final(self).peer_max == old(self).peer_max,
            frame(*old(self), *final(self), Some(id)),
            req_call(*old(self), *final(self), id, data@, fin, added(old(out)@, final(out)@)),
            final(self).seen == old(self).seen,
    {
        hide(request::rfc_req);
        hide(req_outs);
        hide(request::push_all);
        let ghost c0 = *self;
        let ghost o0 = out@;
        proof {
            lemma_added_refl(o0);
        }
        match find_req(&self.reqs, id) {
            Some(i) => {
                proof {
                    assert(c0.rstate@[id] == state_of(c0.reqs@[i as int]));
                    assert(c0.rhist@[id] == req_hist_of(c0.reqs@[i as int]));
                }
                if !self.reqs[i].rx_open {
                    // Finished, or abandoned and awaiting the peer's FIN or reset.
                    if fin {
                        let mut e = self.reqs.remove(i);
                        if e.send_open {
                            e.fin_seen = true;
                            proof {
                                lemma_reqs_update(c0.reqs@, c0.rhist@, i as int, e);
                                lemma_dom_update(c0.reqs@, c0.rhist@, c0.rstate@, i as int, e);
                                assert(c0.rhist@.insert(e.id, req_hist_of(e)) =~= c0.rhist@);
                            }
                            self.reqs.insert(i, e);
                            self.rstate = Ghost(self.rstate@.insert(id, state_of(e)));
                            proof {
                                assert(self.reqs@ =~= c0.reqs@.update(i as int, e));
                            }
                        } else {
                            proof {
                                lemma_reqs_remove(c0.reqs@, c0.rhist@, c0.rhist@, i as int);
                                lemma_dom_remove(c0.reqs@, c0.rhist@, c0.rstate@, i as int);
                            }
                            self.rstate = Ghost(self.rstate@.remove(id));
                        }
                    }
                    proof {
                        Self::lemma_idle(*self, out@);
                        assert(c0.goaways@.take(c0.goaways@.len() as int) =~= c0.goaways@);
                        assert(c0.ctrl@ + Seq::<u8>::empty() =~= c0.ctrl@);
                    }
                    return;
                }
                let mut e = self.reqs.remove(i);
                let pm = self.peer_max;
                let closing = feed_req(&mut e, data, fin, pm, out);
                self.rhist = Ghost(self.rhist@.insert(id, req_hist_of(e)));
                proof {
                    lemma_writes_none(added(o0, out@), 3);
                    assert(self.ctrl@ + Seq::<u8>::empty() =~= self.ctrl@);
                    assert(self.goaways@.take(self.goaways@.len() as int) =~= self.goaways@);
                }
                if closing {
                    self.closed = true;
                    return;
                }
                if e.fin_seen && !e.send_open {
                    proof {
                        lemma_reqs_remove(c0.reqs@, c0.rhist@, self.rhist@, i as int);
                        lemma_dom_remove(c0.reqs@, c0.rhist@, c0.rstate@, i as int);
                    }
                    self.rstate = Ghost(self.rstate@.remove(id));
                } else {
                    proof {
                        lemma_reqs_update(c0.reqs@, c0.rhist@, i as int, e);
                        lemma_dom_update(c0.reqs@, c0.rhist@, c0.rstate@, i as int, e);
                    }
                    self.reqs.insert(i, e);
                    self.rstate = Ghost(self.rstate@.insert(id, state_of(e)));
                    proof {
                        assert(self.reqs@ =~= c0.reqs@.update(i as int, e));
                    }
                }
            },
            None => {
                proof {
                    assert(!c0.rstate@.contains_key(id)) by {
                        if c0.rstate@.contains_key(id) {
                            let k = choose|k: int| 0 <= k < c0.reqs@.len() && (#[trigger] c0.reqs@[k]).id == id;
                        }
                    }
                }
                self.request_data_new(id, data, fin, out);
            },
        }
    }

    /// `request_data` for a stream with no entry yet (split out for the rlimit).
    #[verifier::spinoff_prover]
    fn request_data_new(&mut self, id: u64, data: &[u8], fin: bool, out: &mut Vec<Output>)
        requires
            old(self).wf(),
            !old(self).closed,
            id % 4 == 0,
            !old(self).rstate@.contains_key(id),
            forall|k: int| 0 <= k < old(self).reqs@.len() ==> (#[trigger] old(self).reqs@[k]).id != id,
        ensures
            step(*old(self), *final(self), old(out)@, final(out)@),
            final(self).goaways() == old(self).goaways(),
            final(self).peer_max == old(self).peer_max,
            frame(*old(self), *final(self), Some(id)),
            req_call(*old(self), *final(self), id, data@, fin, added(old(out)@, final(out)@)),
            final(self).seen == old(self).seen,
    {
        hide(request::rfc_req);
        hide(req_outs);
        hide(request::push_all);
        let ghost c0 = *self;
        let ghost o0 = out@;
        proof {
            lemma_added_refl(o0);
        }
        if let Some(g) = self.goaway {
            if id >= g {
                //= https://www.rfc-editor.org/rfc/rfc9114#section-5.2
                //# Upon sending a GOAWAY frame, the endpoint
                //# SHOULD explicitly cancel (see Sections 4.1.1 and 7.2.3) any requests
                //# or pushes that have identifiers greater than or equal to the one
                //# indicated, in order to clean up transport state for the affected
                //# streams.
                reject(id, fin, out);
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
                    proof {
                        lemma_reqs_push(self.reqs@, self.rhist@, e);
                        lemma_dom_push(self.reqs@, self.rstate@, e);
                    }
                    self.reqs.push(e);
                    self.rhist = Ghost(self.rhist@.insert(id, req_hist_of(e)));
                    self.rstate = Ghost(self.rstate@.insert(id, state_of(e)));
                }
                proof {
                    assert(rejected_id(c0, id));
                    lemma_writes_none(added(o0, out@), 3);
                    assert(self.ctrl@ + Seq::<u8>::empty() =~= self.ctrl@);
                    assert(self.goaways@.take(self.goaways@.len() as int) =~= self.goaways@);
                }
                return;
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
        proof {
            assert(fields_view(e.trailers@) =~= Seq::<(Seq<u8>, Seq<u8>)>::empty());
        }
        self.highest = match self.highest {
            Some(h) => if h < id {
                Some(id)
            } else {
                Some(h)
            },
            None => Some(id),
        };
        let pm = self.peer_max;
        let closing = feed_req(&mut e, data, fin, pm, out);
        self.rhist = Ghost(self.rhist@.insert(id, req_hist_of(e)));
        proof {
            lemma_writes_none(added(o0, out@), 3);
            assert(self.ctrl@ + Seq::<u8>::empty() =~= self.ctrl@);
            assert(self.goaways@.take(self.goaways@.len() as int) =~= self.goaways@);
            assert(Seq::<u8>::empty() + data@ =~= data@);
        }
        if closing {
            self.closed = true;
            return;
        }
        if !(e.fin_seen && !e.send_open) {
            proof {
                lemma_reqs_push(c0.reqs@, c0.rhist@, e);
                lemma_dom_push(c0.reqs@, c0.rstate@, e);
            }
            self.reqs.push(e);
            self.rstate = Ghost(self.rstate@.insert(id, state_of(e)));
        } else {
            proof {
                assert forall|k: int| 0 <= k < self.reqs@.len() implies req_entry_ok(
                    #[trigger] self.reqs@[k],
                ) && self.rhist@.contains_key(self.reqs@[k].id) && self.rhist@[self.reqs@[k].id]
                    == req_hist_of(self.reqs@[k]) by {
                    assert(self.reqs@[k].id != id);
                }
            }
        }
    }

    fn uni_data(&mut self, id: u64, data: &[u8], fin: bool, out: &mut Vec<Output>)
        requires
            old(self).wf(),
            !old(self).closed,
            id % 4 == 2,
        ensures
            step(*old(self), *final(self), old(out)@, final(out)@),
            final(self).goaways() == old(self).goaways(),
            frame(*old(self), *final(self), Some(id)),
            uni_fed(*old(self), *final(self), id, data@, fin, added(old(out)@, final(out)@)),
            final(self).highest == old(self).highest,
    {
        let ghost c0 = *self;
        let ghost o0 = out@;
        let found = find_uni(&self.unis, id);
        let mut e = match found {
            Some(i) => {
                proof {
                    assert(c0.uset@.contains(id));
                    assert(c0.uhist@[id] == uni_hist_of(c0.unis@[i as int]));
                }
                self.unis.remove(i)
            },
            None => {
                proof {
                    assert(!c0.uset@.contains(id)) by {
                        if c0.uset@.contains(id) {
                            let k = choose|k: int| 0 <= k < c0.unis@.len() && (#[trigger] c0.unis@[k]).id == id;
                        }
                    }
                }
                UniEntry { id, stream: UniStream::new() }
            },
        };
        let ghost e_old = e;
        let mut evs: Vec<UniEvent> = Vec::new();
        let r = e.stream.on_data(data, fin, &mut self.seen, &mut evs);
        self.uhist = Ghost(self.uhist@.insert(id, uni_hist_of(e)));
        proof {
            assert(evs@.skip(0) =~= evs@);
            assert(Seq::<u8>::empty() + data@ =~= data@);
            let e0 = e_old.stream.emitted();
            assert(e.stream.emitted().take(e0.len() as int) =~= e0);
            assert(e.stream.emitted().skip(e0.len() as int) =~= uni::views(evs@));
        }
        match r {
            Err(c) => {
                self.close(c, out);
            },
            Ok(()) => {
                self.apply_settings(&evs);
                if !fin {
                    match found {
                        Some(i) => {
                            proof {
                                lemma_unis_update(c0.unis@, c0.uhist@, i as int, e);
                                lemma_udom_update(c0.unis@, c0.uset@, i as int, e);
                            }
                            self.unis.insert(i, e);
                            proof {
                                assert(self.unis@ =~= c0.unis@.update(i as int, e));
                            }
                        },
                        None => {
                            proof {
                                lemma_unis_push(c0.unis@, c0.uhist@, e);
                                lemma_udom_push(c0.unis@, c0.uset@, e);
                            }
                            self.unis.push(e);
                            self.uset = Ghost(self.uset@.insert(id));
                        },
                    }
                } else {
                    // Only a stream of unknown type ends cleanly; it is forgotten.
                    proof {
                        if let Some(i) = found {
                            lemma_unis_remove(c0.unis@, c0.uhist@, i as int);
                            lemma_udom_remove(c0.unis@, c0.uhist@, c0.uset@, i as int);
                        }
                        lemma_unis_hist(self.unis@, c0.uhist@, self.uhist@, id);
                    }
                    if found.is_some() {
                        self.uset = Ghost(self.uset@.remove(id));
                    }
                }
                proof {
                    Self::lemma_idle(*self, out@);
                    lemma_added_refl(o0);
                    assert(c0.ctrl@ + Seq::<u8>::empty() =~= c0.ctrl@);
                    assert(c0.goaways@.take(c0.goaways@.len() as int) =~= c0.goaways@);
                }
            },
        }
    }

    //= https://www.rfc-editor.org/rfc/rfc9114#section-9
    //# Implementations MUST ignore unknown or unsupported values in all
    //# extensible protocol elements.
    /// Records the peer's SETTINGS_MAX_FIELD_SECTION_SIZE (the last one); every other identifier
    /// is ignored (the QPACK settings don't matter with a dynamic table of capacity 0).
    fn apply_settings(&mut self, evs: &Vec<UniEvent>)
        ensures
            final(self).peer_max == events_fs(uni::views(evs@), old(self).peer_max),
            *final(self) == (H3Conn { peer_max: final(self).peer_max, ..*old(self) }),
    {
        let ghost ev = uni::views(evs@);
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
            decreases evs@.len() - k,
        {
            let ghost before = self.peer_max;
            proof {
                assert(ev.take(k + 1).drop_last() =~= ev.take(k as int));
                assert(ev.take(k + 1).last() == evs@[k as int]@);
            }
            if let UniEvent::PeerSettings(v) = &evs[k] {
                let mut j: usize = 0;
                proof {
                    assert(v@.take(0) =~= Seq::<(u64, u64)>::empty());
                }
                while j < v.len()
                    invariant
                        j <= v@.len(),
                        *self == (H3Conn { peer_max: self.peer_max, ..*old(self) }),
                        self.peer_max == pairs_fs(v@.take(j as int), before),
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
                }
                proof {
                    assert(v@.take(v@.len() as int) =~= v@);
                }
            }
            k += 1;
        }
        proof {
            assert(ev.take(evs@.len() as int) =~= ev);
        }
    }

    /// Closes our sending part of request entry `i`; the entry is dropped if the request has
    /// also ended.
    fn end_send(&mut self, i: usize)
        requires
            old(self).wf(),
            !old(self).closed,
            i < old(self).reqs@.len(),
        ensures
            final(self).wf(),
            *final(self) == (H3Conn { reqs: final(self).reqs, rstate: final(self).rstate, ..*old(self) }),
            frame(*old(self), *final(self), Some(old(self).reqs@[i as int].id)),
            !final(self).req_respondable(old(self).reqs@[i as int].id),
            final(self).req_receiving(old(self).reqs@[i as int].id) == old(self).req_receiving(
                old(self).reqs@[i as int].id,
            ),
            final(self).req_known(old(self).reqs@[i as int].id) ==> final(self).req_state(
                old(self).reqs@[i as int].id,
            ) == Some(
                ReqState {
                    send_open: false,
                    ..old(self).req_state(old(self).reqs@[i as int].id)->0
                },
            ),
    {
        let ghost c0 = *self;
        let ghost id = self.reqs@[i as int].id;
        proof {
            assert(c0.rstate@[id] == state_of(c0.reqs@[i as int]));
        }
        let mut e = self.reqs.remove(i);
        e.send_open = false;
        if !e.fin_seen {
            proof {
                lemma_reqs_update(c0.reqs@, c0.rhist@, i as int, e);
                lemma_dom_update(c0.reqs@, c0.rhist@, c0.rstate@, i as int, e);
                assert(c0.rhist@.insert(e.id, req_hist_of(e)) =~= c0.rhist@);
            }
            self.reqs.insert(i, e);
            self.rstate = Ghost(self.rstate@.insert(id, state_of(e)));
            proof {
                assert(self.reqs@ =~= c0.reqs@.update(i as int, e));
            }
        } else {
            proof {
                lemma_reqs_remove(c0.reqs@, c0.rhist@, c0.rhist@, i as int);
                lemma_dom_remove(c0.reqs@, c0.rhist@, c0.rstate@, i as int);
                assert(!c0.reqs@[i as int].rx_open);
            }
            self.rstate = Ghost(self.rstate@.remove(id));
        }
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
    pub fn on_stream_reset(&mut self, stream_id: u64, _code: u64, out: &mut Vec<Output>)
        requires
            old(self).wf(),
        ensures
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
    {
        let ghost c0 = *self;
        let ghost o0 = out@;
        proof {
            lemma_added_refl(o0);
        }
        if self.closed {
            proof {
                Self::lemma_idle(*self, out@);
            }
            return;
        }
        if stream_id % 4 == 2 {
            if let Some(i) = find_uni(&self.unis, stream_id) {
                proof {
                    assert(c0.uset@.contains(stream_id));
                    assert(c0.uhist@[stream_id] == uni_hist_of(c0.unis@[i as int]));
                }
                let k = self.unis[i].stream.kind();
                match k {
                    UniKind::Control | UniKind::QpackEncoder | UniKind::QpackDecoder => {
                        self.close(H3_CLOSED_CRITICAL_STREAM, out);
                        return;
                    },
                    _ => {
                        proof {
                            lemma_unis_remove(self.unis@, self.uhist@, i as int);
                            lemma_udom_remove(self.unis@, self.uhist@, self.uset@, i as int);
                        }
                        self.unis.remove(i);
                        self.uset = Ghost(self.uset@.remove(stream_id));
                    },
                }
            } else {
                proof {
                    assert(!c0.uset@.contains(stream_id)) by {
                        if c0.uset@.contains(stream_id) {
                            let k = choose|k: int| 0 <= k < c0.unis@.len() && (#[trigger] c0.unis@[k]).id == stream_id;
                        }
                    }
                }
            }
        } else if stream_id % 4 == 0 {
            match find_req(&self.reqs, stream_id) {
                Some(i) => {
                    proof {
                        assert(c0.rstate@[stream_id] == state_of(c0.reqs@[i as int]));
                        lemma_reqs_remove(self.reqs@, self.rhist@, self.rhist@, i as int);
                        lemma_dom_remove(self.reqs@, self.rhist@, self.rstate@, i as int);
                    }
                    let e = self.reqs.remove(i);
                    self.rstate = Ghost(self.rstate@.remove(stream_id));
                    if e.send_open {
                        let code = if e.fin_seen {
                            H3_REQUEST_CANCELLED
                        } else {
                            H3_REQUEST_INCOMPLETE
                        };
                        let w = Output::ResetStream { stream_id, code };
                        out.push(w);
                        proof {
                            lemma_added_push(o0, o0, w);
                            assert(added(o0, out@) =~= seq![w@]);
                            lemma_writes_one(w@, 3);
                        }
                    }
                },
                None => {
                    proof {
                        assert(!c0.rstate@.contains_key(stream_id)) by {
                            if c0.rstate@.contains_key(stream_id) {
                                let k = choose|k: int| 0 <= k < c0.reqs@.len() && (#[trigger] c0.reqs@[k]).id == stream_id;
                            }
                        }
                    }
                },
            }
        }
        proof {
            if added(o0, out@).len() == 0 {
                Self::lemma_idle(c0, o0);
            }
            assert(c0.ctrl@ + Seq::<u8>::empty() =~= c0.ctrl@);
            assert(c0.goaways@.take(c0.goaways@.len() as int) =~= c0.goaways@);
        }
    }

    //= https://www.rfc-editor.org/rfc/rfc9114#section-6.2.1
    //# The
    //# sender MUST NOT close the control stream, and the receiver MUST NOT
    //# request that the sender close the control stream.
    /// The peer sent STOP_SENDING for our sending part of `stream_id`; the error code changes
    /// nothing (RFC 9114 §8). On our control stream it is a request to close a critical stream:
    /// H3_CLOSED_CRITICAL_STREAM. On a request stream, the pending response is dropped (the QUIC
    /// layer answers with RESET_STREAM, RFC 9000 §3.5); the request is still received.
    pub fn on_stop_sending(&mut self, stream_id: u64, _code: u64, out: &mut Vec<Output>)
        requires
            old(self).wf(),
        ensures
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
    {
        let ghost c0 = *self;
        if self.closed {
            proof {
                Self::lemma_idle(*self, out@);
            }
            return;
        }
        if stream_id == 3 {
            self.close(H3_CLOSED_CRITICAL_STREAM, out);
            proof {
                assert(!c0.rstate@.contains_key(3)) by {
                    if c0.rstate@.contains_key(3) {
                        let k = choose|k: int| 0 <= k < c0.reqs@.len() && (#[trigger] c0.reqs@[k]).id == 3;
                        assert(req_entry_ok(c0.reqs@[k]));
                    }
                }
            }
            return;
        }
        match find_req(&self.reqs, stream_id) {
            Some(i) => {
                self.end_send(i);
            },
            None => {
                proof {
                    assert(!c0.rstate@.contains_key(stream_id)) by {
                        if c0.rstate@.contains_key(stream_id) {
                            let k = choose|k: int| 0 <= k < c0.reqs@.len() && (#[trigger] c0.reqs@[k]).id == stream_id;
                        }
                    }
                }
            },
        }
        proof {
            Self::lemma_idle(*self, out@);
            assert(c0.ctrl@ + Seq::<u8>::empty() =~= c0.ctrl@);
            assert(c0.goaways@.take(c0.goaways@.len() as int) =~= c0.goaways@);
        }
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
        let ghost c0 = *self;
        let ghost o0 = out@;
        proof {
            Self::lemma_idle(*self, out@);
        }
        if self.closed {
            return Err(());
        }
        let i = match find_req(&self.reqs, stream_id) {
            Some(i) => i,
            None => {
                proof {
                    assert(!c0.rstate@.contains_key(stream_id)) by {
                        if c0.rstate@.contains_key(stream_id) {
                            let k = choose|k: int| 0 <= k < c0.reqs@.len() && (#[trigger] c0.reqs@[k]).id == stream_id;
                        }
                    }
                }
                return Err(());
            },
        };
        proof {
            assert(c0.rstate@[stream_id] == state_of(c0.reqs@[i as int]));
        }
        if !(self.reqs[i].head && self.reqs[i].send_open) {
            return Err(());
        }
        if !check_response(resp, self.reqs[i].is_head) {
            return Err(());
        }
        //= https://www.rfc-editor.org/rfc/rfc9114#section-7.2.4.2
        //# An HTTP implementation MUST NOT send frames or requests that would be
        //# invalid based on its current understanding of the peer's settings.
        if !write_response(stream_id, resp, self.peer_max, out) {
            return Err(());
        }
        self.end_send(i);
        proof {
            reveal(one_response);
            let a = added(o0, out@);
            assert(req_entry_ok(c0.reqs@[i as int]));
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
