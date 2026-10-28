//! The HTTP/3 server connection (RFC 9114): dispatch by stream ID to the verified stream machines
//! (`h3::request`, `h3::uni`), our control stream (one SETTINGS frame, then GOAWAYs), responses,
//! and the connection-error latch. Sans-IO: QUIC stream events in, `Output`s out.
//!
//! Contract with the QUIC layer: stream IDs follow RFC 9000 §2.1, and no data is delivered on a
//! stream after its FIN or the peer's reset. Data that was in flight when we sent STOP_SENDING
//! may still arrive; it is ignored until the stream's FIN or reset.
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
    seq![0u8] + spec_frame_bytes(FRAME_SETTINGS, spec_settings_payload(our_settings()))
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
                spec_settings_payload(our_settings()).len() as u64,
            ).len();
            &&& rfc_frame_header(p) == Some(
                (h, FRAME_SETTINGS, spec_settings_payload(our_settings()).len() as u64),
            )
            &&& h + spec_settings_payload(our_settings()).len() == p.len()
            &&& rfc_frame_payload(FRAME_SETTINGS, p.skip(h as int)) == Ok::<SpecFrame, u64>(
                SpecFrame::Settings(our_settings()),
            )
        }),
{
    let pl = spec_settings_payload(our_settings());
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
        spec_settings_payload(our_settings()).len() <= VARINT_MAX,
{
    let s = our_settings();
    assert(s.skip(1).skip(1) =~= Seq::<(u64, u64)>::empty());
    reveal_with_fuel(spec_settings_payload, 3);
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

//= https://www.rfc-editor.org/rfc/rfc9114#section-4.1.2
//# Malformed requests or responses that are
//# detected MUST be treated as a stream error of type H3_MESSAGE_ERROR.
/// The outputs for the request machine's error: a connection error closes the connection; a
/// stream error resets our sending part and aborts reading, with that code.
pub open spec fn err_outs(id: u64, e: Option<ReqError>) -> Seq<SpecOutput> {
    match e {
        None => Seq::empty(),
        Some(ReqError::Connection(c)) => seq![SpecOutput::CloseConnection { code: c }],
        Some(ReqError::Stream(c)) => seq![
            SpecOutput::ResetStream { stream_id: id, code: c },
            SpecOutput::StopSending { stream_id: id, code: c },
        ],
    }
}

//= https://www.rfc-editor.org/rfc/rfc9114#section-4.1
//# When the server does
//# not need to receive the remainder of the request, it MAY abort
//# reading the request stream, send a complete response, and cleanly
//# close the sending part of the stream.  The error code H3_NO_ERROR
//# SHOULD be used when requesting that the client stop sending on the
//# request stream.
//= https://www.rfc-editor.org/rfc/rfc9114#section-4.1.1
//# When the server cancels a request without performing any application
//# processing, the request is considered "rejected".  The server SHOULD
//# abort its response stream with the error code H3_REQUEST_REJECTED.
/// A request the connection answers itself with `status` (no headers, no body), never passed to
/// the application: the response with FIN, then STOP_SENDING(H3_NO_ERROR) unless the request has
/// ended. If the response can't be sent (the peer's field-section limit), the request is
/// rejected instead.
pub open spec fn answered_outs(id: u64, status: u16, fin: bool, o: Seq<SpecOutput>) -> bool {
    let stop = if fin {
        Seq::<SpecOutput>::empty()
    } else {
        seq![SpecOutput::StopSending { stream_id: id, code: H3_NO_ERROR }]
    };
    ||| (o.len() == 1 + stop.len() && one_response(o.take(1), id, empty_response(status)) && o.skip(1)
        == stop)
    ||| o == rejected_outs(id)
}

pub open spec fn rejected_outs(id: u64) -> Seq<SpecOutput> {
    seq![
        SpecOutput::ResetStream { stream_id: id, code: H3_REQUEST_REJECTED },
        SpecOutput::StopSending { stream_id: id, code: H3_REQUEST_REJECTED },
    ]
}

//= https://www.rfc-editor.org/rfc/rfc9114#section-4.4
//# A CONNECT request MUST be constructed as follows:
/// `o` is what the connection outputs for new request-machine events `evs` on stream `id`,
/// given the trailer section `tr` held from earlier calls, the machine's error `err` and the FIN
/// flag. A CONNECT is answered 501 (RFC 9110 §9.1: an unimplemented method) and a scheme other
/// than http/https 421 (RFC 9110 §15.5.20: Misdirected Request); either ends the stream's
/// processing, so later events and the error are not output. Trailers are held until the end.
pub open spec fn req_outs(
    id: u64,
    evs: Seq<SpecReqEvent>,
    tr: Fields,
    err: Option<ReqError>,
    fin: bool,
    o: Seq<SpecOutput>,
) -> bool
    decreases evs.len(),
{
    if evs.len() == 0 {
        o == err_outs(id, err)
    } else {
        match evs[0] {
            SpecReqEvent::Head(SpecRequestHead::Connect { .. }) => answered_outs(id, 501, fin, o),
            SpecReqEvent::Head(SpecRequestHead::Request(r)) => if !http_scheme(r.scheme) {
                answered_outs(id, 421, fin, o)
            } else {
                o.len() > 0 && o[0] == SpecOutput::Request { stream_id: id, head: r } && req_outs(
                    id,
                    evs.skip(1),
                    tr,
                    err,
                    fin,
                    o.skip(1),
                )
            },
            SpecReqEvent::BodyBytes(d) => o.len() > 0 && o[0] == SpecOutput::RequestBody {
                stream_id: id,
                data: d,
            } && req_outs(id, evs.skip(1), tr, err, fin, o.skip(1)),
            SpecReqEvent::Trailers(t) => req_outs(id, evs.skip(1), t, err, fin, o),
            SpecReqEvent::End => o.len() > 0 && o[0] == SpecOutput::RequestEnd {
                stream_id: id,
                trailers: tr,
            } && req_outs(id, evs.skip(1), Seq::empty(), err, fin, o.skip(1)),
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

pub open spec fn stop_ok(o: SpecOutput) -> bool {
    match o {
        SpecOutput::StopSending { stream_id, .. } => stream_id % 4 == 0,
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
/// control or QPACK streams), our control stream never FIN-ed, and a CloseConnection, if any, is
/// the last output and only when `closing`.
pub open spec fn outs_ok(o: Seq<SpecOutput>, closing: bool) -> bool {
    &&& forall|i: int| 0 <= i < o.len() ==> stop_ok(#[trigger] o[i]) && ctrl_open(o[i])
    &&& forall|i: int|
        0 <= i < o.len() && (#[trigger] o[i]) is CloseConnection ==> closing && i == o.len() - 1
    &&& closing ==> o.len() > 0 && o.last() is CloseConnection
}

/// Outputs on request streams only: no control-stream write, STOP_SENDING only on request
/// streams.
pub open spec fn req_only(o: Seq<SpecOutput>) -> bool {
    forall|i: int| 0 <= i < o.len() ==> ctrl_free(#[trigger] o[i]) && stop_ok(o[i])
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
fn write_response(id: u64, r: &Response, peer: Option<u64>, out: &mut Vec<Output>) -> (ok: bool)
    requires
        valid_response(r@),
    ensures
        extends(old(out)@, final(out)@),
        ok ==> fits_peer(peer, fields_size(resp_fields(r@))) && one_response(
            added(old(out)@, final(out)@),
            id,
            r@,
        ),
        !ok ==> final(out)@ == old(out)@,
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
    /// Our sending part is open: no response, reset, or peer STOP_SENDING yet.
    send_open: bool,
    /// A trailer section received, held until the request ends.
    trailers: Vec<FieldLine>,
}

spec fn req_entry_ok(e: ReqEntry) -> bool {
    &&& e.id % 4 == 0
    &&& e.stream.wf()
    &&& e.rx_open ==> !e.stream.done()
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

/// Answers the request on `e` itself with an empty `status` response (rejecting it if that can't
/// be sent) and stops processing it.
fn answer(e: &mut ReqEntry, status: u16, fin: bool, peer: Option<u64>, out: &mut Vec<Output>)
    requires
        old(e).id % 4 == 0,
        old(e).stream.wf(),
        status == 501 || status == 421,
    ensures
        extends(old(out)@, final(out)@),
        answered_outs(old(e).id, status, fin, added(old(out)@, final(out)@)),
        final(e).id == old(e).id,
        final(e).stream == old(e).stream,
        final(e).trailers == old(e).trailers,
        req_entry_ok(*final(e)),
        !final(e).rx_open && !final(e).send_open,
        final(e).fin_seen == (old(e).fin_seen || fin),
{
    let ghost o0 = out@;
    let r = Response { status, headers: Vec::new(), body: Vec::new() };
    proof {
        assert(fields_view(r.headers@) =~= Seq::<(Seq<u8>, Seq<u8>)>::empty());
        assert(r.body@ =~= Seq::<u8>::empty());
        assert(r@ == empty_response(status));
    }
    if write_response(e.id, &r, peer, out) {
        if !fin {
            let ghost o1 = out@;
            let s = Output::StopSending { stream_id: e.id, code: H3_NO_ERROR };
            out.push(s);
            proof {
                lemma_added_push(o0, o1, s);
                assert(added(o0, out@).take(1) =~= added(o0, o1));
                assert(added(o0, out@).skip(1) =~= seq![s@]);
            }
        } else {
            proof {
                assert(added(o0, out@).take(1) =~= added(o0, out@));
                assert(added(o0, out@).skip(1) =~= Seq::<SpecOutput>::empty());
            }
        }
    } else {
        reject(e.id, out);
    }
    e.rx_open = false;
    e.send_open = false;
    e.fin_seen = e.fin_seen || fin;
}

fn reject(id: u64, out: &mut Vec<Output>)
    ensures
        extends(old(out)@, final(out)@),
        added(old(out)@, final(out)@) == rejected_outs(id),
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
    let b = Output::StopSending { stream_id: id, code: H3_REQUEST_REJECTED };
    out.push(b);
    proof {
        lemma_added_push(o0, o1, b);
        assert(added(o0, out@) =~= rejected_outs(id));
    }
}

proof fn lemma_answered_shape(id: u64, status: u16, fin: bool, o: Seq<SpecOutput>)
    requires
        answered_outs(id, status, fin, o),
        id % 4 == 0,
    ensures
        req_only(o),
        no_close(o),
{
    if o != rejected_outs(id) {
        assert(o.take(1)[0] == o[0]);
        if !fin {
            assert(o.skip(1)[0] == o[1]);
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
        && ctrl_open(c[i]) by {
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

proof fn lemma_err_outs_shape(id: u64, e: Option<ReqError>)
    requires
        id % 4 == 0,
    ensures
        req_only(err_outs(id, e)),
        outs_ok(err_outs(id, e), e matches Some(ReqError::Connection(_))),
{
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
    fin: bool,
    o0: Seq<Output>,
    o1: Seq<Output>,
    w: Output,
)
    requires
        0 <= k < ev.len(),
        extends(o0, o1),
        forall|x: Seq<SpecOutput>| #[trigger]
            req_outs(id, ev.skip(k), tr, err, fin, x) ==> req_outs(
                id,
                ev,
                tr0,
                err,
                fin,
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
            req_outs(id, ev.skip(k + 1), tr2, err, fin, x) ==> req_outs(
                id,
                ev,
                tr0,
                err,
                fin,
                added(o0, o1.push(w)) + x,
            ),
{
    lemma_added_push(o0, o1, w);
    let s = ev.skip(k);
    assert(s.skip(1) =~= ev.skip(k + 1));
    assert(s[0] == ev[k]);
    assert forall|x: Seq<SpecOutput>| #[trigger]
        req_outs(id, ev.skip(k + 1), tr2, err, fin, x) implies req_outs(
        id,
        ev,
        tr0,
        err,
        fin,
        added(o0, o1.push(w)) + x,
    ) by {
        let y = seq![w@] + x;
        assert(y[0] == w@);
        assert(y.skip(1) =~= x);
        assert(req_outs(id, s, tr, err, fin, y));
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
    fin: bool,
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
            req_outs(id, ev.skip(k), tr, err, fin, x) ==> req_outs(
                id,
                ev,
                tr0,
                err,
                fin,
                added(o0, o1) + x,
            ),
        answered_outs(id, status, fin, added(o1, o2)),
        match ev[k] {
            SpecReqEvent::Head(SpecRequestHead::Connect { .. }) => status == 501,
            SpecReqEvent::Head(SpecRequestHead::Request(r)) => !http_scheme(r.scheme) && status
                == 421,
            _ => false,
        },
    ensures
        extends(o0, o2),
        added(o0, o2) == added(o0, o1) + added(o1, o2),
        req_outs(id, ev, tr0, err, fin, added(o0, o2)),
{
    lemma_added_trans(o0, o1, o2);
    let s = ev.skip(k);
    assert(s[0] == ev[k]);
    assert(req_outs(id, s, tr, err, fin, added(o1, o2)));
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
    out: &mut Vec<Output>,
) -> (answered: bool)
    requires
        ev == request::views(evs@),
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
            fin,
            added(old(out)@, final(out)@),
        ),
        !answered ==> req_outs(
            old(e).id,
            ev,
            fields_view(old(e).trailers@),
            err,
            fin,
            added(old(out)@, final(out)@) + err_outs(old(e).id, err),
        ),
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
    let mut rv = rev(evs);
    let mut k: usize = 0;
    proof {
        lemma_added_refl(o0);
        assert(ev.skip(0) =~= ev);
        assert forall|x: Seq<SpecOutput>| #[trigger]
            req_outs(id, ev.skip(0), tr0, err, fin, x) implies req_outs(
            id,
            ev,
            tr0,
            err,
            fin,
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
            extends(o0, out@),
            forall|x: Seq<SpecOutput>| #[trigger]
                req_outs(id, ev.skip(k as int), fields_view(e.trailers@), err, fin, x) ==> req_outs(
                    id,
                    ev,
                    tr0,
                    err,
                    fin,
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
        }
        match x {
            ReqEvent::Head(RequestHead::Connect { .. }) => {
                answer(e, 501, fin, peer, out);
                proof {
                    lemma_answer_done(id, ev, k as int, tr, tr0, err, fin, 501, o0, o1, out@);
                    lemma_answered_shape(id, 501, fin, added(o1, out@));
                    lemma_req_concat(added(o0, o1), added(o1, out@), false);
                }
                return true;
            },
            ReqEvent::Head(RequestHead::Request(req)) => {
                if !is_http_scheme(req.scheme.as_slice()) {
                    answer(e, 421, fin, peer, out);
                    proof {
                        lemma_answer_done(id, ev, k as int, tr, tr0, err, fin, 421, o0, o1, out@);
                        lemma_answered_shape(id, 421, fin, added(o1, out@));
                        lemma_req_concat(added(o0, o1), added(o1, out@), false);
                    }
                    return true;
                }
                e.head = true;
                let w = Output::Request { stream_id: e.id, head: req };
                proof {
                    lemma_deliver(id, ev, k as int, tr, tr, tr0, err, fin, o0, o1, w);
                }
                out.push(w);
            },
            ReqEvent::Body(d) => {
                let w = Output::RequestBody { stream_id: e.id, data: d };
                proof {
                    lemma_deliver(id, ev, k as int, tr, tr, tr0, err, fin, o0, o1, w);
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
                        req_outs(id, ev.skip(k + 1), fields_view(e.trailers@), err, fin, x) implies req_outs(
                        id,
                        ev,
                        tr0,
                        err,
                        fin,
                        added(o0, out@) + x,
                    ) by {
                        assert(req_outs(id, s, tr, err, fin, x));
                    }
                }
            },
            ReqEvent::End => {
                let mut t: Vec<FieldLine> = Vec::new();
                core::mem::swap(&mut t, &mut e.trailers);
                let w = Output::RequestEnd { stream_id: e.id, trailers: t };
                proof {
                    assert(fields_view(e.trailers@) =~= Seq::<(Seq<u8>, Seq<u8>)>::empty());
                    lemma_deliver(id, ev, k as int, tr, Seq::empty(), tr0, err, fin, o0, o1, w);
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
                ) && !(a[i] is CloseConnection) by {
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
        assert(req_outs(id, ev.skip(n as int), fields_view(e.trailers@), err, fin, err_outs(id, err)));
    }
    false
}

/// Outputs what the request machine's error means (`err_outs`); `true` for a connection error.
fn push_err(id: u64, res: &Result<(), ReqError>, out: &mut Vec<Output>) -> (closing: bool)
    ensures
        extends(old(out)@, final(out)@),
        added(old(out)@, final(out)@) == err_outs(id, request::err_of(*res)),
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
                assert(added(o0, out@) =~= err_outs(id, request::err_of(*res)));
            }
            true
        },
        Err(ReqError::Stream(c)) => {
            let a = Output::ResetStream { stream_id: id, code: *c };
            out.push(a);
            proof {
                lemma_added_push(o0, o0, a);
            }
            let ghost o1 = out@;
            let b = Output::StopSending { stream_id: id, code: *c };
            out.push(b);
            proof {
                lemma_added_push(o0, o1, b);
                assert(added(o0, out@) =~= err_outs(id, request::err_of(*res)));
            }
            false
        },
        Ok(()) => false,
    }
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
            request::rfc_request_stream(final(e).stream.all(), fin).1,
            fin,
            added(old(out)@, final(out)@),
        ),
        outs_ok(added(old(out)@, final(out)@), closing),
        req_only(added(old(out)@, final(out)@)),
        final(e).fin_seen == (old(e).fin_seen || fin),
        !old(e).send_open ==> !final(e).send_open,
{
    hide(request::rfc_req);
    let ghost id = e.id;
    let ghost o0 = out@;
    let ghost em0 = e.stream.emitted();
    let mut evs: Vec<ReqEvent> = Vec::new();
    let res = e.stream.on_data(data, fin, &mut evs);
    proof {
        assert(evs@.skip(0) =~= evs@);
        assert(e.stream.emitted().skip(em0.len() as int) =~= request::views(evs@));
    }
    let ghost err = request::err_of(res);
    if deliver(e, evs, fin, peer, Ghost(request::views(evs@)), Ghost(err), out) {
        proof {
            lemma_added_refl(out@);
            lemma_req_concat(added(o0, out@), Seq::empty(), false);
            assert(added(o0, out@) + Seq::<SpecOutput>::empty() =~= added(o0, out@));
        }
        return false;
    }
    let ghost o2 = out@;
    let closing = push_err(e.id, &res, out);
    match res {
        Err(ReqError::Stream(_)) => {
            e.rx_open = false;
            e.send_open = false;
        },
        Err(ReqError::Connection(_)) => {
            e.rx_open = false;
        },
        Ok(()) => {
            if fin {
                e.rx_open = false;
            }
        },
    }
    e.fin_seen = e.fin_seen || fin;
    proof {
        lemma_added_trans(o0, o2, out@);
        lemma_err_outs_shape(id, err);
        lemma_req_concat(added(o0, o2), added(o2, out@), closing);
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

/// A request-stream call that fed the machine: the stream's bytes (continued if it was being
/// received, else from empty) grew by `data`; its cumulative events (body chunks concatenated)
/// are `rfc_request_stream` of those bytes; and the call's outputs `o` are exactly what the new
/// events and the machine's error mean (`req_outs`).
pub open spec fn req_fed(c0: H3Conn, c1: H3Conn, id: u64, data: Seq<u8>, fin: bool, o: Seq<SpecOutput>) -> bool {
    let b0 = if c0.req_receiving(id) { c0.req_hist(id).0 } else { Seq::<u8>::empty() };
    let e0 = if c0.req_receiving(id) { c0.req_hist(id).1 } else { Seq::<SpecReqEvent>::empty() };
    let t0 = if c0.req_receiving(id) { c0.req_hist(id).2 } else { Seq::<(Seq<u8>, Seq<u8>)>::empty() };
    let h = c1.req_hist(id);
    &&& h.0 == b0 + data
    &&& h.1.len() >= e0.len()
    &&& h.1.take(e0.len() as int) == e0
    &&& request::concat_bodies(h.1) == request::rfc_request_stream(h.0, fin).0
    &&& req_outs(id, h.1.skip(e0.len() as int), t0, request::rfc_request_stream(h.0, fin).1, fin, o)
}

/// A peer uni stream call: the stream's bytes grew by `data`; its events and error are
/// `rfc_uni_stream` of them; the only output is CloseConnection on that error.
pub open spec fn uni_fed(c0: H3Conn, c1: H3Conn, id: u64, data: Seq<u8>, fin: bool, o: Seq<SpecOutput>) -> bool {
    let b0 = if c0.uni_known(id) { c0.uni_hist(id).0 } else { Seq::<u8>::empty() };
    let e0 = if c0.uni_known(id) { c0.uni_hist(id).2 } else { Seq::<SpecUniEvent>::empty() };
    let h = c1.uni_hist(id);
    &&& h.0 == b0 + data
    &&& h.2.len() >= e0.len()
    &&& h.2.take(e0.len() as int) == e0
    &&& uni::rfc_uni_stream(h.0, fin, h.1).0 == h.2
    &&& o == uni_err_outs(uni::rfc_uni_stream(h.0, fin, h.1).1)
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

    /// The connection tracks request stream `id` (it may be finished or abandoned).
    pub closed spec fn req_known(&self, id: u64) -> bool {
        exists|k: int| 0 <= k < self.reqs@.len() && (#[trigger] self.reqs@[k]).id == id
    }

    /// Request stream `id` is still being received and processed.
    pub closed spec fn req_receiving(&self, id: u64) -> bool {
        exists|k: int|
            0 <= k < self.reqs@.len() && (#[trigger] self.reqs@[k]).id == id && self.reqs@[k].rx_open
    }

    /// Request stream `id` had its head delivered and has no response yet.
    pub closed spec fn req_respondable(&self, id: u64) -> bool {
        exists|k: int|
            0 <= k < self.reqs@.len() && (#[trigger] self.reqs@[k]).id == id && self.reqs@[k].head
                && self.reqs@[k].send_open
    }

    pub closed spec fn req_hist(&self, id: u64) -> (Seq<u8>, Seq<SpecReqEvent>, Fields) {
        self.rhist@[id]
    }

    pub closed spec fn uni_known(&self, id: u64) -> bool {
        exists|k: int| 0 <= k < self.unis@.len() && (#[trigger] self.unis@[k]).id == id
    }

    pub closed spec fn uni_hist(&self, id: u64) -> (Seq<u8>, SeenUni, Seq<SpecUniEvent>) {
        self.uhist@[id]
    }

    pub closed spec fn wf(&self) -> bool {
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
        &&& !self.closed ==> reqs_ok(self.reqs@, self.rhist@) && unis_ok(self.unis@, self.uhist@)
    }

    /// What the invariant means for our control stream and GOAWAYs: nothing written yet, or the
    /// stream type and one SETTINGS frame (`theorem_ctrl_preamble`) followed only by GOAWAY
    /// frames with non-increasing IDs, all above every request we accepted.
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
    {
        if !c.started {
        } else {
            assert(ctrl_preamble().len() > 0);
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
        }
    }

    /// Outputs CloseConnection and latches the connection closed.
    fn close(&mut self, code: u64, out: &mut Vec<Output>)
        requires
            old(self).wf(),
            !old(self).closed,
        ensures
            final(self).wf(),
            final(self).closed,
            final(self).ctrl == old(self).ctrl,
            final(self).goaways == old(self).goaways,
            final(self).highest == old(self).highest,
            final(self).peer_max == old(self).peer_max,
            final(self).reqs == old(self).reqs,
            final(self).rhist == old(self).rhist,
            final(self).uhist == old(self).uhist,
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
            !old(self).closed() ==> final(self).ctrl_bytes().len() > 0,
            !old(self).closed() && old(self).ctrl_bytes().len() == 0 ==> final(self).ctrl_bytes()
                == ctrl_preamble(),
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
            !old(self).closed() && goaway_id(old(self).highest_accepted(), old(self).goaways())
                <= VARINT_MAX ==> final(self).goaways() == old(self).goaways().push(
                goaway_id(old(self).highest_accepted(), old(self).goaways()) as u64,
            ),
            !old(self).closed() ==> final(self).ctrl_bytes().len() > 0,
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
        ensures
            step(*old(self), *final(self), old(out)@, final(out)@),
            !final(self).closed,
            final(self).goaways@ == old(self).goaways@.push(id),
    {
        let ghost o0 = out@;
        let mut data: Vec<u8> = Vec::new();
        serialize_goaway(id, &mut data);
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
        assert forall|i: int| 0 <= i < c.len() implies stop_ok(#[trigger] c[i]) && ctrl_open(c[i]) && !(c[i] is CloseConnection) by {
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
            !old(self).closed() && stream_id % 4 != 0 && stream_id % 4 != 2 ==> added(
                old(out)@,
                final(out)@,
            ) == seq![SpecOutput::CloseConnection { code: H3_STREAM_CREATION_ERROR }],
            !old(self).closed() && stream_id % 4 == 0 && !old(self).req_known(stream_id)
                && rejected_id(*old(self), stream_id) ==> added(old(out)@, final(out)@)
                == rejected_outs(stream_id),
            !old(self).closed() && stream_id % 4 == 0 && old(self).req_known(stream_id) && !old(self).req_receiving(stream_id) ==> added(old(out)@, final(out)@) == Seq::<
                SpecOutput,
            >::empty(),
            !old(self).closed() && stream_id % 4 == 0 && (old(self).req_receiving(stream_id) || (
            !old(self).req_known(stream_id) && !rejected_id(*old(self), stream_id))) ==> req_fed(
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
            //= https://www.rfc-editor.org/rfc/rfc9114#section-6.2
            //# The purpose is indicated by a stream type, which is sent
            //# as a variable-length integer at the start of the stream.
            // Server-initiated IDs: the peer cannot send on them (RFC 9000 §2.1).
            self.close(H3_STREAM_CREATION_ERROR, out);
        }
    }

    fn request_data(&mut self, id: u64, data: &[u8], fin: bool, out: &mut Vec<Output>)
        requires
            old(self).wf(),
            !old(self).closed,
            id % 4 == 0,
        ensures
            step(*old(self), *final(self), old(out)@, final(out)@),
            final(self).goaways() == old(self).goaways(),
            !old(self).req_known(id) && rejected_id(*old(self), id) ==> added(old(out)@, final(out)@)
                == rejected_outs(id),
            old(self).req_known(id) && !old(self).req_receiving(id) ==> added(old(out)@, final(out)@)
                == Seq::<SpecOutput>::empty(),
            (old(self).req_receiving(id) || (!old(self).req_known(id) && !rejected_id(*old(self), id)))
                ==> req_fed(*old(self), *final(self), id, data@, fin, added(old(out)@, final(out)@)),
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
                    assert(c0.req_known(id));
                }
                if !self.reqs[i].rx_open {
                    // Finished, or abandoned and awaiting the peer's FIN or reset.
                    proof {
                        assert(!c0.req_receiving(id)) by {
                            if c0.req_receiving(id) {
                                let k = choose|k: int|
                                    0 <= k < c0.reqs@.len() && (#[trigger] c0.reqs@[k]).id == id
                                        && c0.reqs@[k].rx_open;
                                assert(k == i);
                            }
                        }
                    }
                    if fin && !self.reqs[i].send_open {
                        proof {
                            lemma_reqs_remove(self.reqs@, self.rhist@, self.rhist@, i as int);
                        }
                        self.reqs.remove(i);
                    }
                    proof {
                        Self::lemma_idle(*self, out@);
                        assert(c0.goaways@.take(c0.goaways@.len() as int) =~= c0.goaways@);
                        assert(c0.ctrl@ + Seq::<u8>::empty() =~= c0.ctrl@);
                    }
                    return;
                }
                proof {
                    assert(c0.req_receiving(id));
                    assert(c0.rhist@[id] == req_hist_of(c0.reqs@[i as int]));
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
                        assert(self.reqs@ == c0.reqs@.remove(i as int));
                    }
                } else {
                    proof {
                        lemma_reqs_update(c0.reqs@, c0.rhist@, i as int, e);
                    }
                    self.reqs.insert(i, e);
                    proof {
                        assert(self.reqs@ =~= c0.reqs@.update(i as int, e));
                    }
                }
            },
            None => {
                proof {
                    assert(!c0.req_known(id));
                    assert(!c0.req_receiving(id));
                }
                if let Some(g) = self.goaway {
                    if id >= g {
                        //= https://www.rfc-editor.org/rfc/rfc9114#section-5.2
                        //# Upon sending a GOAWAY frame, the endpoint
                        //# SHOULD explicitly cancel (see Sections 4.1.1 and 7.2.3) any requests
                        //# or pushes that have identifiers greater than or equal to the one
                        //# indicated, in order to clean up transport state for the affected
                        //# streams.
                        reject(id, out);
                        if !fin {
                            // Kept until the peer's FIN or reset, so data in flight is ignored.
                            let e = ReqEntry {
                                id,
                                stream: RequestStream::new(),
                                rx_open: false,
                                fin_seen: false,
                                head: false,
                                send_open: false,
                                trailers: Vec::new(),
                            };
                            proof {
                                lemma_reqs_push(self.reqs@, self.rhist@, e);
                            }
                            self.reqs.push(e);
                            self.rhist = Ghost(self.rhist@.insert(id, req_hist_of(e)));
                        }
                        proof {
                            assert(rejected_id(c0, id));
                            assert forall|i: int| 0 <= i < added(o0, out@).len() implies ctrl_free(#[trigger] added(o0, out@)[i]) by {}
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
                    }
                    self.reqs.push(e);
                } else {
                    proof {
                        assert forall|k: int| 0 <= k < self.reqs@.len() implies req_entry_ok(#[trigger] self.reqs@[k]) && self.rhist@.contains_key(self.reqs@[k].id) && self.rhist@[self.reqs@[k].id] == req_hist_of(self.reqs@[k]) by {
                            assert(self.reqs@[k].id != id);
                        }
                    }
                }
            },
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
            uni_fed(*old(self), *final(self), id, data@, fin, added(old(out)@, final(out)@)),
    {
        let ghost c0 = *self;
        let ghost o0 = out@;
        let found = find_uni(&self.unis, id);
        let mut e = match found {
            Some(i) => {
                proof {
                    assert(c0.uni_known(id));
                    assert(c0.uhist@[id] == uni_hist_of(c0.unis@[i as int]));
                }
                self.unis.remove(i)
            },
            None => {
                proof {
                    assert(!c0.uni_known(id));
                }
                UniEntry { id, stream: UniStream::new() }
            },
        };
        let mut evs: Vec<UniEvent> = Vec::new();
        let r = e.stream.on_data(data, fin, &mut self.seen, &mut evs);
        self.uhist = Ghost(self.uhist@.insert(id, uni_hist_of(e)));
        proof {
            assert(evs@.skip(0) =~= evs@);
            assert(Seq::<u8>::empty() + data@ =~= data@);
            assert(e.stream.emitted().take(0) =~= Seq::<SpecUniEvent>::empty());
            if let Some(i) = found {
                let e0 = c0.unis@[i as int].stream.emitted();
                assert(e.stream.emitted().take(e0.len() as int) =~= e0);
            }
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
                            }
                            self.unis.insert(i, e);
                            proof {
                                assert(self.unis@ =~= c0.unis@.update(i as int, e));
                            }
                        },
                        None => {
                            proof {
                                lemma_unis_push(c0.unis@, c0.uhist@, e);
                            }
                            self.unis.push(e);
                        },
                    }
                } else {
                    // Only a stream of unknown type ends cleanly; it is forgotten.
                    proof {
                        if let Some(i) = found {
                            lemma_unis_remove(c0.unis@, c0.uhist@, i as int);
                        }
                        lemma_unis_hist(self.unis@, c0.uhist@, self.uhist@, id);
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
    /// Records the peer's SETTINGS_MAX_FIELD_SECTION_SIZE; every other identifier is ignored
    /// (the QPACK settings don't matter with a dynamic table of capacity 0).
    fn apply_settings(&mut self, evs: &Vec<UniEvent>)
        ensures
            final(self).peer_max is Some || final(self).peer_max == old(self).peer_max,
            *final(self) == (H3Conn { peer_max: final(self).peer_max, ..*old(self) }),
    {
        let mut k: usize = 0;
        while k < evs.len()
            invariant
                k <= evs@.len(),
                *self == (H3Conn { peer_max: self.peer_max, ..*old(self) }),
                self.peer_max is Some || self.peer_max == old(self).peer_max,
            decreases evs@.len() - k,
        {
            if let UniEvent::PeerSettings(v) = &evs[k] {
                let mut j: usize = 0;
                while j < v.len()
                    invariant
                        j <= v@.len(),
                        *self == (H3Conn { peer_max: self.peer_max, ..*old(self) }),
                        self.peer_max is Some || self.peer_max == old(self).peer_max,
                    decreases v@.len() - j,
                {
                    let (s, x) = v[j];
                    if s == SETTINGS_MAX_FIELD_SECTION_SIZE {
                        self.peer_max = Some(x);
                    }
                    j += 1;
                }
            }
            k += 1;
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
            *final(self) == (H3Conn { reqs: final(self).reqs, ..*old(self) }),
            !final(self).req_respondable(old(self).reqs@[i as int].id),
    {
        let ghost c0 = *self;
        let ghost id = self.reqs@[i as int].id;
        let mut e = self.reqs.remove(i);
        e.send_open = false;
        if !e.fin_seen {
            proof {
                lemma_reqs_update(c0.reqs@, c0.rhist@, i as int, e);
                assert(c0.rhist@.insert(e.id, req_hist_of(e)) =~= c0.rhist@);
            }
            self.reqs.insert(i, e);
            proof {
                assert(self.reqs@ =~= c0.reqs@.update(i as int, e));
                assert(!self.req_respondable(id)) by {
                    if self.req_respondable(id) {
                        let k = choose|k: int|
                            0 <= k < self.reqs@.len() && (#[trigger] self.reqs@[k]).id == id
                                && self.reqs@[k].head && self.reqs@[k].send_open;
                        if k != i {
                            assert(c0.reqs@[k].id != c0.reqs@[i as int].id);
                        }
                    }
                }
            }
        } else {
            proof {
                lemma_reqs_remove(c0.reqs@, c0.rhist@, c0.rhist@, i as int);
                assert(!self.req_respondable(id)) by {
                    if self.req_respondable(id) {
                        let k = choose|k: int|
                            0 <= k < self.reqs@.len() && (#[trigger] self.reqs@[k]).id == id
                                && self.reqs@[k].head && self.reqs@[k].send_open;
                        assert(c0.reqs@.remove(i as int)[k].id != c0.reqs@[i as int].id);
                    }
                }
            }
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
    /// The peer reset its sending part of `stream_id`. The error code changes nothing: every code
    /// is handled as H3_NO_ERROR would be. A reset peer control or QPACK stream closes the
    /// connection; any other stream is forgotten silently.
    pub fn on_stream_reset(&mut self, stream_id: u64, _code: u64, out: &mut Vec<Output>)
        requires
            old(self).wf(),
        ensures
            step(*old(self), *final(self), old(out)@, final(out)@),
            final(self).goaways() == old(self).goaways(),
            !old(self).closed() && stream_id % 4 == 2 && old(self).uni_known(stream_id) && critical(
                uni::kind_of_bytes(old(self).uni_hist(stream_id).0),
            ) ==> added(old(out)@, final(out)@) == seq![
                SpecOutput::CloseConnection { code: H3_CLOSED_CRITICAL_STREAM },
            ],
            !old(self).closed() && !(stream_id % 4 == 2 && old(self).uni_known(stream_id) && critical(
                uni::kind_of_bytes(old(self).uni_hist(stream_id).0),
            )) ==> added(old(out)@, final(out)@) == Seq::<SpecOutput>::empty() && !final(self).closed(),
            !old(self).closed() && stream_id % 4 == 0 ==> !final(self).req_known(stream_id),
    {
        let ghost c0 = *self;
        if self.closed {
            proof {
                Self::lemma_idle(*self, out@);
            }
            return;
        }
        if stream_id % 4 == 2 {
            if let Some(i) = find_uni(&self.unis, stream_id) {
                proof {
                    assert(c0.uni_known(stream_id));
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
                        }
                        self.unis.remove(i);
                    },
                }
            } else {
                proof {
                    assert(!c0.uni_known(stream_id));
                }
            }
        } else if stream_id % 4 == 0 {
            if let Some(i) = find_req(&self.reqs, stream_id) {
                proof {
                    lemma_reqs_remove(self.reqs@, self.rhist@, self.rhist@, i as int);
                }
                self.reqs.remove(i);
            }
            proof {
                assert(!self.req_known(stream_id));
            }
        }
        proof {
            Self::lemma_idle(*self, out@);
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
            !old(self).closed() && stream_id == 3 ==> added(old(out)@, final(out)@) == seq![
                SpecOutput::CloseConnection { code: H3_CLOSED_CRITICAL_STREAM },
            ],
            !old(self).closed() && stream_id != 3 ==> added(old(out)@, final(out)@) == Seq::<
                SpecOutput,
            >::empty() && !final(self).closed(),
            !old(self).closed() ==> !final(self).req_respondable(stream_id),
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
                assert(!self.req_respondable(stream_id)) by {
                    if self.req_respondable(stream_id) {
                        let k = choose|k: int| 0 <= k < self.reqs@.len() && (#[trigger] self.reqs@[k]).id == stream_id && self.reqs@[k].head && self.reqs@[k].send_open;
                        assert(reqs_ok(c0.reqs@, c0.rhist@));
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
                    assert(!self.req_respondable(stream_id));
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
    /// `resp` would violate RFC 9114 (`check_response`), the stream has no delivered request or
    /// already has a response, or the field section exceeds the peer's limit.
    pub fn send_response(&mut self, stream_id: u64, resp: &Response, out: &mut Vec<Output>) -> (r: Result<(), ()>)
        requires
            old(self).wf(),
        ensures
            step(*old(self), *final(self), old(out)@, final(out)@),
            final(self).goaways() == old(self).goaways(),
            final(self).closed() == old(self).closed(),
            r is Ok ==> !old(self).closed() && old(self).req_respondable(stream_id) && valid_response(
                resp@,
            ) && fits_peer(old(self).peer_max_field_section(), fields_size(resp_fields(resp@)))
                && one_response(added(old(out)@, final(out)@), stream_id, resp@) && !final(self).req_respondable(stream_id),
            r is Err ==> final(out)@ == old(out)@,
            old(self).closed() || !valid_response(resp@) || !old(self).req_respondable(stream_id)
                ==> r is Err,
    {
        let ghost c0 = *self;
        let ghost o0 = out@;
        proof {
            Self::lemma_idle(*self, out@);
        }
        if self.closed || !check_response(resp) {
            return Err(());
        }
        let i = match find_req(&self.reqs, stream_id) {
            Some(i) => i,
            None => {
                proof {
                    assert(!c0.req_respondable(stream_id));
                }
                return Err(());
            },
        };
        if !(self.reqs[i].head && self.reqs[i].send_open) {
            proof {
                assert(!c0.req_respondable(stream_id)) by {
                    if c0.req_respondable(stream_id) {
                        let k = choose|k: int| 0 <= k < c0.reqs@.len() && (#[trigger] c0.reqs@[k]).id == stream_id && c0.reqs@[k].head && c0.reqs@[k].send_open;
                        assert(k == i);
                    }
                }
            }
            return Err(());
        }
        proof {
            assert(c0.req_respondable(stream_id));
        }
        //= https://www.rfc-editor.org/rfc/rfc9114#section-7.2.4.2
        //# An HTTP implementation MUST NOT send frames or requests that would be
        //# invalid based on its current understanding of the peer's settings.
        if !write_response(stream_id, resp, self.peer_max, out) {
            return Err(());
        }
        self.end_send(i);
        proof {
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
