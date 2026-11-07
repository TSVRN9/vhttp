//! The receiving part of a stream (RFC 9000 §3.2): STREAM and RESET_STREAM frames checked
//! against the final size (§4.5) and the stream data limit we sent (§4.1), with contiguous
//! bytes delivered as events in the call that completes them.
use vstd::prelude::*;
use crate::codes::*;
use crate::flow::*;
use crate::reassembly::*;
// Used only in ghost code, which a plain `cargo build` erases.
#[allow(unused_imports)]
use wire::varint::*;

verus! {

/// Figure 3's receive states under eager delivery: "Data Recvd" and "Reset Recvd" are passed
/// through within one call.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum RecvState {
    Recv,
    SizeKnown,
    DataRead,
    ResetRead,
}

/// What the stream layer reports to the application.
#[derive(Debug, PartialEq, Eq)]
pub enum StreamEvent {
    Data { id: u64, data: Vec<u8>, fin: bool },
    Reset { id: u64, code: u64 },
    StopSending { id: u64, code: u64 },
}

pub enum SpecStreamEvent {
    Data { id: u64, data: Seq<u8>, fin: bool },
    Reset { id: u64, code: u64 },
    StopSending { id: u64, code: u64 },
}

impl View for StreamEvent {
    type V = SpecStreamEvent;

    open spec fn view(&self) -> SpecStreamEvent {
        match self {
            StreamEvent::Data { id, data, fin } => SpecStreamEvent::Data {
                id: *id,
                data: data@,
                fin: *fin,
            },
            StreamEvent::Reset { id, code } => SpecStreamEvent::Reset { id: *id, code: *code },
            StreamEvent::StopSending { id, code } => SpecStreamEvent::StopSending {
                id: *id,
                code: *code,
            },
        }
    }
}

pub open spec fn event_views(s: Seq<StreamEvent>) -> Seq<SpecStreamEvent> {
    s.map_values(|e: StreamEvent| e@)
}

pub open spec fn terminal(a: RecvState) -> bool {
    a is DataRead || a is ResetRead
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-3.2
//# When a STREAM frame with a FIN bit is received, the final size of the
//# stream is known; see Section 4.5.  The receiving part of the stream
//# then enters the "Size Known" state.
//= https://www.rfc-editor.org/rfc/rfc9000#section-3.2
//# Receiving a RESET_STREAM frame in the "Recv" or "Size Known" state
//# causes the stream to enter the "Reset Recvd" state.
//= https://www.rfc-editor.org/rfc/rfc9000#section-3.2
//# Once the application receives the signal indicating that the stream
//# was reset, the receiving part of the stream transitions to the "Reset
//# Read" state, which is a terminal state.
//= https://www.rfc-editor.org/rfc/rfc9000#section-3.2
//# Once all data for the stream has been received, the receiving part
//# enters the "Data Recvd" state.
//= https://www.rfc-editor.org/rfc/rfc9000#section-3.2
//# Once stream data has been delivered, the stream
//# enters the "Data Read" state, which is a terminal state.
/// Figure 3's edges, each through "Data Recvd" or "Reset Recvd" within one call.
pub open spec fn recv_edge(a: RecvState, b: RecvState) -> bool {
    ||| a is Recv && b is SizeKnown
    ||| (a is Recv || a is SizeKnown) && b is ResetRead
    ||| a is SizeKnown && b is DataRead
}

/// One call moves along at most two edges: Recv to DataRead is a frame that carries the FIN
/// and completes the data.
pub open spec fn recv_step_ok(a: RecvState, b: RecvState) -> bool {
    a == b || recv_edge(a, b) || exists|c: RecvState| recv_edge(a, c) && recv_edge(c, b)
}

/// The inputs of a receiving part: STREAM, RESET_STREAM, a MAX_STREAM_DATA value we sent,
/// and a local STOP_SENDING.
pub enum SpecRecvIn {
    Data { off: nat, data: Seq<u8>, fin: bool },
    Reset { code: u64, final_size: nat },
    Credit { limit: nat },
    Stop,
}

pub struct SpecRecv {
    pub state: RecvState,
    pub ins: Seq<(nat, Seq<u8>)>,
    pub delivered: nat,
    pub high: nat,
    pub final_size: Option<nat>,
    pub limit: nat,
    pub stopped: bool,
    pub events: Seq<SpecStreamEvent>,
    pub err: Option<u64>,
}

pub open spec fn recv_init(window: u64) -> SpecRecv {
    SpecRecv {
        state: RecvState::Recv,
        ins: Seq::empty(),
        delivered: 0,
        high: 0,
        final_size: None,
        limit: window as nat,
        stopped: false,
        events: Seq::empty(),
        err: None,
    }
}

/// A STREAM frame ending at `end` changes or passes the known final size, or carries a FIN
/// below data already received.
pub open spec fn data_final_bad(s: SpecRecv, end: nat, fin: bool) -> bool {
    match s.final_size {
        Some(f) => end > f || (fin && end != f),
        None => fin && end < s.high,
    }
}

pub open spec fn recv_data(id: u64, s: SpecRecv, off: nat, data: Seq<u8>, fin: bool) -> SpecRecv {
    let end = off + data.len();
    if data_final_bad(s, end, fin) {
        SpecRecv { err: Some(FINAL_SIZE_ERROR), ..s }
    } else if end > s.limit {
        SpecRecv { err: Some(FLOW_CONTROL_ERROR), ..s }
    } else if terminal(s.state) {
        s
    } else {
        let ins = s.ins.push((off, data));
        let m = rfc_received(ins);
        let n = rfc_contiguous(m);
        let fs = if fin {
            Some(end)
        } else {
            s.final_size
        };
        let state = if fs == Some(n) {
            RecvState::DataRead
        } else if fs is Some {
            RecvState::SizeKnown
        } else {
            RecvState::Recv
        };
        SpecRecv {
            state,
            ins,
            delivered: n,
            high: if end > s.high {
                end
            } else {
                s.high
            },
            final_size: fs,
            events: if n > s.delivered || state is DataRead {
                s.events.push(
                    SpecStreamEvent::Data {
                        id,
                        data: rfc_prefix(m, n).subrange(s.delivered as int, n as int),
                        fin: state is DataRead,
                    },
                )
            } else {
                s.events
            },
            ..s
        }
    }
}

pub open spec fn recv_reset(id: u64, s: SpecRecv, code: u64, fs: nat) -> SpecRecv {
    if (s.final_size is Some && s.final_size != Some(fs)) || fs < s.high {
        SpecRecv { err: Some(FINAL_SIZE_ERROR), ..s }
    } else if fs > s.limit {
        SpecRecv { err: Some(FLOW_CONTROL_ERROR), ..s }
    } else if terminal(s.state) {
        s
    } else {
        SpecRecv {
            state: RecvState::ResetRead,
            final_size: Some(fs),
            high: fs,
            events: s.events.push(SpecStreamEvent::Reset { id, code }),
            ..s
        }
    }
}

/// One input. A local STOP_SENDING gates only credit and `stop`, never events (preflight R1).
pub open spec fn rfc_recv_step(id: u64, s: SpecRecv, i: SpecRecvIn) -> SpecRecv {
    match i {
        SpecRecvIn::Data { off, data, fin } => recv_data(id, s, off, data, fin),
        SpecRecvIn::Reset { code, final_size } => recv_reset(id, s, code, final_size),
        SpecRecvIn::Credit { limit } => SpecRecv {
            limit: if limit > s.limit {
                limit
            } else {
                s.limit
            },
            ..s
        },
        SpecRecvIn::Stop => SpecRecv { stopped: true, ..s },
    }
}

/// The receiving part after inputs `t`; frozen at the first error.
pub open spec fn rfc_recv(id: u64, window: u64, t: Seq<SpecRecvIn>) -> SpecRecv
    decreases t.len(),
{
    if t.len() == 0 {
        recv_init(window)
    } else {
        let s = rfc_recv(id, window, t.drop_last());
        if s.err is Some {
            s
        } else {
            rfc_recv_step(id, s, t.last())
        }
    }
}

/// What the stream consumes from connection credit, counted once (§4.5).
pub open spec fn counted(s: SpecRecv) -> nat {
    match s.final_size {
        Some(f) => f,
        None => s.high,
    }
}

/// What is returned as connection credit: the final size once reset (`counted`), else the
/// bytes delivered.
pub open spec fn retired(s: SpecRecv) -> nat {
    if s.state is ResetRead {
        counted(s)
    } else {
        s.delivered
    }
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-19.10
//# When counting data toward this limit, an endpoint accounts for the
//# largest received offset of data that is sent or received on the
//# stream.
//= https://www.rfc-editor.org/rfc/rfc9000#section-19.8
//# The largest offset delivered on a stream -- the sum of the offset and
//# data length
//= https://www.rfc-editor.org/rfc/rfc9000#section-19.8
//# When a Stream Data field has a length of 0, the offset in the STREAM
//# frame is the offset of the next byte that would be sent.
/// The largest received offset of the STREAM frames `ins`: the largest offset plus data length,
/// an empty frame's offset included (the next byte its sender would send), or 0.
pub open spec fn largest_received_offset(ins: Seq<(nat, Seq<u8>)>) -> nat
    decreases ins.len(),
{
    if ins.len() == 0 {
        0
    } else {
        let p = largest_received_offset(ins.drop_last());
        let e = ins.last().0 + ins.last().1.len();
        if e > p {
            e
        } else {
            p
        }
    }
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-4.5
//# The final size is the amount of flow control credit that is consumed
//# by a stream.
/// The flow control credit the stream has consumed: its final size once known, else the
/// largest received offset of the frames received (§19.10).
#[verifier::opaque]
pub open spec fn credit_before(s: SpecRecv) -> nat {
    match s.final_size {
        Some(f) => f,
        None => largest_received_offset(s.ins),
    }
}

/// The flow control credit the stream has consumed once a STREAM frame ending at `end` is
/// received: its final size once known (the frame's own with a FIN), else the largest received
/// offset with the frame's.
#[verifier::opaque]
pub open spec fn credit_after(s: SpecRecv, end: nat, fin: bool) -> nat {
    if fin {
        end
    } else if s.final_size is Some {
        s.final_size->0
    } else if end > largest_received_offset(s.ins) {
        end
    } else {
        largest_received_offset(s.ins)
    }
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-20.1
//# FINAL_SIZE_ERROR (0x06):  (1) An endpoint received a STREAM frame
//# containing data that exceeded the previously established final
//# size, (2) an endpoint received a STREAM frame or a RESET_STREAM
//# frame containing a final size that was lower than the size of
//# stream data that was already received, or (3) an endpoint received
//# a STREAM frame or a RESET_STREAM frame containing a different
//# final size to the one already established.
/// A STREAM frame ending at `end` that is a final-size error, before it is received in `s`:
/// data past the known final size, a final size below the largest received offset, or a
/// final size different from the known one.
#[verifier::opaque]
pub open spec fn final_size_trigger(s: SpecRecv, end: nat, fin: bool) -> bool {
    ||| s.final_size is Some && end > s.final_size->0
    ||| fin && end < largest_received_offset(s.ins)
    ||| fin && s.final_size is Some && end != s.final_size->0
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-4.1
//# A receiver MUST close the connection with an error of type
//# FLOW_CONTROL_ERROR if the sender violates the advertised connection
//# or stream data limits; see Section 11 for details on error handling.
/// A STREAM frame ending at `end` that violates a limit we advertised: the stream's (`s.limit`,
/// the largest maximum stream data sent, §19.10) or the connection's, of which `conn_room`
/// bytes of credit are left for this stream to consume past what it has (`credit_before`).
#[verifier::opaque]
pub open spec fn flow_trigger(s: SpecRecv, end: nat, fin: bool, conn_room: nat) -> bool {
    ||| end > s.limit
    ||| credit_after(s, end, fin) > credit_before(s) + conn_room
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-11
//# In particular, an endpoint MAY use any applicable error
//# code when it detects an error condition; a generic error code (such
//# as PROTOCOL_VIOLATION or INTERNAL_ERROR) can always be used in place
//# of specific error codes.
/// The errors `on_data` may return for a STREAM frame at `off` with `len` bytes: FINAL_SIZE_ERROR
/// on a final-size trigger (§4.5's SHOULDs, which we raise), FLOW_CONTROL_ERROR on a limit
/// violation (§4.1's MUST). With both triggers either code applies (§11).
#[verifier::opaque]
pub open spec fn recv_allowed_err(
    s: SpecRecv,
    off: nat,
    len: nat,
    fin: bool,
    conn_room: nat,
    c: u64,
) -> bool {
    ||| c == FINAL_SIZE_ERROR && final_size_trigger(s, off + len, fin)
    ||| c == FLOW_CONTROL_ERROR && flow_trigger(s, off + len, fin, conn_room)
}

/// The model's STREAM errors are the RFC's, both ways: every error `recv_data` (or the
/// connection credit check after it) raises has its trigger, and every trigger raises one, a
/// final-size trigger as FINAL_SIZE_ERROR. A model stricter than the RFC fails the first two.
pub proof fn lemma_recv_err_rfc(
    id: u64,
    s: SpecRecv,
    off: nat,
    data: Seq<u8>,
    fin: bool,
    conn_room: nat,
)
    requires
        recv_inv(id, s),
        s.err is None,
    ensures
        ({
            let s2 = recv_data(id, s, off, data, fin);
            let end = off + data.len();
            &&& s2.err matches Some(c) ==> recv_allowed_err(s, off, data.len(), fin, conn_room, c)
            &&& (s2.err is None && counted(s2) - counted(s) > conn_room) ==> recv_allowed_err(
                s,
                off,
                data.len(),
                fin,
                conn_room,
                FLOW_CONTROL_ERROR,
            )
            &&& final_size_trigger(s, end, fin) ==> s2.err == Some(FINAL_SIZE_ERROR)
            &&& (flow_trigger(s, end, fin, conn_room) && !final_size_trigger(s, end, fin)) ==> (
            s2.err == Some(FLOW_CONTROL_ERROR) || (s2.err is None && counted(s2) - counted(s)
                > conn_room))
        }),
{
    reveal(credit_before);
    reveal(credit_after);
    reveal(final_size_trigger);
    reveal(flow_trigger);
    reveal(recv_allowed_err);
    let end = off + data.len();
    assert(counted(s) == credit_before(s));
    assert(data_final_bad(s, end, fin) <==> final_size_trigger(s, end, fin));
    if !data_final_bad(s, end, fin) && end <= s.limit {
        if terminal(s.state) {
            assert(credit_after(s, end, fin) == counted(s));
        } else {
            assert(counted(recv_data(id, s, off, data, fin)) == credit_after(s, end, fin));
        }
    }
}

/// `Reassembly::insert`, keeping the window tight: empty data is recorded without touching
/// the buffers, since inserting it past the window's end would extend the window with
/// unreceived slots (split from `data_buffer` for the rlimit).
fn insert_tight(re: &mut Reassembly, off: u64, data: &[u8])
    requires
        old(re).wf(),
        old(re).tight(),
        off + data@.len() <= VARINT_MAX,
    ensures
        final(re).wf(),
        final(re).tight(),
        final(re).inserted() == old(re).inserted().push((off as nat, data@)),
        final(re).base() == old(re).base(),
        final(re).base() + final(re).buf_len() <= if old(re).base() + old(re).buf_len() >= off
            + data@.len() {
            old(re).base() + old(re).buf_len()
        } else {
            off + data@.len()
        },
{
    let ghost re0 = *re;
    if data.len() > 0 {
        re.insert(off, data);
    } else {
        re.insert_empty(off, data);
    }
    proof {
        if off + data@.len() <= re0.base() + re0.buf_len() {
            Reassembly::lemma_insert_tight_within(re0, *re, off, data@);
        } else if data@.len() > 0 {
            Reassembly::lemma_insert_tight(re0, *re, off, data@);
        }
    }
}

/// `recv_allowed_err` is not vacuous: 10 bytes inside a 100-byte window with room raise
/// nothing, and an unrelated code is never allowed.
proof fn lemma_recv_allowed_err_rejects()
    ensures
        !recv_allowed_err(recv_init(100), 0, 10, false, 1000, FLOW_CONTROL_ERROR),
        !recv_allowed_err(recv_init(100), 0, 10, true, 1000, FINAL_SIZE_ERROR),
        !recv_allowed_err(recv_init(100), 0, 200, false, 1000, PROTOCOL_VIOLATION),
        recv_allowed_err(recv_init(100), 0, 200, false, 1000, FLOW_CONTROL_ERROR),
{
    reveal(credit_before);
    reveal(credit_after);
    reveal(final_size_trigger);
    reveal(flow_trigger);
    reveal(recv_allowed_err);
}

/// The concatenated `Data` payloads.
pub open spec fn data_of(evs: Seq<SpecStreamEvent>) -> Seq<u8>
    decreases evs.len(),
{
    if evs.len() == 0 {
        Seq::empty()
    } else {
        data_of(evs.drop_last()) + match evs.last() {
            SpecStreamEvent::Data { data, .. } => data,
            _ => Seq::empty(),
        }
    }
}

/// A terminal receive event: `Data{fin: true}` or `Reset`.
pub open spec fn ends_stream(e: SpecStreamEvent) -> bool {
    match e {
        SpecStreamEvent::Data { fin, .. } => fin,
        SpecStreamEvent::Reset { .. } => true,
        SpecStreamEvent::StopSending { .. } => false,
    }
}

/// One receive event of stream `id`, `last` when nothing follows it: no empty non-FIN
/// `Data` (E2), and a terminal event only last (E1, E3).
pub open spec fn recv_event_ok(e: SpecStreamEvent, id: u64, last: bool) -> bool {
    match e {
        SpecStreamEvent::Data { id: j, data, fin } => j == id && (data.len() > 0 || fin) && (fin
            ==> last),
        SpecStreamEvent::Reset { id: j, .. } => j == id && last,
        SpecStreamEvent::StopSending { .. } => false,
    }
}

/// E1–E3 for stream `id`: `Data* (Data{fin: true} | Reset)?`, no `Data{[], false}`. With
/// `data_of == rfc_prefix(..)` (in `recv_inv`) the payloads have no gaps and no repeats.
pub open spec fn recv_events_ok(evs: Seq<SpecStreamEvent>, id: u64) -> bool {
    forall|i: int|
        #![trigger evs[i]]
        0 <= i < evs.len() ==> recv_event_ok(evs[i], id, i == evs.len() - 1)
}

/// The invariant of every reachable `SpecRecv`.
pub open spec fn recv_inv(id: u64, s: SpecRecv) -> bool {
    let m = rfc_received(s.ins);
    &&& s.delivered == rfc_contiguous(m)
    &&& forall|k: nat| #[trigger] m.contains_key(k) ==> k < s.high
    &&& s.delivered <= s.high <= counted(s) <= s.limit
    // `high` is the RFC's largest received offset until the final size is known (§19.10).
    &&& largest_received_offset(s.ins) <= s.high
    &&& s.final_size is None ==> s.high == largest_received_offset(s.ins)
    &&& (s.state is Recv <==> s.final_size is None)
    &&& s.state is SizeKnown ==> s.final_size != Some(s.delivered)
    &&& s.state is DataRead ==> s.final_size == Some(s.delivered)
    &&& s.state is ResetRead ==> s.final_size == Some(s.high)
    &&& recv_events_ok(s.events, id)
    &&& data_of(s.events) == rfc_prefix(m, s.delivered)
    &&& (terminal(s.state) <==> s.events.len() > 0 && ends_stream(s.events.last()))
    &&& s.state is DataRead ==> s.events.last() is Data
    &&& s.state is ResetRead ==> s.events.last() is Reset
}

/// What one step preserves and guarantees.
pub open spec fn recv_step_facts(id: u64, s: SpecRecv, s2: SpecRecv) -> bool {
    &&& recv_inv(id, s2)
    &&& recv_step_ok(s.state, s2.state)
    &&& s.events.is_prefix_of(s2.events)
    &&& terminal(s.state) ==> s2.state == s.state && s2.events == s.events
    &&& counted(s) <= counted(s2)
    &&& retired(s) <= retired(s2)
    &&& s.limit <= s2.limit
    &&& s.ins.is_prefix_of(s2.ins)
}

proof fn lemma_data_of_push(evs: Seq<SpecStreamEvent>, e: SpecStreamEvent)
    ensures
        data_of(evs.push(e)) == data_of(evs) + match e {
            SpecStreamEvent::Data { data, .. } => data,
            _ => Seq::empty(),
        },
{
    assert(evs.push(e).drop_last() =~= evs);
}

proof fn lemma_data_step(id: u64, s: SpecRecv, off: nat, data: Seq<u8>, fin: bool)
    requires
        recv_inv(id, s),
    ensures
        recv_step_facts(id, s, recv_data(id, s, off, data, fin)),
{
    let s2 = recv_data(id, s, off, data, fin);
    let end = off + data.len();
    if data_final_bad(s, end, fin) || end > s.limit || terminal(s.state) {
        assert(s.events.is_prefix_of(s2.events)) by {
            assert(s.events =~= s2.events.subrange(0, s.events.len() as int));
        }
        assert(s.ins =~= s2.ins.subrange(0, s.ins.len() as int));
        return;
    }
    let m = rfc_received(s.ins);
    let ins = s.ins.push((off, data));
    assert(ins.drop_last() =~= s.ins);
    let m2 = rfc_received(ins);
    let n = rfc_contiguous(m2);
    let d = s.delivered;
    lemma_received_push(s.ins, off, data);
    lemma_contiguous_exists(m);
    lemma_contiguous_exists(m2);
    if n < d {
        assert(m.contains_key(n));
    }
    assert(forall|k: nat| #[trigger] m2.contains_key(k) ==> k < s2.high);
    lemma_contiguous_le(m2, s2.high);
    // The prefix grows by the new contiguous run.
    assert(rfc_prefix(m, d) + rfc_prefix(m2, n).subrange(d as int, n as int) =~= rfc_prefix(m2, n))
        by {
        assert forall|i: int| 0 <= i < d implies #[trigger] rfc_prefix(m2, n)[i] == rfc_prefix(
            m,
            d,
        )[i] by {
            assert(m.contains_key(i as nat));
            assert(m2.contains_key(i as nat));
        }
    }
    if n > d || s2.state is DataRead {
        let e = SpecStreamEvent::Data {
            id,
            data: rfc_prefix(m2, n).subrange(d as int, n as int),
            fin: s2.state is DataRead,
        };
        lemma_data_of_push(s.events, e);
        assert(s2.events == s.events.push(e));
        assert forall|i: int|
            #![trigger s2.events[i]]
            0 <= i < s2.events.len() implies recv_event_ok(
            s2.events[i],
            id,
            i == s2.events.len() - 1,
        ) by {
            if i < s.events.len() {
                assert(s2.events[i] == s.events[i]);
                assert(recv_event_ok(s.events[i], id, i == s.events.len() - 1));
                if i == s.events.len() - 1 {
                    assert(!ends_stream(s.events.last()));
                }
            }
        }
    }
    assert(s.events.is_prefix_of(s2.events)) by {
        assert(s.events =~= s2.events.subrange(0, s.events.len() as int));
    }
    assert(s.ins =~= s2.ins.subrange(0, s.ins.len() as int));
    if s.state is Recv && s2.state is DataRead {
        assert(recv_edge(RecvState::Recv, RecvState::SizeKnown) && recv_edge(
            RecvState::SizeKnown,
            RecvState::DataRead,
        ));
    }
}

proof fn lemma_reset_step(id: u64, s: SpecRecv, code: u64, fs: nat)
    requires
        recv_inv(id, s),
    ensures
        recv_step_facts(id, s, recv_reset(id, s, code, fs)),
{
    let s2 = recv_reset(id, s, code, fs);
    if !((s.final_size is Some && s.final_size != Some(fs)) || fs < s.high || fs > s.limit
        || terminal(s.state)) {
        let e = SpecStreamEvent::Reset { id, code };
        lemma_data_of_push(s.events, e);
        assert(data_of(s2.events) =~= data_of(s.events));
        assert forall|i: int|
            #![trigger s2.events[i]]
            0 <= i < s2.events.len() implies recv_event_ok(
            s2.events[i],
            id,
            i == s2.events.len() - 1,
        ) by {
            if i < s.events.len() {
                assert(s2.events[i] == s.events[i]);
                assert(recv_event_ok(s.events[i], id, i == s.events.len() - 1));
                if i == s.events.len() - 1 {
                    assert(!ends_stream(s.events.last()));
                }
            }
        }
    }
    assert(s.events.is_prefix_of(s2.events)) by {
        assert(s.events =~= s2.events.subrange(0, s.events.len() as int));
    }
    assert(s.ins =~= s2.ins.subrange(0, s.ins.len() as int));
}

proof fn lemma_step(id: u64, s: SpecRecv, i: SpecRecvIn)
    requires
        recv_inv(id, s),
    ensures
        recv_step_facts(id, s, rfc_recv_step(id, s, i)),
{
    match i {
        SpecRecvIn::Data { off, data, fin } => lemma_data_step(id, s, off, data, fin),
        SpecRecvIn::Reset { code, final_size } => lemma_reset_step(id, s, code, final_size),
        _ => {
            let s2 = rfc_recv_step(id, s, i);
            assert(s.events =~= s2.events.subrange(0, s.events.len() as int));
            assert(s.ins =~= s2.ins.subrange(0, s.ins.len() as int));
        },
    }
}

/// One more input, in terms of the fold.
pub proof fn lemma_recv_push(id: u64, window: u64, t: Seq<SpecRecvIn>, i: SpecRecvIn)
    ensures
        rfc_recv(id, window, t.push(i)) == if rfc_recv(id, window, t).err is Some {
            rfc_recv(id, window, t)
        } else {
            rfc_recv_step(id, rfc_recv(id, window, t), i)
        },
        recv_step_facts(id, rfc_recv(id, window, t), rfc_recv(id, window, t.push(i))),
{
    assert(t.push(i).drop_last() =~= t);
    lemma_recv_inv(id, window, t);
    let s = rfc_recv(id, window, t);
    if s.err is Some {
        assert(s.events =~= s.events.subrange(0, s.events.len() as int));
        assert(s.ins =~= s.ins.subrange(0, s.ins.len() as int));
    } else {
        lemma_step(id, s, i);
    }
}

/// Every reachable state satisfies the invariant, E1–E3 among it.
pub proof fn lemma_recv_inv(id: u64, window: u64, t: Seq<SpecRecvIn>)
    ensures
        recv_inv(id, rfc_recv(id, window, t)),
        rfc_recv(id, window, t).limit >= window,
    decreases t.len(),
{
    if t.len() == 0 {
        let m = rfc_received(Seq::<(nat, Seq<u8>)>::empty());
        lemma_contiguous_exists(m);
        assert(!m.contains_key(0));
        lemma_contiguous_le(m, 0);
        assert(rfc_prefix(m, 0) =~= Seq::<u8>::empty());
    } else {
        let p = t.drop_last();
        lemma_recv_inv(id, window, p);
        assert(p.push(t.last()) =~= t);
        let s = rfc_recv(id, window, p);
        if s.err is None {
            lemma_step(id, s, t.last());
        }
    }
}

/// The stream's consumption of connection credit only grows (and so does what it retires).
pub proof fn lemma_counted_monotone(id: u64, window: u64, t: Seq<SpecRecvIn>, i: SpecRecvIn)
    ensures
        counted(rfc_recv(id, window, t)) <= counted(rfc_recv(id, window, t.push(i))),
        retired(rfc_recv(id, window, t)) <= retired(rfc_recv(id, window, t.push(i))),
{
    lemma_recv_push(id, window, t, i);
}

pub proof fn lemma_retired_le_counted(id: u64, window: u64, t: Seq<SpecRecvIn>)
    ensures
        retired(rfc_recv(id, window, t)) <= counted(rfc_recv(id, window, t)),
{
    lemma_recv_inv(id, window, t);
}

/// Every step follows Figure 3 (`recv_step_ok`), events only grow by appending, and nothing
/// changes the state or events after a terminal state (E3).
pub proof fn lemma_recv_step_ok(id: u64, window: u64, t: Seq<SpecRecvIn>, i: SpecRecvIn)
    ensures
        recv_step_ok(rfc_recv(id, window, t).state, rfc_recv(id, window, t.push(i)).state),
        rfc_recv(id, window, t).events.is_prefix_of(rfc_recv(id, window, t.push(i)).events),
        terminal(rfc_recv(id, window, t).state) ==> rfc_recv(id, window, t.push(i)).events
            == rfc_recv(id, window, t).events,
{
    lemma_recv_push(id, window, t, i);
}

// ---- Order independence for consistent STREAM data ----

pub open spec fn data_only(t: Seq<SpecRecvIn>) -> bool {
    forall|j: int| #![trigger t[j]] 0 <= j < t.len() ==> t[j] is Data
}

/// A STREAM input carrying bytes of `s` at their offsets, with a FIN only at its end.
pub open spec fn consistent_with(i: SpecRecvIn, s: Seq<u8>) -> bool {
    match i {
        SpecRecvIn::Data { off, data, fin } => off + data.len() <= s.len() && data == s.subrange(
            off as int,
            (off + data.len()) as int,
        ) && (fin ==> off + data.len() == s.len()),
        _ => true,
    }
}

pub open spec fn all_consistent(t: Seq<SpecRecvIn>, s: Seq<u8>) -> bool {
    forall|j: int| #![trigger t[j]] 0 <= j < t.len() ==> consistent_with(t[j], s)
}

pub open spec fn pair_of(i: SpecRecvIn) -> (nat, Seq<u8>) {
    match i {
        SpecRecvIn::Data { off, data, .. } => (off, data),
        _ => (0, Seq::empty()),
    }
}

pub open spec fn pairs(t: Seq<SpecRecvIn>) -> Seq<(nat, Seq<u8>)> {
    t.map_values(|i: SpecRecvIn| pair_of(i))
}

pub open spec fn is_fin_in(i: SpecRecvIn) -> bool {
    i matches SpecRecvIn::Data { fin: true, .. }
}

pub open spec fn has_fin(t: Seq<SpecRecvIn>) -> bool {
    exists|j: int| 0 <= j < t.len() && is_fin_in(#[trigger] t[j])
}

pub open spec fn is_fin_ev(e: SpecStreamEvent) -> bool {
    e matches SpecStreamEvent::Data { fin: true, .. }
}

/// A `Data{fin: true}` occurred.
pub open spec fn fin_seen(evs: Seq<SpecStreamEvent>) -> bool {
    exists|j: int| 0 <= j < evs.len() && is_fin_ev(#[trigger] evs[j])
}

/// For a consistent, error-free STREAM-only trace: what was inserted is a prefix of the
/// trace's ranges, all of them unless the data was complete, and the final size is `s`'s.
proof fn lemma_data_trace_ind(id: u64, window: u64, t: Seq<SpecRecvIn>, s: Seq<u8>)
    requires
        data_only(t),
        all_consistent(t, s),
        rfc_recv(id, window, t).err is None,
    ensures
        ({
            let st = rfc_recv(id, window, t);
            &&& !(st.state is ResetRead)
            &&& st.ins.len() <= t.len()
            &&& st.ins == pairs(t).take(st.ins.len() as int)
            &&& !(st.state is DataRead) ==> st.ins.len() == t.len()
            &&& st.final_size == if has_fin(t) {
                Some(s.len())
            } else {
                None::<nat>
            }
        }),
    decreases t.len(),
{
    if t.len() == 0 {
        assert(pairs(t).take(0) =~= Seq::<(nat, Seq<u8>)>::empty());
        return;
    }
    let p = t.drop_last();
    let i = t.last();
    assert(p.push(i) =~= t);
    lemma_recv_push(id, window, p, i);
    let sp = rfc_recv(id, window, p);
    assert forall|j: int| #![trigger p[j]] 0 <= j < p.len() implies p[j] is Data && consistent_with(
        p[j],
        s,
    ) by {
        assert(p[j] == t[j]);
    }
    assert(sp.err is None);
    lemma_data_trace_ind(id, window, p, s);
    lemma_recv_inv(id, window, p);
    assert(t[t.len() - 1] == i);
    assert(pairs(t) =~= pairs(p).push(pair_of(i)));
    assert(pairs(t).take(p.len() as int) =~= pairs(p));
    if has_fin(p) {
        let j = choose|j: int| 0 <= j < p.len() && is_fin_in(#[trigger] p[j]);
        assert(t[j] == p[j]);
    }
    if is_fin_in(i) {
        assert(is_fin_in(t[t.len() - 1]));
    }
    if has_fin(t) && !is_fin_in(i) {
        let j = choose|j: int| 0 <= j < t.len() && is_fin_in(#[trigger] t[j]);
        assert(p[j] == t[j]);
    }
    let st = rfc_recv(id, window, t);
    if sp.state is DataRead {
        assert(st == sp);
        assert(pairs(t).take(st.ins.len() as int) =~= pairs(p).take(st.ins.len() as int));
    } else {
        assert(st.ins =~= pairs(t)) by {
            assert(sp.ins =~= pairs(p));
        }
        assert(pairs(t).take(t.len() as int) =~= pairs(t));
    }
}

/// The ranges of a consistent trace are consistent with `s`.
proof fn lemma_pairs_consistent(t: Seq<SpecRecvIn>, s: Seq<u8>, k: nat)
    requires
        data_only(t),
        all_consistent(t, s),
        k <= t.len(),
    ensures
        forall|j: int|
            #![trigger pairs(t).take(k as int)[j]]
            0 <= j < k ==> pairs(t).take(k as int)[j].0 + pairs(t).take(k as int)[j].1.len()
                <= s.len() && pairs(t).take(k as int)[j].1 == s.subrange(
                pairs(t).take(k as int)[j].0 as int,
                (pairs(t).take(k as int)[j].0 + pairs(t).take(k as int)[j].1.len()) as int,
            ),
{
    assert forall|j: int| #![trigger pairs(t).take(k as int)[j]] 0 <= j < k implies pairs(t).take(
        k as int,
    )[j].0 + pairs(t).take(k as int)[j].1.len() <= s.len() && pairs(t).take(k as int)[j].1
        == s.subrange(
        pairs(t).take(k as int)[j].0 as int,
        (pairs(t).take(k as int)[j].0 + pairs(t).take(k as int)[j].1.len()) as int,
    ) by {
        assert(pairs(t).take(k as int)[j] == pair_of(t[j]));
        assert(consistent_with(t[j], s));
    }
}

/// The delivered bytes and the FIN of a consistent STREAM-only trace, in terms of the set of
/// ranges in it.
proof fn lemma_data_trace(id: u64, window: u64, t: Seq<SpecRecvIn>, s: Seq<u8>)
    requires
        data_only(t),
        all_consistent(t, s),
        rfc_recv(id, window, t).err is None,
    ensures
        fin_seen(rfc_recv(id, window, t).events) <==> has_fin(t) && rfc_contiguous(
            rfc_received(pairs(t)),
        ) == s.len(),
        data_of(rfc_recv(id, window, t).events) == s.take(
            rfc_contiguous(rfc_received(pairs(t))) as int,
        ),
{
    hide(rfc_recv_step);
    let st = rfc_recv(id, window, t);
    lemma_data_trace_ind(id, window, t, s);
    lemma_recv_inv(id, window, t);
    let full = pairs(t);
    let mm = rfc_received(full);
    let m = rfc_received(st.ins);
    lemma_pairs_consistent(t, s, t.len());
    assert(full.take(t.len() as int) =~= full);
    theorem_reassembly_order_free(full, s);
    lemma_pairs_consistent(t, s, st.ins.len());
    theorem_reassembly_order_free(st.ins, s);
    lemma_contiguous_exists(mm);
    lemma_contiguous_exists(m);
    assert forall|k: nat| #[trigger] mm.contains_key(k) implies k < s.len() by {
        let j = choose|j: int| #![trigger full[j]] 0 <= j < full.len() && full[j].0 <= k < full[j].0
            + full[j].1.len();
    }
    // fin_seen <==> DataRead.
    if st.state is DataRead {
        let l = st.events.len() - 1;
        assert(is_fin_ev(st.events[l]));
    }
    if fin_seen(st.events) {
        let j = choose|j: int| 0 <= j < st.events.len() && is_fin_ev(#[trigger] st.events[j]);
        assert(recv_event_ok(st.events[j], id, j == st.events.len() - 1));
    }
    if st.state is DataRead {
        // Everything below the final size was received, so the full map is complete too.
        assert forall|j: nat| j < s.len() implies mm.contains_key(j) by {
            assert(m.contains_key(j));
            let q = choose|q: int| #![trigger st.ins[q]] 0 <= q < st.ins.len() && st.ins[q].0 <= j
                < st.ins[q].0 + st.ins[q].1.len();
            assert(st.ins[q] == full[q]);
        }
        lemma_contiguous_is(mm, s.len());
    } else {
        assert(st.ins =~= full);
    }
}

/// When every STREAM input carries bytes of `s` at their offsets, the bytes delivered and
/// whether the FIN was delivered depend only on the multiset of inputs, not their order or
/// duplication. Event chunking may differ.
pub proof fn theorem_recv_order_free(
    id: u64,
    window: u64,
    t1: Seq<SpecRecvIn>,
    t2: Seq<SpecRecvIn>,
    s: Seq<u8>,
)
    requires
        data_only(t1),
        data_only(t2),
        t1.to_multiset() == t2.to_multiset(),
        all_consistent(t1, s),
        all_consistent(t2, s),
        rfc_recv(id, window, t1).err is None,
        rfc_recv(id, window, t2).err is None,
    ensures
        data_of(rfc_recv(id, window, t1).events) == data_of(rfc_recv(id, window, t2).events),
        fin_seen(rfc_recv(id, window, t1).events) == fin_seen(rfc_recv(id, window, t2).events),
{
    hide(rfc_recv_step);
    lemma_data_trace(id, window, t1, s);
    lemma_data_trace(id, window, t2, s);
    lemma_same_ranges(t1, t2, s);
    lemma_same_ranges(t2, t1, s);
    let m1 = rfc_received(pairs(t1));
    let m2 = rfc_received(pairs(t2));
    lemma_contiguous_exists(m1);
    assert forall|j: nat| j < rfc_contiguous(m1) implies m2.contains_key(j) by {
        assert(m1.contains_key(j));
    }
    lemma_contiguous_is(m2, rfc_contiguous(m1));
}

/// An element of `t1` is an element of `t2`.
proof fn lemma_in_both(t1: Seq<SpecRecvIn>, t2: Seq<SpecRecvIn>, j: int)
    requires
        t1.to_multiset() == t2.to_multiset(),
        0 <= j < t1.len(),
    ensures
        exists|q: int| 0 <= q < t2.len() && t2[q] == t1[j],
{
    t1.to_multiset_ensures();
    t2.to_multiset_ensures();
    assert(t1.contains(t1[j]));
    assert(t2.to_multiset().count(t1[j]) > 0);
    assert(t2.contains(t1[j]));
}

/// Every range and FIN of `t1` is in `t2`.
proof fn lemma_same_ranges(t1: Seq<SpecRecvIn>, t2: Seq<SpecRecvIn>, s: Seq<u8>)
    requires
        data_only(t1),
        data_only(t2),
        t1.to_multiset() == t2.to_multiset(),
        all_consistent(t1, s),
        all_consistent(t2, s),
    ensures
        forall|k: nat| #[trigger] rfc_received(pairs(t1)).contains_key(k) ==> rfc_received(
            pairs(t2),
        ).contains_key(k),
        has_fin(t1) ==> has_fin(t2),
{
    hide(rfc_recv_step);
    lemma_pairs_consistent(t1, s, t1.len());
    lemma_pairs_consistent(t2, s, t2.len());
    assert(pairs(t1).take(t1.len() as int) =~= pairs(t1));
    assert(pairs(t2).take(t2.len() as int) =~= pairs(t2));
    theorem_reassembly_order_free(pairs(t1), s);
    theorem_reassembly_order_free(pairs(t2), s);
    assert forall|k: nat| #[trigger] rfc_received(pairs(t1)).contains_key(k) implies rfc_received(
        pairs(t2),
    ).contains_key(k) by {
        let p1 = pairs(t1);
        let j = choose|j: int| #![trigger p1[j]] 0 <= j < p1.len() && p1[j].0 <= k < p1[j].0
            + p1[j].1.len();
        lemma_in_both(t1, t2, j);
        let q = choose|q: int| 0 <= q < t2.len() && t2[q] == t1[j];
        assert(pairs(t2)[q] == p1[j]);
    }
    if has_fin(t1) {
        let j = choose|j: int| 0 <= j < t1.len() && is_fin_in(#[trigger] t1[j]);
        lemma_in_both(t1, t2, j);
        let q = choose|q: int| 0 <= q < t2.len() && t2[q] == t1[j];
        assert(is_fin_in(t2[q]));
    }
}

// ---- Exec ----

pub open spec fn opt_nat(o: Option<u64>) -> Option<nat> {
    match o {
        Some(v) => Some(v as nat),
        None => None,
    }
}

/// The receiving part of one stream.
pub struct RecvStream {
    id: u64,
    state: RecvState,
    re: Option<Reassembly>,
    high: u64,
    final_size: Option<u64>,
    credit: RecvCredit,
    /// The code of our STOP_SENDING, once we sent one.
    stopped: Option<u64>,
    stop_pending: bool,
    trace: Ghost<Seq<SpecRecvIn>>,
    emitted: Ghost<Seq<SpecStreamEvent>>,
}

impl RecvStream {
    pub closed spec fn trace(&self) -> Seq<SpecRecvIn> {
        self.trace@
    }

    pub closed spec fn emitted(&self) -> Seq<SpecStreamEvent> {
        self.emitted@
    }

    pub closed spec fn id_spec(&self) -> u64 {
        self.id
    }

    pub closed spec fn window_spec(&self) -> u64 {
        self.credit.window_spec()
    }

    /// The code of our STOP_SENDING, once stopped.
    pub closed spec fn stop_code(&self) -> Option<u64> {
        self.stopped
    }

    /// The spec state after the inputs so far.
    pub open spec fn rfc(&self) -> SpecRecv {
        rfc_recv(self.id_spec(), self.window_spec(), self.trace())
    }

    pub closed spec fn buffered_len_spec(&self) -> usize {
        match self.re {
            Some(r) => r.buf_len(),
            None => 0,
        }
    }

    pub closed spec fn pending_credit_spec(&self) -> Option<u64> {
        if self.state is Recv && self.stopped is None {
            self.credit.pending()
        } else {
            None
        }
    }

    /// The physical length of each of the reassembly's two buffers (a length bound: Verus
    /// does not model capacity).
    pub closed spec fn buffered_phys(&self) -> nat {
        match self.re {
            Some(r) => r.phys_len(),
            None => 0,
        }
    }

    pub closed spec fn pending_stop_spec(&self) -> Option<u64> {
        if self.stop_pending && (self.state is Recv || self.state is SizeKnown) {
            self.stopped
        } else {
            None
        }
    }

    pub closed spec fn wf(&self) -> bool {
        let s = self.rfc();
        &&& s.err is None
        &&& s.events == self.emitted@
        &&& recv_inv(self.id, s)
        &&& self.credit.wf()
        &&& self.credit.cap_spec() == VARINT_MAX
        &&& s.state == self.state
        &&& s.high == self.high as nat
        &&& s.final_size == opt_nat(self.final_size)
        &&& s.limit == self.credit.limit() as nat
        &&& s.delivered == self.credit.consumed() as nat
        &&& s.stopped == self.stopped is Some
        &&& self.stop_pending ==> self.stopped is Some
        &&& self.stopped matches Some(c) ==> c <= VARINT_MAX
        &&& (self.re is None <==> s.state is ResetRead)
        &&& self.re matches Some(r) ==> r.wf() && r.inserted() == s.ins && r.base() == s.delivered
        // The window ends at a received byte: an empty STREAM frame does not grow it.
        &&& self.re matches Some(r) ==> r.tight()
        // The per-stream buffer bound, from `insert`'s and `pop`'s high-water ensures.
        &&& self.buffered_len_spec() <= s.limit - s.delivered
        &&& self.buffered_len_spec() <= counted(s) - retired(s)
    }

    /// The invariant, in terms of the accessors.
    pub proof fn lemma_wf(&self)
        requires
            self.wf(),
        ensures
            self.rfc().err is None,
            self.rfc().events == self.emitted(),
            recv_inv(self.id_spec(), self.rfc()),
            self.rfc().limit <= VARINT_MAX,
            self.buffered_len() <= self.rfc().limit - self.rfc().delivered,
            self.buffered_len() <= counted(self.rfc()) - retired(self.rfc()),
            self.rfc().state is ResetRead ==> self.buffered_len() == 0,
            self.pending_credit() matches Some(v) ==> self.rfc().limit <= v <= VARINT_MAX,
            self.pending_credit() is Some ==> self.rfc().state is Recv && !self.rfc().stopped,
            self.stop_code() is Some <==> self.rfc().stopped,
            self.stop_code() matches Some(c) ==> c <= VARINT_MAX,
            self.pending_stop() is Some ==> self.pending_stop() == self.stop_code(),
            self.pending_stop() is Some ==> self.rfc().state is Recv
                || self.rfc().state is SizeKnown,
            self.buffered_len() <= self.buffered_phys() <= 2 * self.buffered_len(),
    {
        self.credit.lemma_wf();
        if let Some(r) = self.re {
            r.lemma_wf();
        }
    }

    pub fn new(id: u64, window: u64) -> (r: RecvStream)
        requires
            window <= VARINT_MAX,
        ensures
            r.wf(),
            r.id_spec() == id,
            r.window_spec() == window,
            r.trace() == Seq::<SpecRecvIn>::empty(),
            r.emitted() == Seq::<SpecStreamEvent>::empty(),
            r.stop_code() is None,
            r.pending_stop() is None,
    {
        let re = Reassembly::new();
        proof {
            re.lemma_new_tight();
        }
        let r = RecvStream {
            id,
            state: RecvState::Recv,
            re: Some(re),
            high: 0,
            final_size: None,
            credit: RecvCredit::new(window, VARINT_MAX),
            stopped: None,
            stop_pending: false,
            trace: Ghost(Seq::empty()),
            emitted: Ghost(Seq::empty()),
        };
        proof {
            lemma_recv_inv(id, window, Seq::empty());
        }
        r
    }

    pub fn state(&self) -> (r: RecvState)
        requires
            self.wf(),
        ensures
            r == self.rfc().state,
    {
        self.state
    }

    pub fn is_terminal(&self) -> (r: bool)
        requires
            self.wf(),
        ensures
            r == terminal(self.rfc().state),
    {
        match self.state {
            RecvState::DataRead | RecvState::ResetRead => true,
            _ => false,
        }
    }

    pub fn counted_exec(&self) -> (r: u64)
        requires
            self.wf(),
        ensures
            r == counted(self.rfc()),
    {
        match self.final_size {
            Some(f) => f,
            None => self.high,
        }
    }

    pub fn retired_exec(&self) -> (r: u64)
        requires
            self.wf(),
        ensures
            r == retired(self.rfc()),
    {
        match self.state {
            RecvState::ResetRead => self.counted_exec(),
            _ => self.credit.consumed(),
        }
    }

    #[verifier::when_used_as_spec(buffered_len_spec)]
    pub fn buffered_len(&self) -> (r: usize)
        requires
            self.wf(),
        ensures
            r == self.buffered_len_spec(),
    {
        match &self.re {
            Some(r) => r.buf_len(),
            None => 0,
        }
    }

    /// The MAX_STREAM_DATA value to send, if any: only in Recv (§3.3), and never after our
    /// STOP_SENDING.
    #[verifier::when_used_as_spec(pending_credit_spec)]
    pub fn pending_credit(&self) -> (r: Option<u64>)
        ensures
            r == self.pending_credit_spec(),
    {
        match self.state {
            RecvState::Recv => if self.stopped.is_none() {
                self.credit.pending()
            } else {
                None
            },
            _ => None,
        }
    }

    /// The pending MAX_STREAM_DATA was sent: it becomes the enforced limit.
    pub fn commit_credit(&mut self)
        requires
            old(self).wf(),
            old(self).pending_credit() is Some,
        ensures
            final(self).wf(),
            final(self).id_spec() == old(self).id_spec(),
            final(self).window_spec() == old(self).window_spec(),
            final(self).trace() == old(self).trace().push(
                SpecRecvIn::Credit { limit: old(self).pending_credit()->0 as nat },
            ),
            final(self).emitted() == old(self).emitted(),
            final(self).stop_code() == old(self).stop_code(),
            final(self).pending_stop() == old(self).pending_stop(),
            final(self).pending_credit() is None,
    {
        proof {
            self.credit.lemma_wf();
            lemma_recv_push(self.id, self.credit.window_spec(), self.trace@, SpecRecvIn::Credit {
                limit: self.credit.pending()->0 as nat,
            });
        }
        self.trace = Ghost(
            self.trace@.push(SpecRecvIn::Credit { limit: self.credit.pending()->0 as nat }),
        );
        self.credit.commit();
    }

    /// The frame carrying our MAX_STREAM_DATA was lost: send the current value again.
    pub fn credit_lost(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).id_spec() == old(self).id_spec(),
            final(self).window_spec() == old(self).window_spec(),
            final(self).trace() == old(self).trace(),
            final(self).emitted() == old(self).emitted(),
            final(self).stop_code() == old(self).stop_code(),
            final(self).pending_stop() == old(self).pending_stop(),
            (old(self).rfc().state is Recv && !old(self).rfc().stopped)
                ==> final(self).pending_credit() is Some,
    {
        self.credit.on_lost();
    }

    /// Our STOP_SENDING with `code`: queued only while data may still arrive and if not
    /// already stopped.
    pub fn stop(&mut self, code: u64) -> (queued: bool)
        requires
            old(self).wf(),
            code <= VARINT_MAX,
        ensures
            final(self).wf(),
            final(self).id_spec() == old(self).id_spec(),
            final(self).window_spec() == old(self).window_spec(),
            final(self).emitted() == old(self).emitted(),
            queued == ((old(self).rfc().state is Recv || old(self).rfc().state is SizeKnown)
                && !old(self).rfc().stopped),
            queued ==> final(self).trace() == old(self).trace().push(SpecRecvIn::Stop)
                && final(self).stop_code() == Some(code) && final(self).pending_stop() == Some(
                code,
            ),
            !queued ==> *final(self) == *old(self),
    {
        let open = match self.state {
            RecvState::Recv | RecvState::SizeKnown => true,
            _ => false,
        };
        if !open || self.stopped.is_some() {
            return false;
        }
        proof {
            lemma_recv_push(self.id, self.credit.window_spec(), self.trace@, SpecRecvIn::Stop);
        }
        self.trace = Ghost(self.trace@.push(SpecRecvIn::Stop));
        self.stopped = Some(code);
        self.stop_pending = true;
        true
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-3.5
    //# STOP_SENDING SHOULD only be sent for a stream that has not been reset
    //# by the peer.
    /// Our STOP_SENDING code to send, if any: only while data may still arrive (Recv or Size
    /// Known), so never after the peer's RESET_STREAM.
    #[verifier::when_used_as_spec(pending_stop_spec)]
    pub fn pending_stop(&self) -> (r: Option<u64>)
        ensures
            r == self.pending_stop_spec(),
    {
        match self.state {
            RecvState::Recv | RecvState::SizeKnown => if self.stop_pending {
                self.stopped
            } else {
                None
            },
            _ => None,
        }
    }

    /// The pending STOP_SENDING was sent.
    pub fn commit_stop(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).id_spec() == old(self).id_spec(),
            final(self).window_spec() == old(self).window_spec(),
            final(self).trace() == old(self).trace(),
            final(self).emitted() == old(self).emitted(),
            final(self).stop_code() == old(self).stop_code(),
            final(self).pending_credit() == old(self).pending_credit(),
            final(self).pending_stop() is None,
    {
        self.stop_pending = false;
    }

    /// The frame carrying our STOP_SENDING was lost: send the same code again while data may
    /// still arrive.
    pub fn stop_lost(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).id_spec() == old(self).id_spec(),
            final(self).window_spec() == old(self).window_spec(),
            final(self).trace() == old(self).trace(),
            final(self).emitted() == old(self).emitted(),
            final(self).stop_code() == old(self).stop_code(),
            final(self).pending_credit() == old(self).pending_credit(),
            final(self).pending_stop() == if old(self).rfc().state is Recv
                || old(self).rfc().state is SizeKnown {
                old(self).stop_code()
            } else {
                old(self).pending_stop()
            },
    {
        match self.state {
            RecvState::Recv | RecvState::SizeKnown => {
                if self.stopped.is_some() {
                    self.stop_pending = true;
                }
            },
            _ => {},
        }
    }

    /// A STREAM frame's `offset`, `data` and FIN bit, with `conn_room` bytes of connection
    /// credit left. `Ok(n)`: the stream consumed `n` more bytes of connection credit.
    pub fn on_data(
        &mut self,
        off: u64,
        data: &[u8],
        fin: bool,
        conn_room: u64,
        ev: &mut Vec<StreamEvent>,
    ) -> (r: Result<u64, u64>)
        requires
            old(self).wf(),
            off + data@.len() <= VARINT_MAX,
        ensures
            final(self).id_spec() == old(self).id_spec(),
            final(self).window_spec() == old(self).window_spec(),
            final(self).wf(),
            ({
                let t2 = old(self).trace().push(
                    SpecRecvIn::Data { off: off as nat, data: data@, fin },
                );
                let s1 = old(self).rfc();
                let s2 = rfc_recv(old(self).id_spec(), old(self).window_spec(), t2);
                &&& s2.err matches Some(c) ==> r == Err::<u64, u64>(c) && *final(self) == *old(self)
                    && final(ev)@ == old(ev)@
                &&& (s2.err is None && counted(s2) - counted(s1) > conn_room) ==> r == Err::<
                    u64,
                    u64,
                >(FLOW_CONTROL_ERROR) && *final(self) == *old(self) && final(ev)@ == old(ev)@
                &&& (s2.err is None && counted(s2) - counted(s1) <= conn_room) ==> {
                    &&& r == Ok::<u64, u64>((counted(s2) - counted(s1)) as u64)
                    &&& final(self).trace() == t2
                    &&& event_views(final(ev)@) == event_views(old(ev)@) + s2.events.skip(
                        s1.events.len() as int,
                    )
                }
            }),
            final(self).stop_code() == old(self).stop_code(),
            final(self).pending_stop() == if terminal(final(self).rfc().state) {
                None
            } else {
                old(self).pending_stop()
            },
            r matches Err(c) ==> recv_allowed_err(
                old(self).rfc(),
                off as nat,
                data@.len(),
                fin,
                conn_room as nat,
                c,
            ),
            final_size_trigger(old(self).rfc(), off as nat + data@.len(), fin) ==> r == Err::<u64, u64>(
                FINAL_SIZE_ERROR,
            ),
            (flow_trigger(old(self).rfc(), off as nat + data@.len(), fin, conn_room as nat)
                && !final_size_trigger(old(self).rfc(), off as nat + data@.len(), fin)) ==> r == Err::<
                u64,
                u64,
            >(FLOW_CONTROL_ERROR),
    {
        let ghost t2 = self.trace@.push(SpecRecvIn::Data { off: off as nat, data: data@, fin });
        let ghost s1 = self.rfc();
        proof {
            lemma_recv_push(self.id, self.credit.window_spec(), self.trace@, SpecRecvIn::Data {
                off: off as nat,
                data: data@,
                fin,
            });
        }
        let n_new = match self.data_gate(off, data, fin, conn_room) {
            Ok(n) => n,
            Err(c) => {
                return Err(c);
            },
        };
        if self.is_terminal() {
            self.trace = Ghost(t2);
            proof {
                assert(rfc_recv(self.id, self.credit.window_spec(), t2).events.skip(
                    s1.events.len() as int,
                ) =~= Seq::<SpecStreamEvent>::empty());
                assert(event_views(ev@) =~= event_views(ev@) + Seq::<SpecStreamEvent>::empty());
            }
            return Ok(0);
        }
        self.data_buffer(off, data, fin, ev);
        Ok(n_new)
    }

    /// `on_data`'s flow-control and final-size half: the error the frame raises, else the
    /// connection credit it consumes (split from `on_data` for the rlimit).
    #[verifier::spinoff_prover]
    fn data_gate(&self, off: u64, data: &[u8], fin: bool, conn_room: u64) -> (r: Result<u64, u64>)
        requires
            self.wf(),
            off + data@.len() <= VARINT_MAX,
        ensures
            ({
                let s1 = self.rfc();
                let s2 = recv_data(self.id_spec(), s1, off as nat, data@, fin);
                &&& s2.err matches Some(c) ==> r == Err::<u64, u64>(c)
                &&& (s2.err is None && counted(s2) - counted(s1) > conn_room) ==> r == Err::<
                    u64,
                    u64,
                >(FLOW_CONTROL_ERROR)
                &&& (s2.err is None && counted(s2) - counted(s1) <= conn_room) ==> r == Ok::<
                    u64,
                    u64,
                >((counted(s2) - counted(s1)) as u64)
            }),
            r matches Err(c) ==> recv_allowed_err(
                self.rfc(),
                off as nat,
                data@.len(),
                fin,
                conn_room as nat,
                c,
            ),
            final_size_trigger(self.rfc(), off as nat + data@.len(), fin) ==> r == Err::<u64, u64>(
                FINAL_SIZE_ERROR,
            ),
            (flow_trigger(self.rfc(), off as nat + data@.len(), fin, conn_room as nat)
                && !final_size_trigger(self.rfc(), off as nat + data@.len(), fin)) ==> r == Err::<
                u64,
                u64,
            >(FLOW_CONTROL_ERROR),
    {
        proof {
            self.credit.lemma_wf();
            self.lemma_wf();
            lemma_recv_err_rfc(self.id, self.rfc(), off as nat, data@, fin, conn_room as nat);
        }
        let end = off + data.len() as u64;
        let bad = match self.final_size {
            //= https://www.rfc-editor.org/rfc/rfc9000#section-4.5
            //# A receiver SHOULD treat receipt of data at or beyond the
            //# final size as an error of type FINAL_SIZE_ERROR, even after a stream
            //# is closed.
            //= https://www.rfc-editor.org/rfc/rfc9000#section-4.5
            //# If a
            //# RESET_STREAM or STREAM frame is received indicating a change in the
            //# final size for the stream, an endpoint SHOULD respond with an error
            //# of type FINAL_SIZE_ERROR; see Section 11 for details on error
            //# handling.
            Some(f) => end > f || (fin && end != f),
            None => fin && end < self.high,
        };
        if bad {
            return Err(FINAL_SIZE_ERROR);
        }
        //= https://www.rfc-editor.org/rfc/rfc9000#section-4.1
        //# A receiver MUST close the connection with an error of type
        //# FLOW_CONTROL_ERROR if the sender violates the advertised connection
        //# or stream data limits; see Section 11 for details on error handling.
        //= https://www.rfc-editor.org/rfc/rfc9000#section-19.10
        //# An endpoint MUST terminate a
        //# connection with an error of type FLOW_CONTROL_ERROR if it receives
        //# more data than the largest maximum stream data that it has sent for
        //# the affected stream.
        //= https://www.rfc-editor.org/rfc/rfc9000#section-3.5
        //# STREAM frames received after sending a STOP_SENDING frame are still
        //# counted toward connection and stream flow control, even though these
        //# frames can be discarded upon receipt.
        if end > self.credit.limit() {
            return Err(FLOW_CONTROL_ERROR);
        }
        if self.is_terminal() {
            return Ok(0);
        }
        let fs = if fin {
            Some(end)
        } else {
            self.final_size
        };
        let high = if end > self.high {
            end
        } else {
            self.high
        };
        let c2 = match fs {
            Some(f) => f,
            None => high,
        };
        let n_new = c2 - self.counted_exec();
        if n_new > conn_room {
            return Err(FLOW_CONTROL_ERROR);
        }
        Ok(n_new)
    }

    /// `on_data`'s buffering half: the frame passed `data_gate` and the stream is not
    /// terminal; its bytes are reassembled and the newly contiguous ones delivered (split from
    /// `on_data` for the rlimit).
    #[verifier::spinoff_prover]
    fn data_buffer(&mut self, off: u64, data: &[u8], fin: bool, ev: &mut Vec<StreamEvent>)
        requires
            old(self).wf(),
            off + data@.len() <= VARINT_MAX,
            !terminal(old(self).rfc().state),
            recv_data(old(self).id_spec(), old(self).rfc(), off as nat, data@, fin).err is None,
        ensures
            final(self).id_spec() == old(self).id_spec(),
            final(self).window_spec() == old(self).window_spec(),
            final(self).wf(),
            ({
                let t2 = old(self).trace().push(
                    SpecRecvIn::Data { off: off as nat, data: data@, fin },
                );
                let s1 = old(self).rfc();
                let s2 = rfc_recv(old(self).id_spec(), old(self).window_spec(), t2);
                &&& final(self).trace() == t2
                &&& event_views(final(ev)@) == event_views(old(ev)@) + s2.events.skip(
                    s1.events.len() as int,
                )
            }),
            final(self).stop_code() == old(self).stop_code(),
            final(self).pending_stop() == if terminal(final(self).rfc().state) {
                None
            } else {
                old(self).pending_stop()
            },
    {
        let ghost t2 = self.trace@.push(SpecRecvIn::Data { off: off as nat, data: data@, fin });
        let ghost s1 = self.rfc();
        proof {
            lemma_recv_push(self.id, self.credit.window_spec(), self.trace@, SpecRecvIn::Data {
                off: off as nat,
                data: data@,
                fin,
            });
            self.credit.lemma_wf();
        }
        let end = off + data.len() as u64;
        let fs = if fin {
            Some(end)
        } else {
            self.final_size
        };
        let high = if end > self.high {
            end
        } else {
            self.high
        };
        let mut re = match self.re.take() {
            Some(r) => r,
            None => Reassembly::new(),  // unreachable: `re` is Some unless ResetRead
        };
        proof {
            re.lemma_wf();
        }
        let delivered = re.base_exec();
        insert_tight(&mut re, off, data);
        let ghost re1 = re;
        let mut out: Vec<u8> = Vec::new();
        re.pop(&mut out);
        let n = re.base_exec();
        proof {
            Reassembly::lemma_pop_tight(re1, re);
            re.lemma_wf();
        }
        let done = match fs {
            Some(f) => f == n,
            None => false,
        };
        let st = if done {
            RecvState::DataRead
        } else if fs.is_some() {
            RecvState::SizeKnown
        } else {
            RecvState::Recv
        };
        let ghost s2 = rfc_recv(self.id, self.credit.window_spec(), t2);
        proof {
            assert(out@ == rfc_prefix(rfc_received(s2.ins), n as nat).subrange(
                delivered as int,
                n as int,
            ));
        }
        let ghost old_ev = ev@;
        if n > delivered || done {
            ev.push(StreamEvent::Data { id: self.id, data: out, fin: done });
            proof {
                assert(ev@ =~= old_ev.push(ev@.last()));
                assert(event_views(ev@) =~= event_views(old_ev).push(ev@.last()@));
                assert(s2.events.skip(s1.events.len() as int) =~= seq![s2.events.last()]);
            }
        } else {
            proof {
                assert(s2.events.skip(s1.events.len() as int) =~= Seq::<SpecStreamEvent>::empty());
                assert(event_views(ev@) =~= event_views(ev@) + Seq::<SpecStreamEvent>::empty());
            }
        }
        self.credit.on_consumed(n - delivered);
        self.re = Some(re);
        self.state = st;
        self.high = high;
        self.final_size = fs;
        self.trace = Ghost(t2);
        self.emitted = Ghost(s2.events);
        proof {
            assert(self.wf());
        }
    }

    /// A RESET_STREAM frame's error code and final size, with `conn_room` bytes of connection
    /// credit left. `Ok(n)`: the stream consumed `n` more bytes of connection credit.
    pub fn on_reset(
        &mut self,
        code: u64,
        final_size: u64,
        conn_room: u64,
        ev: &mut Vec<StreamEvent>,
    ) -> (r: Result<u64, u64>)
        requires
            old(self).wf(),
        ensures
            final(self).id_spec() == old(self).id_spec(),
            final(self).window_spec() == old(self).window_spec(),
            final(self).wf(),
            ({
                let t2 = old(self).trace().push(
                    SpecRecvIn::Reset { code, final_size: final_size as nat },
                );
                let s1 = old(self).rfc();
                let s2 = rfc_recv(old(self).id_spec(), old(self).window_spec(), t2);
                &&& s2.err matches Some(c) ==> r == Err::<u64, u64>(c) && *final(self) == *old(self)
                    && final(ev)@ == old(ev)@
                &&& (s2.err is None && counted(s2) - counted(s1) > conn_room) ==> r == Err::<
                    u64,
                    u64,
                >(FLOW_CONTROL_ERROR) && *final(self) == *old(self) && final(ev)@ == old(ev)@
                &&& (s2.err is None && counted(s2) - counted(s1) <= conn_room) ==> {
                    &&& r == Ok::<u64, u64>((counted(s2) - counted(s1)) as u64)
                    &&& final(self).trace() == t2
                    &&& event_views(final(ev)@) == event_views(old(ev)@) + s2.events.skip(
                        s1.events.len() as int,
                    )
                }
            }),
            final(self).stop_code() == old(self).stop_code(),
            final(self).pending_stop() == if terminal(final(self).rfc().state) {
                None
            } else {
                old(self).pending_stop()
            },
            // Reset or suppressed after all data was delivered: nothing stays buffered.
            r is Ok ==> final(self).buffered_len() == 0,
    {
        let ghost t2 = self.trace@.push(
            SpecRecvIn::Reset { code, final_size: final_size as nat },
        );
        let ghost s1 = self.rfc();
        proof {
            lemma_recv_push(self.id, self.credit.window_spec(), self.trace@, SpecRecvIn::Reset {
                code,
                final_size: final_size as nat,
            });
            self.credit.lemma_wf();
        }
        let changed = match self.final_size {
            Some(f) => f != final_size,
            None => false,
        };
        // §4.5 (cited at `on_data`): a changed final size, or one below data received.
        if changed || final_size < self.high {
            return Err(FINAL_SIZE_ERROR);
        }
        if final_size > self.credit.limit() {
            return Err(FLOW_CONTROL_ERROR);
        }
        if self.is_terminal() {
            //= https://www.rfc-editor.org/rfc/rfc9000#section-3.2
            //# A RESET_STREAM signal might be suppressed or withheld
            //# if stream data is completely received and is buffered to be read by
            //# the application.
            self.trace = Ghost(t2);
            proof {
                assert(rfc_recv(self.id, self.credit.window_spec(), t2).events.skip(
                    s1.events.len() as int,
                ) =~= Seq::<SpecStreamEvent>::empty());
                assert(event_views(ev@) =~= event_views(ev@) + Seq::<SpecStreamEvent>::empty());
            }
            return Ok(0);
        }
        let n_new = final_size - self.counted_exec();
        if n_new > conn_room {
            return Err(FLOW_CONTROL_ERROR);
        }
        let ghost s2 = rfc_recv(self.id, self.credit.window_spec(), t2);
        let ghost old_ev = ev@;
        ev.push(StreamEvent::Reset { id: self.id, code });
        proof {
            assert(ev@ =~= old_ev.push(ev@.last()));
            assert(event_views(ev@) =~= event_views(old_ev).push(ev@.last()@));
            assert(s2.events.skip(s1.events.len() as int) =~= seq![s2.events.last()]);
        }
        self.re = None;
        self.state = RecvState::ResetRead;
        self.high = final_size;
        self.final_size = Some(final_size);
        self.trace = Ghost(t2);
        self.emitted = Ghost(s2.events);
        Ok(n_new)
    }
}

} // verus!

impl RecvStream {
    /// Test support: the allocated capacities of the reassembly buffers, `(0, 0)` once reset.
    /// Verus models `Vec` length, not capacity (TRUSTED.md).
    #[doc(hidden)]
    pub fn capacities(&self) -> (usize, usize) {
        match &self.re {
            Some(r) => r.capacities(),
            None => (0, 0),
        }
    }
}
