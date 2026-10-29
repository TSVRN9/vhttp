//! A connection's streams (RFC 9000 §2–4). Each frame naming a stream is checked against the
//! stream's type and our limits, opens peer streams implicitly (§3.2), and goes to that stream's
//! receiving or sending part. Connection receive credit counts each stream's final size, or else
//! its high-water mark, exactly once (§4.5). On the way out, `poll_frames` emits resets, stops,
//! credit updates and STREAM chunks within a byte budget and every flow control limit
//! (§4.1); the application writes, resets and stops streams through `write`, `reset` and
//! `stop_sending`. Sans-IO.
//!
//! Caller obligations (Phase 3d; stated here, not proven by this module):
//! - **Frames polled are frames sent.** Report every frame `poll_frames` returns to
//!   `on_frame_acked` or `on_frame_lost` once its packet is acknowledged or declared lost; one
//!   that is never transmitted is reported lost at once.
//! - **`start()` first.** Call `H3Conn::start` before delivering the first `StreamEvent` or
//!   calling `send_response`, so SETTINGS opens stream 3 (RFC 9114 §6.2.1, §7.2.4.2).
//! - **Every event, in order.** Pass each `StreamEvent` to `H3Conn` in the order pushed
//!   (`Data` to `on_stream_data`, `Reset` to `on_stream_reset`), so `H3Conn` has forgotten a
//!   stream by the time MAX_STREAMS re-credits it (2b obligation 1).
//! - **Abort signal.** When a `Reset` reaches a request stream whose response already went
//!   out (`send_open` false), `H3Conn` outputs nothing; tell the application that any
//!   `RequestBody` stream for that request was aborted (2b obligation 4). Every `Reset` is
//!   delivered, also after a local `stop_sending`.
//! - **Forward every `StopSending`** to `H3Conn::on_stop_sending`, on every stream (stream 3
//!   gets H3_CLOSED_CRITICAL_STREAM).
//! - `Output::ResetStream` goes to `reset`, `Output::StopSending` to `stop_sending`, and
//!   `Output::StreamWrite` to `write`.
//! - **Our own uni streams.** `write` opens them up to the peer's MAX_STREAMS limit (up to
//!   2^60) and nothing here caps them; the adapter opens only stream 3.
//! - **Write backpressure.** The proven send-side bound is relative: buffered bytes ≤
//!   2·(unacknowledged bytes) per stream. Nothing here caps the total, so the caller must stop
//!   calling `write` once its own absolute budget is reached.
//! - **ACK-range growth.** Each send part keeps acked/lost range lists whose length grows when
//!   the peer acks alternate packets while drip-feeding credit; the caller caps ACK ranges or
//!   enforces a minimum chunk size.
//! - **Loop on `poll_data`, not `next_off`.** `next_off()` returning `Some` does not mean
//!   `poll_data` sends anything (stream or connection credit may be 0); a
//!   `while next_off().is_some()` loop spins forever on a blocked stream.
//! - **Window is not pinned.** `lemma_wf` bounds receive memory by 2·limit; the tighter
//!   2·window bound also needs the window to stay fixed, which no ensures states yet.
use vstd::prelude::*;
use crate::codes::*;
use crate::flow::*;
use crate::frame::*;
// `PacketKind` and `frame_permitted` appear only in contracts, which a plain `cargo build` erases.
#[allow(unused_imports)]
use crate::payload::*;
use crate::recv_stream::*;
use crate::send_stream::*;
use crate::stream_id::*;
use crate::tp::*;
// Used only in ghost code, which a plain `cargo build` erases.
#[allow(unused_imports)]
use wire::varint::*;

verus! {

// ponytail: linear scan over open streams, bounded by our advertised stream windows; HashMap if concurrency grows past ~100.
/// One open stream. A client bidirectional stream has both parts, a client unidirectional
/// stream only a receiving part, and one of ours only a sending part.
struct Entry {
    id: u64,
    recv: Option<RecvStream>,
    send: Option<SendStream>,
}

// ponytail: matches the linear-scan bound above; raise both together.
/// The most peer streams of each type we let the peer have open (our `initial_max_streams_*`).
pub const MAX_LOCAL_STREAMS: u64 = 100;

/// The transport parameters `Streams` reads, in range.
pub open spec fn stream_tp_ok(p: SpecTp) -> bool {
    &&& p.initial_max_data <= VARINT_MAX
    &&& p.initial_max_stream_data_bidi_local <= VARINT_MAX
    &&& p.initial_max_stream_data_bidi_remote <= VARINT_MAX
    &&& p.initial_max_stream_data_uni <= VARINT_MAX
    &&& p.initial_max_streams_bidi <= MAX_STREAMS_LIMIT
    &&& p.initial_max_streams_uni <= MAX_STREAMS_LIMIT
}

/// Our own transport parameters satisfy `stream_tp_ok`.
pub proof fn lemma_server_tp_stream_ok(p: SpecTp)
    requires
        server_tp_wf(p),
    ensures
        stream_tp_ok(p),
{
}

/// The frames `Streams::on_frame` takes: types 0x04, 0x05 and 0x08–0x17.
pub open spec fn is_stream_layer_frame(f: SpecFrame) -> bool {
    ||| f is ResetStream
    ||| f is StopSending
    ||| f is Stream
    ||| f is MaxData
    ||| f is MaxStreamData
    ||| f is MaxStreams
    ||| f is DataBlocked
    ||| f is StreamDataBlocked
    ||| f is StreamsBlocked
}

/// The stream named by one of the five stream frames.
pub open spec fn frame_stream_id(f: SpecFrame) -> Option<u64> {
    match f {
        SpecFrame::Stream { stream_id, .. } => Some(stream_id),
        SpecFrame::ResetStream { stream_id, .. } => Some(stream_id),
        SpecFrame::StopSending { stream_id, .. } => Some(stream_id),
        SpecFrame::MaxStreamData { stream_id, .. } => Some(stream_id),
        SpecFrame::StreamDataBlocked { stream_id, .. } => Some(stream_id),
        _ => None,
    }
}

/// The receiving-part input a STREAM or RESET_STREAM frame carries.
pub open spec fn frame_recv_in(f: SpecFrame) -> Option<SpecRecvIn> {
    match f {
        SpecFrame::Stream { offset, data, fin, .. } => Some(
            SpecRecvIn::Data { off: offset as nat, data, fin },
        ),
        SpecFrame::ResetStream { error_code, final_size, .. } => Some(
            SpecRecvIn::Reset { code: error_code, final_size: final_size as nat },
        ),
        _ => None,
    }
}

// The direction, creation and limit table, checked before anything else. With k the type of
// the frame's stream (Table 1), the first matching row wins:
//
//   k                    | frame                                     | result
//   ---------------------+-------------------------------------------+--------------------
//   server bidi          | any of the five stream frames             | STREAM_STATE_ERROR
//   server uni           | STREAM, RESET_STREAM, STREAM_DATA_BLOCKED | STREAM_STATE_ERROR
//   client uni           | MAX_STREAM_DATA, STOP_SENDING             | STREAM_STATE_ERROR
//   server uni, unopened | MAX_STREAM_DATA, STOP_SENDING             | STREAM_STATE_ERROR
//   client bidi/uni      | ID at or past the limit we sent           | STREAM_LIMIT_ERROR
//   otherwise            |                                           | none
//
// We never open a bidirectional stream, so a server-bidi ID is always "a locally initiated
// stream that has not yet been created" (§19.5, §19.8, §19.10); the RFC names no code for
// RESET_STREAM or STREAM_DATA_BLOCKED there, and we use the same one. Server uni streams are
// send-only for us (§19.4, §19.8, §19.13), client uni streams receive-only (§19.5, §19.10).
// The limit is §4.6 and §19.11.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-19.4
//# An endpoint that receives a RESET_STREAM frame for a send-only stream
//# MUST terminate the connection with error STREAM_STATE_ERROR.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-19.5
//# Receiving a STOP_SENDING frame for a
//# locally initiated stream that has not yet been created MUST be
//# treated as a connection error of type STREAM_STATE_ERROR.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-19.5
//# An
//# endpoint that receives a STOP_SENDING frame for a receive-only stream
//# MUST terminate the connection with error STREAM_STATE_ERROR.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-19.8
//# An endpoint MUST terminate the connection with error
//# STREAM_STATE_ERROR if it receives a STREAM frame for a locally
//# initiated stream that has not yet been created, or for a send-only
//# stream.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-19.10
//# Receiving a MAX_STREAM_DATA frame for a locally
//# initiated stream that has not yet been created MUST be treated as a
//# connection error of type STREAM_STATE_ERROR.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-19.10
//# An endpoint that
//# receives a MAX_STREAM_DATA frame for a receive-only stream MUST
//# terminate the connection with error STREAM_STATE_ERROR.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-19.13
//# An endpoint that receives a STREAM_DATA_BLOCKED frame for a send-only
//# stream MUST terminate the connection with error STREAM_STATE_ERROR.
pub open spec fn rfc_stream_frame_check(ids: StreamIds, f: SpecFrame) -> Option<u64> {
    match frame_stream_id(f) {
        None => None,
        Some(id) => {
            let k = spec_stream_kind(id);
            let senders = f is Stream || f is ResetStream || f is StreamDataBlocked;
            let receivers = f is MaxStreamData || f is StopSending;
            if k is ServerBidi {
                Some(STREAM_STATE_ERROR)
            } else if k is ServerUni && senders {
                Some(STREAM_STATE_ERROR)
            } else if k is ClientUni && receivers {
                Some(STREAM_STATE_ERROR)
            } else if k is ServerUni && receivers && !ids.local_uni_created(id) {
                Some(STREAM_STATE_ERROR)
            } else if (k is ClientBidi || k is ClientUni) && !peer_id_allowed(
                id,
                ids.peer_limit(k is ClientBidi),
            ) {
                Some(STREAM_LIMIT_ERROR)
            } else {
                None
            }
        },
    }
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-4.1
//# A receiver MUST close the connection with an error of type
//# FLOW_CONTROL_ERROR if the sender violates the advertised connection
//# or stream data limits; see Section 11 for details on error handling.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-19.9
//# An
//# endpoint MUST terminate a connection with an error of type
//# FLOW_CONTROL_ERROR if it receives more data than the maximum data
//# value that it has sent.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-19.10
//# An endpoint MUST terminate a
//# connection with an error of type FLOW_CONTROL_ERROR if it receives
//# more data than the largest maximum stream data that it has sent for
//# the affected stream.
//
// The 2^62-1 bound on a STREAM frame's end is enforced by 3b's parser (`frame_wf`, which
// `on_frame` requires), so it never reaches this table:
//= https://www.rfc-editor.org/rfc/rfc9000#section-19.8
//# The largest offset
//# delivered on a stream -- the sum of the offset and data length --
//# cannot exceed 2^62-1, as it is not possible to provide flow control
//# credit for that data.  Receipt of a frame that exceeds this limit
//# MUST be treated as a connection error of type FRAME_ENCODING_ERROR or
//# FLOW_CONTROL_ERROR.
/// The result once the table passed: a STREAM or RESET_STREAM frame on a stream not removed
/// fails as its receiving part does (FINAL_SIZE_ERROR, then FLOW_CONTROL_ERROR for the stream),
/// then with FLOW_CONTROL_ERROR if it would take more connection credit than is left.
pub open spec fn rx_outcome(s: Streams, f: SpecFrame) -> Result<(), u64> {
    match (frame_stream_id(f), frame_recv_in(f)) {
        (Some(id), Some(i)) => if s.is_removed(id) {
            Ok(())
        } else {
            let s2 = rfc_recv(id, s.rx_window(id), s.rx_trace(id).push(i));
            match s2.err {
                Some(c) => Err(c),
                None => if counted(s2) - counted(s.rx_spec(id)) > s.conn_room() {
                    Err(FLOW_CONTROL_ERROR)
                } else {
                    Ok(())
                },
            }
        },
        _ => Ok(()),
    }
}

/// The receive trace of stream `j` after one frame: the frame's input appended, for its own
/// stream unless that stream was removed.
pub open spec fn rx_trace_after(s0: Streams, f: SpecFrame, r: Result<(), u64>, j: u64) -> Seq<
    SpecRecvIn,
> {
    if r is Ok && frame_stream_id(f) == Some(j) && frame_recv_in(f) is Some && !s0.is_removed(j) {
        s0.rx_trace(j).push(frame_recv_in(f)->0)
    } else {
        s0.rx_trace(j)
    }
}

/// The events one successful frame pushes: the new receive events of its stream, or one
/// `StopSending` when the peer's STOP_SENDING freshly reset our sending part.
pub open spec fn frame_events(s0: Streams, s1: Streams, f: SpecFrame) -> Seq<SpecStreamEvent> {
    match f {
        SpecFrame::StopSending { stream_id, error_code } => if s1.send_reset(stream_id)
            && !s0.send_reset(stream_id) {
            seq![SpecStreamEvent::StopSending { id: stream_id, code: error_code }]
        } else {
            Seq::empty()
        },
        _ => match frame_stream_id(f) {
            Some(id) => s1.rx_spec(id).events.skip(s0.rx_spec(id).events.len() as int),
            None => Seq::empty(),
        },
    }
}

/// What `on_frame` guarantees besides `wf` and the latch.
pub open spec fn frame_post(
    s0: Streams,
    s1: Streams,
    f: SpecFrame,
    ev0: Seq<SpecStreamEvent>,
    ev1: Seq<SpecStreamEvent>,
    r: Result<(), u64>,
) -> bool {
    // Error classification: the table, then the stream's receiving part.
    &&& r == match rfc_stream_frame_check(s0.ids_spec(), f) {
        Some(c) => Err(c),
        None => rx_outcome(s0, f),
    }
    &&& post_rest(s0, s1, f, ev0, ev1, r)
}

/// §3.5: an accepted STOP_SENDING for a sending part in Ready, Send or Data Sent resets it with
/// the peer's code.
pub open spec fn stop_resets(s0: Streams, s1: Streams, f: SpecFrame, r: Result<(), u64>) -> bool {
    match f {
        SpecFrame::StopSending { stream_id, error_code } => r is Ok ==> match s0.tx_part(
            stream_id,
        ) {
            Some(p) => (p.state() is Ready || p.state() is Send || p.state() is DataSent)
                ==> s1.reset_code(stream_id) == Some(error_code),
            None => true,
        },
        _ => true,
    }
}

/// The open stream's sending part is unchanged when other streams open.
spec fn parts_kept(s0: Streams, s1: Streams) -> bool {
    forall|j: u64| #[trigger] s0.tx_part(j) is Some ==> s1.tx_part(j) == s0.tx_part(j)
}

/// `frame_post` past the result.
pub open spec fn post_rest(
    s0: Streams,
    s1: Streams,
    f: SpecFrame,
    ev0: Seq<SpecStreamEvent>,
    ev1: Seq<SpecStreamEvent>,
    r: Result<(), u64>,
) -> bool {
    // Delegation: the new events are exactly the stream's machine outputs for its extended
    // trace, and no other stream's trace changes.
    &&& r is Err ==> ev1 == ev0
    &&& r is Ok ==> ev1 == ev0 + frame_events(s0, s1, f)
    &&& forall|j: u64| #[trigger] s1.rx_trace(j) == rx_trace_after(s0, f, r, j)
    // Removal and reset records only grow, and only for the frame's stream.
    &&& forall|j: u64| #[trigger] s0.is_removed(j) ==> s1.is_removed(j)
    &&& forall|j: u64| #[trigger]
        s1.is_removed(j) && !s0.is_removed(j) ==> frame_stream_id(f) == Some(j)
    &&& forall|j: u64| #[trigger] s0.send_reset(j) ==> s1.send_reset(j)
    &&& forall|j: u64| #[trigger]
        s1.send_reset(j) && !s0.send_reset(j) ==> f is StopSending && frame_stream_id(f)
            == Some(j)
    &&& forall|j: u64| #[trigger] s0.reset_code(j) is Some ==> s1.reset_code(j) == s0.reset_code(j)
    &&& stop_resets(s0, s1, f, r)
    // E5: a closed peer stream is re-credited only as its entry is removed.
    &&& forall|b: bool| #[trigger]
        s1.peer_closed(b) == s0.peer_closed(b) || (s1.peer_closed(b) == s0.peer_closed(b) + 1
            && (frame_stream_id(f) matches Some(id) && (id % 4 == 0) == b && (id % 4 == 0 || id
            % 4 == 2) && s1.is_removed(id) && !s0.is_removed(id)))
}

// ---- Sums over the entries ----

/// Per-entry quantities: 0 counted, 1 retired, 2 buffered, 3 physically buffered; 4 + k is 1
/// for a stream of type k; on the sending part, 8 bytes sent (`sent_end`), 9 buffered, 10
/// written but not acknowledged.
spec fn val(e: Entry, q: int) -> int {
    if q >= 8 {
        match e.send {
            Some(p) => if q == 8 {
                p.sent_end() as int
            } else if q == 9 {
                p.buffered_spec() as int
            } else {
                p.all_written().len() - p.acked_point_spec()
            },
            None => 0,
        }
    } else {
        val_rx(e, q)
    }
}

spec fn val_rx(e: Entry, q: int) -> int {
    if q == 0 {
        match e.recv {
            Some(r) => counted(r.rfc()) as int,
            None => 0,
        }
    } else if q == 1 {
        match e.recv {
            Some(r) => retired(r.rfc()) as int,
            None => 0,
        }
    } else if q == 2 {
        match e.recv {
            Some(r) => r.buffered_len() as int,
            None => 0,
        }
    } else if q == 3 {
        match e.recv {
            Some(r) => r.buffered_phys() as int,
            None => 0,
        }
    } else if (e.id % 4) as int == q - 4 {
        1
    } else {
        0
    }
}

/// The selector counting peer streams of one direction.
spec fn kq(bidi: bool) -> int {
    if bidi {
        4
    } else {
        6
    }
}

spec fn sum(s: Seq<Entry>, q: int) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        sum(s.drop_last(), q) + val(s.last(), q)
    }
}

proof fn lemma_sum_push(s: Seq<Entry>, e: Entry, q: int)
    ensures
        sum(s.push(e), q) == sum(s, q) + val(e, q),
{
    assert(s.push(e).drop_last() =~= s);
}

proof fn lemma_sum_update(s: Seq<Entry>, i: int, e: Entry, q: int)
    requires
        0 <= i < s.len(),
    ensures
        sum(s.update(i, e), q) == sum(s, q) - val(s[i], q) + val(e, q),
    decreases s.len(),
{
    let t = s.update(i, e);
    if i == s.len() - 1 {
        assert(t.drop_last() =~= s.drop_last());
    } else {
        assert(t.drop_last() =~= s.drop_last().update(i, e));
        lemma_sum_update(s.drop_last(), i, e, q);
    }
}

proof fn lemma_sum_remove(s: Seq<Entry>, i: int, q: int)
    requires
        0 <= i < s.len(),
    ensures
        sum(s.remove(i), q) == sum(s, q) - val(s[i], q),
    decreases s.len(),
{
    if i == s.len() - 1 {
        assert(s.remove(i) =~= s.drop_last());
    } else {
        assert(s.remove(i).drop_last() =~= s.drop_last().remove(i));
        assert(s.remove(i).last() == s.last());
        lemma_sum_remove(s.drop_last(), i, q);
    }
}

proof fn lemma_sum_kind_nonneg(s: Seq<Entry>, q: int)
    requires
        4 <= q < 8,
    ensures
        sum(s, q) >= 0,
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_sum_kind_nonneg(s.drop_last(), q);
    }
}

/// The per-entry bounds behind the connection-level ones.
spec fn terms_ok(e: Entry) -> bool {
    &&& 0 <= val(e, 2) <= val(e, 3) <= 2 * val(e, 2)
    &&& val(e, 2) <= val(e, 0) - val(e, 1)
    &&& 0 <= val(e, 1) <= val(e, 0)
}

proof fn lemma_sum_bounds(s: Seq<Entry>)
    requires
        forall|k: int| 0 <= k < s.len() ==> terms_ok(#[trigger] s[k]),
    ensures
        0 <= sum(s, 2) <= sum(s, 3) <= 2 * sum(s, 2),
        sum(s, 2) <= sum(s, 0) - sum(s, 1),
        0 <= sum(s, 1) <= sum(s, 0),
    decreases s.len(),
{
    if s.len() > 0 {
        let p = s.drop_last();
        assert forall|k: int| 0 <= k < p.len() implies terms_ok(#[trigger] p[k]) by {
            assert(p[k] == s[k]);
        }
        lemma_sum_bounds(p);
        assert(terms_ok(s[s.len() - 1]));
    }
}

/// The per-entry send-side bounds behind the connection-level ones.
spec fn tx_terms_ok(e: Entry) -> bool {
    0 <= val(e, 9) <= 2 * val(e, 10)
}

proof fn lemma_sum_tx(s: Seq<Entry>)
    requires
        forall|k: int| 0 <= k < s.len() ==> tx_terms_ok(#[trigger] s[k]),
    ensures
        0 <= sum(s, 9) <= 2 * sum(s, 10),
    decreases s.len(),
{
    if s.len() > 0 {
        let p = s.drop_last();
        assert forall|k: int| 0 <= k < p.len() implies tx_terms_ok(#[trigger] p[k]) by {
            assert(p[k] == s[k]);
        }
        lemma_sum_tx(p);
        assert(tx_terms_ok(s[s.len() - 1]));
    }
}

// ---- Entry invariants ----

/// Some entry is stream `id`.
spec fn has_id(s: Seq<Entry>, id: u64) -> bool {
    exists|k: int| 0 <= k < s.len() && (#[trigger] s[k]).id == id
}

/// One entry: its parts match its type, and its receiving part runs our window for that type.
spec fn entry_ok(e: Entry, rxb: u64, rxu: u64) -> bool {
    &&& e.id % 4 != 1
    &&& ((e.id % 4 == 0 || e.id % 4 == 2) <==> e.recv is Some)
    &&& ((e.id % 4 == 0 || e.id % 4 == 3) <==> e.send is Some)
    &&& e.recv matches Some(r) ==> r.wf() && r.id_spec() == e.id && r.window_spec() == (if e.id
        % 4 == 0 {
        rxb
    } else {
        rxu
    })
    &&& e.send matches Some(s) ==> s.wf()
}

proof fn lemma_terms(e: Entry, rxb: u64, rxu: u64)
    requires
        entry_ok(e, rxb, rxu),
    ensures
        terms_ok(e),
{
    if let Some(r) = e.recv {
        r.lemma_wf();
        lemma_retired_le_counted(r.id_spec(), r.window_spec(), r.trace());
    }
}

/// A stream ID that was opened: by the peer, or by us.
spec fn created(ids: StreamIds, id: u64) -> bool {
    ids.peer_created(id) || ids.local_uni_created(id)
}

/// The per-entry invariants and the ID bookkeeping around them.
spec fn entries_ok(
    s: Seq<Entry>,
    ids: StreamIds,
    rxb: u64,
    rxu: u64,
    rtr: Map<u64, Seq<SpecRecvIn>>,
    removed: Set<u64>,
    resets: Map<u64, u64>,
) -> bool {
    &&& forall|k: int| 0 <= k < s.len() ==> entry_ok(#[trigger] s[k], rxb, rxu)
    &&& forall|j: int, k: int|
        0 <= j < s.len() && 0 <= k < s.len() && j != k ==> (#[trigger] s[j]).id != (
        #[trigger] s[k]).id
    &&& forall|k: int| 0 <= k < s.len() ==> created(ids, (#[trigger] s[k]).id)
    &&& forall|k: int| 0 <= k < s.len() ==> !removed.contains((#[trigger] s[k]).id)
    // Each receiving part's trace is the recorded one.
    &&& forall|k: int|
        0 <= k < s.len() ==> ((#[trigger] s[k]).recv matches Some(r) ==> rtr.contains_key(s[k].id)
            && rtr[s[k].id] == r.trace())
    // §11.2 (finished in Task 6): a sending part is reset only by the peer's STOP_SENDING, with
    // its code.
    &&& forall|k: int|
        0 <= k < s.len() ==> ((#[trigger] s[k]).send matches Some(p) ==> (
        p.reset_spec() matches Some(c) ==> resets.contains_key(s[k].id) && resets[s[k].id] == c.0)
            && (resets.contains_key(s[k].id) ==> p.reset_spec() is Some))
}

/// A removed stream's receiving part: terminal, without error.
spec fn removed_ok(s: SpecRecv) -> bool {
    terminal(s.state) && s.err is None
}

/// The recorded traces: one per peer stream opened, each removed stream's terminal, and every
/// other one live.
spec fn records_ok(
    s: Seq<Entry>,
    ids: StreamIds,
    rxb: u64,
    rxu: u64,
    rtr: Map<u64, Seq<SpecRecvIn>>,
    removed: Set<u64>,
    resets: Map<u64, u64>,
) -> bool {
    &&& forall|id: u64| #[trigger] rtr.contains_key(id) == ids.peer_created(id)
    &&& forall|id: u64| #[trigger]
        removed.contains(id) ==> rtr.contains_key(id) && removed_ok(
            rfc_recv(
                id,
                if id % 4 == 0 {
                    rxb
                } else {
                    rxu
                },
                rtr[id],
            ),
        )
    &&& forall|id: u64| #[trigger]
        rtr.contains_key(id) && !removed.contains(id) ==> has_id(s, id)
    &&& forall|id: u64| #[trigger] resets.contains_key(id) ==> created(ids, id)
}

/// The connection's streams.
pub struct Streams {
    ids: StreamIds,
    entries: Vec<Entry>,
    /// Our MAX_DATA: `consumed` is Σ retired over every stream, removed ones included.
    conn_recv: RecvCredit,
    /// Σ counted (final size, else high-water mark) over every stream, removed ones included.
    conn_counted: u64,
    /// The peer's MAX_DATA.
    conn_send: SendCredit,
    /// Our receive window on client bidi and client uni streams
    /// (`local.initial_max_stream_data_bidi_remote`, `_uni`).
    rx_bidi: u64,
    rx_uni: u64,
    /// Our initial send limit on client bidi streams (`peer.initial_max_stream_data_bidi_local`)
    /// and on our uni streams (`peer.initial_max_stream_data_uni`).
    tx_bidi: u64,
    tx_uni: u64,
    failed: bool,
    /// Every peer stream's receive trace, removed streams included.
    rtr: Ghost<Map<u64, Seq<SpecRecvIn>>>,
    /// Peer streams whose entry was removed.
    removed: Ghost<Set<u64>>,
    /// The code each sending part was reset with: by the peer's STOP_SENDING (§3.5) or by
    /// `reset` (§11.2), the only two writers.
    resets: Ghost<Map<u64, u64>>,
    /// Σ counted (which equals Σ retired) over the removed streams.
    gone: Ghost<nat>,
    /// Σ bytes sent (`sent_end`) over the removed entries.
    tx_gone: Ghost<nat>,
}

impl Streams {
    pub closed spec fn ids_spec(&self) -> StreamIds {
        self.ids
    }

    pub closed spec fn failed_spec(&self) -> bool {
        self.failed
    }

    /// This state with the latch set.
    pub closed spec fn latched(&self) -> Streams {
        Streams { failed: true, ..*self }
    }

    /// Our receive window on peer stream `id`.
    pub closed spec fn rx_window(&self, id: u64) -> u64 {
        if id % 4 == 0 {
            self.rx_bidi
        } else {
            self.rx_uni
        }
    }

    /// Every STREAM and RESET_STREAM input stream `id`'s receiving part has taken.
    pub closed spec fn rx_trace(&self, id: u64) -> Seq<SpecRecvIn> {
        if self.rtr@.contains_key(id) {
            self.rtr@[id]
        } else {
            Seq::empty()
        }
    }

    /// Stream `id`'s receiving part, as specified.
    pub open spec fn rx_spec(&self, id: u64) -> SpecRecv {
        rfc_recv(id, self.rx_window(id), self.rx_trace(id))
    }

    /// Peer stream `id` was removed: both its parts reached a terminal state.
    pub closed spec fn is_removed(&self, id: u64) -> bool {
        self.removed@.contains(id)
    }

    /// Our sending part of stream `id` was reset: by the peer's STOP_SENDING or by `reset`.
    pub closed spec fn send_reset(&self, id: u64) -> bool {
        self.resets@.contains_key(id)
    }

    /// The code our sending part of stream `id` was reset with, once reset.
    pub closed spec fn reset_code(&self, id: u64) -> Option<u64> {
        if self.resets@.contains_key(id) {
            Some(self.resets@[id])
        } else {
            None
        }
    }

    /// The sending part of stream `id`, while it has an entry.
    pub closed spec fn tx_part(&self, id: u64) -> Option<SendStream> {
        if has_id(self.entries@, id) {
            let k = choose|k: int|
                0 <= k < self.entries@.len() && (#[trigger] self.entries@[k]).id == id;
            self.entries@[k].send
        } else {
            None
        }
    }

    /// Peer stream `id` is open: created and not yet removed, so it has a receiving part.
    pub open spec fn rx_live(&self, id: u64) -> bool {
        self.ids_spec().peer_created(id) && !self.is_removed(id)
    }

    /// Σ bytes sent over every sending part, removed ones included: what the peer's MAX_DATA
    /// has been spent on (§4.1, §19.9).
    pub closed spec fn tx_sent(&self) -> int {
        self.tx_gone@ + sum(self.entries@, 8)
    }

    /// Σ `buffered_spec()` over the sending parts.
    pub closed spec fn tx_buffered(&self) -> int {
        sum(self.entries@, 9)
    }

    /// Σ bytes written but not yet acknowledged over the sending parts.
    pub closed spec fn tx_unacked(&self) -> int {
        sum(self.entries@, 10)
    }

    /// Streams with an entry.
    pub closed spec fn live_streams(&self) -> nat {
        self.entries@.len()
    }

    /// How many peer streams of this direction were closed (MAX_STREAMS `consumed`).
    pub closed spec fn peer_closed(&self, bidi: bool) -> u64 {
        self.ids.peer_credit_spec(bidi).consumed_spec()
    }

    /// Connection credit left under the MAX_DATA we sent.
    pub closed spec fn conn_room(&self) -> int {
        self.conn_recv.limit_spec() - self.conn_counted
    }

    pub closed spec fn conn_counted_spec(&self) -> u64 {
        self.conn_counted
    }

    pub closed spec fn conn_recv_spec(&self) -> RecvCredit {
        self.conn_recv
    }

    pub closed spec fn conn_send_spec(&self) -> SendCredit {
        self.conn_send
    }

    /// Open peer streams of this direction.
    pub closed spec fn live_peer_streams(&self, bidi: bool) -> int {
        sum(self.entries@, kq(bidi))
    }

    /// Our `initial_max_streams_*` for this direction: the MAX_STREAMS window, which never
    /// changes.
    pub closed spec fn init_max_streams(&self, bidi: bool) -> u64 {
        self.ids.peer_credit_spec(bidi).window_spec()
    }

    /// Σ `buffered_len()` over the receiving parts.
    pub closed spec fn rx_buffered(&self) -> int {
        sum(self.entries@, 2)
    }

    /// Σ `buffered_phys()` over the receiving parts.
    pub closed spec fn rx_buffered_phys(&self) -> int {
        sum(self.entries@, 3)
    }

    pub closed spec fn wf(&self) -> bool {
        &&& self.ids.wf()
        &&& self.conn_recv.wf()
        &&& self.conn_recv.cap_spec() == VARINT_MAX
        &&& self.conn_send.wf()
        &&& self.rx_bidi <= VARINT_MAX
        &&& self.rx_uni <= VARINT_MAX
        &&& self.ids.peer_credit_spec(true).window_spec() <= MAX_LOCAL_STREAMS
        &&& self.ids.peer_credit_spec(false).window_spec() <= MAX_LOCAL_STREAMS
        &&& self.tx_uni <= VARINT_MAX
        // What we sent, removed streams included, is what the peer's MAX_DATA was spent on.
        &&& self.conn_send.used_spec() == self.tx_gone@ + sum(self.entries@, 8)
        // Connection flow control (§4.1, §4.5, §19.9).
        &&& self.conn_counted <= self.conn_recv.limit()
        &&& self.conn_counted == self.gone@ + sum(self.entries@, 0)
        &&& self.conn_recv.consumed() == self.gone@ + sum(self.entries@, 1)
        // Live peer streams + closed ones = opened ones, per direction.
        &&& sum(self.entries@, 4) + self.ids.peer_credit_spec(true).consumed_spec()
            == self.ids.peer_opened_spec(true)
        &&& sum(self.entries@, 6) + self.ids.peer_credit_spec(false).consumed_spec()
            == self.ids.peer_opened_spec(false)
        &&& entries_ok(
            self.entries@,
            self.ids,
            self.rx_bidi,
            self.rx_uni,
            self.rtr@,
            self.removed@,
            self.resets@,
        )
        &&& records_ok(
            self.entries@,
            self.ids,
            self.rx_bidi,
            self.rx_uni,
            self.rtr@,
            self.removed@,
            self.resets@,
        )
    }

    /// The invariant's consequences, in terms of the accessors.
    pub proof fn lemma_wf(&self)
        requires
            self.wf(),
        ensures
            self.ids_spec().wf(),
            self.conn_recv_spec().wf(),
            self.conn_send_spec().wf(),
            // Connection flow control: a violation is detectable (§4.1, §19.9).
            self.conn_recv_spec().consumed_spec() <= self.conn_counted_spec()
                <= self.conn_recv_spec().limit_spec() <= VARINT_MAX,
            // Memory: no receive buffer goes beyond the advertised connection window, and the
            // physical buffers are at most twice that.
            0 <= self.rx_buffered() <= self.rx_buffered_phys() <= 2 * self.rx_buffered(),
            self.rx_buffered() <= self.conn_counted_spec() - self.conn_recv_spec().consumed_spec(),
            self.rx_buffered_phys() <= 2 * self.conn_recv_spec().limit_spec(),
            // Live peer streams: at most our initial limit (binding obligation 1).
            forall|b: bool|
                0 <= #[trigger] self.live_peer_streams(b) <= self.init_max_streams(b)
                    <= MAX_LOCAL_STREAMS,
            // E5: a removed stream's receiving part is terminal, so its terminal event went out.
            forall|id: u64| #[trigger]
                self.is_removed(id) ==> terminal(self.rx_spec(id).state) && self.rx_spec(
                    id,
                ).err is None,
            // E4: streams 1 and 3 mod 4 never take receive inputs, so never emit Data/Reset.
            forall|id: u64|
                (id % 4 == 1 || id % 4 == 3) ==> #[trigger] self.rx_trace(id) == Seq::<
                    SpecRecvIn,
                >::empty(),
            // Sending: every byte sent, removed streams included, is within the peer's MAX_DATA
            // (§4.1, §19.9), and each stream's within its MAX_STREAM_DATA (§19.10).
            self.conn_send_spec().used_spec() == self.tx_sent() <= self.conn_send_spec().max_spec(),
            forall|id: u64| #[trigger]
                self.tx_part(id) is Some ==> self.tx_part(id)->0.wf() && self.tx_part(
                    id,
                )->0.sent_end() <= self.tx_part(id)->0.max(),
            // Memory: the send buffers hold at most twice the bytes not yet acknowledged.
            0 <= self.tx_buffered() <= 2 * self.tx_unacked(),
    {
        self.ids.lemma_wf();
        self.conn_recv.lemma_wf();
        let s = self.entries@;
        assert forall|k: int| 0 <= k < s.len() implies terms_ok(#[trigger] s[k]) by {
            lemma_terms(s[k], self.rx_bidi, self.rx_uni);
        }
        lemma_sum_bounds(s);
        lemma_sum_kind_nonneg(s, 4);
        lemma_sum_kind_nonneg(s, 6);
        assert forall|b: bool|
            0 <= #[trigger] self.live_peer_streams(b) <= self.init_max_streams(b)
                <= MAX_LOCAL_STREAMS by {
            assert(self.ids.peer_side_ok(b));
        }
        assert forall|id: u64| #[trigger] self.is_removed(id) implies terminal(
            self.rx_spec(id).state,
        ) && self.rx_spec(id).err is None by {
            assert(self.removed@.contains(id));
        }
        assert forall|id: u64| (id % 4 == 1 || id % 4 == 3) implies #[trigger] self.rx_trace(id)
            == Seq::<SpecRecvIn>::empty() by {
            assert(!self.rtr@.contains_key(id));
        }
        self.conn_send.lemma_wf();
        assert forall|id: u64| #[trigger] self.tx_part(id) is Some implies self.tx_part(
            id,
        )->0.wf() && self.tx_part(id)->0.sent_end() <= self.tx_part(id)->0.max() by {
            if has_id(s, id) {
                let k = choose|k: int| 0 <= k < s.len() && (#[trigger] s[k]).id == id;
                assert(entry_ok(s[k], self.rx_bidi, self.rx_uni));
                if let Some(p) = s[k].send {
                    p.lemma_wf();
                }
            }
        }
        assert forall|k: int| 0 <= k < s.len() implies tx_terms_ok(#[trigger] s[k]) by {
            assert(entry_ok(s[k], self.rx_bidi, self.rx_uni));
            if let Some(p) = s[k].send {
                p.lemma_wf();
            }
        }
        lemma_sum_tx(s);
    }

    //= https://www.rfc-editor.org/rfc/rfc9114#section-6.2
    //# Therefore, the transport parameters sent by both clients
    //# and servers MUST allow the peer to create at least three
    //# unidirectional streams.
    /// `local` is our transport parameters, `peer` the client's. `initial_max_streams_uni >= 3`
    /// is `h3::limits::MIN_PEER_UNI_STREAMS`, written as a literal so `quic` needn't depend on
    /// `h3`.
    pub fn new(local: &TransportParams, peer: &TransportParams) -> (r: Streams)
        requires
            local.initial_max_streams_uni >= 3,
            local.initial_max_streams_bidi <= MAX_LOCAL_STREAMS,
            local.initial_max_streams_uni <= MAX_LOCAL_STREAMS,
            stream_tp_ok(local@),
            stream_tp_ok(peer@),
        ensures
            r.wf(),
            !r.failed(),
            r.init_max_streams(true) == local.initial_max_streams_bidi,
            r.init_max_streams(false) == local.initial_max_streams_uni,
            r.conn_recv_spec().limit_spec() == local.initial_max_data,
            r.conn_send_spec().max_spec() == peer.initial_max_data,
            r.rx_window(0) == local.initial_max_stream_data_bidi_remote,
            r.rx_window(2) == local.initial_max_stream_data_uni,
            forall|id: u64| #[trigger] r.rx_trace(id) == Seq::<SpecRecvIn>::empty(),
            forall|id: u64| !#[trigger] r.is_removed(id),
            forall|id: u64| !#[trigger] r.send_reset(id),
    {
        let r = Streams {
            ids: StreamIds::new(
                local.initial_max_streams_bidi,
                local.initial_max_streams_uni,
                peer.initial_max_streams_uni,
            ),
            entries: Vec::new(),
            conn_recv: RecvCredit::new(local.initial_max_data, VARINT_MAX),
            conn_counted: 0,
            conn_send: SendCredit::new(peer.initial_max_data),
            rx_bidi: local.initial_max_stream_data_bidi_remote,
            rx_uni: local.initial_max_stream_data_uni,
            tx_bidi: peer.initial_max_stream_data_bidi_local,
            tx_uni: peer.initial_max_stream_data_uni,
            failed: false,
            rtr: Ghost(Map::empty()),
            removed: Ghost(Set::empty()),
            resets: Ghost(Map::empty()),
            gone: Ghost(0),
            tx_gone: Ghost(0),
        };
        proof {
            r.ids.lemma_wf();
            assert(r.ids.peer_credit_spec(true).window_spec() == r.ids.peer_limit(true));
            assert(r.ids.peer_credit_spec(false).window_spec() == r.ids.peer_limit(false));
            assert forall|id: u64| #[trigger] r.rtr@.contains_key(id) == r.ids.peer_created(id) by {
                assert(r.ids.peer_opened_spec(true) == 0 && r.ids.peer_opened_spec(false) == 0);
            }
            assert forall|id: u64| #[trigger] r.resets@.contains_key(id) implies created(r.ids, id)
                by {}
        }
        r
    }

    #[verifier::when_used_as_spec(failed_spec)]
    pub fn failed(&self) -> (r: bool)
        ensures
            r == self.failed_spec(),
    {
        self.failed
    }

    /// The peer's MAX_DATA.
    pub fn peer_max_data(&self) -> (r: u64)
        ensures
            r == self.conn_send_spec().max_spec(),
    {
        self.conn_send.max()
    }

    /// The peer's limit on our unidirectional streams.
    pub fn local_uni_limit(&self) -> (r: u64)
        ensures
            r == self.ids_spec().local_uni_limit_spec(),
    {
        self.ids.local_uni_limit()
    }

    /// Streams with an entry: not yet terminal in both parts.
    pub fn open_streams(&self) -> (r: usize)
        ensures
            r == self.live_streams(),
    {
        self.entries.len()
    }

    /// Everything but the entries and the stream IDs is as in `o`, and so is every receive
    /// trace.
    spec fn same_rest(&self, o: Streams) -> bool {
        &&& self.conn_recv == o.conn_recv
        &&& self.conn_counted == o.conn_counted
        &&& self.conn_send == o.conn_send
        &&& self.rx_bidi == o.rx_bidi
        &&& self.rx_uni == o.rx_uni
        &&& self.tx_bidi == o.tx_bidi
        &&& self.tx_uni == o.tx_uni
        &&& self.failed == o.failed
        &&& self.removed == o.removed
        &&& self.resets == o.resets
        &&& self.gone == o.gone
        &&& self.tx_gone == o.tx_gone
        &&& forall|j: u64| #[trigger] self.rx_trace(j) == o.rx_trace(j)
    }

    /// The exec form of `rfc_stream_frame_check`.
    fn check(&self, f: &Frame, id: u64) -> (r: Option<u64>)
        requires
            self.wf(),
            frame_stream_id(f@) == Some(id),
        ensures
            r == rfc_stream_frame_check(self.ids, f@),
    {
        let senders = match f {
            Frame::Stream { .. }
            | Frame::ResetStream { .. }
            | Frame::StreamDataBlocked { .. } => true,
            _ => false,
        };
        match stream_kind(id) {
            StreamKind::ServerBidi => Some(STREAM_STATE_ERROR),
            StreamKind::ServerUni => if senders || !self.ids.local_uni_created(id) {
                Some(STREAM_STATE_ERROR)
            } else {
                None
            },
            StreamKind::ClientUni => if !senders {
                Some(STREAM_STATE_ERROR)
            } else if id / 4 >= self.ids.peer_limit(false) {
                Some(STREAM_LIMIT_ERROR)
            } else {
                None
            },
            StreamKind::ClientBidi => if id / 4 >= self.ids.peer_limit(true) {
                Some(STREAM_LIMIT_ERROR)
            } else {
                None
            },
        }
    }

    /// The entry of stream `id`, by linear scan.
    fn find(&self, id: u64) -> (r: Option<usize>)
        ensures
            match r {
                Some(i) => i < self.entries@.len() && self.entries@[i as int].id == id,
                None => !has_id(self.entries@, id),
            },
    {
        let mut i: usize = 0;
        while i < self.entries.len()
            invariant
                i <= self.entries@.len(),
                forall|k: int| 0 <= k < i ==> (#[trigger] self.entries@[k]).id != id,
            decreases self.entries@.len() - i,
        {
            if self.entries[i].id == id {
                return Some(i);
            }
            i += 1;
        }
        None
    }

    /// Opens peer stream `x`, the next of its type.
    fn open_one(&mut self, x: u64)
        requires
            old(self).wf(),
            x <= VARINT_MAX,
            x % 4 == 0 || x % 4 == 2,
            x / 4 == old(self).ids.peer_opened_spec(x % 4 == 0),
            peer_id_allowed(x, old(self).ids.peer_limit(x % 4 == 0)),
        ensures
            final(self).wf(),
            final(self).same_rest(*old(self)),
            final(self).ids.peer_opened_spec(x % 4 == 0) == x / 4 + 1,
            final(self).ids.peer_opened_spec(x % 4 != 0) == old(self).ids.peer_opened_spec(
                x % 4 != 0,
            ),
            forall|b: bool| #[trigger]
                final(self).ids.peer_credit_spec(b) == old(self).ids.peer_credit_spec(b),
            final(self).ids.local_uni_spec() == old(self).ids.local_uni_spec(),
            parts_kept(*old(self), *final(self)),
    {
        let ghost s0 = *self;
        let bidi = x % 4 == 0;
        let _ = self.ids.on_peer_stream(x);
        let recv = RecvStream::new(x, if bidi { self.rx_bidi } else { self.rx_uni });
        let send = if bidi {
            Some(SendStream::new(self.tx_bidi))
        } else {
            None
        };
        let e = Entry { id: x, recv: Some(recv), send };
        self.entries.push(e);
        self.rtr = Ghost(self.rtr@.insert(x, Seq::empty()));
        proof {
            lemma_open_one(s0, *self, x, e);
            lemma_part_push(s0, *self, e);
        }
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-3.2
    //# Before a stream is created, all streams of the same type with lower-
    //# numbered stream IDs MUST be created.
    /// Opens peer stream `id` and every lower one of its type not yet open, one at a time.
    fn open_to(&mut self, id: u64)
        requires
            old(self).wf(),
            id <= VARINT_MAX,
            id % 4 == 0 || id % 4 == 2,
            peer_id_allowed(id, old(self).ids.peer_limit(id % 4 == 0)),
        ensures
            final(self).wf(),
            final(self).same_rest(*old(self)),
            final(self).ids.peer_created(id),
            forall|b: bool| #[trigger]
                final(self).ids.peer_credit_spec(b) == old(self).ids.peer_credit_spec(b),
            final(self).ids.local_uni_spec() == old(self).ids.local_uni_spec(),
            parts_kept(*old(self), *final(self)),
    {
        let ghost s0 = *self;
        let bidi = id % 4 == 0;
        proof {
            self.ids.lemma_wf();
            assert(MAX_STREAMS_LIMIT == 0x1000_0000_0000_0000) by (compute_only);
        }
        let mut x = 4 * self.ids.peer_opened(bidi) + id % 4;
        while x <= id
            invariant
                self.wf(),
                self.same_rest(s0),
                s0.wf(),
                id <= VARINT_MAX,
                id % 4 == 0 || id % 4 == 2,
                bidi == (id % 4 == 0),
                x == 4 * self.ids.peer_opened_spec(bidi) + id % 4,
                forall|b: bool| #[trigger]
                    self.ids.peer_credit_spec(b) == s0.ids.peer_credit_spec(b),
                self.ids.local_uni_spec() == s0.ids.local_uni_spec(),
                peer_id_allowed(id, s0.ids.peer_limit(bidi)),
                parts_kept(s0, *self),
            decreases id + 4 - x,
        {
            proof {
                self.ids.lemma_wf();
                s0.ids.lemma_wf();
            }
            let ghost s1 = *self;
            self.open_one(x);
            proof {
                self.ids.lemma_wf();
                assert(MAX_STREAMS_LIMIT == 0x1000_0000_0000_0000) by (compute_only);
                assert forall|j: u64| #[trigger] self.rx_trace(j) == s0.rx_trace(j) by {
                    assert(self.rx_trace(j) == s1.rx_trace(j));
                }
                assert forall|j: u64| #[trigger] s0.tx_part(j) is Some implies self.tx_part(j)
                    == s0.tx_part(j) by {
                    assert(s1.tx_part(j) == s0.tx_part(j));
                }
            }
            x = x + 4;
        }
        proof {
            self.ids.lemma_wf();
        }
    }

    /// STREAM or RESET_STREAM `f` to entry `i`'s receiving part, then the connection credit.
    fn apply_recv(&mut self, i: usize, f: &Frame, ev: &mut Vec<StreamEvent>) -> (r: Result<
        (),
        u64,
    >)
        requires
            old(self).wf(),
            i < old(self).entries@.len(),
            frame_wf(f@),
            frame_recv_in(f@) is Some,
            frame_stream_id(f@) == Some(old(self).entries@[i as int].id),
            old(self).entries@[i as int].id % 4 == 0 || old(self).entries@[i as int].id % 4 == 2,
        ensures
            final(self).wf(),
            final(self).entries@.len() == old(self).entries@.len(),
            final(self).entries@[i as int].id == old(self).entries@[i as int].id,
            final(self).ids == old(self).ids,
            final(self).removed == old(self).removed,
            final(self).resets == old(self).resets,
            final(self).failed == old(self).failed,
            r == rx_outcome(*old(self), f@),
            r is Err ==> final(ev)@ == old(ev)@,
            r is Ok ==> event_views(final(ev)@) == event_views(old(ev)@) + frame_events(
                *old(self),
                *final(self),
                f@,
            ),
            forall|j: u64| #[trigger]
                final(self).rx_trace(j) == rx_trace_after(*old(self), f@, r, j),
    {
        let ghost s0 = *self;
        let ghost id = self.entries@[i as int].id;
        let ghost a = self.entries@;
        let mut e = Entry { id: 0, recv: None, send: None };
        self.entries.set_and_swap(i, &mut e);
        let ghost e0 = e;
        proof {
            assert(e0 == a[i as int]);
            assert(entry_ok(e0, s0.rx_bidi, s0.rx_uni));
            assert(!s0.removed@.contains(id));
            self.conn_recv.lemma_wf();
        }
        let mut rs = match e.recv.take() {
            Some(rs) => rs,
            None => RecvStream::new(0, 0),  // unreachable: a client stream has a receiving part
        };
        let ghost rs0 = rs;
        //= https://www.rfc-editor.org/rfc/rfc9000#section-4.5
        //# The receiver MUST use the final size of the stream to
        //# account for all bytes sent on the stream in its connection-level flow
        //# controller.
        // The stream reports only the growth of its final size, else high-water mark (`counted`),
        // so duplicate bytes count once; the connection credit we return is what it retired.
        let room = self.conn_recv.limit() - self.conn_counted;
        let t0 = rs.retired_exec();
        let res = feed_recv(&mut rs, f, room, ev);
        let t1 = rs.retired_exec();
        let ghost tr = rs.trace();
        e.recv = Some(rs);
        let ghost ne = e;
        self.entries.set_and_swap(i, &mut e);
        proof {
            assert(rs0 == e0.recv->0);
            assert(self.entries@ == a.update(i as int, ne));
            lemma_counted_monotone(id, s0.rx_window(id), rs0.trace(), frame_recv_in(f@)->0);
        }
        match res {
            Ok(n) => {
                proof {
                    lemma_recv_ok(s0, i as int, ne, n);
                }
                self.conn_counted = self.conn_counted + n;
                self.conn_recv.on_consumed(t1 - t0);
                self.rtr = Ghost(self.rtr@.insert(id, tr));
                proof {
                    assert(forall|j: u64| #[trigger]
                        self.rx_trace(j) == rx_trace_after(s0, f@, Ok(()), j));
                }
                Ok(())
            },
            Err(c) => {
                proof {
                    assert(ne == e0);
                    assert(self.entries@ =~= a);
                }
                Err(c)
            },
        }
    }

    /// STOP_SENDING or MAX_STREAM_DATA `f` to entry `i`'s sending part.
    fn apply_send(&mut self, i: usize, f: &Frame, ev: &mut Vec<StreamEvent>)
        requires
            old(self).wf(),
            i < old(self).entries@.len(),
            frame_wf(f@),
            f@ is StopSending || f@ is MaxStreamData,
            frame_stream_id(f@) == Some(old(self).entries@[i as int].id),
            old(self).entries@[i as int].id % 4 == 0 || old(self).entries@[i as int].id % 4 == 3,
        ensures
            final(self).wf(),
            final(self).entries@.len() == old(self).entries@.len(),
            final(self).entries@[i as int].id == old(self).entries@[i as int].id,
            final(self).ids == old(self).ids,
            final(self).removed == old(self).removed,
            final(self).failed == old(self).failed,
            final(self).same_traces(*old(self)),
            event_views(final(ev)@) == event_views(old(ev)@) + frame_events(
                *old(self),
                *final(self),
                f@,
            ),
            forall|j: u64| #[trigger] old(self).send_reset(j) ==> final(self).send_reset(j),
            forall|j: u64| #[trigger]
                final(self).send_reset(j) && !old(self).send_reset(j) ==> f@ is StopSending
                    && frame_stream_id(f@) == Some(j),
            forall|j: u64| #[trigger]
                old(self).reset_code(j) is Some ==> final(self).reset_code(j) == old(
                    self,
                ).reset_code(j),
            ({
                let e = old(self).entries@[i as int];
                match f@ {
                    SpecFrame::StopSending { stream_id, error_code } => (e.send is Some && (
                    e.send->0.state() is Ready || e.send->0.state() is Send
                        || e.send->0.state() is DataSent)) ==> final(self).reset_code(stream_id)
                        == Some(error_code),
                    _ => true,
                }
            }),
    {
        let ghost s0 = *self;
        let ghost id = self.entries@[i as int].id;
        let ghost a = self.entries@;
        let ghost ev0 = ev@;
        let mut e = Entry { id: 0, recv: None, send: None };
        self.entries.set_and_swap(i, &mut e);
        let ghost e0 = e;
        proof {
            assert(e0 == a[i as int]);
            assert(entry_ok(e0, s0.rx_bidi, s0.rx_uni));
        }
        if let Some(mut p) = e.send.take() {
            proof {
                p.lemma_wf();
            }
            match f {
                Frame::StopSending { stream_id, error_code } => {
                    //= https://www.rfc-editor.org/rfc/rfc9000#section-3.5
                    //# An endpoint that receives a STOP_SENDING frame
                    //# MUST send a RESET_STREAM frame if the stream is in the "Ready" or
                    //# "Send" state.
                    // We reset in Data Sent too; `poll_frames` sends the RESET_STREAM.
                    if p.on_stop_sending(*error_code) {
                        ev.push(StreamEvent::StopSending { id: *stream_id, code: *error_code });
                        self.resets = Ghost(self.resets@.insert(*stream_id, *error_code));
                    }
                },
                Frame::MaxStreamData { max, .. } => p.on_max_stream_data(*max),
                _ => {},
            }
            e.send = Some(p);
        }
        let ghost ne = e;
        self.entries.set_and_swap(i, &mut e);
        proof {
            assert(self.entries@ == a.update(i as int, ne));
            assert(ne.recv == e0.recv);
            if let Some(r) = ne.recv {
                assert(s0.rtr@.insert(id, r.trace()) =~= s0.rtr@);
            }
            lemma_update(s0, i as int, ne, s0.rtr@, self.resets@);
            lemma_sum_update(a, i as int, ne, 0);
            lemma_sum_update(a, i as int, ne, 1);
            lemma_sum_update(a, i as int, ne, 4);
            lemma_sum_update(a, i as int, ne, 6);
            lemma_sum_update(a, i as int, ne, 8);
            let sp = s0.rx_spec(id);
            assert(sp.events.skip(sp.events.len() as int) =~= Seq::<SpecStreamEvent>::empty());
            if self.resets@ == s0.resets@ {
                assert(ev@ == ev0);
                assert(event_views(ev0) + Seq::<SpecStreamEvent>::empty() =~= event_views(ev0));
            } else {
                assert(event_views(ev@) =~= event_views(ev0).push(ev@.last()@));
            }
        }
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-4.4
    //# Both endpoints MUST maintain flow control state
    //# for the stream in the unterminated direction until that direction
    //# enters a terminal state.
    /// Removes entry `i` once all its parts are terminal; a removed peer stream is re-credited
    /// (MAX_STREAMS), and its buffers are dropped.
    fn gc(&mut self, i: usize)
        requires
            old(self).wf(),
            i < old(self).entries@.len(),
        ensures
            final(self).wf(),
            final(self).same_traces(*old(self)),
            final(self).resets == old(self).resets,
            final(self).failed == old(self).failed,
            final(self).conn_recv == old(self).conn_recv,
            final(self).conn_counted == old(self).conn_counted,
            ({
                let id = old(self).entries@[i as int].id;
                &&& forall|j: u64| #[trigger]
                    final(self).is_removed(j) == (old(self).is_removed(j) || (j == id
                        && final(self).is_removed(id)))
                &&& final(self).is_removed(id) ==> !old(self).is_removed(id) && (id % 4 == 0 || id
                    % 4 == 2)
                &&& forall|b: bool| #[trigger]
                    final(self).peer_closed(b) == old(self).peer_closed(b) || (
                    final(self).peer_closed(b) == old(self).peer_closed(b) + 1 && (id % 4 == 0)
                        == b && final(self).is_removed(id))
            }),
    {
        let ghost s0 = *self;
        let ghost a = self.entries@;
        proof {
            assert(entry_ok(a[i as int], self.rx_bidi, self.rx_uni));
        }
        let done = {
            let e = &self.entries[i];
            (match &e.recv {
                Some(r) => r.is_terminal(),
                None => true,
            }) && (match &e.send {
                Some(p) => p.is_terminal(),
                None => true,
            })
        };
        if done {
            let e = self.entries.remove(i);
            proof {
                assert(e == a[i as int]);
                self.ids.lemma_wf();
                lemma_sum_remove(a, i as int, 0);
                lemma_sum_remove(a, i as int, 1);
                lemma_sum_remove(a, i as int, 4);
                lemma_sum_remove(a, i as int, 6);
                lemma_sum_remove(a, i as int, 8);
                lemma_sum_kind_nonneg(a.remove(i as int), 4);
                lemma_sum_kind_nonneg(a.remove(i as int), 6);
                if let Some(r) = e.recv {
                    r.lemma_wf();
                }
            }
            self.tx_gone = Ghost((self.tx_gone@ + val(e, 8)) as nat);
            if e.id % 4 != 3 {
                self.ids.on_peer_closed(e.id % 4 == 0);
                self.removed = Ghost(self.removed@.insert(e.id));
                self.gone = Ghost((self.gone@ + val(e, 0)) as nat);
            }
            proof {
                lemma_gc(s0, *self, i as int, e);
            }
        }
    }

    /// One of the five stream frames, naming stream `id`. Sets the latch on every `Err`.
    fn stream_frame(&mut self, f: &Frame, id: u64, ev: &mut Vec<StreamEvent>) -> (r: Result<
        (),
        u64,
    >)
        requires
            old(self).wf(),
            frame_wf(f@),
            frame_stream_id(f@) == Some(id),
        ensures
            final(self).wf(),
            r is Err ==> final(self).failed_spec(),
            r is Ok ==> final(self).failed_spec() == old(self).failed_spec(),
            rfc_stream_frame_check(old(self).ids_spec(), f@) is Some ==> *final(self) == old(
                self,
            ).latched(),
            frame_post(
                *old(self),
                *final(self),
                f@,
                event_views(old(ev)@),
                event_views(final(ev)@),
                r,
            ),
    {
        let ghost s0 = *self;
        if let Some(c) = self.check(f, id) {
            self.failed = true;
            proof {
                assert(equiv(s0, *self));
                lemma_post_refl(s0, f@, event_views(ev@), Err(c));
                lemma_post_after(s0, s0, *self, f@, event_views(ev@), event_views(ev@), Err(c));
            }
            return Err(c);
        }
        proof {
            self.ids.lemma_wf();
        }
        if id % 4 != 3 {
            self.open_to(id);
        }
        let ghost s1 = *self;
        proof {
            self.ids.lemma_wf();
            assert(equiv(s0, s1));
            assert(parts_kept(s0, s1));
        }
        let r = self.deliver(f, id, ev);
        let ghost s2 = *self;
        if r.is_err() {
            self.failed = true;
        }
        proof {
            lemma_post_before(s0, s1, s2, f@, event_views(old(ev)@), event_views(ev@), r);
            assert(equiv(s2, *self));
            lemma_post_after(s0, s2, *self, f@, event_views(old(ev)@), event_views(ev@), r);
        }
        r
    }

    /// A stream frame that passed the table, its stream opened: to the stream's entry, if it
    /// still has one.
    fn deliver(&mut self, f: &Frame, id: u64, ev: &mut Vec<StreamEvent>) -> (r: Result<(), u64>)
        requires
            old(self).wf(),
            frame_wf(f@),
            frame_stream_id(f@) == Some(id),
            rfc_stream_frame_check(old(self).ids_spec(), f@) is None,
            id % 4 == 0 || id % 4 == 2 ==> old(self).ids.peer_created(id),
        ensures
            final(self).wf(),
            final(self).failed == old(self).failed,
            r == rx_outcome(*old(self), f@),
            post_rest(
                *old(self),
                *final(self),
                f@,
                event_views(old(ev)@),
                event_views(final(ev)@),
                r,
            ),
    {
        let ghost s0 = *self;
        let ghost ev0 = ev@;
        proof {
            self.ids.lemma_wf();
            let sp = s0.rx_spec(id);
            assert(sp.events.skip(sp.events.len() as int) =~= Seq::<SpecStreamEvent>::empty());
            assert(event_views(ev0) + Seq::<SpecStreamEvent>::empty() =~= event_views(ev0));
        }
        match self.find(id) {
            None => {
                proof {
                    assert(frame_recv_in(f@) is Some ==> s0.rtr@.contains_key(id));
                }
                Ok(())
            },
            Some(i) => self.deliver_at(i, f, ev),
        }
    }

    /// `deliver` to entry `i`, then `gc`.
    fn deliver_at(&mut self, i: usize, f: &Frame, ev: &mut Vec<StreamEvent>) -> (r: Result<(), u64>)
        requires
            old(self).wf(),
            frame_wf(f@),
            i < old(self).entries@.len(),
            frame_stream_id(f@) == Some(old(self).entries@[i as int].id),
            rfc_stream_frame_check(old(self).ids_spec(), f@) is None,
        ensures
            final(self).wf(),
            final(self).failed == old(self).failed,
            r == rx_outcome(*old(self), f@),
            post_rest(
                *old(self),
                *final(self),
                f@,
                event_views(old(ev)@),
                event_views(final(ev)@),
                r,
            ),
    {
        let ghost s0 = *self;
        let ghost ev0 = ev@;
        let ghost id = self.entries@[i as int].id;
        proof {
            assert(entry_ok(self.entries@[i as int], self.rx_bidi, self.rx_uni));
            let sp = s0.rx_spec(id);
            assert(sp.events.skip(sp.events.len() as int) =~= Seq::<SpecStreamEvent>::empty());
            assert(event_views(ev0) + Seq::<SpecStreamEvent>::empty() =~= event_views(ev0));
        }
        let r = match f {
            Frame::Stream { .. } | Frame::ResetStream { .. } => self.apply_recv(i, f, ev),
            Frame::StopSending { .. } | Frame::MaxStreamData { .. } => {
                self.apply_send(i, f, ev);
                Ok(())
            },
            _ => Ok(()),
        };
        let ghost s1 = *self;
        proof {
            lemma_part_at(s0, i as int);
            assert forall|j: u64| #[trigger] s1.is_removed(j) == s0.is_removed(j) by {}
            assert forall|b: bool| #[trigger] s1.peer_closed(b) == s0.peer_closed(b) by {}
            assert(post_rest(s0, s1, f@, event_views(ev0), event_views(ev@), r));
        }
        if r.is_ok() {
            self.gc(i);
            proof {
                lemma_post_gc(s0, s1, *self, f@, id, event_views(ev0), event_views(ev@), r);
            }
        }
        r
    }

    /// One frame of types 0x04, 0x05 or 0x08–0x17 from a 1-RTT packet. Its new events go to
    /// `ev`. Any `Err` is a connection error, and sets the latch.
    pub fn on_frame(&mut self, f: &Frame, ev: &mut Vec<StreamEvent>) -> (r: Result<(), u64>)
        requires
            old(self).wf(),
            !old(self).failed(),
            frame_wf(f@),
            is_stream_layer_frame(f@),
        ensures
            final(self).wf(),
            r is Err <==> final(self).failed(),
            rfc_stream_frame_check(old(self).ids_spec(), f@) is Some ==> *final(self) == old(
                self,
            ).latched(),
            frame_post(
                *old(self),
                *final(self),
                f@,
                event_views(old(ev)@),
                event_views(final(ev)@),
                r,
            ),
    {
        match frame_id(f) {
            Some(id) => self.stream_frame(f, id, ev),
            None => {
                let ghost s0 = *self;
                match f {
                    Frame::MaxData(v) => self.conn_send.on_max(*v),
                    Frame::MaxStreams { bidi, max } => {
                        self.ids.on_max_streams(*bidi, *max);
                        proof {
                            lemma_ids_frame(s0, *self);
                        }
                    },
                    // DATA_BLOCKED, STREAMS_BLOCKED: nothing to do (§4.2, §4.6).
                    _ => {},
                }
                proof {
                    assert(forall|j: u64| #[trigger] self.rx_trace(j) == s0.rx_trace(j));
                    assert(forall|b: bool| #[trigger] self.peer_closed(b) == s0.peer_closed(b));
                    assert(event_views(ev@) + Seq::<SpecStreamEvent>::empty() =~= event_views(ev@));
                }
                Ok(())
            },
        }
    }

    /// Every receive trace is as in `o`.
    spec fn same_traces(&self, o: Streams) -> bool {
        &&& self.rx_bidi == o.rx_bidi
        &&& self.rx_uni == o.rx_uni
        &&& forall|j: u64| #[trigger] self.rx_trace(j) == o.rx_trace(j)
    }
}

/// The stream a frame names, exec.
fn frame_id(f: &Frame) -> (r: Option<u64>)
    ensures
        r == frame_stream_id(f@),
{
    match f {
        Frame::Stream { stream_id, .. } => Some(*stream_id),
        Frame::ResetStream { stream_id, .. } => Some(*stream_id),
        Frame::StopSending { stream_id, .. } => Some(*stream_id),
        Frame::MaxStreamData { stream_id, .. } => Some(*stream_id),
        Frame::StreamDataBlocked { stream_id, .. } => Some(*stream_id),
        _ => None,
    }
}

/// What feeding input `i` to receiving part `r0` (now `r1`) did, with `room` bytes of
/// connection credit left: `on_data`'s and `on_reset`'s shared contract.
spec fn fed(
    r0: RecvStream,
    r1: RecvStream,
    i: SpecRecvIn,
    room: u64,
    ev0: Seq<StreamEvent>,
    ev1: Seq<StreamEvent>,
    r: Result<u64, u64>,
) -> bool {
    let t2 = r0.trace().push(i);
    let s1 = r0.rfc();
    let s2 = rfc_recv(r0.id_spec(), r0.window_spec(), t2);
    &&& r1.wf()
    &&& r1.id_spec() == r0.id_spec()
    &&& r1.window_spec() == r0.window_spec()
    &&& s2.err matches Some(c) ==> r == Err::<u64, u64>(c) && r1 == r0 && ev1 == ev0
    &&& (s2.err is None && counted(s2) - counted(s1) > room) ==> r == Err::<u64, u64>(
        FLOW_CONTROL_ERROR,
    ) && r1 == r0 && ev1 == ev0
    &&& (s2.err is None && counted(s2) - counted(s1) <= room) ==> {
        &&& r == Ok::<u64, u64>((counted(s2) - counted(s1)) as u64)
        &&& r1.trace() == t2
        &&& event_views(ev1) == event_views(ev0) + s2.events.skip(s1.events.len() as int)
    }
}

/// STREAM or RESET_STREAM `f` to `rs`.
fn feed_recv(rs: &mut RecvStream, f: &Frame, room: u64, ev: &mut Vec<StreamEvent>) -> (r: Result<
    u64,
    u64,
>)
    requires
        old(rs).wf(),
        frame_wf(f@),
        frame_recv_in(f@) is Some,
    ensures
        fed(*old(rs), *final(rs), frame_recv_in(f@)->0, room, old(ev)@, final(ev)@, r),
{
    match f {
        Frame::Stream { offset, data, fin, .. } => rs.on_data(
            *offset,
            data.as_slice(),
            *fin,
            room,
            ev,
        ),
        Frame::ResetStream { error_code, final_size, .. } => rs.on_reset(
            *error_code,
            *final_size,
            room,
            ev,
        ),
        _ => Ok(0),
    }
}

/// `apply_recv`'s bookkeeping after its stream took `n` more bytes of connection credit.
proof fn lemma_recv_ok(s0: Streams, i: int, ne: Entry, n: u64)
    requires
        s0.wf(),
        0 <= i < s0.entries@.len(),
        ne.id == s0.entries@[i].id,
        ne.send == s0.entries@[i].send,
        ne.recv is Some,
        s0.entries@[i].recv is Some,
        ne.recv->0.wf(),
        ne.recv->0.id_spec() == s0.entries@[i].recv->0.id_spec(),
        ne.recv->0.window_spec() == s0.entries@[i].recv->0.window_spec(),
        counted(ne.recv->0.rfc()) - counted(s0.entries@[i].recv->0.rfc()) == n,
        n <= s0.conn_room(),
    ensures
        ({
            let t = s0.entries@.update(i, ne);
            let r = ne.recv->0;
            let rtr = s0.rtr@.insert(ne.id, r.trace());
            &&& entries_ok(t, s0.ids, s0.rx_bidi, s0.rx_uni, rtr, s0.removed@, s0.resets@)
            &&& records_ok(t, s0.ids, s0.rx_bidi, s0.rx_uni, rtr, s0.removed@, s0.resets@)
            &&& s0.conn_counted + n == s0.gone@ + sum(t, 0)
            &&& sum(t, 1) == sum(s0.entries@, 1) - val(s0.entries@[i], 1) + val(ne, 1)
            &&& sum(t, 1) <= sum(t, 0)
            &&& sum(t, 4) == sum(s0.entries@, 4)
            &&& sum(t, 6) == sum(s0.entries@, 6)
            &&& sum(t, 8) == sum(s0.entries@, 8)
        }),
{
    let a = s0.entries@;
    let t = a.update(i, ne);
    assert(entry_ok(a[i], s0.rx_bidi, s0.rx_uni));
    assert(!s0.removed@.contains(ne.id));
    lemma_sum_update(a, i, ne, 0);
    lemma_sum_update(a, i, ne, 1);
    lemma_sum_update(a, i, ne, 4);
    lemma_sum_update(a, i, ne, 6);
    lemma_sum_update(a, i, ne, 8);
    lemma_update(s0, i, ne, s0.rtr@.insert(ne.id, ne.recv->0.trace()), s0.resets@);
    assert forall|k: int| 0 <= k < t.len() implies terms_ok(#[trigger] t[k]) by {
        lemma_terms(t[k], s0.rx_bidi, s0.rx_uni);
    }
    lemma_sum_bounds(t);
}

/// `a` and `b` agree on everything `frame_post` reads.
spec fn equiv(a: Streams, b: Streams) -> bool {
    &&& a.rx_bidi == b.rx_bidi
    &&& a.rx_uni == b.rx_uni
    &&& forall|j: u64| #[trigger] a.rx_trace(j) == b.rx_trace(j)
    &&& a.removed == b.removed
    &&& a.resets == b.resets
    &&& forall|bb: bool| #[trigger] a.peer_closed(bb) == b.peer_closed(bb)
    &&& a.conn_recv == b.conn_recv
    &&& a.conn_counted == b.conn_counted
}

proof fn lemma_post_refl(s: Streams, f: SpecFrame, ev: Seq<SpecStreamEvent>, r: Result<(), u64>)
    requires
        r is Err,
    ensures
        post_rest(s, s, f, ev, ev, r),
{
}

/// `post_rest` from a state equivalent to the starting one.
proof fn lemma_post_before(
    s0: Streams,
    s1: Streams,
    s2: Streams,
    f: SpecFrame,
    ev0: Seq<SpecStreamEvent>,
    ev1: Seq<SpecStreamEvent>,
    r: Result<(), u64>,
)
    requires
        equiv(s0, s1),
        parts_kept(s0, s1),
        post_rest(s1, s2, f, ev0, ev1, r),
    ensures
        post_rest(s0, s2, f, ev0, ev1, r),
        rx_outcome(s1, f) == rx_outcome(s0, f),
{
    if let SpecFrame::StopSending { stream_id, .. } = f {
        if s0.tx_part(stream_id) is Some {
            assert(s1.tx_part(stream_id) == s0.tx_part(stream_id));
        }
    }
    assert forall|j: u64| #[trigger] s0.reset_code(j) is Some implies s2.reset_code(j)
        == s0.reset_code(j) by {
        assert(s1.reset_code(j) == s0.reset_code(j));
    }
    assert(frame_events(s1, s2, f) == frame_events(s0, s2, f));
    assert forall|j: u64| #[trigger] s2.rx_trace(j) == rx_trace_after(s0, f, r, j) by {
        assert(s2.rx_trace(j) == rx_trace_after(s1, f, r, j));
    }
    assert forall|j: u64| #[trigger] s0.is_removed(j) implies s2.is_removed(j) by {
        assert(s1.is_removed(j));
    }
    assert forall|j: u64| #[trigger] s2.is_removed(j) && !s0.is_removed(j) implies frame_stream_id(
        f,
    ) == Some(j) by {
        assert(!s1.is_removed(j));
    }
    assert forall|j: u64| #[trigger] s0.send_reset(j) implies s2.send_reset(j) by {
        assert(s1.send_reset(j));
    }
    assert forall|j: u64| #[trigger] s2.send_reset(j) && !s0.send_reset(j) implies f
        is StopSending && frame_stream_id(f) == Some(j) by {
        assert(!s1.send_reset(j));
    }
    assert forall|bb: bool| #[trigger]
        s2.peer_closed(bb) == s0.peer_closed(bb) || (s2.peer_closed(bb) == s0.peer_closed(bb) + 1
            && (frame_stream_id(f) matches Some(id) && (id % 4 == 0) == bb && (id % 4 == 0 || id
            % 4 == 2) && s2.is_removed(id) && !s0.is_removed(id))) by {
        assert(s1.peer_closed(bb) == s0.peer_closed(bb));
        if let Some(id) = frame_stream_id(f) {
            assert(s1.is_removed(id) == s0.is_removed(id));
        }
    }
}

/// `post_rest` to a state equivalent to the final one.
proof fn lemma_post_after(
    s0: Streams,
    s1: Streams,
    s2: Streams,
    f: SpecFrame,
    ev0: Seq<SpecStreamEvent>,
    ev1: Seq<SpecStreamEvent>,
    r: Result<(), u64>,
)
    requires
        equiv(s1, s2),
        post_rest(s0, s1, f, ev0, ev1, r),
    ensures
        post_rest(s0, s2, f, ev0, ev1, r),
{
    assert(frame_events(s0, s1, f) == frame_events(s0, s2, f));
    assert forall|j: u64| #[trigger] s2.rx_trace(j) == rx_trace_after(s0, f, r, j) by {
        assert(s1.rx_trace(j) == rx_trace_after(s0, f, r, j));
    }
    assert forall|j: u64| #[trigger] s0.is_removed(j) implies s2.is_removed(j) by {
        assert(s1.is_removed(j));
    }
    assert forall|j: u64| #[trigger] s2.is_removed(j) && !s0.is_removed(j) implies frame_stream_id(
        f,
    ) == Some(j) by {
        assert(s1.is_removed(j));
    }
    assert forall|j: u64| #[trigger] s0.send_reset(j) implies s2.send_reset(j) by {
        assert(s1.send_reset(j));
    }
    assert forall|j: u64| #[trigger] s2.send_reset(j) && !s0.send_reset(j) implies f
        is StopSending && frame_stream_id(f) == Some(j) by {
        assert(s1.send_reset(j));
    }
    assert forall|bb: bool| #[trigger]
        s2.peer_closed(bb) == s0.peer_closed(bb) || (s2.peer_closed(bb) == s0.peer_closed(bb) + 1
            && (frame_stream_id(f) matches Some(id) && (id % 4 == 0) == bb && (id % 4 == 0 || id
            % 4 == 2) && s2.is_removed(id) && !s0.is_removed(id))) by {
        assert(s1.peer_closed(bb) == s2.peer_closed(bb));
        if let Some(id) = frame_stream_id(f) {
            assert(s1.is_removed(id) == s2.is_removed(id));
        }
    }
}

/// `post_rest` across `gc` of the frame's stream.
proof fn lemma_post_gc(
    s0: Streams,
    s1: Streams,
    s2: Streams,
    f: SpecFrame,
    id: u64,
    ev0: Seq<SpecStreamEvent>,
    ev1: Seq<SpecStreamEvent>,
    r: Result<(), u64>,
)
    requires
        post_rest(s0, s1, f, ev0, ev1, r),
        forall|j: u64| #[trigger] s1.is_removed(j) == s0.is_removed(j),
        forall|b: bool| #[trigger] s1.peer_closed(b) == s0.peer_closed(b),
        frame_stream_id(f) == Some(id),
        s2.same_traces(s1),
        s2.resets == s1.resets,
        forall|j: u64| #[trigger]
            s2.is_removed(j) == (s1.is_removed(j) || (j == id && s2.is_removed(id))),
        s2.is_removed(id) ==> !s1.is_removed(id) && (id % 4 == 0 || id % 4 == 2),
        forall|b: bool| #[trigger]
            s2.peer_closed(b) == s1.peer_closed(b) || (s2.peer_closed(b) == s1.peer_closed(b) + 1
                && (id % 4 == 0) == b && s2.is_removed(id)),
    ensures
        post_rest(s0, s2, f, ev0, ev1, r),
{
    assert(frame_events(s0, s1, f) == frame_events(s0, s2, f));
    assert forall|j: u64| #[trigger] s2.rx_trace(j) == rx_trace_after(s0, f, r, j) by {
        assert(s1.rx_trace(j) == rx_trace_after(s0, f, r, j));
    }
    assert forall|j: u64| #[trigger] s0.is_removed(j) implies s2.is_removed(j) by {
        assert(s1.is_removed(j));
    }
    assert forall|j: u64| #[trigger] s0.send_reset(j) implies s2.send_reset(j) by {
        assert(s1.send_reset(j));
    }
    assert forall|j: u64| #[trigger] s2.send_reset(j) && !s0.send_reset(j) implies f
        is StopSending && frame_stream_id(f) == Some(j) by {
        assert(s1.send_reset(j));
    }
    assert forall|bb: bool| #[trigger]
        s2.peer_closed(bb) == s0.peer_closed(bb) || (s2.peer_closed(bb) == s0.peer_closed(bb) + 1
            && (frame_stream_id(f) matches Some(id) && (id % 4 == 0) == bb && (id % 4 == 0 || id
            % 4 == 2) && s2.is_removed(id) && !s0.is_removed(id))) by {
        assert(s1.peer_closed(bb) == s0.peer_closed(bb));
        assert(s1.is_removed(id) == s0.is_removed(id));
    }
}

/// Only the stream IDs changed, keeping every count of streams opened and closed.
proof fn lemma_ids_frame(s0: Streams, s1: Streams)
    requires
        s0.wf(),
        s1.ids.wf(),
        forall|b: bool|
            {
                &&& #[trigger] s1.ids.peer_opened_spec(b) == s0.ids.peer_opened_spec(b)
                &&& s1.ids.peer_credit_spec(b).consumed_spec() == s0.ids.peer_credit_spec(
                    b,
                ).consumed_spec()
                &&& s1.ids.peer_credit_spec(b).window_spec() == s0.ids.peer_credit_spec(
                    b,
                ).window_spec()
            },
        s1.ids.local_uni_spec().used_spec() == s0.ids.local_uni_spec().used_spec(),
        s1 == (Streams { ids: s1.ids, ..s0 }),
    ensures
        s1.wf(),
{
    s0.ids.lemma_wf();
    s1.ids.lemma_wf();
    assert(s1.ids.peer_opened_spec(true) == s0.ids.peer_opened_spec(true));
    assert(s1.ids.peer_opened_spec(false) == s0.ids.peer_opened_spec(false));
    assert(s1.ids.peer_credit_spec(true).window_spec() == s0.ids.peer_credit_spec(
        true,
    ).window_spec());
    assert(s1.ids.peer_credit_spec(false).window_spec() == s0.ids.peer_credit_spec(
        false,
    ).window_spec());
    assert(s1.ids.peer_credit_spec(true).consumed_spec() == s0.ids.peer_credit_spec(
        true,
    ).consumed_spec());
    assert(s1.ids.peer_credit_spec(false).consumed_spec() == s0.ids.peer_credit_spec(
        false,
    ).consumed_spec());
    assert(forall|y: u64| #[trigger] s1.ids.peer_created(y) == s0.ids.peer_created(y));
    assert forall|y: u64| #[trigger] created(s1.ids, y) == created(s0.ids, y) by {}
}

/// Entry `i` replaced by `ne`, with the same ID, the trace record following its receiving part
/// and the reset record its sending part: the entry invariants still hold.
proof fn lemma_update(
    s0: Streams,
    i: int,
    ne: Entry,
    rtr: Map<u64, Seq<SpecRecvIn>>,
    resets: Map<u64, u64>,
)
    requires
        s0.wf(),
        0 <= i < s0.entries@.len(),
        ne.id == s0.entries@[i].id,
        entry_ok(ne, s0.rx_bidi, s0.rx_uni),
        rtr == match ne.recv {
            Some(r) => s0.rtr@.insert(ne.id, r.trace()),
            None => s0.rtr@,
        },
        forall|y: u64|
            y != ne.id ==> #[trigger] resets.contains_key(y) == s0.resets@.contains_key(y)
            && resets[y] == s0.resets@[y],
        s0.resets@.contains_key(ne.id) ==> resets.contains_key(ne.id),
        ne.send matches Some(p) ==> (p.reset_spec() matches Some(c) ==> resets.contains_key(ne.id)
            && resets[ne.id] == c.0) && (resets.contains_key(ne.id) ==> p.reset_spec() is Some),
        ne.recv matches Some(r) ==> s0.removed@.contains(ne.id) ==> removed_ok(r.rfc()),
    ensures
        entries_ok(
            s0.entries@.update(i, ne),
            s0.ids,
            s0.rx_bidi,
            s0.rx_uni,
            rtr,
            s0.removed@,
            resets,
        ),
        records_ok(
            s0.entries@.update(i, ne),
            s0.ids,
            s0.rx_bidi,
            s0.rx_uni,
            rtr,
            s0.removed@,
            resets,
        ),
{
    let a = s0.entries@;
    let t = a.update(i, ne);
    let id = ne.id;
    assert(entry_ok(a[i], s0.rx_bidi, s0.rx_uni));
    assert(!s0.removed@.contains(id));
    assert(s0.rtr@.contains_key(id) == (id % 4 == 0 || id % 4 == 2)) by {
        s0.ids.lemma_wf();
        assert(created(s0.ids, id));
    }
    assert forall|k: int| 0 <= k < t.len() && k != i implies (#[trigger] t[k]).id != id by {
        assert(t[k] == a[k]);
    }
    assert forall|j: int, k: int|
        0 <= j < t.len() && 0 <= k < t.len() && j != k implies (#[trigger] t[j]).id != (
        #[trigger] t[k]).id by {
        assert(a[j].id != a[k].id);
    }
    assert forall|k: int| 0 <= k < t.len() implies {
        &&& entry_ok(#[trigger] t[k], s0.rx_bidi, s0.rx_uni)
        &&& created(s0.ids, t[k].id)
        &&& !s0.removed@.contains(t[k].id)
        &&& (t[k].recv matches Some(r) ==> rtr.contains_key(t[k].id) && rtr[t[k].id] == r.trace())
        &&& (t[k].send matches Some(p) ==> (p.reset_spec() matches Some(c) ==> resets.contains_key(
            t[k].id,
        ) && resets[t[k].id] == c.0) && (resets.contains_key(t[k].id) ==> p.reset_spec() is Some))
    } by {
        assert(a[k].id == t[k].id);
    }
    assert forall|y: u64| #[trigger] rtr.contains_key(y) == s0.ids.peer_created(y) by {
        assert(rtr.contains_key(y) == s0.rtr@.contains_key(y));
    }
    assert forall|y: u64| #[trigger] s0.removed@.contains(y) implies rtr.contains_key(y)
        && removed_ok(rfc_recv(y, if y % 4 == 0 { s0.rx_bidi } else { s0.rx_uni }, rtr[y])) by {
        assert(y != id);
    }
    assert forall|y: u64| #[trigger]
        rtr.contains_key(y) && !s0.removed@.contains(y) implies has_id(t, y) by {
        assert(s0.rtr@.contains_key(y));
        let k = choose|k: int| 0 <= k < a.len() && (#[trigger] a[k]).id == y;
        assert(t[k].id == y);
    }
    assert forall|y: u64| #[trigger] resets.contains_key(y) implies created(s0.ids, y) by {
        if y == id {
            assert(created(s0.ids, a[i].id));
        }
    }
}

/// Pushing an entry keeps every existing sending part where `tx_part` finds it.
proof fn lemma_part_push(s0: Streams, s1: Streams, e: Entry)
    requires
        s0.wf(),
        s1.wf(),
        s1.entries@ == s0.entries@.push(e),
    ensures
        parts_kept(s0, s1),
{
    assert forall|j: u64| #[trigger] s0.tx_part(j) is Some implies s1.tx_part(j) == s0.tx_part(
        j,
    ) by {
        assert(has_id(s0.entries@, j));
        let k = choose|k: int| 0 <= k < s0.entries@.len() && (#[trigger] s0.entries@[k]).id == j;
        lemma_part_at(s0, k);
        assert(s1.entries@[k] == s0.entries@[k]);
        lemma_part_at(s1, k);
    }
}

/// `gc`'s removal preserves the invariant.
proof fn lemma_gc(s0: Streams, s1: Streams, i: int, e: Entry)
    requires
        s0.wf(),
        0 <= i < s0.entries@.len(),
        e == s0.entries@[i],
        e.recv matches Some(r) ==> terminal(r.rfc().state),
        s1.entries@ == s0.entries@.remove(i),
        s1.conn_recv == s0.conn_recv,
        s1.conn_counted == s0.conn_counted,
        s1.conn_send == s0.conn_send,
        s1.rx_bidi == s0.rx_bidi,
        s1.rx_uni == s0.rx_uni,
        s1.tx_bidi == s0.tx_bidi,
        s1.tx_uni == s0.tx_uni,
        s1.tx_gone@ == s0.tx_gone@ + val(e, 8),
        s1.failed == s0.failed,
        s1.rtr == s0.rtr,
        s1.resets == s0.resets,
        e.id % 4 == 3 ==> s1.ids == s0.ids && s1.removed == s0.removed && s1.gone == s0.gone,
        e.id % 4 != 3 ==> {
            let b = e.id % 4 == 0;
            let c0 = s0.ids.peer_credit_spec(b);
            let c1 = s1.ids.peer_credit_spec(b);
            &&& s1.ids.wf()
            &&& forall|bb: bool| #[trigger]
                s1.ids.peer_opened_spec(bb) == s0.ids.peer_opened_spec(bb)
            &&& s1.ids.peer_credit_spec(!b) == s0.ids.peer_credit_spec(!b)
            &&& s1.ids.local_uni_spec() == s0.ids.local_uni_spec()
            &&& c1.consumed_spec() == c0.consumed_spec() + 1
            &&& c1.window_spec() == c0.window_spec()
            &&& s1.removed@ == s0.removed@.insert(e.id)
            &&& s1.gone@ == s0.gone@ + val(e, 0)
        },
    ensures
        s1.wf(),
{
    let a = s0.entries@;
    let t = s1.entries@;
    let id = e.id;
    s0.ids.lemma_wf();
    s1.ids.lemma_wf();
    assert(entry_ok(e, s0.rx_bidi, s0.rx_uni));
    lemma_sum_remove(a, i, 0);
    lemma_sum_remove(a, i, 1);
    lemma_sum_remove(a, i, 4);
    lemma_sum_remove(a, i, 6);
    lemma_sum_remove(a, i, 8);
    if let Some(r) = e.recv {
        r.lemma_wf();
        assert(val(e, 0) == val(e, 1));
        let w = if id % 4 == 0 {
            s0.rx_bidi
        } else {
            s0.rx_uni
        };
        assert(r.rfc() == rfc_recv(id, w, s0.rtr@[id]));
    }
    assert forall|k: int| 0 <= k < t.len() implies t[k] == a[if k < i { k } else { k + 1 }] by {}
    assert forall|y: u64| #[trigger] created(s1.ids, y) == created(s0.ids, y) by {}
    assert forall|k: int| 0 <= k < t.len() implies (#[trigger] t[k]).id != id by {
        let kk = if k < i { k } else { k + 1 };
        assert(t[k] == a[kk]);
    }
    assert forall|j: int, k: int|
        0 <= j < t.len() && 0 <= k < t.len() && j != k implies (#[trigger] t[j]).id != (
        #[trigger] t[k]).id by {
        let jj = if j < i { j } else { j + 1 };
        let kk = if k < i { k } else { k + 1 };
        assert(t[j] == a[jj] && t[k] == a[kk]);
    }
    assert forall|k: int| 0 <= k < t.len() implies {
        &&& entry_ok(#[trigger] t[k], s1.rx_bidi, s1.rx_uni)
        &&& created(s1.ids, t[k].id)
        &&& !s1.removed@.contains(t[k].id)
        &&& (t[k].recv matches Some(r) ==> s1.rtr@.contains_key(t[k].id) && s1.rtr@[t[k].id]
            == r.trace())
        &&& (t[k].send matches Some(p) ==> (p.reset_spec() matches Some(c)
            ==> s1.resets@.contains_key(t[k].id) && s1.resets@[t[k].id] == c.0) && (
        s1.resets@.contains_key(t[k].id) ==> p.reset_spec() is Some))
    } by {
        let kk = if k < i { k } else { k + 1 };
        assert(t[k] == a[kk]);
    }
    assert forall|y: u64| #[trigger] s1.rtr@.contains_key(y) == s1.ids.peer_created(y) by {
        assert(s0.rtr@.contains_key(y) == s0.ids.peer_created(y));
    }
    assert forall|y: u64| #[trigger] s1.removed@.contains(y) implies s1.rtr@.contains_key(y)
        && removed_ok(rfc_recv(y, if y % 4 == 0 { s1.rx_bidi } else { s1.rx_uni }, s1.rtr@[y]))
        by {
        if y != id {
            assert(s0.removed@.contains(y));
        }
    }
    assert forall|y: u64| #[trigger]
        s1.rtr@.contains_key(y) && !s1.removed@.contains(y) implies has_id(t, y) by {
        assert(y != id) by {
            if y == id {
                assert(id % 4 == 0 || id % 4 == 2);
            }
        }
        let k = choose|k: int| 0 <= k < a.len() && (#[trigger] a[k]).id == y;
        assert(k != i);
        let kk = if k < i { k } else { k - 1 };
        assert(t[kk] == a[k]);
    }
    assert forall|y: u64| #[trigger] s1.resets@.contains_key(y) implies created(s1.ids, y) by {
        assert(created(s0.ids, y));
    }
}

/// `open_one`'s step preserves the invariant.
proof fn lemma_open_one(s0: Streams, s1: Streams, x: u64, e: Entry)
    requires
        s0.wf(),
        x % 4 == 0 || x % 4 == 2,
        x / 4 == s0.ids.peer_opened_spec(x % 4 == 0),
        s1.ids.wf(),
        s1.ids.peer_opened_spec(x % 4 == 0) == x / 4 + 1,
        s1.ids.peer_opened_spec(x % 4 != 0) == s0.ids.peer_opened_spec(x % 4 != 0),
        forall|b: bool| #[trigger] s1.ids.peer_credit_spec(b) == s0.ids.peer_credit_spec(b),
        s1.ids.local_uni_spec() == s0.ids.local_uni_spec(),
        e.id == x,
        e.recv matches Some(r) && r.wf() && r.id_spec() == x && r.window_spec() == s0.rx_window(x)
            && r.trace() == Seq::<SpecRecvIn>::empty(),
        (x % 4 == 0) == (e.send is Some),
        e.send matches Some(p) ==> p.wf() && p.reset_spec() is None && p.sent_end() == 0,
        s1.entries@ == s0.entries@.push(e),
        s1.rtr@ == s0.rtr@.insert(x, Seq::<SpecRecvIn>::empty()),
        s1.conn_recv == s0.conn_recv,
        s1.conn_counted == s0.conn_counted,
        s1.conn_send == s0.conn_send,
        s1.rx_bidi == s0.rx_bidi,
        s1.rx_uni == s0.rx_uni,
        s1.tx_bidi == s0.tx_bidi,
        s1.tx_uni == s0.tx_uni,
        s1.tx_gone == s0.tx_gone,
        s1.failed == s0.failed,
        s1.removed == s0.removed,
        s1.resets == s0.resets,
        s1.gone == s0.gone,
    ensures
        s1.wf(),
        s1.same_rest(s0),
{
    let b = x % 4 == 0;
    let a = s0.entries@;
    let t = s1.entries@;
    s0.ids.lemma_wf();
    s1.ids.lemma_wf();
    let r = e.recv->0;
    r.lemma_wf();
    lemma_recv_inv(x, r.window_spec(), Seq::empty());
    // The new entry counts nothing yet.
    assert(val(e, 0) == 0 && val(e, 1) == 0 && val(e, 2) == 0 && val(e, 3) == 0);
    assert(val(e, kq(b)) == 1 && val(e, kq(!b)) == 0 && val(e, 8) == 0);
    lemma_sum_push(a, e, 0);
    lemma_sum_push(a, e, 1);
    lemma_sum_push(a, e, 2);
    lemma_sum_push(a, e, 3);
    lemma_sum_push(a, e, 4);
    lemma_sum_push(a, e, 6);
    lemma_sum_push(a, e, 8);
    // Created before means a lower ID of this type, or another type.
    assert forall|y: u64| #[trigger] created(s0.ids, y) implies created(s1.ids, y) && y != x by {}
    assert forall|y: u64| #[trigger] s1.ids.peer_created(y) == (s0.ids.peer_created(y) || y == x)
        by {}
    assert(!s0.rtr@.contains_key(x));
    assert(!s0.removed@.contains(x));
    assert(!s0.resets@.contains_key(x));
    assert forall|k: int| 0 <= k < a.len() implies (#[trigger] a[k]).id != x by {
        assert(created(s0.ids, a[k].id));
    }
    assert forall|k: int| 0 <= k < t.len() implies entry_ok(#[trigger] t[k], s1.rx_bidi, s1.rx_uni)
        by {
        if k < a.len() {
            assert(t[k] == a[k]);
        }
    }
    assert forall|j: int, k: int|
        0 <= j < t.len() && 0 <= k < t.len() && j != k implies (#[trigger] t[j]).id != (
        #[trigger] t[k]).id by {
        if j < a.len() {
            assert(t[j] == a[j]);
        }
        if k < a.len() {
            assert(t[k] == a[k]);
        }
    }
    assert forall|k: int| 0 <= k < t.len() implies {
        &&& created(s1.ids, (#[trigger] t[k]).id)
        &&& !s1.removed@.contains(t[k].id)
        &&& (t[k].recv matches Some(r) ==> s1.rtr@.contains_key(t[k].id) && s1.rtr@[t[k].id]
            == r.trace())
        &&& (t[k].send matches Some(p) ==> (p.reset_spec() matches Some(c)
            ==> s1.resets@.contains_key(t[k].id) && s1.resets@[t[k].id] == c.0) && (
        s1.resets@.contains_key(t[k].id) ==> p.reset_spec() is Some))
    } by {
        if k < a.len() {
            assert(t[k] == a[k]);
        }
    }
    assert forall|id: u64| #[trigger]
        s1.rtr@.contains_key(id) && !s1.removed@.contains(id) implies has_id(t, id) by {
        if id == x {
            assert(t[a.len() as int].id == x);
        } else {
            let k = choose|k: int| 0 <= k < a.len() && (#[trigger] a[k]).id == id;
            assert(t[k] == a[k]);
        }
    }
    assert forall|id: u64| #[trigger] s1.removed@.contains(id) implies s1.rtr@.contains_key(id)
        && removed_ok(rfc_recv(id, if id % 4 == 0 { s1.rx_bidi } else { s1.rx_uni }, s1.rtr@[id]))
        by {
        assert(s0.rtr@.contains_key(id));
    }
    assert forall|j: u64| #[trigger] s1.rx_trace(j) == s0.rx_trace(j) by {}
}

// ---- Transmit ----

/// What each frame `poll_frames` returns guarantees besides being sendable, judged against the
/// state before the call: MAX_STREAM_DATA only for a live receiving part in Recv that we did
/// not stop, STREAM never from a sending part in Data Recvd, Reset Sent or Reset Recvd, and
/// RESET_STREAM only with the code it was reset with (by `reset` or the peer's STOP_SENDING).
pub open spec fn polled_rule(s: Streams, f: SpecFrame) -> bool {
    match f {
        SpecFrame::MaxStreamData { stream_id, .. } => s.rx_live(stream_id) && s.rx_spec(
            stream_id,
        ).state is Recv && !s.rx_spec(stream_id).stopped,
        SpecFrame::Stream { stream_id, .. } => match s.tx_part(stream_id) {
            Some(p) => !no_data(p.state()),
            None => false,
        },
        SpecFrame::ResetStream { stream_id, error_code, .. } => s.reset_code(stream_id) == Some(
            error_code,
        ),
        _ => true,
    }
}

/// A frame `poll_frames` may return: encodable, permitted in a 1-RTT packet, and `polled_rule`.
pub open spec fn polled_ok(s: Streams, f: SpecFrame) -> bool {
    &&& frame_wf(f)
    &&& frame_permitted(spec_frame_type(f), PacketKind::OneRtt)
    &&& polled_rule(s, f)
}

/// `SendStream::write` of `n` bytes succeeds on `p`.
pub open spec fn write_ok(p: SendStream, n: nat) -> bool {
    &&& p.state() is Ready || p.state() is Send
    &&& !p.fin_written_spec()
    &&& p.all_written().len() + n <= VARINT_MAX
}

/// The encoded size of a STREAM frame on stream `id` at offset `off` carrying `n` bytes: the
/// type, the ID, the offset only when nonzero, the length, then the data.
pub open spec fn stream_frame_len(id: u64, off: u64, n: u64) -> nat {
    1 + rfc_varint_min_len(id) + (if off > 0 {
        rfc_varint_min_len(off)
    } else {
        0
    }) + rfc_varint_min_len(n) + n as nat
}

pub proof fn lemma_stream_frame_len(id: u64, off: u64, d: Seq<u8>, fin: bool)
    requires
        id <= VARINT_MAX,
        off + d.len() <= VARINT_MAX,
    ensures
        spec_frame_bytes(SpecFrame::Stream { stream_id: id, offset: off, data: d, fin }).len()
            == stream_frame_len(id, off, d.len() as u64),
        spec_frame_type(SpecFrame::Stream { stream_id: id, offset: off, data: d, fin }) <= 0x0f,
{
    let f = SpecFrame::Stream { stream_id: id, offset: off, data: d, fin };
    let a: u64 = if off > 0 {
        0x04
    } else {
        0
    };
    let b: u64 = if fin {
        0x01
    } else {
        0
    };
    assert((0x08u64 | a | 0x02u64 | b) <= 0x0f) by (bit_vector)
        requires
            a == 0 || a == 4,
            b == 0 || b == 1,
    ;
    assert(spec_frame_type(f) == (0x08u64 | a | 0x02u64 | b));
    theorem_serialize_matches_rfc(spec_frame_type(f));
    theorem_serialize_matches_rfc(id);
    theorem_serialize_matches_rfc(off);
    theorem_serialize_matches_rfc(d.len() as u64);
}

proof fn lemma_vlen_mono(a: u64, b: u64)
    requires
        a <= b,
    ensures
        rfc_varint_min_len(a) <= rfc_varint_min_len(b),
{
}

proof fn lemma_frames_bytes_push(fs: Seq<SpecFrame>, f: SpecFrame)
    ensures
        spec_frames_bytes(fs.push(f)).len() == spec_frames_bytes(fs).len() + spec_frame_bytes(
            f,
        ).len(),
    decreases fs.len(),
{
    if fs.len() == 0 {
        assert(fs.push(f).skip(1) =~= Seq::<SpecFrame>::empty());
        assert(fs.push(f)[0] == f);
        reveal_with_fuel(spec_frames_bytes, 2);
    } else {
        assert(fs.push(f).skip(1) =~= fs.skip(1).push(f));
        assert(fs.push(f)[0] == fs[0]);
        lemma_frames_bytes_push(fs.skip(1), f);
    }
}

/// What each frame `poll_frames` returns says about the state after the call: a STREAM frame's
/// bytes end at or below its stream's bytes sent, which are within the peer's MAX_STREAM_DATA
/// (and, by `lemma_wf`, Σ bytes sent is within MAX_DATA), and a RESET_STREAM's final size is
/// its stream's bytes sent (§4.1, §19.9, §19.10).
pub open spec fn tx_ok(s: Streams, f: SpecFrame) -> bool {
    match f {
        SpecFrame::Stream { stream_id, offset, data, .. } => match s.tx_part(stream_id) {
            Some(q) => offset + data.len() <= q.sent_end() && q.sent_end() <= q.max(),
            None => false,
        },
        SpecFrame::ResetStream { stream_id, final_size, .. } => match s.tx_part(stream_id) {
            Some(q) => final_size == q.sent_end(),
            None => false,
        },
        _ => true,
    }
}

/// `tx_ok` as carried through `poll_frames`: a RESET_STREAM by its part's reset.
spec fn tx_inv(s: Streams, f: SpecFrame) -> bool {
    match f {
        SpecFrame::Stream { stream_id, offset, data, .. } => match s.tx_part(stream_id) {
            Some(q) => offset + data.len() <= q.sent_end(),
            None => false,
        },
        SpecFrame::ResetStream { stream_id, error_code, final_size } => match s.tx_part(
            stream_id,
        ) {
            Some(q) => q.reset_spec() == Some((error_code, final_size)),
            None => false,
        },
        _ => true,
    }
}

/// Every frame from index `n` on satisfies `tx_inv` in `s`.
spec fn out_tx(s: Streams, n: int, out: Seq<Frame>) -> bool {
    forall|k: int| n <= k < out.len() ==> tx_inv(s, (#[trigger] out[k])@)
}

/// Every frame from index `n` on is a STREAM frame of stream `id` ending at or below `se`.
spec fn streamed(out: Seq<Frame>, n: int, id: u64, se: u64) -> bool {
    forall|k: int|
        n <= k < out.len() ==> match (#[trigger] out[k])@ {
            SpecFrame::Stream { stream_id, offset, data, .. } => stream_id == id && offset
                + data.len() <= se,
            _ => false,
        }
}

proof fn lemma_out_tx_push(s: Streams, n: int, out: Seq<Frame>, f: Frame)
    requires
        out_tx(s, n, out),
        tx_inv(s, f@),
    ensures
        out_tx(s, n, out.push(f)),
{
    assert forall|k: int| n <= k < out.push(f).len() implies tx_inv(
        s,
        (#[trigger] out.push(f)[k])@,
    ) by {
        if k < out.len() {
            assert(out.push(f)[k] == out[k]);
        }
    }
}

proof fn lemma_streamed_push(out: Seq<Frame>, o0: Seq<Frame>, id: u64, se: u64, se2: u64, f: Frame)
    requires
        out.len() >= o0.len(),
        out.subrange(0, o0.len() as int) == o0,
        streamed(out, o0.len() as int, id, se),
        se <= se2,
        f@ matches SpecFrame::Stream { stream_id, offset, data, .. } && stream_id == id && offset
            + data.len() <= se2,
    ensures
        out.push(f).subrange(0, o0.len() as int) == o0,
        streamed(out.push(f), o0.len() as int, id, se2),
{
    assert(out.push(f).subrange(0, o0.len() as int) =~= out.subrange(0, o0.len() as int));
    assert forall|k: int| o0.len() <= k < out.push(f).len() implies match (#[trigger] out.push(
        f,
    )[k])@ {
        SpecFrame::Stream { stream_id, offset, data, .. } => stream_id == id && offset + data.len()
            <= se2,
        _ => false,
    } by {
        if k < out.len() {
            assert(out.push(f)[k] == out[k]);
        }
    }
}

/// Entry `i` changed only by bytes sent growing, with its ID and reset kept: `out_tx` carries
/// over.
proof fn lemma_tx_grows(s1: Streams, s2: Streams, i: int, n: int, o: Seq<Frame>)
    requires
        s1.wf(),
        s2.wf(),
        0 <= i < s1.entries@.len(),
        s2.entries@.len() == s1.entries@.len(),
        forall|k: int|
            0 <= k < s1.entries@.len() && k != i ==> #[trigger] s2.entries@[k] == s1.entries@[k],
        s2.entries@[i].id == s1.entries@[i].id,
        s1.entries@[i].send is Some ==> s2.entries@[i].send is Some
            && s2.entries@[i].send->0.sent_end() >= s1.entries@[i].send->0.sent_end()
            && s2.entries@[i].send->0.reset_spec() == s1.entries@[i].send->0.reset_spec(),
        out_tx(s1, n, o),
    ensures
        out_tx(s2, n, o),
{
    assert forall|k: int| n <= k < o.len() implies tx_inv(s2, (#[trigger] o[k])@) by {
        let f = o[k]@;
        let id = match f {
            SpecFrame::Stream { stream_id, .. } => stream_id,
            SpecFrame::ResetStream { stream_id, .. } => stream_id,
            _ => 0,
        };
        if (f is Stream || f is ResetStream) && s1.tx_part(id) is Some {
            assert(has_id(s1.entries@, id));
            let j = choose|j: int|
                0 <= j < s1.entries@.len() && (#[trigger] s1.entries@[j]).id == id;
            lemma_part_at(s1, j);
            assert(s2.entries@[j].id == id);
            lemma_part_at(s2, j);
        }
    }
}

/// `out_tx` after `poll_stream` on entry `i` (stream `id`): the frames before it by
/// `lemma_tx_grows`, the new ones by `streamed`.
proof fn lemma_out_tx_stream(s: Streams, n: int, o0: Seq<Frame>, out: Seq<Frame>, id: u64)
    requires
        out_tx(s, n, o0),
        0 <= n <= o0.len(),
        out.len() >= o0.len(),
        out.subrange(0, o0.len() as int) == o0,
        s.tx_part(id) is Some,
        streamed(out, o0.len() as int, id, s.tx_part(id)->0.sent_end()),
    ensures
        out_tx(s, n, out),
{
    assert forall|k: int| n <= k < out.len() implies tx_inv(s, (#[trigger] out[k])@) by {
        if k < o0.len() {
            assert(out[k] == out.subrange(0, o0.len() as int)[k]);
        }
    }
}

/// `poll_frames`'s ensures, from the passes' invariants.
proof fn lemma_poll_post(
    s0: Streams,
    s: Streams,
    pre: Seq<Frame>,
    budget: nat,
    out: Seq<Frame>,
    room: usize,
)
    requires
        kept(s0, s),
        out_ok(s0, pre, budget, out, room),
        out_tx(s, pre.len() as int, out),
    ensures
        ({
            let new = out.skip(pre.len() as int);
            &&& out.len() >= pre.len()
            &&& out.subrange(0, pre.len() as int) == pre
            &&& frames_sendable(frames_view(new), PacketKind::OneRtt)
            &&& spec_frames_bytes(frames_view(new)).len() <= budget
            &&& forall|k: int| 0 <= k < new.len() ==> polled_rule(s0, (#[trigger] new[k])@)
            &&& forall|k: int| 0 <= k < new.len() ==> tx_ok(s, (#[trigger] new[k])@)
        }),
        s.wf(),
        s.failed_spec() == s0.failed_spec(),
        s.conn_send_spec().used_spec() == s.tx_sent() <= s.conn_send_spec().max_spec(),
        forall|j: u64| #[trigger] s.reset_code(j) == s0.reset_code(j),
        forall|j: u64| #[trigger] s.is_removed(j) == s0.is_removed(j),
        forall|j: u64| #[trigger] s.rx_spec(j).events == s0.rx_spec(j).events,
{
    lemma_out_final(s0, pre, budget, out, room);
    lemma_out_tx_final(s, pre, out);
    s.lemma_wf();
    assert forall|j: u64| #[trigger] s.rx_spec(j).events == s0.rx_spec(j).events by {
        assert(s.rx_spec(j).state == s0.rx_spec(j).state);
    }
}

/// `out_tx` at the end of `poll_frames` gives `tx_ok`.
proof fn lemma_out_tx_final(s: Streams, pre: Seq<Frame>, out: Seq<Frame>)
    requires
        s.wf(),
        pre.len() <= out.len(),
        out_tx(s, pre.len() as int, out),
    ensures
        forall|k: int|
            0 <= k < out.skip(pre.len() as int).len() ==> tx_ok(
                s,
                (#[trigger] out.skip(pre.len() as int)[k])@,
            ),
{
    s.lemma_wf();
    let new = out.skip(pre.len() as int);
    assert forall|k: int| 0 <= k < new.len() implies tx_ok(s, (#[trigger] new[k])@) by {
        assert(new[k] == out[pre.len() + k]);
        let f = new[k]@;
        let id = match f {
            SpecFrame::Stream { stream_id, .. } => stream_id,
            SpecFrame::ResetStream { stream_id, .. } => stream_id,
            _ => 0,
        };
        if (f is Stream || f is ResetStream) && s.tx_part(id) is Some {
            s.tx_part(id)->0.lemma_wf();
        }
    }
}

/// `poll_frames`'s output so far: `pre` kept, each new frame `polled_ok` against `s0`, and
/// their bytes plus `room` the budget.
spec fn out_ok(s0: Streams, pre: Seq<Frame>, budget: nat, out: Seq<Frame>, room: usize) -> bool {
    &&& pre.len() <= out.len()
    &&& out.subrange(0, pre.len() as int) == pre
    &&& forall|k: int| pre.len() <= k < out.len() ==> polled_ok(s0, (#[trigger] out[k])@)
    &&& spec_frames_bytes(frames_view(out.skip(pre.len() as int))).len() + room == budget
}

proof fn lemma_out_push(
    s0: Streams,
    pre: Seq<Frame>,
    budget: nat,
    out: Seq<Frame>,
    room: usize,
    f: Frame,
    room2: usize,
)
    requires
        out_ok(s0, pre, budget, out, room),
        polled_ok(s0, f@),
        room2 + spec_frame_bytes(f@).len() == room,
    ensures
        out_ok(s0, pre, budget, out.push(f), room2),
{
    let n = pre.len() as int;
    let o2 = out.push(f);
    assert(o2.subrange(0, n) =~= out.subrange(0, n));
    assert(frames_view(o2.skip(n)) =~= frames_view(out.skip(n)).push(f@));
    lemma_frames_bytes_push(frames_view(out.skip(n)), f@);
    assert forall|k: int| n <= k < o2.len() implies polled_ok(s0, (#[trigger] o2[k])@) by {
        if k < out.len() {
            assert(o2[k] == out[k]);
        }
    }
}

proof fn lemma_out_init(s0: Streams, pre: Seq<Frame>, budget: nat, room: usize)
    requires
        s0.wf(),
        room == budget,
    ensures
        out_ok(s0, pre, budget, pre, room),
        out_tx(s0, pre.len() as int, pre),
        kept(s0, s0),
        sends_same(s0, s0),
{
    assert(pre.subrange(0, pre.len() as int) =~= pre);
    assert(frames_view(pre.skip(pre.len() as int)) =~= Seq::<SpecFrame>::empty());
}

proof fn lemma_out_final(s0: Streams, pre: Seq<Frame>, budget: nat, out: Seq<Frame>, room: usize)
    requires
        out_ok(s0, pre, budget, out, room),
    ensures
        ({
            let new = out.skip(pre.len() as int);
            &&& out.len() >= pre.len()
            &&& out.subrange(0, pre.len() as int) == pre
            &&& frames_sendable(frames_view(new), PacketKind::OneRtt)
            &&& spec_frames_bytes(frames_view(new)).len() <= budget
            &&& forall|k: int| 0 <= k < new.len() ==> polled_rule(s0, (#[trigger] new[k])@)
        }),
{
    let new = out.skip(pre.len() as int);
    assert forall|k: int| 0 <= k < new.len() implies polled_ok(s0, (#[trigger] new[k])@) by {
        assert(new[k] == out[pre.len() + k]);
    }
    assert forall|k: int| 0 <= k < frames_view(new).len() implies frame_wf(
        #[trigger] frames_view(new)[k],
    ) && frame_permitted(spec_frame_type(frames_view(new)[k]), PacketKind::OneRtt) by {
        assert(frames_view(new)[k] == new[k]@);
        assert(polled_ok(s0, new[k]@));
    }
}

/// Appends control frame `f` if its encoding fits in `room`.
fn emit(
    f: Frame,
    room: &mut usize,
    out: &mut Vec<Frame>,
    Ghost(s0): Ghost<Streams>,
    Ghost(pre): Ghost<Seq<Frame>>,
    Ghost(budget): Ghost<nat>,
    Ghost(cur): Ghost<Streams>,
) -> (sent: bool)
    requires
        frame_wf(f@),
        polled_rule(s0, f@),
        out_ok(s0, pre, budget, old(out)@, *old(room)),
        out_tx(cur, pre.len() as int, old(out)@),
        tx_inv(cur, f@),
    ensures
        out_ok(s0, pre, budget, final(out)@, *final(room)),
        out_tx(cur, pre.len() as int, final(out)@),
{
    // ponytail: double serialization for control frames; compute lengths with varint_len if it shows in profiles.
    let mut b: Vec<u8> = Vec::new();
    serialize_frame(&f, &mut b);
    proof {
        lemma_frame_type_small(f@);
    }
    if b.len() <= *room {
        proof {
            lemma_out_push(s0, pre, budget, out@, *room, f, (*room - b.len()) as usize);
            lemma_out_tx_push(cur, pre.len() as int, out@, f);
        }
        *room = *room - b.len();
        out.push(f);
        true
    } else {
        false
    }
}

/// The largest STREAM payload whose frame fits in `room` with a `w`-byte length, at most
/// `want` (the fit rule for one `w`).
fn fit(room: usize, hdr: usize, w: usize, want: u64) -> (r: Option<u64>)
    ensures
        r matches Some(n) ==> hdr + w + n <= room && rfc_varint_min_len(n) <= w && n <= VARINT_MAX,
{
    if hdr > room || w > room - hdr {
        return None;
    }
    let avail = (room - hdr - w) as u64;
    let mut n = if avail < want {
        avail
    } else {
        want
    };
    if n > VARINT_MAX {
        n = VARINT_MAX;
    }
    if varint_len(n) <= w {
        Some(n)
    } else {
        None
    }
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-2.2
//# An endpoint MUST NOT send data on any stream without ensuring that it
//# is within the flow control limits set by its peer.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-4.1
//# Senders MUST NOT send data in excess of either limit.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-19.10
//# The data sent on a stream MUST NOT exceed the largest maximum stream
//# data value advertised by the receiver.
/// STREAM chunks of sending part `p` (stream `id`) while they fit in `room`: `poll_data` stays
/// under the stream's limit and, with `cs.available()`, the connection's, and `cs` is charged
/// each chunk's new bytes.
fn poll_stream(
    p: &mut SendStream,
    id: u64,
    cs: &mut SendCredit,
    room: &mut usize,
    out: &mut Vec<Frame>,
    Ghost(s0): Ghost<Streams>,
    Ghost(pre): Ghost<Seq<Frame>>,
    Ghost(budget): Ghost<nat>,
)
    requires
        old(p).wf(),
        old(cs).wf(),
        id <= VARINT_MAX,
        match s0.tx_part(id) {
            Some(q) => !no_data(q.state()),
            None => false,
        },
        out_ok(s0, pre, budget, old(out)@, *old(room)),
    ensures
        final(p).wf(),
        final(cs).wf(),
        final(p).reset_spec() == old(p).reset_spec(),
        final(cs).max() == old(cs).max(),
        final(p).sent_end() - old(p).sent_end() == final(cs).used() - old(cs).used(),
        final(p).sent_end() >= old(p).sent_end(),
        out_ok(s0, pre, budget, final(out)@, *final(room)),
        final(out)@.len() >= old(out)@.len(),
        final(out)@.subrange(0, old(out)@.len() as int) == old(out)@,
        streamed(final(out)@, old(out)@.len() as int, id, final(p).sent_end()),
{
    let ghost p0 = *p;
    let ghost c0 = *cs;
    let ghost o0 = out@;
    proof {
        assert(out@.subrange(0, o0.len() as int) =~= o0);
    }
    loop
        invariant
            p.wf(),
            cs.wf(),
            id <= VARINT_MAX,
            match s0.tx_part(id) {
                Some(q) => !no_data(q.state()),
                None => false,
            },
            out_ok(s0, pre, budget, out@, *room),
            p.reset_spec() == p0.reset_spec(),
            cs.max() == c0.max(),
            p.sent_end() - p0.sent_end() == cs.used() - c0.used(),
            p.sent_end() >= p0.sent_end(),
            out@.len() >= o0.len(),
            out@.subrange(0, o0.len() as int) == o0,
            streamed(out@, o0.len() as int, id, p.sent_end()),
        decreases *room,
    {
        // `next_off` Some does not mean `poll_data` sends: loop on what `poll_data` returns.
        let off = match p.next_off() {
            Some(o) => o,
            None => break,
        };
        proof {
            p.lemma_wf();
        }
        let hdr: usize = 1 + varint_len(id) + if off > 0 {
            varint_len(off)
        } else {
            0
        };
        if *room < hdr + 1 {
            break;
        }
        // The fit rule: the best length over 1-, 2-, 4- and 8-byte length fields; 0 (a lone
        // FIN) when only `hdr + 1` fits.
        let want = p.want();
        let mut best: u64 = 0;
        let ghost mut bw: int = 1;
        if let Some(n) = fit(*room, hdr, 1, want) {
            if n > best {
                best = n;
                proof {
                    bw = 1;
                }
            }
        }
        if let Some(n) = fit(*room, hdr, 2, want) {
            if n > best {
                best = n;
                proof {
                    bw = 2;
                }
            }
        }
        if let Some(n) = fit(*room, hdr, 4, want) {
            if n > best {
                best = n;
                proof {
                    bw = 4;
                }
            }
        }
        if let Some(n) = fit(*room, hdr, 8, want) {
            if n > best {
                best = n;
                proof {
                    bw = 8;
                }
            }
        }
        proof {
            cs.lemma_wf();
        }
        let ghost ps = p.sent_end();
        match p.poll_data(best, cs.available()) {
            None => break,
            Some(c) => {
                let ghost cv = c@;
                proof {
                    p.lemma_wf();
                    lemma_stream_frame_len(id, cv.off, cv.data, cv.fin);
                    lemma_vlen_mono(cv.data.len() as u64, best);
                }
                //= https://www.rfc-editor.org/rfc/rfc9000#section-19.9
                //# The sum of
                //# the final sizes on all streams -- including streams in terminal
                //# states -- MUST NOT exceed the value advertised by a receiver.
                cs.consume(c.new_bytes);
                let n = c.data.len();
                let len = hdr + varint_len(n as u64) + n;
                let f = Frame::Stream { stream_id: id, offset: c.off, data: c.data, fin: c.fin };
                proof {
                    assert(f@ == SpecFrame::Stream {
                        stream_id: id,
                        offset: cv.off,
                        data: cv.data,
                        fin: cv.fin,
                    });
                    lemma_out_push(s0, pre, budget, out@, *room, f, (*room - len) as usize);
                    lemma_streamed_push(out@, o0, id, ps, p.sent_end(), f);
                }
                *room = *room - len;
                out.push(f);
            },
        }
    }
}

/// The send state of an entry's sending part.
spec fn sstate(e: Entry) -> Option<SendState> {
    match e.send {
        Some(p) => Some(p.state()),
        None => None,
    }
}

/// The state during `poll_frames` against the one at its start: still `wf`, with the same
/// entries (by ID), records, peer streams and receive-side states and events.
spec fn kept(s0: Streams, s: Streams) -> bool {
    &&& s0.wf()
    &&& s.wf()
    &&& s.failed == s0.failed
    &&& s.removed == s0.removed
    &&& s.resets == s0.resets
    &&& s.rx_bidi == s0.rx_bidi
    &&& s.rx_uni == s0.rx_uni
    &&& s.entries@.len() == s0.entries@.len()
    &&& forall|k: int|
        0 <= k < s.entries@.len() ==> (#[trigger] s.entries@[k]).id == s0.entries@[k].id
    &&& forall|b: bool| #[trigger] s.ids.peer_opened_spec(b) == s0.ids.peer_opened_spec(b)
    &&& forall|j: u64| #[trigger]
        s.rx_spec(j).state == s0.rx_spec(j).state && s.rx_spec(j).stopped == s0.rx_spec(
            j,
        ).stopped && s.rx_spec(j).events == s0.rx_spec(j).events
}

/// Every sending part is in the state it had at the start.
spec fn sends_same(s0: Streams, s: Streams) -> bool {
    forall|k: int|
        0 <= k < s.entries@.len() ==> sstate(#[trigger] s.entries@[k]) == sstate(s0.entries@[k])
}

/// A receiving part's spec after at most one more Credit or Stop input `i`: the same but
/// for the limit or the stop flag.
proof fn lemma_ctl(r0: RecvStream, r1: RecvStream, i: SpecRecvIn)
    requires
        r0.wf(),
        r1.id_spec() == r0.id_spec(),
        r1.window_spec() == r0.window_spec(),
        i is Stop || i is Credit,
        r1.trace() == r0.trace() || r1.trace() == r0.trace().push(i),
    ensures
        r1.rfc().state == r0.rfc().state,
        r1.rfc().events == r0.rfc().events,
        counted(r1.rfc()) == counted(r0.rfc()),
        retired(r1.rfc()) == retired(r0.rfc()),
        (r1.trace() == r0.trace() || i is Credit) ==> r1.rfc().stopped == r0.rfc().stopped,
        r1.trace() == r0.trace().push(i) && i is Stop ==> r1.rfc().stopped,
{
    r0.lemma_wf();
    lemma_recv_push(r0.id_spec(), r0.window_spec(), r0.trace(), i);
    if r1.trace() == r0.trace().push(i) {
        assert(r1.trace().len() == r0.trace().len() + 1);
    }
}

/// Entry `i` replaced by `ne` (same ID), with the trace record following its receiving part and
/// `resets` its sending part, and the bytes sent charged to `conn_send`: `wf` again.
proof fn lemma_swap(s0: Streams, s1: Streams, i: int, ne: Entry)
    requires
        s0.wf(),
        0 <= i < s0.entries@.len(),
        ne.id == s0.entries@[i].id,
        entry_ok(ne, s0.rx_bidi, s0.rx_uni),
        s1.entries@ == s0.entries@.update(i, ne),
        s1.rtr@ == match ne.recv {
            Some(r) => s0.rtr@.insert(ne.id, r.trace()),
            None => s0.rtr@,
        },
        val(ne, 0) == val(s0.entries@[i], 0),
        val(ne, 1) == val(s0.entries@[i], 1),
        s1.conn_send.wf(),
        s1.conn_send.used_spec() + val(s0.entries@[i], 8) == s0.conn_send.used_spec() + val(ne, 8),
        forall|y: u64|
            y != ne.id ==> #[trigger] s1.resets@.contains_key(y) == s0.resets@.contains_key(y)
                && s1.resets@[y] == s0.resets@[y],
        s0.resets@.contains_key(ne.id) ==> s1.resets@.contains_key(ne.id),
        ne.send matches Some(p) ==> (p.reset_spec() matches Some(c) ==> s1.resets@.contains_key(
            ne.id,
        ) && s1.resets@[ne.id] == c.0) && (s1.resets@.contains_key(ne.id) ==> p.reset_spec()
            is Some),
        s1.ids == s0.ids,
        s1.conn_recv == s0.conn_recv,
        s1.conn_counted == s0.conn_counted,
        s1.rx_bidi == s0.rx_bidi,
        s1.rx_uni == s0.rx_uni,
        s1.tx_bidi == s0.tx_bidi,
        s1.tx_uni == s0.tx_uni,
        s1.failed == s0.failed,
        s1.removed == s0.removed,
        s1.gone == s0.gone,
        s1.tx_gone == s0.tx_gone,
    ensures
        s1.wf(),
        forall|j: u64| j != ne.id ==> #[trigger] s1.rx_trace(j) == s0.rx_trace(j),
        ne.recv matches Some(r) ==> s1.rx_spec(ne.id) == r.rfc(),
        ne.recv is None ==> s1.rx_trace(ne.id) == s0.rx_trace(ne.id),
        s0.entries@[i].recv matches Some(r) ==> s0.rx_spec(ne.id) == r.rfc(),
        forall|k: int|
            0 <= k < s1.entries@.len() && k != i ==> #[trigger] s1.entries@[k] == s0.entries@[k],
{
    let a = s0.entries@;
    assert(entry_ok(a[i], s0.rx_bidi, s0.rx_uni));
    assert(!s0.removed@.contains(ne.id));
    lemma_update(s0, i, ne, s1.rtr@, s1.resets@);
    lemma_sum_update(a, i, ne, 0);
    lemma_sum_update(a, i, ne, 1);
    lemma_sum_update(a, i, ne, 4);
    lemma_sum_update(a, i, ne, 6);
    lemma_sum_update(a, i, ne, 8);
    assert(val(ne, 4) == val(a[i], 4) && val(ne, 6) == val(a[i], 6));
    s0.ids.lemma_wf();
}

/// `lemma_swap` during `poll_frames`: `kept` and `sends_same` carry over when the new entry's
/// receive side and send state are as before (up to a Credit input).
proof fn lemma_swap_kept(s0: Streams, s1: Streams, s2: Streams, i: int, ne: Entry)
    requires
        kept(s0, s1),
        0 <= i < s1.entries@.len(),
        ne.id == s1.entries@[i].id,
        s2.resets == s1.resets,
        s2.wf(),
        forall|j: u64| j != ne.id ==> #[trigger] s2.rx_trace(j) == s1.rx_trace(j),
        ne.recv matches Some(r) ==> s2.rx_spec(ne.id) == r.rfc(),
        ne.recv is None ==> s2.rx_trace(ne.id) == s1.rx_trace(ne.id),
        s1.entries@[i].recv matches Some(r) ==> s1.rx_spec(ne.id) == r.rfc(),
        ne.recv is Some == s1.entries@[i].recv is Some,
        ne.recv matches Some(r) ==> (r.rfc().state == s1.entries@[i].recv->0.rfc().state
            && r.rfc().stopped == s1.entries@[i].recv->0.rfc().stopped && r.rfc().events
            == s1.entries@[i].recv->0.rfc().events),
        forall|k: int|
            0 <= k < s2.entries@.len() && k != i ==> #[trigger] s2.entries@[k] == s1.entries@[k],
        s2.entries@.len() == s1.entries@.len(),
        s2.entries@[i] == ne,
        s2.ids == s1.ids,
        s2.failed == s1.failed,
        s2.removed == s1.removed,
        s2.rx_bidi == s1.rx_bidi,
        s2.rx_uni == s1.rx_uni,
    ensures
        kept(s0, s2),
        sends_same(s0, s1) && sstate(ne) == sstate(s1.entries@[i]) ==> sends_same(s0, s2),
{
    assert forall|k: int| 0 <= k < s2.entries@.len() implies (#[trigger] s2.entries@[k]).id
        == s0.entries@[k].id by {
        if k != i {
            assert(s2.entries@[k] == s1.entries@[k]);
        }
    }
    assert forall|j: u64| #[trigger]
        s2.rx_spec(j).state == s0.rx_spec(j).state && s2.rx_spec(j).stopped == s0.rx_spec(
            j,
        ).stopped && s2.rx_spec(j).events == s0.rx_spec(j).events by {
        assert(s1.rx_spec(j).state == s0.rx_spec(j).state);
        if j != ne.id {
            assert(s2.rx_trace(j) == s1.rx_trace(j));
        } else if ne.recv is None {
            assert(s2.rx_trace(j) == s1.rx_trace(j));
        } else {
            assert(s2.rx_spec(j) == ne.recv->0.rfc());
            assert(s1.rx_spec(j) == s1.entries@[i].recv->0.rfc());
        }
    }
    if sends_same(s0, s1) && sstate(ne) == sstate(s1.entries@[i]) {
        assert forall|k: int| 0 <= k < s2.entries@.len() implies sstate(#[trigger] s2.entries@[k])
            == sstate(s0.entries@[k]) by {
            if k != i {
                assert(s2.entries@[k] == s1.entries@[k]);
            }
        }
    }
}

/// The sending part of the entry at `k` is `tx_part` of its ID.
proof fn lemma_part_at(s: Streams, k: int)
    requires
        s.wf(),
        0 <= k < s.entries@.len(),
    ensures
        s.tx_part(s.entries@[k].id) == s.entries@[k].send,
{
    let a = s.entries@;
    let id = a[k].id;
    assert(has_id(a, id));
    let k2 = choose|k2: int| 0 <= k2 < a.len() && (#[trigger] a[k2]).id == id;
    if k2 != k {
        assert(a[k2].id != a[k].id);
    }
}

/// Every entry's ID is a stream ID (§2.1: at most 2^62 - 1).
proof fn lemma_id_bound(s: Streams, k: int)
    requires
        s.wf(),
        0 <= k < s.entries@.len(),
    ensures
        s.entries@[k].id <= VARINT_MAX,
        s.entries@[k].recv is Some ==> s.ids.peer_created(s.entries@[k].id),
{
    s.ids.lemma_wf();
    assert(MAX_STREAMS_LIMIT == 0x1000_0000_0000_0000) by (compute_only);
    assert(created(s.ids, s.entries@[k].id));
    assert(entry_ok(s.entries@[k], s.rx_bidi, s.rx_uni));
}

/// A receiving part at entry `k` during `poll_frames` is a live peer stream whose spec matches
/// the starting state's.
proof fn lemma_rx_entry(s0: Streams, s: Streams, k: int)
    requires
        kept(s0, s),
        0 <= k < s.entries@.len(),
        s.entries@[k].recv is Some,
    ensures
        ({
            let id = s.entries@[k].id;
            let r = s.entries@[k].recv->0;
            &&& id <= VARINT_MAX
            &&& r.wf()
            &&& s.rx_spec(id) == r.rfc()
            &&& s0.rx_live(id)
            &&& s0.rx_spec(id).state == r.rfc().state
            &&& s0.rx_spec(id).stopped == r.rfc().stopped
        }),
{
    let id = s.entries@[k].id;
    lemma_id_bound(s, k);
    assert(entry_ok(s.entries@[k], s.rx_bidi, s.rx_uni));
    assert(!s.removed@.contains(id));
    s.ids.lemma_wf();
    s0.ids.lemma_wf();
    assert(s.ids.peer_opened_spec(id % 4 == 0) == s0.ids.peer_opened_spec(id % 4 == 0));
    assert(s.rx_spec(id).state == s0.rx_spec(id).state);
}

impl Streams {
    /// Our next unidirectional stream is `id`, within the peer's limit.
    pub open spec fn uni_openable(&self, id: u64) -> bool {
        let u = self.ids_spec().local_uni_spec();
        &&& id % 4 == 3
        &&& id / 4 == u.used_spec()
        &&& u.available_spec() > 0
    }

    /// Appends `data` to stream `id`, with the FIN if `fin`. Opens our next unidirectional
    /// stream if `id` is it.
    pub fn write(&mut self, id: u64, data: &[u8], fin: bool) -> (r: Result<(), ()>)
        requires
            old(self).wf(),
            !old(self).failed(),
        ensures
            final(self).wf(),
            !final(self).failed(),
            r is Ok <==> match old(self).tx_part(id) {
                Some(p) => write_ok(p, data@.len()),
                None => old(self).uni_openable(id) && data@.len() <= VARINT_MAX,
            },
            r is Err ==> *final(self) == *old(self),
            r is Ok ==> match final(self).tx_part(id) {
                Some(q) => q.all_written() == (match old(self).tx_part(id) {
                    Some(p) => p.all_written(),
                    None => Seq::<u8>::empty(),
                }) + data@ && q.fin_written_spec() == fin,
                None => false,
            },
            forall|j: u64| #[trigger] final(self).reset_code(j) == old(self).reset_code(j),
            forall|j: u64| #[trigger] final(self).rx_trace(j) == old(self).rx_trace(j),
            forall|j: u64| #[trigger] final(self).is_removed(j) == old(self).is_removed(j),
    {
        match self.find(id) {
            Some(i) => self.write_at(i, data, fin),
            None => self.write_new(id, data, fin),
        }
    }

    fn write_at(&mut self, i: usize, data: &[u8], fin: bool) -> (r: Result<(), ()>)
        requires
            old(self).wf(),
            i < old(self).entries@.len(),
        ensures
            ({
                let id = old(self).entries@[i as int].id;
                &&& final(self).wf()
                &&& final(self).failed() == old(self).failed()
                &&& r is Ok <==> match old(self).tx_part(id) {
                    Some(p) => write_ok(p, data@.len()),
                    None => old(self).uni_openable(id) && data@.len() <= VARINT_MAX,
                }
                &&& r is Err ==> *final(self) == *old(self)
                &&& r is Ok ==> match final(self).tx_part(id) {
                    Some(q) => q.all_written() == (match old(self).tx_part(id) {
                        Some(p) => p.all_written(),
                        None => Seq::<u8>::empty(),
                    }) + data@ && q.fin_written_spec() == fin,
                    None => false,
                }
                &&& forall|j: u64| #[trigger] final(self).reset_code(j) == old(self).reset_code(j)
                &&& forall|j: u64| #[trigger] final(self).rx_trace(j) == old(self).rx_trace(j)
                &&& forall|j: u64| #[trigger] final(self).is_removed(j) == old(self).is_removed(j)
            }),
    {
        let ghost s0 = *self;
        let ghost id = self.entries@[i as int].id;
        proof {
            lemma_part_at(s0, i as int);
            assert(entry_ok(s0.entries@[i as int], s0.rx_bidi, s0.rx_uni));
            s0.ids.lemma_wf();
            assert(created(s0.ids, id));
        }
        let ok = match &self.entries[i].send {
            Some(p) => p.writable(data.len()),
            None => false,
        };
        if !ok {
            return Err(());
        }
        let mut e = Entry { id: 0, recv: None, send: None };
        self.entries.set_and_swap(i, &mut e);
        if let Some(mut p) = e.send.take() {
            let _ = p.write(data, fin);
            e.send = Some(p);
        }
        let ghost ne = e;
        self.entries.set_and_swap(i, &mut e);
        proof {
            assert(self.entries@ == s0.entries@.update(i as int, ne));
            assert(ne.recv == s0.entries@[i as int].recv);
            if let Some(r) = ne.recv {
                assert(s0.rtr@.insert(id, r.trace()) =~= s0.rtr@);
            }
            lemma_swap(s0, *self, i as int, ne);
            lemma_part_at(*self, i as int);
            assert forall|j: u64| #[trigger] self.rx_trace(j) == s0.rx_trace(j) by {}
        }
        Ok(())
    }

    fn write_new(&mut self, id: u64, data: &[u8], fin: bool) -> (r: Result<(), ()>)
        requires
            old(self).wf(),
            !has_id(old(self).entries@, id),
        ensures
            final(self).wf(),
            final(self).failed() == old(self).failed(),
            r is Ok <==> old(self).uni_openable(id) && data@.len() <= VARINT_MAX,
            r is Err ==> *final(self) == *old(self),
            r is Ok ==> match final(self).tx_part(id) {
                Some(q) => q.all_written() == Seq::<u8>::empty() + data@ && q.fin_written_spec()
                    == fin,
                None => false,
            },
            old(self).tx_part(id) is None,
            forall|j: u64| #[trigger] final(self).reset_code(j) == old(self).reset_code(j),
            forall|j: u64| #[trigger] final(self).rx_trace(j) == old(self).rx_trace(j),
            forall|j: u64| #[trigger] final(self).is_removed(j) == old(self).is_removed(j),
    {
        let ghost s0 = *self;
        proof {
            self.ids.lemma_wf();
        }
        if id % 4 != 3 || data.len() as u64 > VARINT_MAX {
            return Err(());
        }
        if !self.ids.open_local_uni(id) {
            return Err(());
        }
        let mut p = SendStream::new(self.tx_uni);
        let _ = p.write(data, fin);
        let e = Entry { id, recv: None, send: Some(p) };
        self.entries.push(e);
        proof {
            lemma_push_local(s0, *self, e);
            lemma_part_at(*self, s0.entries@.len() as int);
            assert(self.entries@[s0.entries@.len() as int] == e);
        }
        Ok(())
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-11.2
    //# RESET_STREAM MUST only be instigated by the
    //# application protocol that uses QUIC.
    /// The application abandons sending on stream `id` with error `code`: RESET_STREAM is
    /// queued if the sending part exists and was not already reset or fully acknowledged.
    /// With the peer's STOP_SENDING (`on_frame`), this is the only way a reset is queued.
    pub fn reset(&mut self, id: u64, code: u64)
        requires
            old(self).wf(),
            !old(self).failed(),
            code <= VARINT_MAX,
        ensures
            final(self).wf(),
            !final(self).failed(),
            final(self).reset_code(id) == match old(self).tx_part(id) {
                Some(p) => if p.state() is Ready || p.state() is Send || p.state() is DataSent {
                    Some(code)
                } else {
                    old(self).reset_code(id)
                },
                None => old(self).reset_code(id),
            },
            forall|j: u64|
                j != id ==> #[trigger] final(self).reset_code(j) == old(self).reset_code(j),
            forall|j: u64| #[trigger] final(self).rx_trace(j) == old(self).rx_trace(j),
            forall|j: u64| #[trigger] final(self).is_removed(j) == old(self).is_removed(j),
    {
        let ghost s0 = *self;
        if let Some(i) = self.find(id) {
            proof {
                lemma_part_at(s0, i as int);
                assert(entry_ok(s0.entries@[i as int], s0.rx_bidi, s0.rx_uni));
            }
            let fresh = match &self.entries[i].send {
                Some(p) => match p.state_exec() {
                    SendState::Ready | SendState::Send | SendState::DataSent => true,
                    _ => false,
                },
                None => false,
            };
            if fresh {
                let mut e = Entry { id: 0, recv: None, send: None };
                self.entries.set_and_swap(i, &mut e);
                if let Some(mut p) = e.send.take() {
                    let _ = p.reset(code);
                    e.send = Some(p);
                }
                let ghost ne = e;
                self.entries.set_and_swap(i, &mut e);
                self.resets = Ghost(self.resets@.insert(id, code));
                proof {
                    assert(self.entries@ == s0.entries@.update(i as int, ne));
                    assert(ne.recv == s0.entries@[i as int].recv);
                    if let Some(r) = ne.recv {
                        assert(s0.rtr@.insert(id, r.trace()) =~= s0.rtr@);
                    }
                    lemma_swap(s0, *self, i as int, ne);
                    assert forall|j: u64| #[trigger] self.rx_trace(j) == s0.rx_trace(j) by {}
                }
            }
        }
    }

    /// The application stops reading stream `id` with error `code`: STOP_SENDING is queued if
    /// the receiving part exists and data may still arrive. No MAX_STREAM_DATA is sent for it
    /// afterwards; its `Data`/`Reset` events still come, up to the terminal one.
    pub fn stop_sending(&mut self, id: u64, code: u64)
        requires
            old(self).wf(),
            !old(self).failed(),
            code <= VARINT_MAX,
        ensures
            final(self).wf(),
            !final(self).failed(),
            forall|j: u64| j != id ==> #[trigger] final(self).rx_trace(j) == old(self).rx_trace(j),
            final(self).rx_trace(id) == old(self).rx_trace(id) || final(self).rx_trace(id) == old(
                self,
            ).rx_trace(id).push(SpecRecvIn::Stop),
            old(self).rx_live(id) && !terminal(old(self).rx_spec(id).state)
                ==> final(self).rx_spec(id).stopped,
            forall|j: u64| #[trigger] final(self).reset_code(j) == old(self).reset_code(j),
            forall|j: u64| #[trigger] final(self).is_removed(j) == old(self).is_removed(j),
    {
        let ghost s0 = *self;
        proof {
            s0.ids.lemma_wf();
            if s0.rx_live(id) {
                assert(s0.rtr@.contains_key(id));
            }
        }
        if let Some(i) = self.find(id) {
            proof {
                assert(entry_ok(s0.entries@[i as int], s0.rx_bidi, s0.rx_uni));
            }
            if self.entries[i].recv.is_some() {
                let mut e = Entry { id: 0, recv: None, send: None };
                self.entries.set_and_swap(i, &mut e);
                let ghost e0 = e;
                if let Some(mut r) = e.recv.take() {
                    let _ = r.stop(code);
                    proof {
                        lemma_ctl(e0.recv->0, r, SpecRecvIn::Stop);
                    }
                    self.rtr = Ghost(self.rtr@.insert(id, r.trace()));
                    e.recv = Some(r);
                }
                let ghost ne = e;
                self.entries.set_and_swap(i, &mut e);
                proof {
                    assert(self.entries@ == s0.entries@.update(i as int, ne));
                    lemma_swap(s0, *self, i as int, ne);
                }
            }
        }
    }
}

impl Streams {
    /// Appends what is due, in order, while it fits in `budget` encoded bytes: every pending
    /// RESET_STREAM, STOP_SENDING, MAX_DATA, MAX_STREAM_DATA, MAX_STREAMS (bidi, then uni),
    /// then STREAM chunks in entry order. A control frame that does not fit stays pending.
    /// The frames returned count as sent: each must later be reported to `on_frame_acked` or
    /// `on_frame_lost`.
    #[verifier::spinoff_prover]
    pub fn poll_frames(&mut self, budget: usize, out: &mut Vec<Frame>)
        requires
            old(self).wf(),
            !old(self).failed(),
        ensures
            final(self).wf(),
            !final(self).failed(),
            ({
                let new = final(out)@.skip(old(out)@.len() as int);
                &&& final(out)@.len() >= old(out)@.len()
                &&& final(out)@.subrange(0, old(out)@.len() as int) == old(out)@
                &&& frames_sendable(frames_view(new), PacketKind::OneRtt)
                &&& spec_frames_bytes(frames_view(new)).len() <= budget
                &&& forall|k: int|
                    0 <= k < new.len() ==> polled_rule(*old(self), (#[trigger] new[k])@)
                &&& forall|k: int| 0 <= k < new.len() ==> tx_ok(*final(self), (#[trigger] new[k])@)
            }),
            final(self).conn_send_spec().used_spec() == final(self).tx_sent()
                <= final(self).conn_send_spec().max_spec(),
            forall|j: u64| #[trigger] final(self).reset_code(j) == old(self).reset_code(j),
            forall|j: u64| #[trigger] final(self).is_removed(j) == old(self).is_removed(j),
            forall|j: u64| #[trigger] final(self).rx_spec(j).events == old(self).rx_spec(j).events,
    {
        let ghost s0 = *self;
        let ghost pre = out@;
        let ghost b = budget as nat;
        let mut room = budget;
        proof {
            lemma_out_init(s0, pre, b, room);
        }
        self.poll_control(&mut room, out, Ghost(s0), Ghost(pre), Ghost(b));
        self.poll_streams(&mut room, out, Ghost(s0), Ghost(pre), Ghost(b));
        proof {
            lemma_poll_post(s0, *self, pre, b, out@, room);
        }
    }

    /// The control frames, in `poll_frames`'s order.
    fn poll_control(
        &mut self,
        room: &mut usize,
        out: &mut Vec<Frame>,
        Ghost(s0): Ghost<Streams>,
        Ghost(pre): Ghost<Seq<Frame>>,
        Ghost(budget): Ghost<nat>,
    )
        requires
            kept(s0, *old(self)),
            sends_same(s0, *old(self)),
            out_ok(s0, pre, budget, old(out)@, *old(room)),
            out_tx(*old(self), pre.len() as int, old(out)@),
        ensures
            kept(s0, *final(self)),
            sends_same(s0, *final(self)),
            out_ok(s0, pre, budget, final(out)@, *final(room)),
            out_tx(*final(self), pre.len() as int, final(out)@),
    {
        self.poll_resets(room, out, Ghost(s0), Ghost(pre), Ghost(budget));
        self.poll_stops(room, out, Ghost(s0), Ghost(pre), Ghost(budget));
        self.poll_max_data(room, out, Ghost(s0), Ghost(pre), Ghost(budget));
        self.poll_credits(room, out, Ghost(s0), Ghost(pre), Ghost(budget));
        self.poll_max_streams(true, room, out, Ghost(s0), Ghost(pre), Ghost(budget));
        self.poll_max_streams(false, room, out, Ghost(s0), Ghost(pre), Ghost(budget));
    }

    /// Every pending RESET_STREAM.
    fn poll_resets(
        &mut self,
        room: &mut usize,
        out: &mut Vec<Frame>,
        Ghost(s0): Ghost<Streams>,
        Ghost(pre): Ghost<Seq<Frame>>,
        Ghost(budget): Ghost<nat>,
    )
        requires
            kept(s0, *old(self)),
            sends_same(s0, *old(self)),
            out_ok(s0, pre, budget, old(out)@, *old(room)),
            out_tx(*old(self), pre.len() as int, old(out)@),
        ensures
            kept(s0, *final(self)),
            sends_same(s0, *final(self)),
            out_ok(s0, pre, budget, final(out)@, *final(room)),
            out_tx(*final(self), pre.len() as int, final(out)@),
    {
        let mut i: usize = 0;
        while i < self.entries.len()
            invariant
                kept(s0, *self),
                sends_same(s0, *self),
                out_ok(s0, pre, budget, out@, *room),
                out_tx(*self, pre.len() as int, out@),
            decreases self.entries@.len() - i,
        {
            proof {
                lemma_id_bound(*self, i as int);
                assert(entry_ok(self.entries@[i as int], self.rx_bidi, self.rx_uni));
            }
            let id = self.entries[i].id;
            let pr = match &self.entries[i].send {
                Some(p) => p.pending_reset(),
                None => None,
            };
            if let Some((code, fs)) = pr {
                proof {
                    let p = self.entries@[i as int].send->0;
                    p.lemma_wf();
                    assert(self.resets@.contains_key(id) && self.resets@[id] == code);
                    lemma_part_at(*self, i as int);
                }
                if emit(
                    Frame::ResetStream { stream_id: id, error_code: code, final_size: fs },
                    room,
                    out,
                    Ghost(s0),
                    Ghost(pre),
                    Ghost(budget),
                    Ghost(*self),
                ) {
                    self.commit_reset_at(i, Ghost(s0), Ghost(pre.len() as int), Ghost(out@));
                }
            }
            i += 1;
        }
    }

    fn commit_reset_at(
        &mut self,
        i: usize,
        Ghost(s0): Ghost<Streams>,
        Ghost(n): Ghost<int>,
        Ghost(o): Ghost<Seq<Frame>>,
    )
        requires
            kept(s0, *old(self)),
            sends_same(s0, *old(self)),
            i < old(self).entries@.len(),
            out_tx(*old(self), n, o),
        ensures
            kept(s0, *final(self)),
            sends_same(s0, *final(self)),
            out_tx(*final(self), n, o),
    {
        let ghost s1 = *self;
        let mut e = Entry { id: 0, recv: None, send: None };
        self.entries.set_and_swap(i, &mut e);
        proof {
            assert(entry_ok(e, s1.rx_bidi, s1.rx_uni));
        }
        if let Some(mut p) = e.send.take() {
            p.commit_reset();
            e.send = Some(p);
        }
        let ghost ne = e;
        self.entries.set_and_swap(i, &mut e);
        proof {
            assert(self.entries@ == s1.entries@.update(i as int, ne));
            lemma_swap_same_rx(s1, *self, i as int, ne);
            lemma_swap_kept(s0, s1, *self, i as int, ne);
            lemma_tx_grows(s1, *self, i as int, n, o);
        }
    }

    /// Every pending STOP_SENDING.
    fn poll_stops(
        &mut self,
        room: &mut usize,
        out: &mut Vec<Frame>,
        Ghost(s0): Ghost<Streams>,
        Ghost(pre): Ghost<Seq<Frame>>,
        Ghost(budget): Ghost<nat>,
    )
        requires
            kept(s0, *old(self)),
            sends_same(s0, *old(self)),
            out_ok(s0, pre, budget, old(out)@, *old(room)),
            out_tx(*old(self), pre.len() as int, old(out)@),
        ensures
            kept(s0, *final(self)),
            sends_same(s0, *final(self)),
            out_ok(s0, pre, budget, final(out)@, *final(room)),
            out_tx(*final(self), pre.len() as int, final(out)@),
    {
        let mut i: usize = 0;
        while i < self.entries.len()
            invariant
                kept(s0, *self),
                sends_same(s0, *self),
                out_ok(s0, pre, budget, out@, *room),
                out_tx(*self, pre.len() as int, out@),
            decreases self.entries@.len() - i,
        {
            proof {
                lemma_id_bound(*self, i as int);
                assert(entry_ok(self.entries@[i as int], self.rx_bidi, self.rx_uni));
            }
            let id = self.entries[i].id;
            let ps = match &self.entries[i].recv {
                Some(r) => r.pending_stop(),
                None => None,
            };
            if let Some(code) = ps {
                proof {
                    self.entries@[i as int].recv->0.lemma_wf();
                }
                if emit(
                    Frame::StopSending { stream_id: id, error_code: code },
                    room,
                    out,
                    Ghost(s0),
                    Ghost(pre),
                    Ghost(budget),
                    Ghost(*self),
                ) {
                    self.recv_op_at(i, 0, Ghost(s0), Ghost(pre.len() as int), Ghost(out@));
                }
            }
            i += 1;
        }
    }

    /// A control operation on entry `i`'s receiving part: 0 `commit_stop`, 1 `commit_credit`
    /// (if pending), 2 `stop_lost`, 3 `credit_lost`.
    #[verifier::spinoff_prover]
    fn recv_op_at(
        &mut self,
        i: usize,
        op: u8,
        Ghost(s0): Ghost<Streams>,
        Ghost(n): Ghost<int>,
        Ghost(o): Ghost<Seq<Frame>>,
    )
        requires
            kept(s0, *old(self)),
            i < old(self).entries@.len(),
            out_tx(*old(self), n, o),
        ensures
            out_tx(*final(self), n, o),
            kept(s0, *final(self)),
            sends_same(s0, *old(self)) ==> sends_same(s0, *final(self)),
            final(self).ids == old(self).ids,
            forall|j: u64| j != old(self).entries@[i as int].id ==> #[trigger] final(self).rx_trace(
                j,
            ) == old(self).rx_trace(j),
            op != 1 ==> forall|j: u64| #[trigger] final(self).rx_trace(j) == old(self).rx_trace(j),
    {
        let ghost s1 = *self;
        let ghost id = self.entries@[i as int].id;
        let mut e = Entry { id: 0, recv: None, send: None };
        self.entries.set_and_swap(i, &mut e);
        let ghost e0 = e;
        proof {
            assert(entry_ok(e, s1.rx_bidi, s1.rx_uni));
        }
        if let Some(mut r) = e.recv.take() {
            let ghost r0 = r;
            let ghost inp = if op == 1 {
                SpecRecvIn::Credit { limit: r0.pending_credit_spec()->0 as nat }
            } else {
                SpecRecvIn::Stop
            };
            if op == 0 {
                r.commit_stop();
            } else if op == 1 {
                if r.pending_credit().is_some() {
                    r.commit_credit();
                }
            } else if op == 2 {
                r.stop_lost();
            } else {
                r.credit_lost();
            }
            proof {
                lemma_ctl(r0, r, inp);
            }
            self.rtr = Ghost(self.rtr@.insert(id, r.trace()));
            e.recv = Some(r);
        }
        let ghost ne = e;
        self.entries.set_and_swap(i, &mut e);
        proof {
            assert(self.entries@ == s1.entries@.update(i as int, ne));
            if e0.recv is None {
                assert(self.rtr@ == s1.rtr@);
            }
            lemma_swap(s1, *self, i as int, ne);
            lemma_swap_kept(s0, s1, *self, i as int, ne);
            lemma_tx_grows(s1, *self, i as int, n, o);
            if op != 1 {
                assert forall|j: u64| #[trigger] self.rx_trace(j) == s1.rx_trace(j) by {
                    if j == id && ne.recv is Some {
                        assert(s1.rtr@[id] == e0.recv->0.trace());
                    }
                }
            }
        }
    }

    /// The pending MAX_DATA.
    fn poll_max_data(
        &mut self,
        room: &mut usize,
        out: &mut Vec<Frame>,
        Ghost(s0): Ghost<Streams>,
        Ghost(pre): Ghost<Seq<Frame>>,
        Ghost(budget): Ghost<nat>,
    )
        requires
            kept(s0, *old(self)),
            sends_same(s0, *old(self)),
            out_ok(s0, pre, budget, old(out)@, *old(room)),
            out_tx(*old(self), pre.len() as int, old(out)@),
        ensures
            kept(s0, *final(self)),
            sends_same(s0, *final(self)),
            out_ok(s0, pre, budget, final(out)@, *final(room)),
            out_tx(*final(self), pre.len() as int, final(out)@),
    {
        if let Some(v) = self.conn_recv.pending() {
            proof {
                self.conn_recv.lemma_wf();
            }
            let f = Frame::MaxData(v);
            if emit(f, room, out, Ghost(s0), Ghost(pre), Ghost(budget), Ghost(*self)) {
                let ghost s1 = *self;
                self.conn_recv.commit();
                proof {
                    assert(forall|j: u64| #[trigger] self.rx_spec(j) == s1.rx_spec(j));
                }
            }
        }
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-4.2
    //# Therefore, a receiver MUST NOT wait for a
    //# STREAM_DATA_BLOCKED or DATA_BLOCKED frame before sending a
    //# MAX_STREAM_DATA or MAX_DATA frame
    /// Every pending MAX_STREAM_DATA: only in Recv and never after our STOP_SENDING
    /// (`pending_credit`). Like MAX_DATA's and MAX_STREAMS's, each update depends on
    /// consumption alone (`RecvCredit`), never on a received *_BLOCKED frame.
    fn poll_credits(
        &mut self,
        room: &mut usize,
        out: &mut Vec<Frame>,
        Ghost(s0): Ghost<Streams>,
        Ghost(pre): Ghost<Seq<Frame>>,
        Ghost(budget): Ghost<nat>,
    )
        requires
            kept(s0, *old(self)),
            sends_same(s0, *old(self)),
            out_ok(s0, pre, budget, old(out)@, *old(room)),
            out_tx(*old(self), pre.len() as int, old(out)@),
        ensures
            kept(s0, *final(self)),
            sends_same(s0, *final(self)),
            out_ok(s0, pre, budget, final(out)@, *final(room)),
            out_tx(*final(self), pre.len() as int, final(out)@),
    {
        let mut i: usize = 0;
        while i < self.entries.len()
            invariant
                kept(s0, *self),
                sends_same(s0, *self),
                out_ok(s0, pre, budget, out@, *room),
                out_tx(*self, pre.len() as int, out@),
            decreases self.entries@.len() - i,
        {
            let id = self.entries[i].id;
            let pc = match &self.entries[i].recv {
                Some(r) => r.pending_credit(),
                None => None,
            };
            if let Some(v) = pc {
                proof {
                    lemma_rx_entry(s0, *self, i as int);
                    self.entries@[i as int].recv->0.lemma_wf();
                }
                if emit(
                    Frame::MaxStreamData { stream_id: id, max: v },
                    room,
                    out,
                    Ghost(s0),
                    Ghost(pre),
                    Ghost(budget),
                    Ghost(*self),
                ) {
                    self.recv_op_at(i, 1, Ghost(s0), Ghost(pre.len() as int), Ghost(out@));
                }
            }
            i += 1;
        }
    }

    /// This direction's pending MAX_STREAMS.
    fn poll_max_streams(
        &mut self,
        bidi: bool,
        room: &mut usize,
        out: &mut Vec<Frame>,
        Ghost(s0): Ghost<Streams>,
        Ghost(pre): Ghost<Seq<Frame>>,
        Ghost(budget): Ghost<nat>,
    )
        requires
            kept(s0, *old(self)),
            sends_same(s0, *old(self)),
            out_ok(s0, pre, budget, old(out)@, *old(room)),
            out_tx(*old(self), pre.len() as int, old(out)@),
        ensures
            kept(s0, *final(self)),
            sends_same(s0, *final(self)),
            out_ok(s0, pre, budget, final(out)@, *final(room)),
            out_tx(*final(self), pre.len() as int, final(out)@),
    {
        if let Some(v) = self.ids.pending_max_streams(bidi) {
            let f = Frame::MaxStreams { bidi, max: v };
            if emit(f, room, out, Ghost(s0), Ghost(pre), Ghost(budget), Ghost(*self)) {
                let ghost s1 = *self;
                self.ids.commit_max_streams(bidi);
                proof {
                    lemma_ids_frame(s1, *self);
                    assert(forall|j: u64| #[trigger] self.rx_spec(j) == s1.rx_spec(j));
                }
            }
        }
    }

    /// STREAM chunks, entry by entry.
    fn poll_streams(
        &mut self,
        room: &mut usize,
        out: &mut Vec<Frame>,
        Ghost(s0): Ghost<Streams>,
        Ghost(pre): Ghost<Seq<Frame>>,
        Ghost(budget): Ghost<nat>,
    )
        requires
            kept(s0, *old(self)),
            sends_same(s0, *old(self)),
            out_ok(s0, pre, budget, old(out)@, *old(room)),
            out_tx(*old(self), pre.len() as int, old(out)@),
        ensures
            kept(s0, *final(self)),
            out_ok(s0, pre, budget, final(out)@, *final(room)),
            out_tx(*final(self), pre.len() as int, final(out)@),
    {
        let mut i: usize = 0;
        while i < self.entries.len()
            invariant
                kept(s0, *self),
                forall|k: int|
                    i <= k < self.entries@.len() ==> sstate(#[trigger] self.entries@[k]) == sstate(
                        s0.entries@[k],
                    ),
                out_ok(s0, pre, budget, out@, *room),
                out_tx(*self, pre.len() as int, out@),
            decreases self.entries@.len() - i,
        {
            proof {
                lemma_id_bound(*self, i as int);
                assert(entry_ok(self.entries@[i as int], self.rx_bidi, self.rx_uni));
            }
            let open = match &self.entries[i].send {
                Some(p) => match p.state_exec() {
                    SendState::Ready | SendState::Send | SendState::DataSent => true,
                    _ => false,
                },
                None => false,
            };
            if open {
                self.poll_stream_at(i, room, out, Ghost(s0), Ghost(pre), Ghost(budget));
            }
            i += 1;
        }
    }

    fn poll_stream_at(
        &mut self,
        i: usize,
        room: &mut usize,
        out: &mut Vec<Frame>,
        Ghost(s0): Ghost<Streams>,
        Ghost(pre): Ghost<Seq<Frame>>,
        Ghost(budget): Ghost<nat>,
    )
        requires
            kept(s0, *old(self)),
            i < old(self).entries@.len(),
            old(self).entries@[i as int].send matches Some(p) && !no_data(p.state()),
            sstate(old(self).entries@[i as int]) == sstate(s0.entries@[i as int]),
            out_ok(s0, pre, budget, old(out)@, *old(room)),
            out_tx(*old(self), pre.len() as int, old(out)@),
        ensures
            kept(s0, *final(self)),
            forall|k: int|
                0 <= k < final(self).entries@.len() && k != i ==> #[trigger] final(self).entries@[k]
                    == old(self).entries@[k],
            out_ok(s0, pre, budget, final(out)@, *final(room)),
            out_tx(*final(self), pre.len() as int, final(out)@),
    {
        let ghost s1 = *self;
        proof {
            lemma_id_bound(s1, i as int);
            lemma_part_at(s0, i as int);
            assert(s0.entries@[i as int].id == s1.entries@[i as int].id);
        }
        let id = self.entries[i].id;
        let ghost o0 = out@;
        let mut e = Entry { id: 0, recv: None, send: None };
        self.entries.set_and_swap(i, &mut e);
        proof {
            assert(entry_ok(e, s1.rx_bidi, s1.rx_uni));
        }
        if let Some(mut p) = e.send.take() {
            let cs = &mut self.conn_send;
            poll_stream(&mut p, id, cs, room, out, Ghost(s0), Ghost(pre), Ghost(budget));
            e.send = Some(p);
        }
        let ghost ne = e;
        self.entries.set_and_swap(i, &mut e);
        proof {
            assert(self.entries@ == s1.entries@.update(i as int, ne));
            assert(ne.recv == s1.entries@[i as int].recv);
            if let Some(r) = ne.recv {
                assert(s1.rtr@.insert(id, r.trace()) =~= s1.rtr@);
            }
            lemma_swap(s1, *self, i as int, ne);
            lemma_swap_kept(s0, s1, *self, i as int, ne);
            lemma_tx_grows(s1, *self, i as int, pre.len() as int, o0);
            lemma_part_at(*self, i as int);
            lemma_out_tx_stream(*self, pre.len() as int, o0, out@, id);
        }
    }

    /// Frame `f`, returned by `poll_frames`, was acknowledged. A sending part's ack may end the
    /// stream, which is then removed (§4.4: flow control state is kept until then).
    pub fn on_frame_acked(&mut self, f: &Frame)
        requires
            old(self).wf(),
            !old(self).failed(),
        ensures
            final(self).wf(),
            !final(self).failed(),
            forall|j: u64| #[trigger] final(self).reset_code(j) == old(self).reset_code(j),
            forall|j: u64| #[trigger] final(self).rx_trace(j) == old(self).rx_trace(j),
            forall|j: u64| #[trigger] old(self).is_removed(j) ==> final(self).is_removed(j),
            // E5: a peer stream is re-credited only as this ack removes it.
            forall|b: bool| #[trigger]
                final(self).peer_closed(b) == old(self).peer_closed(b) || (final(self).peer_closed(
                    b,
                ) == old(self).peer_closed(b) + 1 && (frame_stream_id(f@) matches Some(id) && (id
                    % 4 == 0) == b && (id % 4 == 0 || id % 4 == 2) && final(self).is_removed(id)
                    && !old(self).is_removed(id))),
    {
        match f {
            Frame::Stream { stream_id, offset, data, fin } => {
                self.send_op(*stream_id, 0, *offset, data.len() as u64, *fin);
            },
            Frame::ResetStream { stream_id, .. } => {
                self.send_op(*stream_id, 1, 0, 0, false);
            },
            _ => {},
        }
    }

    /// Frame `f`, returned by `poll_frames`, was lost: lost STREAM bytes are queued again
    /// (unless the stream was reset since), RESET_STREAM and STOP_SENDING resent unchanged,
    /// and credit frames resent with the current value (§13.3).
    pub fn on_frame_lost(&mut self, f: &Frame)
        requires
            old(self).wf(),
            !old(self).failed(),
        ensures
            final(self).wf(),
            !final(self).failed(),
            forall|j: u64| #[trigger] final(self).reset_code(j) == old(self).reset_code(j),
            forall|j: u64| #[trigger] final(self).rx_trace(j) == old(self).rx_trace(j),
            forall|j: u64| #[trigger] final(self).is_removed(j) == old(self).is_removed(j),
    {
        let ghost s0 = *self;
        match f {
            Frame::Stream { stream_id, offset, data, fin } => {
                self.send_op(*stream_id, 2, *offset, data.len() as u64, *fin);
            },
            Frame::ResetStream { stream_id, .. } => {
                self.send_op(*stream_id, 3, 0, 0, false);
            },
            Frame::StopSending { stream_id, .. } => self.recv_lost(*stream_id, 2),
            Frame::MaxStreamData { stream_id, .. } => self.recv_lost(*stream_id, 3),
            Frame::MaxData(_) => {
                self.conn_recv.on_lost();
                proof {
                    assert(forall|j: u64| #[trigger] self.rx_trace(j) == s0.rx_trace(j));
                }
            },
            Frame::MaxStreams { bidi, .. } => {
                self.ids.max_streams_lost(*bidi);
                proof {
                    lemma_ids_frame(s0, *self);
                    assert(forall|j: u64| #[trigger] self.rx_trace(j) == s0.rx_trace(j));
                }
            },
            _ => {},
        }
    }

    /// `recv_op_at` on stream `id`'s entry, if it has one with a receiving part.
    fn recv_lost(&mut self, id: u64, op: u8)
        requires
            old(self).wf(),
            op == 2 || op == 3,
        ensures
            final(self).wf(),
            final(self).failed == old(self).failed,
            forall|j: u64| #[trigger] final(self).reset_code(j) == old(self).reset_code(j),
            forall|j: u64| #[trigger] final(self).rx_trace(j) == old(self).rx_trace(j),
            forall|j: u64| #[trigger] final(self).is_removed(j) == old(self).is_removed(j),
    {
        let ghost s0 = *self;
        if let Some(i) = self.find(id) {
            proof {
                assert(kept(s0, s0));
            }
            self.recv_op_at(i, op, Ghost(s0), Ghost(0), Ghost(Seq::<Frame>::empty()));
        }
    }

    /// An ack or loss on stream `id`'s sending part: op 0 data acked, 1 reset acked (each
    /// followed by `gc`), 2 data lost, 3 reset lost.
    fn send_op(&mut self, id: u64, op: u8, off: u64, len: u64, fin: bool)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).failed == old(self).failed,
            forall|j: u64| #[trigger] final(self).reset_code(j) == old(self).reset_code(j),
            forall|j: u64| #[trigger] final(self).rx_trace(j) == old(self).rx_trace(j),
            forall|j: u64| #[trigger] old(self).is_removed(j) ==> final(self).is_removed(j),
            op >= 2 ==> forall|j: u64|
                #[trigger] final(self).is_removed(j) == old(self).is_removed(j),
            forall|b: bool| #[trigger]
                final(self).peer_closed(b) == old(self).peer_closed(b) || (final(self).peer_closed(
                    b,
                ) == old(self).peer_closed(b) + 1 && (id % 4 == 0) == b && (id % 4 == 0 || id % 4
                    == 2) && final(self).is_removed(id) && !old(self).is_removed(id)),
    {
        let ghost s0 = *self;
        if let Some(i) = self.find(id) {
            let mut e = Entry { id: 0, recv: None, send: None };
            self.entries.set_and_swap(i, &mut e);
            proof {
                assert(entry_ok(e, s0.rx_bidi, s0.rx_uni));
            }
            if let Some(mut p) = e.send.take() {
                if op == 0 {
                    p.on_data_acked(off, len, fin);
                } else if op == 1 {
                    p.on_reset_acked();
                } else if op == 2 {
                    p.on_data_lost(off, len, fin);
                } else {
                    p.on_reset_lost();
                }
                e.send = Some(p);
            }
            let ghost ne = e;
            self.entries.set_and_swap(i, &mut e);
            proof {
                assert(self.entries@ == s0.entries@.update(i as int, ne));
                lemma_swap_same_rx(s0, *self, i as int, ne);
            }
            if op < 2 {
                self.gc(i);
            }
        }
    }
}

/// `lemma_swap` for an entry whose receiving part is unchanged and whose sending part kept its
/// bytes sent and its reset: no record changes.
proof fn lemma_swap_same_rx(s0: Streams, s1: Streams, i: int, ne: Entry)
    requires
        s0.wf(),
        0 <= i < s0.entries@.len(),
        ne.id == s0.entries@[i].id,
        ne.recv == s0.entries@[i].recv,
        ne.send is Some == s0.entries@[i].send is Some,
        ne.send matches Some(p) ==> p.wf() && p.sent_end() == s0.entries@[i].send->0.sent_end()
            && p.reset_spec() == s0.entries@[i].send->0.reset_spec(),
        s1.entries@ == s0.entries@.update(i, ne),
        s1 == (Streams { entries: s1.entries, ..s0 }),
    ensures
        s1.wf(),
        forall|j: u64| #[trigger] s1.rx_trace(j) == s0.rx_trace(j),
        ne.recv matches Some(r) ==> s1.rx_spec(ne.id) == r.rfc(),
        ne.recv is None ==> s1.rx_trace(ne.id) == s0.rx_trace(ne.id),
        s0.entries@[i].recv matches Some(r) ==> s0.rx_spec(ne.id) == r.rfc(),
        forall|k: int|
            0 <= k < s1.entries@.len() && k != i ==> #[trigger] s1.entries@[k] == s0.entries@[k],
{
    assert(entry_ok(s0.entries@[i], s0.rx_bidi, s0.rx_uni));
    if let Some(r) = ne.recv {
        assert(s0.rtr@.insert(ne.id, r.trace()) =~= s0.rtr@);
    }
    lemma_swap(s0, s1, i, ne);
}

/// Opening our next unidirectional stream `e` preserves the invariant.
proof fn lemma_push_local(s0: Streams, s1: Streams, e: Entry)
    requires
        s0.wf(),
        e.id % 4 == 3,
        !created(s0.ids, e.id),
        s1.ids.wf(),
        s1.ids.local_uni_created(e.id),
        s1.ids.local_uni_spec().used_spec() == e.id / 4 + 1,
        forall|x: u64| #[trigger] s0.ids.local_uni_created(x) ==> s1.ids.local_uni_created(x),
        forall|b: bool|
            {
                &&& #[trigger] s1.ids.peer_opened_spec(b) == s0.ids.peer_opened_spec(b)
                &&& s1.ids.peer_credit_spec(b) == s0.ids.peer_credit_spec(b)
            },
        e.recv is None,
        e.send matches Some(p) && p.wf() && p.reset_spec() is None && p.sent_end() == 0,
        s1.entries@ == s0.entries@.push(e),
        s1 == (Streams { entries: s1.entries, ids: s1.ids, ..s0 }),
    ensures
        s1.wf(),
        forall|j: u64| #[trigger] s1.rx_trace(j) == s0.rx_trace(j),
{
    let a = s0.entries@;
    let t = s1.entries@;
    s0.ids.lemma_wf();
    s1.ids.lemma_wf();
    lemma_sum_push(a, e, 0);
    lemma_sum_push(a, e, 1);
    lemma_sum_push(a, e, 4);
    lemma_sum_push(a, e, 6);
    lemma_sum_push(a, e, 8);
    assert(val(e, 0) == 0 && val(e, 1) == 0 && val(e, 4) == 0 && val(e, 6) == 0 && val(e, 8)
        == 0);
    assert(s1.ids.peer_credit_spec(true) == s0.ids.peer_credit_spec(true));
    assert(s1.ids.peer_credit_spec(false) == s0.ids.peer_credit_spec(false));
    assert forall|y: u64| #[trigger] s1.ids.peer_created(y) == s0.ids.peer_created(y) by {
        assert(s1.ids.peer_opened_spec(true) == s0.ids.peer_opened_spec(true));
        assert(s1.ids.peer_opened_spec(false) == s0.ids.peer_opened_spec(false));
    }
    assert forall|y: u64| #[trigger] created(s0.ids, y) implies created(s1.ids, y) by {}
    assert(!s0.resets@.contains_key(e.id));
    assert(!s0.rtr@.contains_key(e.id));
    assert forall|k: int| 0 <= k < a.len() implies (#[trigger] a[k]).id != e.id by {
        assert(created(s0.ids, a[k].id));
    }
    assert forall|k: int| 0 <= k < t.len() implies {
        &&& entry_ok(#[trigger] t[k], s1.rx_bidi, s1.rx_uni)
        &&& created(s1.ids, t[k].id)
        &&& !s1.removed@.contains(t[k].id)
        &&& (t[k].recv matches Some(r) ==> s1.rtr@.contains_key(t[k].id) && s1.rtr@[t[k].id]
            == r.trace())
        &&& (t[k].send matches Some(p) ==> (p.reset_spec() matches Some(c)
            ==> s1.resets@.contains_key(t[k].id) && s1.resets@[t[k].id] == c.0) && (
        s1.resets@.contains_key(t[k].id) ==> p.reset_spec() is Some))
    } by {
        if k < a.len() {
            assert(t[k] == a[k]);
        } else {
            assert(t[k] == e);
        }
    }
    assert forall|j: int, k: int|
        0 <= j < t.len() && 0 <= k < t.len() && j != k implies (#[trigger] t[j]).id != (
        #[trigger] t[k]).id by {
        if j < a.len() {
            assert(t[j] == a[j]);
        }
        if k < a.len() {
            assert(t[k] == a[k]);
        }
    }
    assert forall|y: u64| #[trigger]
        s1.rtr@.contains_key(y) && !s1.removed@.contains(y) implies has_id(t, y) by {
        let k = choose|k: int| 0 <= k < a.len() && (#[trigger] a[k]).id == y;
        assert(t[k] == a[k]);
    }
    assert forall|y: u64| #[trigger] s1.rtr@.contains_key(y) == s1.ids.peer_created(y) by {
        assert(s0.rtr@.contains_key(y) == s0.ids.peer_created(y));
    }
    assert forall|y: u64| #[trigger] s1.resets@.contains_key(y) implies created(s1.ids, y) by {
        assert(created(s0.ids, y));
    }
}

} // verus!
