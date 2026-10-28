//! A connection's streams (RFC 9000 §2–4). Each frame naming a stream is checked against the
//! stream's type and our limits, opens peer streams implicitly (§3.2), and goes to that stream's
//! receiving or sending part. Connection receive credit counts each stream's final size, or else
//! its high-water mark, exactly once (§4.5). Sans-IO.
use vstd::prelude::*;
use crate::codes::*;
use crate::flow::*;
use crate::frame::*;
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
        SpecFrame::StopSending { stream_id, error_code } => if s1.peer_stopped(stream_id)
            && !s0.peer_stopped(stream_id) {
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
    // Removal and STOP_SENDING records only grow, and only for the frame's stream.
    &&& forall|j: u64| #[trigger] s0.is_removed(j) ==> s1.is_removed(j)
    &&& forall|j: u64| #[trigger]
        s1.is_removed(j) && !s0.is_removed(j) ==> frame_stream_id(f) == Some(j)
    &&& forall|j: u64| #[trigger] s0.peer_stopped(j) ==> s1.peer_stopped(j)
    &&& forall|j: u64| #[trigger]
        s1.peer_stopped(j) && !s0.peer_stopped(j) ==> f is StopSending && frame_stream_id(f)
            == Some(j)
    // E5: a closed peer stream is re-credited only as its entry is removed.
    &&& forall|b: bool| #[trigger]
        s1.peer_closed(b) == s0.peer_closed(b) || (s1.peer_closed(b) == s0.peer_closed(b) + 1
            && (frame_stream_id(f) matches Some(id) && (id % 4 == 0) == b && (id % 4 == 0 || id
            % 4 == 2) && s1.is_removed(id) && !s0.is_removed(id)))
}

// ---- Sums over the entries ----

/// Per-entry quantities: 0 counted, 1 retired, 2 buffered, 3 physically buffered; 4 + k is 1
/// for a stream of type k.
spec fn val(e: Entry, q: int) -> int {
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
        q >= 4,
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
    stops: Map<u64, u64>,
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
        p.reset_spec() matches Some(c) ==> stops.contains_key(s[k].id) && stops[s[k].id] == c.0)
            && (stops.contains_key(s[k].id) ==> p.reset_spec() is Some))
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
    stops: Map<u64, u64>,
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
    &&& forall|id: u64| #[trigger] stops.contains_key(id) ==> created(ids, id)
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
    /// Our initial send limit on client bidi streams (`peer.initial_max_stream_data_bidi_local`).
    tx_bidi: u64,
    failed: bool,
    /// Every peer stream's receive trace, removed streams included.
    rtr: Ghost<Map<u64, Seq<SpecRecvIn>>>,
    /// Peer streams whose entry was removed.
    removed: Ghost<Set<u64>>,
    /// The peer's STOP_SENDING code, for each sending part it reset.
    stops: Ghost<Map<u64, u64>>,
    /// Σ counted (which equals Σ retired) over the removed streams.
    gone: Ghost<nat>,
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

    /// The peer's STOP_SENDING reset our sending part of stream `id`.
    pub closed spec fn peer_stopped(&self, id: u64) -> bool {
        self.stops@.contains_key(id)
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
            self.stops@,
        )
        &&& records_ok(
            self.entries@,
            self.ids,
            self.rx_bidi,
            self.rx_uni,
            self.rtr@,
            self.removed@,
            self.stops@,
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
            forall|id: u64| !#[trigger] r.peer_stopped(id),
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
            failed: false,
            rtr: Ghost(Map::empty()),
            removed: Ghost(Set::empty()),
            stops: Ghost(Map::empty()),
            gone: Ghost(0),
        };
        proof {
            r.ids.lemma_wf();
            assert(r.ids.peer_credit_spec(true).window_spec() == r.ids.peer_limit(true));
            assert(r.ids.peer_credit_spec(false).window_spec() == r.ids.peer_limit(false));
            assert forall|id: u64| #[trigger] r.rtr@.contains_key(id) == r.ids.peer_created(id) by {
                assert(r.ids.peer_opened_spec(true) == 0 && r.ids.peer_opened_spec(false) == 0);
            }
            assert forall|id: u64| #[trigger] r.stops@.contains_key(id) implies created(r.ids, id)
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
    pub fn open_streams(&self) -> usize {
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
        &&& self.failed == o.failed
        &&& self.removed == o.removed
        &&& self.stops == o.stops
        &&& self.gone == o.gone
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
            final(self).stops == old(self).stops,
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
            forall|j: u64| #[trigger] old(self).peer_stopped(j) ==> final(self).peer_stopped(j),
            forall|j: u64| #[trigger]
                final(self).peer_stopped(j) && !old(self).peer_stopped(j) ==> f@ is StopSending
                    && frame_stream_id(f@) == Some(j),
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
                    if p.on_stop_sending(*error_code) {
                        ev.push(StreamEvent::StopSending { id: *stream_id, code: *error_code });
                        self.stops = Ghost(self.stops@.insert(*stream_id, *error_code));
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
            lemma_update(s0, i as int, ne, s0.rtr@, self.stops@);
            lemma_sum_update(a, i as int, ne, 0);
            lemma_sum_update(a, i as int, ne, 1);
            lemma_sum_update(a, i as int, ne, 4);
            lemma_sum_update(a, i as int, ne, 6);
            let sp = s0.rx_spec(id);
            assert(sp.events.skip(sp.events.len() as int) =~= Seq::<SpecStreamEvent>::empty());
            if self.stops@ == s0.stops@ {
                assert(ev@ == ev0);
                assert(event_views(ev0) + Seq::<SpecStreamEvent>::empty() =~= event_views(ev0));
            } else {
                assert(event_views(ev@) =~= event_views(ev0).push(ev@.last()@));
            }
        }
    }

    /// Removes entry `i` once all its parts are terminal; a removed peer stream is re-credited
    /// (MAX_STREAMS), and its buffers are dropped.
    fn gc(&mut self, i: usize)
        requires
            old(self).wf(),
            i < old(self).entries@.len(),
        ensures
            final(self).wf(),
            final(self).same_traces(*old(self)),
            final(self).stops == old(self).stops,
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
                lemma_sum_kind_nonneg(a.remove(i as int), 4);
                lemma_sum_kind_nonneg(a.remove(i as int), 6);
                if let Some(r) = e.recv {
                    r.lemma_wf();
                }
            }
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
            &&& entries_ok(t, s0.ids, s0.rx_bidi, s0.rx_uni, rtr, s0.removed@, s0.stops@)
            &&& records_ok(t, s0.ids, s0.rx_bidi, s0.rx_uni, rtr, s0.removed@, s0.stops@)
            &&& s0.conn_counted + n == s0.gone@ + sum(t, 0)
            &&& sum(t, 1) == sum(s0.entries@, 1) - val(s0.entries@[i], 1) + val(ne, 1)
            &&& sum(t, 1) <= sum(t, 0)
            &&& sum(t, 4) == sum(s0.entries@, 4)
            &&& sum(t, 6) == sum(s0.entries@, 6)
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
    lemma_update(s0, i, ne, s0.rtr@.insert(ne.id, ne.recv->0.trace()), s0.stops@);
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
    &&& a.stops == b.stops
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
        post_rest(s1, s2, f, ev0, ev1, r),
    ensures
        post_rest(s0, s2, f, ev0, ev1, r),
        rx_outcome(s1, f) == rx_outcome(s0, f),
{
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
    assert forall|j: u64| #[trigger] s0.peer_stopped(j) implies s2.peer_stopped(j) by {
        assert(s1.peer_stopped(j));
    }
    assert forall|j: u64| #[trigger] s2.peer_stopped(j) && !s0.peer_stopped(j) implies f
        is StopSending && frame_stream_id(f) == Some(j) by {
        assert(!s1.peer_stopped(j));
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
    assert forall|j: u64| #[trigger] s0.peer_stopped(j) implies s2.peer_stopped(j) by {
        assert(s1.peer_stopped(j));
    }
    assert forall|j: u64| #[trigger] s2.peer_stopped(j) && !s0.peer_stopped(j) implies f
        is StopSending && frame_stream_id(f) == Some(j) by {
        assert(s1.peer_stopped(j));
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
        s2.stops == s1.stops,
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
    assert forall|j: u64| #[trigger] s0.peer_stopped(j) implies s2.peer_stopped(j) by {
        assert(s1.peer_stopped(j));
    }
    assert forall|j: u64| #[trigger] s2.peer_stopped(j) && !s0.peer_stopped(j) implies f
        is StopSending && frame_stream_id(f) == Some(j) by {
        assert(s1.peer_stopped(j));
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
                &&& s1.ids.peer_credit_spec(b) == s0.ids.peer_credit_spec(b)
            },
        s1.ids.local_uni_spec().used_spec() == s0.ids.local_uni_spec().used_spec(),
        s1 == (Streams { ids: s1.ids, ..s0 }),
    ensures
        s1.wf(),
{
    s0.ids.lemma_wf();
    s1.ids.lemma_wf();
    assert(s1.ids.peer_credit_spec(true) == s0.ids.peer_credit_spec(true));
    assert(s1.ids.peer_credit_spec(false) == s0.ids.peer_credit_spec(false));
    assert(forall|y: u64| #[trigger] s1.ids.peer_created(y) == s0.ids.peer_created(y));
    assert forall|y: u64| #[trigger] created(s1.ids, y) == created(s0.ids, y) by {}
}

/// Entry `i` replaced by `ne`, with the same ID, the trace record following its receiving part
/// and the STOP_SENDING record its sending part: the entry invariants still hold.
proof fn lemma_update(
    s0: Streams,
    i: int,
    ne: Entry,
    rtr: Map<u64, Seq<SpecRecvIn>>,
    stops: Map<u64, u64>,
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
        forall|y: u64| y != ne.id ==> #[trigger] stops.contains_key(y) == s0.stops@.contains_key(y)
            && stops[y] == s0.stops@[y],
        s0.stops@.contains_key(ne.id) ==> stops.contains_key(ne.id),
        ne.send matches Some(p) ==> (p.reset_spec() matches Some(c) ==> stops.contains_key(ne.id)
            && stops[ne.id] == c.0) && (stops.contains_key(ne.id) ==> p.reset_spec() is Some),
        ne.recv matches Some(r) ==> s0.removed@.contains(ne.id) ==> removed_ok(r.rfc()),
    ensures
        entries_ok(
            s0.entries@.update(i, ne),
            s0.ids,
            s0.rx_bidi,
            s0.rx_uni,
            rtr,
            s0.removed@,
            stops,
        ),
        records_ok(
            s0.entries@.update(i, ne),
            s0.ids,
            s0.rx_bidi,
            s0.rx_uni,
            rtr,
            s0.removed@,
            stops,
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
        &&& (t[k].send matches Some(p) ==> (p.reset_spec() matches Some(c) ==> stops.contains_key(
            t[k].id,
        ) && stops[t[k].id] == c.0) && (stops.contains_key(t[k].id) ==> p.reset_spec() is Some))
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
    assert forall|y: u64| #[trigger] stops.contains_key(y) implies created(s0.ids, y) by {
        if y == id {
            assert(created(s0.ids, a[i].id));
        }
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
        s1.failed == s0.failed,
        s1.rtr == s0.rtr,
        s1.stops == s0.stops,
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
            ==> s1.stops@.contains_key(t[k].id) && s1.stops@[t[k].id] == c.0) && (
        s1.stops@.contains_key(t[k].id) ==> p.reset_spec() is Some))
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
    assert forall|y: u64| #[trigger] s1.stops@.contains_key(y) implies created(s1.ids, y) by {
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
        e.send matches Some(p) ==> p.wf() && p.reset_spec() is None,
        s1.entries@ == s0.entries@.push(e),
        s1.rtr@ == s0.rtr@.insert(x, Seq::<SpecRecvIn>::empty()),
        s1.conn_recv == s0.conn_recv,
        s1.conn_counted == s0.conn_counted,
        s1.conn_send == s0.conn_send,
        s1.rx_bidi == s0.rx_bidi,
        s1.rx_uni == s0.rx_uni,
        s1.tx_bidi == s0.tx_bidi,
        s1.failed == s0.failed,
        s1.removed == s0.removed,
        s1.stops == s0.stops,
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
    assert(val(e, kq(b)) == 1 && val(e, kq(!b)) == 0);
    lemma_sum_push(a, e, 0);
    lemma_sum_push(a, e, 1);
    lemma_sum_push(a, e, 2);
    lemma_sum_push(a, e, 3);
    lemma_sum_push(a, e, 4);
    lemma_sum_push(a, e, 6);
    // Created before means a lower ID of this type, or another type.
    assert forall|y: u64| #[trigger] created(s0.ids, y) implies created(s1.ids, y) && y != x by {}
    assert forall|y: u64| #[trigger] s1.ids.peer_created(y) == (s0.ids.peer_created(y) || y == x)
        by {}
    assert(!s0.rtr@.contains_key(x));
    assert(!s0.removed@.contains(x));
    assert(!s0.stops@.contains_key(x));
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
            ==> s1.stops@.contains_key(t[k].id) && s1.stops@[t[k].id] == c.0) && (
        s1.stops@.contains_key(t[k].id) ==> p.reset_spec() is Some))
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

} // verus!
