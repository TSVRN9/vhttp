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
//!   that is never transmitted is reported lost at once. For STREAM pieces this is proved, not
//!   only stated: `poll_frames` ensures each stream's `tx_flight` gains exactly the pieces it returns
//!   (`tx_gained`), `on_frame_acked`/`on_frame_lost` require the piece in flight unless the part was
//!   reset (`piece_in_flight`), and `Connection::wf`'s `pieces_ok` ties them (9b2 D10 (b)).
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
//! - **Send-range memory is proved:** a sending part's acked, lost and in-flight sets hold at most
//!   `⌊W/256⌋ + 4` nodes, `W` its bytes buffered (`SendStream::wf` from piece edges, 9b2 D10 (d),
//!   (f)), so at most `4096 + 4·103` nodes per connection under `MAX_SEND_BUFFER`. The
//!   `MAX_SEND_RANGES` gate in `SendStream::poll_data` only throttles new data.
//! - **Flush points:** `write` never flushes; under `FLOOR` (256) bytes unsent, new bytes wait for
//!   `flush(id)` (`Connection::stream_write` flushes every write it takes whole).
//! - **Loop on `poll_data`, not `next_off`.** `next_off()` returning `Some` does not mean
//!   `poll_data` sends anything (stream or connection credit may be 0); a
//!   `while next_off().is_some()` loop spins forever on a blocked stream.
//!
//! Enforced here since Phase 3d (former caller obligations):
//! - **Our own uni streams:** at most `MAX_OWN_UNI` (3), in `StreamIds::wf`; `write` refuses a
//!   fourth (`uni_openable`).
//! - **Write backpressure:** Σ send-queue reservations (`max(128, 6·peak)` per non-empty queue,
//!   which bounds its buffers) ≤ `MAX_SEND_BUFFER` (1 MiB) is in `wf`; `write` fails, changing
//!   nothing, beyond `send_room(id)`.
//! - **Receive window pinned (3d D8):** every mutator keeps the connection window at
//!   `initial_max_data`, and `lemma_wf` bounds receive memory (ring positions) by the window plus
//!   two pages per stream (9b2 D11).
use vstd::prelude::*;
// Used only in ghost code, which a plain `cargo build` erases.
#[allow(unused_imports)]
use vstd::multiset::Multiset;
use crate::codes::*;
use crate::flow::*;
use crate::frame::*;
// `PacketKind` and `frame_permitted` appear only in contracts, which a plain `cargo build` erases.
#[allow(unused_imports)]
use crate::payload::*;
use crate::idq::*;
use crate::recv_stream::*;
// Used only in contracts and ghost code, which a plain `cargo build` erases.
#[allow(unused_imports)]
use crate::ring::*;
#[allow(unused_imports)]
use crate::reassembly::*;
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
    /// The id is in `Streams::q` (9b2 D13): set when bytes or the FIN are left to deliver, cleared
    /// only by `deliver_some` as it pops the id.
    queued: bool,
}

// ponytail: matches the linear-scan bound above; raise both together.
/// The most peer streams of each type we let the peer have open (our `initial_max_streams_*`).
pub const MAX_LOCAL_STREAMS: u64 = 100;

// ponytail: one 1 MiB send budget per connection; per-stream budgets if one response must not starve others.
/// The most bytes all send buffers of a connection hold together.
pub const MAX_SEND_BUFFER: u64 = 1 << 20;

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

/// The receiving-part inputs a STREAM or RESET_STREAM frame gives: STREAM's data, then a delivery
/// of at most its length (9b2 D12: no frame hands over more bytes than it carries; `deliver_some`
/// hands over the rest); RESET_STREAM's reset.
pub open spec fn frame_recv_ins(f: SpecFrame) -> Seq<SpecRecvIn> {
    match f {
        SpecFrame::Stream { offset, data, fin, .. } => seq![
            SpecRecvIn::Data { off: offset as nat, data, fin },
            SpecRecvIn::Deliver { max: data.len() },
        ],
        SpecFrame::ResetStream { error_code, final_size, .. } => seq![
            SpecRecvIn::Reset { code: error_code, final_size: final_size as nat },
        ],
        _ => Seq::empty(),
    }
}

/// The receive trace of stream `j` after one frame: the frame's inputs appended, for its own
/// stream unless that stream was removed.
pub open spec fn rx_trace_after(s0: Streams, f: SpecFrame, r: Result<(), u64>, j: u64) -> Seq<
    SpecRecvIn,
> {
    if r is Ok && frame_stream_id(f) == Some(j) && frame_recv_in(f) is Some && !s0.is_removed(j) {
        s0.rx_trace(j) + frame_recv_ins(f)
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
    // D10 (b): no unreset stream's flight changes; a STOP_SENDING's stream is reset, a new one's flight empty.
    &&& tx_kept_but(s0, s1, None)
    // E5: a closed peer stream is re-credited only as its entry is removed.
    &&& forall|b: bool| #[trigger]
        s1.peer_closed(b) == s0.peer_closed(b) || (s1.peer_closed(b) == s0.peer_closed(b) + 1
            && (frame_stream_id(f) matches Some(id) && (id % 4 == 0) == b && (id % 4 == 0 || id
            % 4 == 2) && s1.is_removed(id) && !s0.is_removed(id)))
}

// ---- Pieces in flight (D10 (b)) ----

/// A piece's key: CRYPTO `None`, STREAM its stream; and the piece `(start, end)`.
pub type PieceKey = (Option<u64>, (u64, u64));

/// Each stream id's reset flag and pieces in flight: what conn's `pieces_ok` reads of `Streams`.
pub type TxView = spec_fn(u64) -> (bool, Set<(u64, u64)>);

/// The key of a data frame whose end passes `VARINT_MAX`: no frame sent has one, so none is counted.
pub open spec fn bad_piece() -> (u64, u64) {
    (0, 0)
}

/// Bytes `[off, off + len)` as a piece, `bad_piece()` past `VARINT_MAX`.
pub open spec fn span(off: u64, len: nat) -> (u64, u64) {
    if off + len <= VARINT_MAX {
        (off, (off + len) as u64)
    } else {
        bad_piece()
    }
}

/// A frame's piece: CRYPTO and STREAM frames with data have one, keyed by their target.
pub open spec fn piece_of(f: SpecFrame) -> Option<PieceKey> {
    match f {
        SpecFrame::Crypto { offset, data } => if data.len() > 0 {
            Some((None, span(offset, data.len())))
        } else {
            None
        },
        SpecFrame::Stream { stream_id, offset, data, .. } => if data.len() > 0 {
            Some((Some(stream_id), span(offset, data.len())))
        } else {
            None
        },
        _ => None,
    }
}

pub open spec fn ms_of(k: Option<PieceKey>) -> Multiset<PieceKey> {
    match k {
        Some(k) => Multiset::singleton(k),
        None => Multiset::empty(),
    }
}

/// The pieces of `sf`, counted.
#[verifier::opaque]
pub open spec fn frame_pieces(sf: Seq<SpecFrame>) -> Multiset<PieceKey>
    decreases sf.len(),
{
    if sf.len() == 0 {
        Multiset::empty()
    } else {
        frame_pieces(sf.drop_last()).add(ms_of(piece_of(sf.last())))
    }
}

/// 1 if `p` is in `f`.
pub open spec fn ind(f: Set<(u64, u64)>, p: (u64, u64)) -> nat {
    if f.contains(p) {
        1
    } else {
        0
    }
}

/// `s1`'s pieces in flight are `s0`'s and, per stream, exactly `new`'s, each once and fresh; `new` holds no CRYPTO
/// or out-of-range piece (`poll_frames`, D10 (b)).
pub open spec fn tx_gained(s0: Streams, s1: Streams, new: Seq<SpecFrame>) -> bool {
    &&& forall|j: u64, q: (u64, u64)|
        q != bad_piece() ==> #[trigger] frame_pieces(new).count((Some(j), q)) + ind(s0.tx_flight(j), q) == ind(
            s1.tx_flight(j),
            q,
        )
    &&& forall|q: (u64, u64)| #[trigger] frame_pieces(new).count((None, q)) == 0
    &&& forall|k: Option<u64>| #[trigger] frame_pieces(new).count((k, bad_piece())) == 0
}

/// A STREAM frame with data whose part `s` has not reset: its piece is in flight there, and in range (D10 (b)).
pub open spec fn piece_in_flight(s: Streams, f: SpecFrame) -> bool {
    match f {
        SpecFrame::Stream { stream_id, offset, data, .. } => data.len() > 0 && !s.send_reset(stream_id) ==> offset
            + data.len() <= VARINT_MAX && s.tx_flight(stream_id).contains((offset, (offset + data.len()) as u64)),
        _ => true,
    }
}

/// That piece left the flight from `s0` to `s1`.
pub open spec fn piece_removed(s0: Streams, s1: Streams, f: SpecFrame) -> bool {
    match f {
        SpecFrame::Stream { stream_id, offset, data, .. } => data.len() > 0 && !s0.send_reset(stream_id) ==> s1.tx_flight(
            stream_id,
        ) == s0.tx_flight(stream_id).remove((offset, (offset + data.len()) as u64)),
        _ => true,
    }
}

/// The stream whose piece frame `f` carries, if it is a STREAM frame with data.
pub open spec fn piece_stream(f: SpecFrame) -> Option<u64> {
    match piece_of(f) {
        Some((Some(id), _)) => Some(id),
        _ => None,
    }
}

/// Every stream other than `j` that `s1` has not reset has `s0`'s flight and reset flag (D10 (b); re-review F2).
pub open spec fn tx_kept_but(s0: Streams, s1: Streams, j: Option<u64>) -> bool {
    forall|id: u64|
        Some(id) != j && !#[trigger] s1.send_reset(id) ==> s1.tx_flight(id) == s0.tx_flight(id) && s1.send_reset(id)
            == s0.send_reset(id)
}

#[verifier::spinoff_prover]
pub proof fn lemma_frame_pieces_push(sf: Seq<SpecFrame>, f: SpecFrame)
    ensures
        frame_pieces(sf.push(f)) == frame_pieces(sf).add(ms_of(piece_of(f))),
{
    reveal(frame_pieces);
    assert(sf.push(f).drop_last() =~= sf);
}

#[verifier::spinoff_prover]
pub proof fn lemma_frame_pieces_add(a: Seq<SpecFrame>, b: Seq<SpecFrame>)
    ensures
        frame_pieces(a + b) == frame_pieces(a).add(frame_pieces(b)),
    decreases b.len(),
{
    broadcast use vstd::multiset::group_multiset_axioms;
    reveal(frame_pieces);
    if b.len() == 0 {
        assert(a + b =~= a);
        assert(frame_pieces(a).add(frame_pieces(b)) =~= frame_pieces(a));
    } else {
        lemma_frame_pieces_add(a, b.drop_last());
        assert((a + b).drop_last() =~= a + b.drop_last());
        assert((a + b).last() == b.last());
        assert(frame_pieces(a + b) =~= frame_pieces(a).add(frame_pieces(b)));
    }
}

/// No frame of `sf` has a piece.
#[verifier::spinoff_prover]
pub proof fn lemma_frame_pieces_none(sf: Seq<SpecFrame>)
    requires
        forall|i: int| 0 <= i < sf.len() ==> piece_of(#[trigger] sf[i]) is None,
    ensures
        frame_pieces(sf) == Multiset::<PieceKey>::empty(),
    decreases sf.len(),
{
    broadcast use vstd::multiset::group_multiset_axioms;
    reveal(frame_pieces);
    if sf.len() > 0 {
        let p = sf.drop_last();
        assert forall|i: int| 0 <= i < p.len() implies piece_of(#[trigger] p[i]) is None by {
            assert(p[i] == sf[i]);
        }
        lemma_frame_pieces_none(p);
        assert(piece_of(sf[sf.len() - 1]) is None);
        assert(frame_pieces(sf) =~= Multiset::<PieceKey>::empty());
    }
}

/// `f1` is `f0` with `new`'s pieces, all of stream `id`, each fresh and once; none out of range.
spec fn gained(f0: Set<(u64, u64)>, f1: Set<(u64, u64)>, new: Seq<SpecFrame>, id: u64) -> bool {
    &&& forall|q: (u64, u64)|
        q != bad_piece() ==> #[trigger] frame_pieces(new).count((Some(id), q)) + ind(f0, q) == ind(f1, q)
    &&& forall|k: Option<u64>, q: (u64, u64)| k != Some(id) ==> #[trigger] frame_pieces(new).count((k, q)) == 0
    &&& forall|k: Option<u64>| #[trigger] frame_pieces(new).count((k, bad_piece())) == 0
}

#[verifier::spinoff_prover]
proof fn lemma_gained_empty(f: Set<(u64, u64)>, id: u64)
    ensures
        gained(f, f, Seq::empty(), id),
{
    broadcast use vstd::multiset::group_multiset_axioms;
    reveal(frame_pieces);
}

/// One STREAM frame of stream `id` that `poll_data` returned: its piece, if it has data, joined flight fresh.
#[verifier::spinoff_prover]
proof fn lemma_gained_one(f0: Set<(u64, u64)>, f1: Set<(u64, u64)>, g: SpecFrame, id: u64)
    requires
        g matches SpecFrame::Stream { stream_id, offset, data, .. } && stream_id == id && offset + data.len()
            <= VARINT_MAX && (data.len() == 0 ==> f1 == f0) && (data.len() > 0 ==> f1 == f0.insert(
            (offset, (offset + data.len()) as u64),
        ) && !f0.contains((offset, (offset + data.len()) as u64))),
    ensures
        gained(f0, f1, seq![g], id),
{
    broadcast use vstd::multiset::group_multiset_axioms;
    lemma_frame_pieces_push(Seq::empty(), g);
    reveal(frame_pieces);
    assert(seq![g] =~= Seq::<SpecFrame>::empty().push(g));
    assert(frame_pieces(Seq::<SpecFrame>::empty()) == Multiset::<PieceKey>::empty());
    if let SpecFrame::Stream { offset, data, .. } = g {
        if data.len() > 0 {
            assert(offset < (offset + data.len()) as u64);
        }
    }
}

#[verifier::spinoff_prover]
proof fn lemma_gained_trans(
    f0: Set<(u64, u64)>,
    f1: Set<(u64, u64)>,
    f2: Set<(u64, u64)>,
    a: Seq<SpecFrame>,
    b: Seq<SpecFrame>,
    id: u64,
)
    requires
        gained(f0, f1, a, id),
        gained(f1, f2, b, id),
    ensures
        gained(f0, f2, a + b, id),
{
    broadcast use vstd::multiset::group_multiset_axioms;
    lemma_frame_pieces_add(a, b);
    assert forall|q: (u64, u64)| q != bad_piece() implies #[trigger] frame_pieces(a + b).count((Some(id), q)) + ind(
        f0,
        q,
    ) == ind(f2, q) by {
        assert(frame_pieces(a).count((Some(id), q)) + ind(f0, q) == ind(f1, q));
        assert(frame_pieces(b).count((Some(id), q)) + ind(f1, q) == ind(f2, q));
    }
    assert forall|k: Option<u64>, q: (u64, u64)| k != Some(id) implies #[trigger] frame_pieces(a + b).count((k, q))
        == 0 by {
        assert(frame_pieces(a).count((k, q)) == 0 && frame_pieces(b).count((k, q)) == 0);
    }
    assert forall|k: Option<u64>| #[trigger] frame_pieces(a + b).count((k, bad_piece())) == 0 by {
        assert(frame_pieces(a).count((k, bad_piece())) == 0 && frame_pieces(b).count((k, bad_piece())) == 0);
    }
}

#[verifier::spinoff_prover]
proof fn lemma_tx_gained_trans(s0: Streams, s1: Streams, s2: Streams, a: Seq<SpecFrame>, b: Seq<SpecFrame>)
    requires
        tx_gained(s0, s1, a),
        tx_gained(s1, s2, b),
    ensures
        tx_gained(s0, s2, a + b),
{
    broadcast use vstd::multiset::group_multiset_axioms;
    lemma_frame_pieces_add(a, b);
    assert forall|j: u64, q: (u64, u64)| q != bad_piece() implies #[trigger] frame_pieces(a + b).count((Some(j), q))
        + ind(s0.tx_flight(j), q) == ind(s2.tx_flight(j), q) by {
        assert(frame_pieces(a).count((Some(j), q)) + ind(s0.tx_flight(j), q) == ind(s1.tx_flight(j), q));
        assert(frame_pieces(b).count((Some(j), q)) + ind(s1.tx_flight(j), q) == ind(s2.tx_flight(j), q));
    }
    assert forall|q: (u64, u64)| #[trigger] frame_pieces(a + b).count((None, q)) == 0 by {
        assert(frame_pieces(a).count((None, q)) == 0 && frame_pieces(b).count((None, q)) == 0);
    }
    assert forall|k: Option<u64>| #[trigger] frame_pieces(a + b).count((k, bad_piece())) == 0 by {
        assert(frame_pieces(a).count((k, bad_piece())) == 0 && frame_pieces(b).count((k, bad_piece())) == 0);
    }
}

/// Entry `i`'s sending part gained `new`'s pieces; every other entry as before.
#[verifier::spinoff_prover]
proof fn lemma_tx_gained_at(s1: Streams, s2: Streams, i: int, ne: Entry, new: Seq<SpecFrame>)
    requires
        s1.wf(),
        s2.wf(),
        0 <= i < s1.entries@.len(),
        ne.id == s1.entries@[i].id,
        s2.entries@ == s1.entries@.update(i, ne),
        s1.entries@[i].send is Some,
        ne.send is Some,
        gained(s1.entries@[i].send->0.flight_spec(), ne.send->0.flight_spec(), new, ne.id),
    ensures
        tx_gained(s1, s2, new),
{
    lemma_part_at(s1, i);
    lemma_part_at(s2, i);
    assert(s2.entries@[i] == ne);
    assert forall|j: u64, q: (u64, u64)| q != bad_piece() implies #[trigger] frame_pieces(new).count((Some(j), q))
        + ind(s1.tx_flight(j), q) == ind(s2.tx_flight(j), q) by {
        if j != ne.id {
            lemma_part_other(s1, s2, i, j);
            assert(frame_pieces(new).count((Some(j), q)) == 0);
        }
    }
    assert forall|q: (u64, u64)| #[trigger] frame_pieces(new).count((None, q)) == 0 by {
        assert(None::<u64> != Some(ne.id));
    }
}

/// `c` extends `b`, which extends `a`: `c`'s frames past `a` are `b`'s past `a`, then `c`'s past `b`.
#[verifier::spinoff_prover]
proof fn lemma_skip_split(a: Seq<Frame>, b: Seq<Frame>, c: Seq<Frame>)
    requires
        a.len() <= b.len() <= c.len(),
        b.subrange(0, a.len() as int) == a,
        c.subrange(0, b.len() as int) == b,
    ensures
        frames_view(c.skip(a.len() as int)) == frames_view(b.skip(a.len() as int)) + frames_view(
            c.skip(b.len() as int),
        ),
        c.subrange(0, a.len() as int) == a,
{
    assert forall|k: int| 0 <= k < b.len() implies #[trigger] c[k] == b[k] by {
        assert(c.subrange(0, b.len() as int)[k] == c[k]);
    }
    assert(c.subrange(0, a.len() as int) =~= a);
    assert(frames_view(c.skip(a.len() as int)) =~= frames_view(b.skip(a.len() as int)) + frames_view(
        c.skip(b.len() as int),
    ));
}

/// `send_op`'s swap at entry `i` (ID `id`): the acked or lost piece left that part's flight; no other changed.
#[verifier::spinoff_prover]
proof fn lemma_send_op_flight(s0: Streams, s1: Streams, i: int, e0: Entry, ne: Entry, op: u8, off: u64, len: u64)
    requires
        s0.wf(),
        s1.wf(),
        0 <= i < s0.entries@.len(),
        e0 == s0.entries@[i],
        ne.id == e0.id,
        s1.entries@ == s0.entries@.update(i, ne),
        s1.resets == s0.resets,
        e0.send is None ==> ne.send is None,
        e0.send matches Some(p0) ==> ne.send matches Some(p1) && ((op == 0 || op == 2) && len > 0 && !is_reset(
            p0.state(),
        ) && p0.in_flight(off, len) ==> p1.flight_spec() == p0.flight_spec().remove((off, (off + len) as u64))) && (
        !((op == 0 || op == 2) && len > 0) ==> p1.flight_spec() == p0.flight_spec()) && p1.reset_spec()
            == p0.reset_spec(),
        (op == 0 || op == 2) && len > 0 && !s0.send_reset(e0.id) ==> off + len <= VARINT_MAX && s0.tx_flight(
            e0.id,
        ).contains((off, (off + len) as u64)),
    ensures
        (op == 0 || op == 2) && len > 0 && !s0.send_reset(e0.id) ==> s1.tx_flight(e0.id) == s0.tx_flight(e0.id).remove(
            (off, (off + len) as u64),
        ),
        tx_kept_but(
            s0,
            s1,
            if (op == 0 || op == 2) && len > 0 {
                Some(e0.id)
            } else {
                None
            },
        ),
{
    let id = e0.id;
    lemma_part_at(s0, i);
    lemma_part_at(s1, i);
    assert(s1.entries@[i] == ne);
    assert(entry_ok(e0, s0.rx_bidi, s0.rx_uni));
    if let Some(p0) = e0.send {
        p0.lemma_wf();
        p0.lemma_in_flight(off, len);
        assert(p0.reset_spec() is Some <==> is_reset(p0.state()));
    }
    assert forall|j: u64| j != id implies #[trigger] s1.tx_flight(j) == s0.tx_flight(j) by {
        lemma_part_other(s0, s1, i, j);
    }
}

/// A swap at entry `i`: its part's flight kept unless the part is now reset, every other entry kept.
#[verifier::spinoff_prover]
proof fn lemma_swap_flight(s0: Streams, s1: Streams, i: int, ne: Entry)
    requires
        s0.wf(),
        s1.wf(),
        0 <= i < s0.entries@.len(),
        ne.id == s0.entries@[i].id,
        s1.entries@ == s0.entries@.update(i, ne),
        forall|j: u64| #[trigger] s0.send_reset(j) ==> s1.send_reset(j),
        forall|j: u64| j != ne.id ==> #[trigger] s1.send_reset(j) == s0.send_reset(j),
        s1.send_reset(ne.id) || sflight(ne) == sflight(s0.entries@[i]),
    ensures
        tx_kept_but(s0, s1, None),
{
    lemma_part_at(s0, i);
    lemma_part_at(s1, i);
    assert(s1.entries@[i] == ne);
    assert forall|j: u64| !#[trigger] s1.send_reset(j) implies s1.tx_flight(j) == s0.tx_flight(j) && s1.send_reset(j)
        == s0.send_reset(j) by {
        if j != ne.id {
            lemma_part_other(s0, s1, i, j);
        }
    }
}

/// A pushed entry whose part, if any, has nothing in flight: every flight as before.
#[verifier::spinoff_prover]
proof fn lemma_push_flight(s0: Streams, s1: Streams, e: Entry)
    requires
        s0.wf(),
        s1.wf(),
        s1.entries@ == s0.entries@.push(e),
        e.send matches Some(p) ==> p.flight_spec() == Set::<(u64, u64)>::empty(),
    ensures
        forall|j: u64| #[trigger] s1.tx_flight(j) == s0.tx_flight(j),
{
    let n = s0.entries@.len() as int;
    lemma_part_at(s1, n);
    assert(s1.entries@[n] == e);
    assert(!has_id(s0.entries@, e.id)) by {
        if has_id(s0.entries@, e.id) {
            let k = choose|k: int| 0 <= k < s0.entries@.len() && (#[trigger] s0.entries@[k]).id == e.id;
            assert(s1.entries@[k] == s0.entries@[k]);
        }
    }
    assert forall|j: u64| #[trigger] s1.tx_flight(j) == s0.tx_flight(j) by {
        if j != e.id && has_id(s1.entries@, j) {
            let k = choose|k: int| 0 <= k < s1.entries@.len() && (#[trigger] s1.entries@[k]).id == j;
            assert(k < n);
            assert(s1.entries@[k] == s0.entries@[k]);
            lemma_part_at(s1, k);
            lemma_part_at(s0, k);
        } else if j != e.id && has_id(s0.entries@, j) {
            let k = choose|k: int| 0 <= k < s0.entries@.len() && (#[trigger] s0.entries@[k]).id == j;
            assert(s1.entries@[k] == s0.entries@[k]);
        }
    }
}

/// Every flight and reset code as before: `tx_kept_but(.., None)`.
proof fn lemma_kept_of_flights(s0: Streams, s1: Streams)
    requires
        forall|j: u64| #[trigger] s1.tx_flight(j) == s0.tx_flight(j),
        forall|j: u64| #[trigger] s1.reset_code(j) == s0.reset_code(j),
    ensures
        tx_kept_but(s0, s1, None),
        forall|j: u64| #[trigger] s1.send_reset(j) == s0.send_reset(j),
{
    assert forall|j: u64| #[trigger] s1.send_reset(j) == s0.send_reset(j) by {
        assert(s1.reset_code(j) == s0.reset_code(j));
    }
}

/// `gc` removed entry `i`, terminal in both parts: no unreset stream's flight changed (a Data Recvd part's is empty).
#[verifier::spinoff_prover]
proof fn lemma_gc_flight(s0: Streams, s1: Streams, i: int)
    requires
        s0.wf(),
        s1.wf(),
        0 <= i < s0.entries@.len(),
        s1.entries@ == s0.entries@.remove(i),
        s1.resets == s0.resets,
        s0.entries@[i].send matches Some(p) ==> p.state() is DataRecvd || p.state() is ResetRecvd,
    ensures
        tx_kept_but(s0, s1, None),
{
    let a = s0.entries@;
    let id = a[i].id;
    assert forall|j: u64| !#[trigger] s1.send_reset(j) implies s1.tx_flight(j) == s0.tx_flight(j) && s1.send_reset(j)
        == s0.send_reset(j) by {
        if j == id {
            assert(!has_id(s1.entries@, id)) by {
                if has_id(s1.entries@, id) {
                    let k = choose|k: int| 0 <= k < s1.entries@.len() && (#[trigger] s1.entries@[k]).id == id;
                    if k < i {
                        assert(s1.entries@[k] == a[k]);
                    } else {
                        assert(s1.entries@[k] == a[k + 1]);
                    }
                }
            }
            lemma_part_at(s0, i);
            assert(entry_ok(a[i], s0.rx_bidi, s0.rx_uni));
            if let Some(p) = a[i].send {
                p.lemma_wf();
                p.lemma_flight_idle();
            }
        } else if has_id(s1.entries@, j) {
            let k = choose|k: int| 0 <= k < s1.entries@.len() && (#[trigger] s1.entries@[k]).id == j;
            lemma_part_at(s1, k);
            if k < i {
                assert(s1.entries@[k] == a[k]);
                lemma_part_at(s0, k);
            } else {
                assert(s1.entries@[k] == a[k + 1]);
                lemma_part_at(s0, k + 1);
            }
        } else if has_id(a, j) {
            let k = choose|k: int| 0 <= k < a.len() && (#[trigger] a[k]).id == j;
            assert(k != i);
            if k < i {
                assert(s1.entries@[k] == a[k]);
            } else {
                assert(s1.entries@[k - 1] == a[k]);
            }
        }
    }
}

/// Every flight as before, and no piece in `new`.
#[verifier::spinoff_prover]
proof fn lemma_tx_gained_same(s0: Streams, s1: Streams, new: Seq<SpecFrame>)
    requires
        forall|j: u64| #[trigger] s1.tx_flight(j) == s0.tx_flight(j),
        frame_pieces(new) == Multiset::<PieceKey>::empty(),
    ensures
        tx_gained(s0, s1, new),
{
    broadcast use vstd::multiset::group_multiset_axioms;
    assert forall|j: u64, q: (u64, u64)| q != bad_piece() implies #[trigger] frame_pieces(new).count((Some(j), q))
        + ind(s0.tx_flight(j), q) == ind(s1.tx_flight(j), q) by {
        assert(s1.tx_flight(j) == s0.tx_flight(j));
    }
}

// ---- Sums over the entries ----

/// A node's weight in D13's measure: more than a queued id's term (`1 + recv_pending`, at most a window plus one), so
/// a reset that queues its part's slot lowers the measure.
pub open spec fn kw() -> int {
    MAX_RECV_WINDOW as int + 2
}

/// A sending part's weight in D13's measure: `kw()` per node, those in its sets (`r`) twice, those in its slot (`t`)
/// once. Opaque: `lemma_wt` states what the sums need.
#[verifier::opaque]
spec fn wt(r: nat, t: nat) -> int {
    kw() * (2 * r + t)
}

/// `wt` grows with the weighted count `2r + t`, by at least `kw()` per unit; none for none.
proof fn lemma_wt(r1: nat, t1: nat, r2: nat, t2: nat)
    ensures
        wt(r1, t1) >= 0,
        r1 == 0 && t1 == 0 ==> wt(r1, t1) == 0,
        2 * r1 + t1 <= 2 * r2 + t2 ==> wt(r1, t1) <= wt(r2, t2),
        2 * r1 + t1 < 2 * r2 + t2 ==> wt(r1, t1) + kw() <= wt(r2, t2),
        2 * r1 + t1 <= 2058 ==> wt(r1, t1) <= 2058 * kw(),
{
    reveal(wt);
    let (a, b) = ((2 * r1 + t1) as int, (2 * r2 + t2) as int);
    assert(kw() * a >= 0) by (nonlinear_arith)
        requires
            a >= 0,
            kw() > 0,
    ;
    if a <= b {
        assert(kw() * a <= kw() * b) by (nonlinear_arith)
            requires
                a <= b,
                kw() > 0,
        ;
    }
    if a < b {
        assert(kw() * a + kw() <= kw() * b) by (nonlinear_arith)
            requires
                a + 1 <= b,
                kw() > 0,
        ;
    }
    if a <= 2058 {
        assert(kw() * a <= 2058 * kw()) by (nonlinear_arith)
            requires
                a <= 2058,
                kw() > 0,
        ;
    }
}

/// Per-entry quantities: 0 counted, 1 retired, 2 buffered, 3 physically buffered; 4 + k is 1
/// for a stream of type k; on the sending part, 8 bytes sent (`sent_end`), 9 its reservation (the
/// send queue's, `held_spec`, plus its teardown slot's window, `res_of(td_window())`, D10 (e)), 10 its
/// queue's buffers' capacity (`capacity_spec`), 11 its nodes, those in its sets weighing twice, each `kw()`
/// (D13's measure: a move to the slot halves them).
spec fn val(e: Entry, q: int) -> int {
    if q >= 8 {
        match e.send {
            Some(p) => if q == 8 {
                p.sent_end() as int
            } else if q == 9 {
                (p.held_spec() + res_of(p.td_window())) as int
            } else if q == 10 {
                p.capacity_spec() as int
            } else {
                wt(p.ranges_held(), p.td_nodes())
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

proof fn lemma_sum_take(s: Seq<Entry>, i: int, q: int)
    requires
        0 <= i < s.len(),
    ensures
        sum(s.take(i + 1), q) == sum(s.take(i), q) + val(s[i], q),
{
    assert(s.take(i + 1).drop_last() =~= s.take(i));
}

/// A prefix's buffered bytes are at most the whole's.
proof fn lemma_sum_prefix_le(s: Seq<Entry>, i: int)
    requires
        0 <= i <= s.len(),
    ensures
        sum(s.take(i), 9) <= sum(s, 9),
    decreases s.len() - i,
{
    if i == s.len() {
        assert(s.take(i) =~= s);
    } else {
        lemma_sum_take(s, i, 9);
        lemma_sum_prefix_le(s, i + 1);
    }
}

/// Each part's capacity within its reservation, summed.
proof fn lemma_sum_cap(s: Seq<Entry>)
    requires
        forall|k: int| 0 <= k < s.len() ==> 0 <= val(#[trigger] s[k], 10) <= val(s[k], 9),
    ensures
        0 <= sum(s, 10) <= sum(s, 9),
    decreases s.len(),
{
    if s.len() > 0 {
        let p = s.drop_last();
        assert forall|k: int| 0 <= k < p.len() implies 0 <= val(#[trigger] p[k], 10) <= val(p[k], 9) by {
            assert(p[k] == s[k]);
        }
        lemma_sum_cap(p);
        assert(0 <= val(s[s.len() - 1], 10) <= val(s[s.len() - 1], 9));
    }
}

proof fn lemma_sum_buf_nonneg(s: Seq<Entry>)
    ensures
        sum(s, 9) >= 0,
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_sum_buf_nonneg(s.drop_last());
    }
}

/// One sending part's buffered bytes are at most the whole's (`tx_held`).
proof fn lemma_sum_buf_le(s: Seq<Entry>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        0 <= val(s[i], 9) <= sum(s, 9),
{
    lemma_sum_prefix_le(s, i + 1);
    lemma_sum_take(s, i, 9);
    lemma_sum_buf_nonneg(s.take(i));
}

proof fn lemma_sum_w_nonneg(s: Seq<Entry>)
    ensures
        sum(s, 11) >= 0,
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_sum_w_nonneg(s.drop_last());
        if let Some(q) = s.last().send {
            lemma_wt(q.ranges_held(), q.td_nodes(), 0, 0);
        }
    }
}

/// Dead entries' weights, summed: at most 2058 nodes' worth each.
proof fn lemma_sum_w_le(s: Seq<Entry>)
    requires
        forall|k: int| 0 <= k < s.len() ==> dead_ok(#[trigger] s[k]),
    ensures
        sum(s, 11) <= s.len() * (2058 * kw()),
    decreases s.len(),
{
    if s.len() > 0 {
        let p = s.drop_last();
        assert forall|k: int| 0 <= k < p.len() implies dead_ok(#[trigger] p[k]) by {
            assert(p[k] == s[k]);
        }
        lemma_sum_w_le(p);
        let e = s[s.len() - 1];
        assert(dead_ok(e));
        assert(s.last() == e);
        if let Some(q) = e.send {
            lemma_wt(q.ranges_held(), q.td_nodes(), 0, 0);
        }
        let m = p.len() as int;
        assert(m * (2058 * kw()) + 2058 * kw() == (m + 1) * (2058 * kw())) by (nonlinear_arith);
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
    &&& 0 <= val(e, 2)
    &&& 0 <= val(e, 3) <= val(e, 2) + 2 * PAGE
    &&& val(e, 2) <= val(e, 0) - val(e, 1)
    &&& 0 <= val(e, 1) <= val(e, 0)
}

proof fn lemma_sum_bounds(s: Seq<Entry>)
    requires
        forall|k: int| 0 <= k < s.len() ==> terms_ok(#[trigger] s[k]),
    ensures
        0 <= sum(s, 2),
        0 <= sum(s, 3) <= sum(s, 2) + 2 * PAGE * s.len(),
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

// ---- The delivery queue (9b2 D13) ----

/// Entry `e`'s receiving part has bytes or the FIN left to deliver.
spec fn eready(e: Entry) -> bool {
    e.recv matches Some(r) && recv_ready(r.rfc())
}

/// Entry `e`'s sending part holds nodes in its teardown slot (D10 (e)): `deliver_some` reaps it.
spec fn etd(e: Entry) -> bool {
    e.send matches Some(p) && p.td_nodes() > 0
}

/// Entry `e0` became `ne` with the queue unchanged: the flag kept, and nothing newly to deliver or reap unless
/// already queued (a reset of a queued entry adds a slot to it).
spec fn qkeep(e0: Entry, ne: Entry) -> bool {
    &&& ne.queued == e0.queued
    &&& eready(ne) ==> eready(e0) || e0.queued
    &&& etd(ne) ==> etd(e0) || e0.queued
    &&& etd(e0) && !etd(ne) && e0.queued ==> ne.recv is Some
}

/// The queued entries.
spec fn qcount(s: Seq<Entry>) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        qcount(s.drop_last()) + if s.last().queued {
            1nat
        } else {
            0nat
        }
    }
}

/// Some queued entry is stream `id`.
spec fn qd(s: Seq<Entry>, id: u64) -> bool {
    exists|i: int| 0 <= i < s.len() && (#[trigger] s[i]).id == id && s[i].queued
}

/// The queue holds each queued entry's id once, oldest first; a queued entry has a receiving part or a non-empty
/// teardown slot, and one with bytes or the FIN left to deliver, or with a non-empty slot, is queued (D13, D10 (e)).
/// Opaque: only the queue's lemmas read it.
#[verifier::opaque]
spec fn qinv(s: Seq<Entry>, qv: Seq<u64>) -> bool {
    &&& qv.no_duplicates()
    &&& qv.len() == qcount(s)
    &&& forall|k: int| 0 <= k < qv.len() ==> qd(s, #[trigger] qv[k])
    &&& forall|i: int| 0 <= i < s.len() ==> ((#[trigger] s[i]).queued ==> s[i].recv is Some || etd(s[i]))
    &&& forall|i: int| 0 <= i < s.len() ==> (eready(#[trigger] s[i]) ==> s[i].queued)
    &&& forall|i: int| 0 <= i < s.len() ==> (etd(#[trigger] s[i]) ==> s[i].queued)
}

/// The queue is well formed and `qinv` holds: one opaque conjunct of `Streams::wf`.
#[verifier::opaque]
spec fn queue_ok(s: Seq<Entry>, q: IdQueue) -> bool {
    q.wf() && qinv(s, q@)
}

proof fn lemma_queue_ok(s: Seq<Entry>, q: IdQueue)
    ensures
        queue_ok(s, q) == (q.wf() && qinv(s, q@)),
{
    reveal(queue_ok);
}

/// The ids of `s` are distinct.
spec fn ids_distinct(s: Seq<Entry>) -> bool {
    forall|j: int, k: int|
        0 <= j < s.len() && 0 <= k < s.len() && j != k ==> (#[trigger] s[j]).id != (#[trigger] s[k]).id
}

proof fn lemma_qcount_update(s: Seq<Entry>, i: int, e: Entry)
    requires
        0 <= i < s.len(),
    ensures
        qcount(s.update(i, e)) + (if s[i].queued {
            1nat
        } else {
            0nat
        }) == qcount(s) + (if e.queued {
            1nat
        } else {
            0nat
        }),
    decreases s.len(),
{
    let t = s.update(i, e);
    if i == s.len() - 1 {
        assert(t.drop_last() =~= s.drop_last());
    } else {
        assert(t.drop_last() =~= s.drop_last().update(i, e));
        lemma_qcount_update(s.drop_last(), i, e);
    }
}

proof fn lemma_qcount_remove(s: Seq<Entry>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        qcount(s.remove(i)) + (if s[i].queued {
            1nat
        } else {
            0nat
        }) == qcount(s),
    decreases s.len(),
{
    if i == s.len() - 1 {
        assert(s.remove(i) =~= s.drop_last());
    } else {
        assert(s.remove(i).drop_last() =~= s.drop_last().remove(i));
        assert(s.remove(i).last() == s.last());
        lemma_qcount_remove(s.drop_last(), i);
    }
}

/// At most every entry is queued, and fewer while one is not.
proof fn lemma_qcount_le(s: Seq<Entry>)
    ensures
        qcount(s) <= s.len(),
        forall|i: int| 0 <= i < s.len() && !(#[trigger] s[i]).queued ==> qcount(s) < s.len(),
    decreases s.len(),
{
    if s.len() > 0 {
        let p = s.drop_last();
        lemma_qcount_le(p);
        assert forall|i: int| 0 <= i < s.len() && !(#[trigger] s[i]).queued implies qcount(s) < s.len() by {
            if i < p.len() {
                assert(p[i] == s[i]);
            }
        }
    }
}

/// Entry `i` replaced by `ne` (same id), the queue going from `qv` to `qv2`: unchanged with the flag, `ne`'s id
/// appended as it becomes queued, or popped (re-appended while still queued).
proof fn lemma_qinv_set(s: Seq<Entry>, i: int, ne: Entry, qv: Seq<u64>, qv2: Seq<u64>)
    requires
        qinv(s, qv),
        0 <= i < s.len(),
        ids_distinct(s),
        ne.id == s[i].id,
        ne.queued ==> ne.recv is Some || etd(ne),
        eready(ne) ==> ne.queued,
        etd(ne) ==> ne.queued,
        ({
            ||| ne.queued == s[i].queued && qv2 == qv
            ||| !s[i].queued && ne.queued && qv2 == qv.push(ne.id)
            ||| qv.len() > 0 && qv[0] == ne.id && (if ne.queued {
                qv2 == qv.drop_first().push(ne.id)
            } else {
                qv2 == qv.drop_first()
            })
        }),
    ensures
        qinv(s.update(i, ne), qv2),
{
    reveal(qinv);
    let t = s.update(i, ne);
    lemma_qcount_update(s, i, ne);
    if qv.len() > 0 && qv[0] == ne.id && !(ne.queued == s[i].queued && qv2 == qv) && !(!s[i].queued && ne.queued
        && qv2 == qv.push(ne.id)) {
        // The popped id is entry `i`'s: the only entry with that id.
        assert(qd(s, qv[0]));
        let j = choose|j: int| 0 <= j < s.len() && (#[trigger] s[j]).id == qv[0] && s[j].queued;
        assert(j == i);
    }
    if !s[i].queued && ne.queued && qv2 == qv.push(ne.id) {
        assert forall|k: int| 0 <= k < qv.len() implies qv[k] != ne.id by {
            assert(qd(s, qv[k]));
            let j = choose|j: int| 0 <= j < s.len() && (#[trigger] s[j]).id == qv[k] && s[j].queued;
            assert(j != i);
        }
    }
    let rest = if qv.len() > 0 && qv[0] == ne.id && !(ne.queued == s[i].queued && qv2 == qv) && !(!s[i].queued
        && ne.queued && qv2 == qv.push(ne.id)) {
        qv.drop_first()
    } else {
        qv
    };
    assert forall|k: int| 0 <= k < qv2.len() implies qd(t, #[trigger] qv2[k]) by {
        if qv2[k] == ne.id {
            assert(t[i].id == ne.id);
        } else {
            let kk = if rest == qv { k } else { k + 1 };
            assert(qv2[k] == qv[kk]);
            assert(qd(s, qv[kk]));
            let j = choose|j: int| 0 <= j < s.len() && (#[trigger] s[j]).id == qv[kk] && s[j].queued;
            assert(j != i);
            assert(t[j] == s[j]);
        }
    }
    assert forall|k: int| 0 <= k < t.len() implies ((#[trigger] t[k]).queued ==> t[k].recv is Some || etd(t[k])) && (
    eready(t[k]) ==> t[k].queued) && (etd(t[k]) ==> t[k].queued) by {
        if k != i {
            assert(t[k] == s[k]);
        }
    }
}

/// Entry `i` removed while not queued.
proof fn lemma_qinv_remove(s: Seq<Entry>, i: int, qv: Seq<u64>)
    requires
        qinv(s, qv),
        0 <= i < s.len(),
        !s[i].queued,
    ensures
        qinv(s.remove(i), qv),
{
    reveal(qinv);
    let t = s.remove(i);
    lemma_qcount_remove(s, i);
    assert forall|k: int| 0 <= k < qv.len() implies qd(t, #[trigger] qv[k]) by {
        assert(qd(s, qv[k]));
        let j = choose|j: int| 0 <= j < s.len() && (#[trigger] s[j]).id == qv[k] && s[j].queued;
        assert(j != i);
        let jj = if j < i { j } else { j - 1 };
        assert(t[jj] == s[j]);
    }
    assert forall|k: int| 0 <= k < t.len() implies ((#[trigger] t[k]).queued ==> t[k].recv is Some || etd(t[k])) && (
    eready(t[k]) ==> t[k].queued) && (etd(t[k]) ==> t[k].queued) by {
        let kk = if k < i { k } else { k + 1 };
        assert(t[k] == s[kk]);
    }
}

/// An entry pushed unqueued with nothing to deliver.
proof fn lemma_qinv_push(s: Seq<Entry>, e: Entry, qv: Seq<u64>)
    requires
        qinv(s, qv),
        !e.queued,
        !eready(e),
        !etd(e),
    ensures
        qinv(s.push(e), qv),
{
    reveal(qinv);
    let t = s.push(e);
    assert(t.drop_last() =~= s);
    assert forall|k: int| 0 <= k < qv.len() implies qd(t, #[trigger] qv[k]) by {
        assert(qd(s, qv[k]));
        let j = choose|j: int| 0 <= j < s.len() && (#[trigger] s[j]).id == qv[k] && s[j].queued;
        assert(t[j] == s[j]);
    }
    assert forall|k: int| 0 <= k < t.len() implies ((#[trigger] t[k]).queued ==> t[k].recv is Some || etd(t[k])) && (
    eready(t[k]) ==> t[k].queued) && (etd(t[k]) ==> t[k].queued) by {
        if k < s.len() {
            assert(t[k] == s[k]);
        }
    }
}

/// An empty queue over entries none of which is queued or has anything to deliver.
proof fn lemma_qinv_empty()
    ensures
        qinv(Seq::<Entry>::empty(), Seq::<u64>::empty()),
{
    reveal(qinv);
}

/// What `qinv` gives: the queue as long as the queued entries, each queued id a queued entry's, queued entries
/// with receiving parts.
proof fn lemma_qinv_facts(s: Seq<Entry>, qv: Seq<u64>)
    requires
        qinv(s, qv),
    ensures
        qv.len() == qcount(s),
        qv.no_duplicates(),
        forall|k: int| 0 <= k < qv.len() ==> qd(s, #[trigger] qv[k]),
        forall|i: int| 0 <= i < s.len() ==> ((#[trigger] s[i]).queued ==> s[i].recv is Some || etd(s[i])),
        forall|i: int| 0 <= i < s.len() ==> (eready(#[trigger] s[i]) ==> s[i].queued),
        forall|i: int| 0 <= i < s.len() ==> (etd(#[trigger] s[i]) ==> s[i].queued),
{
    reveal(qinv);
}

/// `1 + recv_pending` of each queued id's receiving part, summed: what deliveries work off (D13's measure).
spec fn qm(f: spec_fn(u64) -> nat, qv: Seq<u64>) -> nat
    decreases qv.len(),
{
    if qv.len() == 0 {
        0
    } else {
        qm(f, qv.drop_last()) + f(qv.last())
    }
}

proof fn lemma_qm_push(f: spec_fn(u64) -> nat, qv: Seq<u64>, x: u64)
    ensures
        qm(f, qv.push(x)) == qm(f, qv) + f(x),
{
    assert(qv.push(x).drop_last() =~= qv);
}

proof fn lemma_qm_first(f: spec_fn(u64) -> nat, qv: Seq<u64>)
    requires
        qv.len() > 0,
    ensures
        qm(f, qv) == f(qv[0]) + qm(f, qv.drop_first()),
    decreases qv.len(),
{
    if qv.len() > 1 {
        lemma_qm_first(f, qv.drop_last());
        assert(qv.drop_last().drop_first() =~= qv.drop_first().drop_last());
        assert(qv.drop_first().last() == qv.last());
    } else {
        assert(qv.drop_first() =~= Seq::<u64>::empty());
        assert(qv.drop_last() =~= Seq::<u64>::empty());
    }
}

/// `qm` reads `f` only at the ids queued.
proof fn lemma_qm_ext(f: spec_fn(u64) -> nat, g: spec_fn(u64) -> nat, qv: Seq<u64>)
    requires
        forall|k: int| 0 <= k < qv.len() ==> f(#[trigger] qv[k]) == g(qv[k]),
    ensures
        qm(f, qv) == qm(g, qv),
    decreases qv.len(),
{
    if qv.len() > 0 {
        let p = qv.drop_last();
        assert forall|k: int| 0 <= k < p.len() implies f(#[trigger] p[k]) == g(p[k]) by {
            assert(p[k] == qv[k]);
        }
        lemma_qm_ext(f, g, p);
        assert(f(qv.last()) == g(qv[qv.len() - 1]));
    }
}

proof fn lemma_qm_bound(f: spec_fn(u64) -> nat, qv: Seq<u64>, b: nat)
    requires
        forall|k: int| 0 <= k < qv.len() ==> f(#[trigger] qv[k]) <= b,
    ensures
        qm(f, qv) <= qv.len() * b,
    decreases qv.len(),
{
    if qv.len() > 0 {
        let p = qv.drop_last();
        assert forall|k: int| 0 <= k < p.len() implies f(#[trigger] p[k]) <= b by {
            assert(p[k] == qv[k]);
        }
        lemma_qm_bound(f, p, b);
        assert(f(qv.last()) <= b) by {
            assert(qv.last() == qv[qv.len() - 1]);
        }
        assert((p.len() + 1) * b == p.len() * b + b) by (nonlinear_arith);
    }
}

proof fn lemma_qm_pos(f: spec_fn(u64) -> nat, qv: Seq<u64>)
    requires
        forall|k: int| 0 <= k < qv.len() ==> f(#[trigger] qv[k]) >= 1,
    ensures
        qm(f, qv) >= qv.len(),
    decreases qv.len(),
{
    if qv.len() > 0 {
        let p = qv.drop_last();
        assert forall|k: int| 0 <= k < p.len() implies f(#[trigger] p[k]) >= 1 by {
            assert(p[k] == qv[k]);
        }
        lemma_qm_pos(f, p);
        assert(f(qv.last()) >= 1) by {
            assert(qv.last() == qv[qv.len() - 1]);
        }
    }
}

/// The most entries: our peer streams of both directions and our own unidirectional ones.
pub open spec fn max_entries() -> nat {
    (2 * MAX_LOCAL_STREAMS + MAX_OWN_UNI) as nat
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
    /// `conn_recv`'s window, `local.initial_max_data`, pinned. Only `wf` reads it, which a
    /// plain `cargo build` erases.
    #[allow(dead_code)]
    rx_conn: Ghost<u64>,
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
    /// The streams with bytes or the FIN left to deliver (9b2 D13), each once.
    q: IdQueue,
}

/// A dead entry's parts: each well formed, the sending part's weighted nodes within what `MAX_SEND_BUFFER` allowed
/// when the connection closed (`SendStream::lemma_weight`).
spec fn dead_ok(e: Entry) -> bool {
    &&& e.recv matches Some(r) ==> r.wf()
    &&& e.send matches Some(p) ==> p.wf() && 2 * p.ranges_held() + p.td_nodes() <= 2058
}

/// A closed connection's streams (D13, D10 (e)): moved here whole when the connection leaves Open, in O(1), and freed
/// one bounded step per `backlog_step` (`reap`), so neither the close nor any step frees more than a budget.
pub struct DeadStreams {
    entries: Vec<Entry>,
    /// The delivery queue's slots, freed with the rest.
    #[allow(dead_code)]
    q: IdQueue,
}

/// What dropping an emptied `DeadStreams` frees: its entry vector and the queue's slots.
pub open spec fn c_dfree() -> nat {
    2
}

/// A dead step's frees besides its reaping: a sending part's queue at retirement, and an entry's receiving ring and
/// sending queue when it goes.
pub open spec fn c_dstep() -> nat {
    c_rfree() + 2 * c_sfree()
}

/// `c_dstep()`, exec: what `backlog_step` sets aside of its teardown `B_PUMP` for a dead step's frees.
pub const C_DSTEP: u64 = 779;

impl DeadStreams {
    pub closed spec fn wf(&self) -> bool {
        &&& self.entries@.len() <= max_entries()
        &&& forall|k: int| 0 <= k < self.entries@.len() ==> dead_ok(#[trigger] self.entries@[k])
    }

    /// D13's measure for a closed connection's streams: one per entry and its sending part's weighted nodes, and one
    /// for the vectors themselves.
    pub closed spec fn measure(&self) -> nat {
        self.entries@.len() + sum(self.entries@, 11) as nat + 1
    }

    /// The measure's bound: the entries' and their parts' (`dead_ok`).
    pub proof fn lemma_measure(&self)
        requires
            self.wf(),
        ensures
            1 <= self.measure() <= max_entries() * (1 + 2058 * kw()) + 1,
            self.len_spec() == 0 ==> self.measure() == 1,
    {
        lemma_sum_w_le(self.entries@);
        lemma_sum_w_nonneg(self.entries@);
        let n = self.entries@.len() as int;
        assert(n + n * (2058 * kw()) <= max_entries() * (1 + 2058 * kw())) by (nonlinear_arith)
            requires
                n <= max_entries(),
                kw() > 0,
        ;
    }

    /// The entries left.
    pub closed spec fn len_spec(&self) -> nat {
        self.entries@.len()
    }

    /// No entry is left.
    pub fn is_empty(&self) -> (r: bool)
        ensures
            r == (self.len_spec() == 0),
    {
        self.entries.len() == 0
    }

    /// One bounded step on the last entry: its sending part's sets move to its slot (once, O(1)) and the slot is
    /// reaped within `budget`; an entry with no node left is dropped (its ring and queue, `c_dstep`). The measure falls.
    pub fn reap(&mut self, budget: u64) -> (r: Ghost<nat>)
        requires
            old(self).wf(),
            old(self).len_spec() > 0,
            crate::avl::c_pop() * 127 + 2 <= budget,
        ensures
            final(self).wf(),
            final(self).measure() < old(self).measure(),
            r@ <= budget + c_dstep(),
    {
        let ghost s0 = self.entries@;
        let ghost mut work: nat = 0;
        let n = self.entries.len();
        let mut e = Entry { id: 0, recv: None, send: None, queued: false };
        self.entries.set_and_swap(n - 1, &mut e);
        let ghost e0 = e;
        proof {
            assert(e0 == s0[n - 1]);
            assert(dead_ok(e0));
            if let Some(q) = e0.send {
                q.lemma_td();
                if q.td_nodes() > 0 {
                    q.lemma_sets_idle();
                }
            }
        }
        let mut keep = false;
        if let Some(mut p) = e.send.take() {
            if !p.has_td() {
                let Ghost(c1) = p.retire();
                proof {
                    work = work + c1;
                }
            }
            let ghost p1 = p;
            if p.has_td() {
                let Ghost(c2) = p.reap(budget);
                proof {
                    p.lemma_same_but_td(p1);
                }
                proof {
                    work = work + c2;
                }
                keep = true;
            }
            e.send = Some(p);
        }
        let ghost ne = e;
        proof {
            if let Some(p) = ne.send {
                let q = e0.send->0;
                lemma_wt(p.ranges_held(), p.td_nodes(), q.ranges_held(), q.td_nodes());
            }
        }
        if keep {
            self.entries.set_and_swap(n - 1, &mut e);
            proof {
                assert(self.entries@ == s0.update(n - 1, ne));
                lemma_sum_update(s0, n - 1, ne, 11);
                assert forall|k: int| 0 <= k < self.entries@.len() implies dead_ok(#[trigger] self.entries@[k]) by {
                    if k != n - 1 {
                        assert(self.entries@[k] == s0[k]);
                    }
                }
            }
        } else {
            let _ = self.entries.pop();
            proof {
                // The entry goes with no node left: its ring and its queue are what drop.
                work = work + c_rfree() + c_sfree();
                assert(self.entries@ =~= s0.drop_last());
                assert(s0.drop_last() =~= s0.remove(n - 1));
                lemma_sum_remove(s0, n - 1, 11);
                if let Some(p) = ne.send {
                    assert(p.td_nodes() == 0);
                }
                assert forall|k: int| 0 <= k < self.entries@.len() implies dead_ok(#[trigger] self.entries@[k]) by {
                    assert(self.entries@[k] == s0[k]);
                }
            }
        }
        proof {
            lemma_sum_w_nonneg(s0);
            lemma_sum_w_nonneg(self.entries@);
        }
        Ghost(work)
    }
}

impl Streams {
    /// The streams of a connection leaving Open, whole, in O(1) (D13): `backlog_step` frees them a bounded step at a
    /// time. Their measure is at most this one's sending weight plus one per possible entry and one.
    pub fn into_dead(self) -> (r: DeadStreams)
        requires
            self.wf(),
        ensures
            r.wf(),
            r.measure() <= self.td_weight() + max_entries() + 1,
    {
        proof {
            lemma_entries_bound(self);
            let s = self.entries@;
            assert forall|k: int| 0 <= k < s.len() implies dead_ok(#[trigger] s[k]) by {
                assert(entry_ok(s[k], self.rx_bidi, self.rx_uni));
                if let Some(p) = s[k].send {
                    lemma_sum_buf_le(s, k);
                    assert(MAX_SEND_BUFFER == 1048576) by (compute_only);
                    p.lemma_weight();
                }
            }
            lemma_sum_w_nonneg(s);
        }
        DeadStreams { entries: self.entries, q: self.q }
    }

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

    /// The pieces in flight of stream `id`'s sending part; none without one (D10 (b)).
    pub closed spec fn tx_flight(&self, id: u64) -> Set<(u64, u64)> {
        match self.tx_part(id) {
            Some(p) => p.flight_spec(),
            None => Set::empty(),
        }
    }

    /// Per stream: reset, and its pieces in flight (conn's `pieces_ok` reads only this).
    pub open spec fn tx_view(&self) -> TxView {
        |id: u64| (self.send_reset(id), self.tx_flight(id))
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

    /// Σ `held_spec()` over the sending parts: their send queues' reservations.
    pub closed spec fn tx_held(&self) -> int {
        sum(self.entries@, 9)
    }

    /// Σ `capacity_spec()` over the sending parts: the bytes their send queues requested from the allocator.
    pub closed spec fn tx_capacity(&self) -> int {
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
        &&& crate::ring::window_ok(self.rx_bidi)
        &&& crate::ring::window_ok(self.rx_uni)
        &&& self.ids.peer_credit_spec(true).window_spec() <= MAX_LOCAL_STREAMS
        &&& self.ids.peer_credit_spec(false).window_spec() <= MAX_LOCAL_STREAMS
        &&& self.tx_uni <= VARINT_MAX
        &&& self.conn_recv.window_spec() == self.rx_conn@
        &&& self.tx_held() <= MAX_SEND_BUFFER as int
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
        // D13: the delivery queue.
        &&& queue_ok(self.entries@, self.q)
    }

    /// The per-id term of `rx_backlog`.
    spec fn qterm(&self) -> spec_fn(u64) -> nat {
        |id: u64| 1 + recv_pending(self.rx_spec(id))
    }

    /// D13's STREAM backlog measure: per queued stream, one plus its bytes past delivery up to the
    /// largest received offset. Each `deliver_some` lowers it while the queue is non-empty.
    pub closed spec fn rx_backlog(&self) -> nat {
        qm(self.qterm(), self.q@)
    }

    /// The sending parts' nodes, those in their sets weighing twice: `deliver_some`'s reaping and the closing
    /// connection's teardown work them off; a `reset` halves a part's (D13, D10 (e)).
    pub closed spec fn td_weight(&self) -> nat {
        sum(self.entries@, 11) as nat
    }

    /// D13's measure for the streams: the delivery backlog and the sending parts' weighted nodes. `deliver_some`
    /// lowers it while the queue is non-empty; `write`, `flush`, `reset` and `stop_sending` never raise it.
    pub closed spec fn measure(&self) -> nat {
        self.rx_backlog() + self.td_weight()
    }

    /// Some stream has bytes or the FIN left to deliver: the queue is non-empty.
    pub closed spec fn stream_backlog_spec(&self) -> bool {
        self.q@.len() > 0
    }

    /// Some stream has bytes or the FIN left to deliver. O(1).
    pub fn stream_backlog(&self) -> (r: bool)
        requires
            self.wf(),
        ensures
            r == self.stream_backlog_spec(),
    {
        proof {
            lemma_queue_ok(self.entries@, self.q);
        }
        self.q.len() > 0
    }

    /// The queue's bound: `IDQ_CAP` streams of at most a window each.
    pub proof fn lemma_rx_backlog(&self)
        requires
            self.wf(),
        ensures
            self.rx_backlog() <= IDQ_CAP * (MAX_RECV_WINDOW + 1),
            self.stream_backlog_spec() ==> self.rx_backlog() > 0,
    {
        let qv = self.q@;
        lemma_queue_ok(self.entries@, self.q);
        lemma_qinv_facts(self.entries@, qv);
        assert forall|k: int| 0 <= k < qv.len() implies (self.qterm())(#[trigger] qv[k]) <= MAX_RECV_WINDOW + 1 by {
            let id = qv[k];
            assert(qd(self.entries@, id));
            let i = choose|i: int| 0 <= i < self.entries@.len() && (#[trigger] self.entries@[i]).id == id
                && self.entries@[i].queued;
            lemma_qterm_le(*self, i);
        }
        lemma_qm_bound(self.qterm(), qv, (MAX_RECV_WINDOW + 1) as nat);
        assert forall|k: int| 0 <= k < qv.len() implies (self.qterm())(#[trigger] qv[k]) >= 1 by {}
        lemma_qm_pos(self.qterm(), qv);
        self.q.lemma_len();
        assert(qv.len() * (MAX_RECV_WINDOW + 1) <= IDQ_CAP * (MAX_RECV_WINDOW + 1)) by (nonlinear_arith)
            requires
                qv.len() <= IDQ_CAP,
        ;
    }

    /// The measure's bound: the queue's (`lemma_rx_backlog`) and every sending part's weight within its reservation
    /// (`SendStream::lemma_weight`).
    pub proof fn lemma_measure(&self)
        requires
            self.wf(),
        ensures
            self.measure() <= IDQ_CAP * (MAX_RECV_WINDOW + 1) + max_entries() * (2058 * kw()),
            self.stream_backlog_spec() ==> self.measure() > 0,
            self.td_weight() <= self.measure(),
    {
        self.lemma_rx_backlog();
        lemma_entries_bound(*self);
        let s = self.entries@;
        assert forall|k: int| 0 <= k < s.len() implies dead_ok(#[trigger] s[k]) by {
            assert(entry_ok(s[k], self.rx_bidi, self.rx_uni));
            if let Some(p) = s[k].send {
                lemma_sum_buf_le(s, k);
                assert(MAX_SEND_BUFFER == 1048576) by (compute_only);
                p.lemma_weight();
            }
        }
        lemma_sum_w_le(s);
        lemma_sum_w_nonneg(s);
        let n = s.len() as int;
        assert(n * (2058 * kw()) <= max_entries() * (2058 * kw())) by (nonlinear_arith)
            requires
                n <= max_entries(),
                kw() > 0,
        ;
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
            // ring pages hold at most that plus two pages per stream (D11).
            0 <= self.rx_buffered(),
            0 <= self.rx_buffered_phys() <= self.rx_buffered() + 2 * PAGE * self.live_streams(),
            self.rx_buffered() <= self.conn_counted_spec() - self.conn_recv_spec().consumed_spec(),
            self.rx_buffered_phys() <= self.conn_recv_spec().limit_spec() + 2 * PAGE * self.live_streams(),
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
            // Memory: the send queues' buffers hold at most their reservations, at most
            // `MAX_SEND_BUFFER` bytes in all.
            0 <= self.tx_capacity() <= self.tx_held() <= MAX_SEND_BUFFER,
            // Memory: receive buffers within the pinned window plus two pages per stream (3d D8, D11).
            self.rx_buffered_phys() <= self.conn_recv_spec().window_spec() + 2 * PAGE * self.live_streams(),
            self.live_streams() <= max_entries(),
            self.ids_spec().local_uni_spec().used_spec() <= MAX_OWN_UNI,
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
        lemma_sum_buf_nonneg(s);
        assert forall|k: int| 0 <= k < s.len() implies 0 <= val(#[trigger] s[k], 10) <= val(s[k], 9) by {
            assert(entry_ok(s[k], self.rx_bidi, self.rx_uni));
            if let Some(p) = s[k].send {
                p.lemma_held();
            }
        }
        lemma_sum_cap(s);
        lemma_entries_bound(*self);
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
            local.initial_max_stream_data_bidi_remote <= MAX_RECV_WINDOW,
            local.initial_max_stream_data_uni <= MAX_RECV_WINDOW,
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
            forall|id: u64| #[trigger] r.tx_flight(id) == Set::<(u64, u64)>::empty(),
            r.conn_recv_spec().window_spec() == local.initial_max_data,
            r.tx_held() == 0,
            r.measure() == 0,
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
            rx_conn: Ghost(local.initial_max_data),
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
            q: IdQueue::new(),
        };
        proof {
            lemma_qinv_empty();
            assert(r.entries@ =~= Seq::<Entry>::empty());
            lemma_queue_ok(r.entries@, r.q);
            r.ids.lemma_wf();
            crate::ring::lemma_window_ok(r.rx_bidi);
            crate::ring::lemma_window_ok(r.rx_uni);
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
        &&& self.rx_conn == o.rx_conn
        &&& self.rx_bidi == o.rx_bidi
        &&& self.rx_uni == o.rx_uni
        &&& self.tx_bidi == o.tx_bidi
        &&& self.tx_uni == o.tx_uni
        &&& self.failed == o.failed
        &&& self.removed == o.removed
        &&& self.resets == o.resets
        &&& self.gone == o.gone
        &&& self.tx_gone == o.tx_gone
        &&& self.q == o.q
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
            final(self).tx_held() == old(self).tx_held(),
            final(self).ids.peer_opened_spec(x % 4 == 0) == x / 4 + 1,
            final(self).ids.peer_opened_spec(x % 4 != 0) == old(self).ids.peer_opened_spec(
                x % 4 != 0,
            ),
            forall|b: bool| #[trigger]
                final(self).ids.peer_credit_spec(b) == old(self).ids.peer_credit_spec(b),
            final(self).ids.local_uni_spec() == old(self).ids.local_uni_spec(),
            parts_kept(*old(self), *final(self)),
            forall|j: u64| #[trigger] final(self).tx_flight(j) == old(self).tx_flight(j),
    {
        let ghost s0 = *self;
        let bidi = x % 4 == 0;
        let _ = self.ids.on_peer_stream(x);
        proof {
            crate::ring::lemma_window_ok(self.rx_bidi);
            crate::ring::lemma_window_ok(self.rx_uni);
        }
        let recv = RecvStream::new(x, if bidi { self.rx_bidi } else { self.rx_uni });
        let send = if bidi {
            Some(SendStream::new(self.tx_bidi))
        } else {
            None
        };
        let e = Entry { id: x, recv: Some(recv), send, queued: false };
        self.entries.push(e);
        self.rtr = Ghost(self.rtr@.insert(x, Seq::empty()));
        proof {
            lemma_open_one(s0, *self, x, e);
            lemma_part_push(s0, *self, e);
            lemma_push_flight(s0, *self, e);
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
            final(self).tx_held() == old(self).tx_held(),
            final(self).ids.peer_created(id),
            forall|b: bool| #[trigger]
                final(self).ids.peer_credit_spec(b) == old(self).ids.peer_credit_spec(b),
            final(self).ids.local_uni_spec() == old(self).ids.local_uni_spec(),
            parts_kept(*old(self), *final(self)),
            forall|j: u64| #[trigger] final(self).tx_flight(j) == old(self).tx_flight(j),
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
                self.tx_held() == s0.tx_held(),
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
                forall|j: u64| #[trigger] self.tx_flight(j) == s0.tx_flight(j),
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
                assert forall|j: u64| #[trigger] self.tx_flight(j) == s0.tx_flight(j) by {
                    assert(s1.tx_flight(j) == s0.tx_flight(j));
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
            final(self).tx_held() == old(self).tx_held(),
            final(self).rx_conn == old(self).rx_conn,
            r == rx_outcome(*old(self), f@),
            r is Err ==> final(ev)@ == old(ev)@,
            r is Ok ==> event_views(final(ev)@) == event_views(old(ev)@) + frame_events(
                *old(self),
                *final(self),
                f@,
            ),
            forall|j: u64| #[trigger]
                final(self).rx_trace(j) == rx_trace_after(*old(self), f@, r, j),
            tx_kept_but(*old(self), *final(self), None),
    {
        let ghost s0 = *self;
        let ghost id = self.entries@[i as int].id;
        let ghost a = self.entries@;
        let mut e = Entry { id: 0, recv: None, send: None, queued: false };
        self.entries.set_and_swap(i, &mut e);
        let ghost e0 = e;
        proof {
            assert(e0 == a[i as int]);
            assert(entry_ok(e0, s0.rx_bidi, s0.rx_uni));
            assert(!s0.removed@.contains(id));
            self.conn_recv.lemma_wf();
        }
        proof {
            lemma_queue_ok(a, s0.q);
            lemma_qinv_facts(a, s0.q@);
            assert(eready(e0) ==> e0.queued);
        }
        //= https://www.rfc-editor.org/rfc/rfc9000#section-4.5
        //# The receiver MUST use the final size of the stream to
        //# account for all bytes sent on the stream in its connection-level flow
        //# controller.
        // The stream reports only the growth of its final size, else high-water mark (`counted`),
        // so duplicate bytes count once; the connection credit we return is what it retired.
        let room = self.conn_recv.limit() - self.conn_counted;
        let (res, dt, enq) = feed_entry(&mut e, f, room, ev);
        let xid = e.id;
        let ghost tr = e.recv->0.trace();
        let ghost ne = e;
        self.entries.set_and_swap(i, &mut e);
        proof {
            assert(self.entries@ == a.update(i as int, ne));
            lemma_enqueue(s0, i as int, ne, enq);
        }
        // D13: bytes or the FIN left undelivered queue the stream, once.
        if enq {
            self.q.push(xid);
        }
        proof {
            lemma_queue_ok(self.entries@, self.q);
        }
        let r = match res {
            Ok(n) => {
                proof {
                    lemma_recv_ok(s0, i as int, ne, n);
                }
                self.conn_counted = self.conn_counted + n;
                self.conn_recv.on_consumed(dt);
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
        };
        proof {
            assert(ne.send == e0.send);
            lemma_swap_flight(s0, *self, i as int, ne);
        }
        r
    }

    /// Works the stream at the queue's head (9b2 D13, D10 (e)): pops its id, hands at most `budget` bytes (or its
    /// FIN) to `ev`, frees at most `budget` units of its sending part's teardown slot, re-queues it while bytes, the
    /// FIN or slot nodes are left, and removes the entry once all its parts are terminal and its slot is empty. One
    /// queue entry per call, so the call lowers `measure` while the queue is non-empty. Costs the delivery, the
    /// reaping, the id lookup (linear in the open streams, Q20, 9b4's) and the entry's removal with its buffers: the
    /// receiving part's ring (`c_rfree`) and the sending part's queue (`c_sfree`; its sets and slot are empty then).
    pub fn deliver_some(&mut self, budget: u64, ev: &mut Vec<StreamEvent>) -> (r: Ghost<nat>)
        requires
            old(self).wf(),
            !old(self).failed(),
            crate::avl::c_pop() * 127 + 2 <= budget,
        ensures
            final(self).wf(),
            !final(self).failed(),
            final(self).conn_recv_spec().window_spec() == old(self).conn_recv_spec().window_spec(),
            final(self).tx_held() <= old(self).tx_held(),
            tx_kept_but(*old(self), *final(self), None),
            final(self).measure() <= old(self).measure(),
            old(self).stream_backlog_spec() ==> final(self).measure() < old(self).measure(),
            !old(self).stream_backlog_spec() ==> *final(self) == *old(self) && final(ev)@ == old(ev)@,
            r@ <= c_rd() * (budget + budget as nat / (PAGE as nat) + 2) + budget + 2 * max_entries() + 3 + c_rfree()
                + c_sfree(),
    {
        let ghost s0 = *self;
        proof {
            lemma_queue_ok(self.entries@, self.q);
            lemma_qinv_facts(self.entries@, self.q@);
            self.q.lemma_len();
        }
        let x = match self.q.front() {
            None => {
                return Ghost(0);
            },
            Some(x) => x,
        };
        let i = match self.find(x) {
            Some(i) => i,
            None => {
                proof {
                    assert(qd(s0.entries@, x));
                    let j = choose|j: int| 0 <= j < s0.entries@.len() && (#[trigger] s0.entries@[j]).id == x
                        && s0.entries@[j].queued;
                    assert(has_id(s0.entries@, x));
                }
                return Ghost(0);  // unreachable: a queued id is a live entry's (`qinv`)
            },
        };
        proof {
            lemma_entries_bound(s0);
        }
        let Ghost(c) = self.deliver_at_head(i, budget, ev);
        let ghost s2 = *self;
        self.gc(i);
        proof {
            lemma_backlog_same(s2, *self);
        }
        // The lookup's scan and the removal's shift, each at most the entries; the entry's buffers freed.
        Ghost(c + 2 * s0.entries@.len() + 2 + c_rfree() + c_sfree())
    }

    /// `deliver_some` on entry `i`, the queue's head: pops it, delivers at most `budget` bytes, reaps at most
    /// `budget` units of its slot, and re-queues it while bytes, the FIN or slot nodes are left (split for the rlimit).
    #[verifier::spinoff_prover]
    fn deliver_at_head(&mut self, i: usize, budget: u64, ev: &mut Vec<StreamEvent>) -> (r: Ghost<nat>)
        requires
            old(self).wf(),
            !old(self).failed(),
            crate::avl::c_pop() * 127 + 2 <= budget,
            i < old(self).entries@.len(),
            old(self).q@.len() > 0,
            old(self).q@[0] == old(self).entries@[i as int].id,
        ensures
            final(self).wf(),
            !final(self).failed(),
            final(self).entries@.len() == old(self).entries@.len(),
            final(self).entries@[i as int].id == old(self).entries@[i as int].id,
            final(self).ids == old(self).ids,
            final(self).removed == old(self).removed,
            final(self).resets == old(self).resets,
            final(self).rx_conn == old(self).rx_conn,
            final(self).conn_recv_spec().window_spec() == old(self).conn_recv_spec().window_spec(),
            final(self).tx_held() <= old(self).tx_held(),
            tx_kept_but(*old(self), *final(self), None),
            final(self).measure() < old(self).measure(),
            r@ <= c_rd() * (budget + budget as nat / (PAGE as nat) + 2) + 1 + budget,
    {
        let ghost s0 = *self;
        let ghost a = self.entries@;
        let ghost x = a[i as int].id;
        proof {
            lemma_queue_ok(a, s0.q);
            lemma_qinv_facts(a, s0.q@);
            assert(qd(a, x));
            let j = choose|j: int| 0 <= j < a.len() && (#[trigger] a[j]).id == x && a[j].queued;
            assert(entry_ok(a[j], s0.rx_bidi, s0.rx_uni));
            assert(j == i as int);
            assert(entry_ok(a[i as int], s0.rx_bidi, s0.rx_uni));
            self.conn_recv.lemma_wf();
            self.q.lemma_len();
        }
        let _ = self.q.pop();
        let mut e = Entry { id: 0, recv: None, send: None, queued: false };
        self.entries.set_and_swap(i, &mut e);
        let ghost e0 = e;
        let xid = e.id;
        let has_recv = e.recv.is_some();
        let (dt, Ghost(c), ready) = if has_recv {
            deliver_entry(&mut e, budget, ev)
        } else {
            (0, Ghost(0), false)
        };
        let ghost e1 = e;
        // The sending part's slot (D10 (e)).
        let mut td = false;
        let mut cr: Ghost<nat> = Ghost(0);
        if let Some(mut p) = e.send.take() {
            cr = p.reap(budget);
            td = p.has_td();
            e.send = Some(p);
        }
        let Ghost(c2) = cr;
        e.queued = ready || td;
        let ghost ne = e;
        self.entries.set_and_swap(i, &mut e);
        proof {
            assert(e0 == a[i as int]);
            assert(self.entries@ == a.update(i as int, ne));
            lemma_head_ok(s0, i as int, e1, ne);
        }
        self.conn_recv.on_consumed(dt);
        if has_recv {
            self.rtr = Ghost(self.rtr@.insert(x, ne.recv->0.trace()));
        }
        if ready || td {
            self.q.push(xid);
        }
        proof {
            assert(ids_distinct(a));
            lemma_qinv_set(a, i as int, ne, s0.q@, self.q@);
            lemma_queue_ok(self.entries@, self.q);
            assert forall|j: u64| j != x implies #[trigger] self.rx_spec(j) == s0.rx_spec(j) by {
                assert(self.rx_trace(j) == s0.rx_trace(j));
            }
            lemma_head_measure(s0, *self, i as int, ne);
            lemma_swap_flight(s0, *self, i as int, ne);
        }
        Ghost(c + c2)
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
            final(self).rx_bidi == old(self).rx_bidi,
            final(self).rx_uni == old(self).rx_uni,
            forall|j: u64| #[trigger] final(self).rx_trace(j) == old(self).rx_trace(j),
            final(self).tx_held() <= old(self).tx_held(),
            final(self).rx_conn == old(self).rx_conn,
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
            tx_kept_but(*old(self), *final(self), None),
    {
        let ghost s0 = *self;
        let ghost id = self.entries@[i as int].id;
        let ghost a = self.entries@;
        let ghost ev0 = ev@;
        let mut e = Entry { id: 0, recv: None, send: None, queued: false };
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
        // A non-empty slot is queued, for `deliver_some` to reap (D10 (e)).
        let enq = !e.queued && match &e.send {
            Some(p) => p.has_td(),
            None => false,
        };
        if enq {
            e.queued = true;
        }
        let ghost ne = e;
        let xid = e.id;
        proof {
            if let Some(p0) = e0.send {
                p0.lemma_td();
                p0.lemma_held();
                if ne.send->0.td_window() <= p0.peak_spec() {
                    lemma_res_mono(ne.send->0.td_window(), p0.peak_spec());
                }
            }
            lemma_reset_enqueue(s0, i as int, ne, enq);
        }
        self.entries.set_and_swap(i, &mut e);
        if enq {
            self.q.push(xid);
        }
        proof {
            assert(self.entries@ == a.update(i as int, ne));
            assert(ne.recv == e0.recv);
            if let Some(r) = ne.recv {
                assert(s0.rtr@.insert(id, r.trace()) =~= s0.rtr@);
            }
            lemma_update(s0, i as int, ne, s0.rtr@, self.resets@);
            lemma_queue_step(s0, i as int, ne, self.q);
            lemma_sum_update(a, i as int, ne, 0);
            lemma_sum_update(a, i as int, ne, 1);
            lemma_sum_update(a, i as int, ne, 4);
            lemma_sum_update(a, i as int, ne, 6);
            lemma_sum_update(a, i as int, ne, 8);
            lemma_sum_update(a, i as int, ne, 9);
            assert(val(ne, 9) <= val(e0, 9));
            let sp = s0.rx_spec(id);
            assert(sp.events.skip(sp.events.len() as int) =~= Seq::<SpecStreamEvent>::empty());
            if self.resets@ == s0.resets@ {
                assert(ev@ == ev0);
                assert(event_views(ev0) + Seq::<SpecStreamEvent>::empty() =~= event_views(ev0));
            } else {
                assert(event_views(ev@) =~= event_views(ev0).push(ev@.last()@));
            }
            lemma_swap_flight(s0, *self, i as int, ne);
        }
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-4.4
    //# Both endpoints MUST maintain flow control state
    //# for the stream in the unterminated direction until that direction
    //# enters a terminal state.
    /// Removes entry `i` once all its parts are terminal and it is not queued (so its sending part's teardown slot is
    /// empty, `qinv`); a removed peer stream is re-credited (MAX_STREAMS), and its buffers are dropped: a "Data Read"
    /// receiving part's ring slot vector (one free; delivery freed its pages) and the sending part's queue (its sets
    /// and slot are empty, asserted below: at most `c_sfree()`). `deliver_some` charges its own removal; the frame and
    /// ACK/loss paths' removals are Task 10d's (item 5).
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
            final(self).tx_held() <= old(self).tx_held(),
            final(self).td_weight() == old(self).td_weight(),
            final(self).rx_conn == old(self).rx_conn,
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
            tx_kept_but(*old(self), *final(self), None),
    {
        let ghost s0 = *self;
        let ghost a = self.entries@;
        proof {
            assert(entry_ok(a[i as int], self.rx_bidi, self.rx_uni));
        }
        // A queued entry stays until `deliver_some` pops it (D13: every queued id is a live entry's).
        let done = {
            let e = &self.entries[i];
            !e.queued && (match &e.recv {
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
                // The sending part dropped holds no node: not queued, so its slot is empty; terminal, so its sets are.
                lemma_queue_ok(a, s0.q);
                lemma_qinv_facts(a, s0.q@);
                if let Some(p) = e.send {
                    p.lemma_sets_idle();
                    assert(p.td_nodes() == 0 && p.ranges_held() == 0);
                    lemma_wt(0, 0, 0, 0);
                }
                lemma_sum_remove(a, i as int, 11);
                lemma_sum_w_nonneg(a);
                lemma_sum_w_nonneg(a.remove(i as int));
            }
            self.tx_gone = Ghost((self.tx_gone@ + val(e, 8)) as nat);
            if e.id % 4 != 3 {
                self.ids.on_peer_closed(e.id % 4 == 0);
                self.removed = Ghost(self.removed@.insert(e.id));
                self.gone = Ghost((self.gone@ + val(e, 0)) as nat);
            }
            proof {
                lemma_gc(s0, *self, i as int, e);
                lemma_gc_flight(s0, *self, i as int);
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
            final(self).tx_held() <= old(self).tx_held(),
            final(self).rx_conn == old(self).rx_conn,
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
                assert forall|j: u64| #[trigger] self.tx_flight(j) == s0.tx_flight(j) by {}
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
            assert forall|j: u64| #[trigger] s1.tx_flight(j) == s0.tx_flight(j) by {}
        }
        let r = self.deliver(f, id, ev);
        let ghost s2 = *self;
        if r.is_err() {
            self.failed = true;
        }
        proof {
            lemma_post_before(s0, s1, s2, f@, event_views(old(ev)@), event_views(ev@), r);
            assert(equiv(s2, *self));
            assert forall|j: u64| #[trigger] self.tx_flight(j) == s2.tx_flight(j) by {}
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
            final(self).tx_held() <= old(self).tx_held(),
            final(self).rx_conn == old(self).rx_conn,
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
    #[verifier::spinoff_prover]
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
            final(self).tx_held() <= old(self).tx_held(),
            final(self).rx_conn == old(self).rx_conn,
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
            self.gc_after(i, Ghost(s0), Ghost(f@), Ghost(event_views(ev0)), Ghost(event_views(ev@)), Ghost(r));
        }
        r
    }

    /// `deliver_at`'s `gc` of entry `i` once its frame applied (split for the rlimit).
    fn gc_after(
        &mut self,
        i: usize,
        Ghost(s0): Ghost<Streams>,
        Ghost(f): Ghost<SpecFrame>,
        Ghost(ev0): Ghost<Seq<SpecStreamEvent>>,
        Ghost(ev1): Ghost<Seq<SpecStreamEvent>>,
        Ghost(r): Ghost<Result<(), u64>>,
    )
        requires
            old(self).wf(),
            i < old(self).entries@.len(),
            frame_stream_id(f) == Some(old(self).entries@[i as int].id),
            post_rest(s0, *old(self), f, ev0, ev1, r),
            forall|j: u64| #[trigger] old(self).is_removed(j) == s0.is_removed(j),
            forall|b: bool| #[trigger] old(self).peer_closed(b) == s0.peer_closed(b),
        ensures
            final(self).wf(),
            final(self).failed == old(self).failed,
            final(self).tx_held() <= old(self).tx_held(),
            final(self).rx_conn == old(self).rx_conn,
            post_rest(s0, *final(self), f, ev0, ev1, r),
    {
        let ghost s1 = *self;
        let ghost id = self.entries@[i as int].id;
        self.gc(i);
        proof {
            lemma_post_gc(s0, s1, *self, f, id, ev0, ev1, r);
        }
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
            final(self).tx_held() <= old(self).tx_held(),
            final(self).conn_recv_spec().window_spec() == old(self).conn_recv_spec().window_spec(),
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
                            assert forall|b: bool| #[trigger] self.ids.peer_opened_spec(b) == s0.ids.peer_opened_spec(b)
                                && self.ids.peer_credit_spec(b) == s0.ids.peer_credit_spec(b) by {}
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
        &&& self.q == o.q
        &&& forall|j: u64| #[trigger] self.rx_trace(j) == o.rx_trace(j)
    }
}

/// Entries whose ids are distinct and of the form `4·n + 3` with `n < u`: at most `u`.
proof fn lemma_sum7_le(s: Seq<Entry>, u: nat)
    requires
        ids_distinct(s),
        forall|k: int| 0 <= k < s.len() && (#[trigger] s[k]).id % 4 == 3 ==> s[k].id / 4 < u,
    ensures
        sum(s, 7) <= u,
    decreases u, s.len(),
{
    if u == 0 {
        lemma_sum7_zero(s);
        return;
    }
    let top = (4 * (u - 1) + 3) as int;
    if exists|k: int| 0 <= k < s.len() && (#[trigger] s[k]).id == top {
        let k = choose|k: int| 0 <= k < s.len() && (#[trigger] s[k]).id == top;
        let t = s.remove(k);
        lemma_sum_remove(s, k, 7);
        assert forall|a: int, b: int| 0 <= a < t.len() && 0 <= b < t.len() && a != b implies (#[trigger] t[a]).id
            != (#[trigger] t[b]).id by {
            let aa = if a < k { a } else { a + 1 };
            let bb = if b < k { b } else { b + 1 };
            assert(t[a] == s[aa] && t[b] == s[bb]);
        }
        assert forall|j: int| 0 <= j < t.len() && (#[trigger] t[j]).id % 4 == 3 implies t[j].id / 4 < (u - 1) as nat by {
            let jj = if j < k { j } else { j + 1 };
            assert(t[j] == s[jj]);
            assert(jj != k);
        }
        lemma_sum7_le(t, (u - 1) as nat);
    } else {
        assert forall|j: int| 0 <= j < s.len() && (#[trigger] s[j]).id % 4 == 3 implies s[j].id / 4 < (u - 1) as nat by {
            assert(s[j].id != top);
        }
        lemma_sum7_le(s, (u - 1) as nat);
    }
}

proof fn lemma_sum7_zero(s: Seq<Entry>)
    requires
        forall|k: int| 0 <= k < s.len() ==> (#[trigger] s[k]).id % 4 != 3,
    ensures
        sum(s, 7) == 0,
    decreases s.len(),
{
    if s.len() > 0 {
        let p = s.drop_last();
        assert forall|k: int| 0 <= k < p.len() implies (#[trigger] p[k]).id % 4 != 3 by {
            assert(p[k] == s[k]);
        }
        lemma_sum7_zero(p);
        assert(s.last() == s[s.len() - 1]);
    }
}

/// Every entry is of type 0, 2 or 3: the entries are the three kinds' counts.
proof fn lemma_len_kinds(s: Seq<Entry>)
    requires
        forall|k: int| 0 <= k < s.len() ==> (#[trigger] s[k]).id % 4 != 1,
    ensures
        s.len() == sum(s, 4) + sum(s, 6) + sum(s, 7),
    decreases s.len(),
{
    if s.len() > 0 {
        let p = s.drop_last();
        assert forall|k: int| 0 <= k < p.len() implies (#[trigger] p[k]).id % 4 != 1 by {
            assert(p[k] == s[k]);
        }
        lemma_len_kinds(p);
        assert(s.last() == s[s.len() - 1]);
    }
}

/// At most `max_entries()` streams have an entry.
proof fn lemma_entries_bound(st: Streams)
    requires
        st.wf(),
    ensures
        st.entries@.len() <= max_entries(),
{
    let s = st.entries@;
    st.ids.lemma_wf();
    lemma_sum_kind_nonneg(s, 4);
    lemma_sum_kind_nonneg(s, 6);
    assert(st.ids.peer_side_ok(true));
    assert(st.ids.peer_side_ok(false));
    assert forall|k: int| 0 <= k < s.len() implies (#[trigger] s[k]).id % 4 != 1 by {
        assert(entry_ok(s[k], st.rx_bidi, st.rx_uni));
    }
    lemma_len_kinds(s);
    assert forall|k: int| 0 <= k < s.len() && (#[trigger] s[k]).id % 4 == 3 implies s[k].id / 4
        < st.ids.local_uni_spec().used_spec() by {
        assert(created(st.ids, s[k].id));
    }
    lemma_sum7_le(s, st.ids.local_uni_spec().used_spec() as nat);
    assert(st.live_peer_streams(true) <= MAX_LOCAL_STREAMS);
    assert(st.live_peer_streams(false) <= MAX_LOCAL_STREAMS);
}

/// Entry `i` of `t1` with its sending part's slot reaped (`ne`, all but the slot as before): the entry invariants
/// hold on, the sums but the reservation and the weight are unchanged, and those two do not grow.
proof fn lemma_reap_entry(
    t1: Seq<Entry>,
    i: int,
    ne: Entry,
    ids: StreamIds,
    rxb: u64,
    rxu: u64,
    rtr: Map<u64, Seq<SpecRecvIn>>,
    removed: Set<u64>,
    resets: Map<u64, u64>,
)
    requires
        entries_ok(t1, ids, rxb, rxu, rtr, removed, resets),
        records_ok(t1, ids, rxb, rxu, rtr, removed, resets),
        0 <= i < t1.len(),
        ne.id == t1[i].id,
        ne.recv == t1[i].recv,
        ne.send is Some == t1[i].send is Some,
        ne.send matches Some(p) ==> p.wf() && p.same_but_td(t1[i].send->0) && p.td_window()
            <= t1[i].send->0.td_window() && p.td_nodes() <= t1[i].send->0.td_nodes() && (t1[i].send->0.td_nodes()
            > 0 ==> p.td_nodes() < t1[i].send->0.td_nodes()),
    ensures
        entries_ok(t1.update(i, ne), ids, rxb, rxu, rtr, removed, resets),
        records_ok(t1.update(i, ne), ids, rxb, rxu, rtr, removed, resets),
        sum(t1.update(i, ne), 0) == sum(t1, 0),
        sum(t1.update(i, ne), 1) == sum(t1, 1),
        sum(t1.update(i, ne), 4) == sum(t1, 4),
        sum(t1.update(i, ne), 6) == sum(t1, 6),
        sum(t1.update(i, ne), 8) == sum(t1, 8),
        sum(t1.update(i, ne), 9) <= sum(t1, 9),
        val(ne, 11) <= val(t1[i], 11),
        etd(t1[i]) ==> val(ne, 11) < val(t1[i], 11),
        sum(t1.update(i, ne), 11) == sum(t1, 11) - val(t1[i], 11) + val(ne, 11),
        sflight(ne) == sflight(t1[i]),
{
    let t = t1.update(i, ne);
    assert(entry_ok(t1[i], rxb, rxu));
    if let Some(p) = ne.send {
        let q = t1[i].send->0;
        p.lemma_same_but_td(q);
        lemma_wt(p.ranges_held(), p.td_nodes(), q.ranges_held(), q.td_nodes());
    }
    assert(entry_ok(ne, rxb, rxu));
    assert forall|k: int| 0 <= k < t.len() && k != i implies #[trigger] t[k] == t1[k] by {}
    assert(forall|k: int| 0 <= k < t.len() ==> #[trigger] t[k].id == t1[k].id);
    assert forall|id: u64| #[trigger] has_id(t, id) == has_id(t1, id) by {
        if has_id(t1, id) {
            let k = choose|k: int| 0 <= k < t1.len() && (#[trigger] t1[k]).id == id;
            assert(t[k].id == id);
        }
        if has_id(t, id) {
            let k = choose|k: int| 0 <= k < t.len() && (#[trigger] t[k]).id == id;
            assert(t1[k].id == id);
        }
    }
    lemma_sum_update(t1, i, ne, 0);
    lemma_sum_update(t1, i, ne, 1);
    lemma_sum_update(t1, i, ne, 4);
    lemma_sum_update(t1, i, ne, 6);
    lemma_sum_update(t1, i, ne, 8);
    lemma_sum_update(t1, i, ne, 9);
    lemma_sum_update(t1, i, ne, 11);
}

/// `deliver_at_head`'s entry step: entry `i`'s receiving part delivered (`e1`, when it has one) and its sending part's
/// slot reaped (`ne`): the entry invariants and sums `wf` reads, the delivery's retired credit in `sum(.., 1)`.
#[verifier::spinoff_prover]
proof fn lemma_head_ok(s0: Streams, i: int, e1: Entry, ne: Entry)
    requires
        s0.wf(),
        0 <= i < s0.entries@.len(),
        s0.entries@[i].recv is None ==> e1 == s0.entries@[i],
        s0.entries@[i].recv is Some ==> {
            &&& e1.id == s0.entries@[i].id
            &&& e1.send == s0.entries@[i].send
            &&& e1.recv is Some
            &&& e1.recv->0.wf()
            &&& e1.recv->0.id_spec() == s0.entries@[i].recv->0.id_spec()
            &&& e1.recv->0.window_spec() == s0.entries@[i].recv->0.window_spec()
            &&& counted(e1.recv->0.rfc()) == counted(s0.entries@[i].recv->0.rfc())
        },
        ne.id == e1.id,
        ne.recv == e1.recv,
        ne.send is Some == e1.send is Some,
        ne.send matches Some(p) ==> p.wf() && p.same_but_td(e1.send->0) && p.td_window() <= e1.send->0.td_window()
            && p.td_nodes() <= e1.send->0.td_nodes() && (e1.send->0.td_nodes() > 0 ==> p.td_nodes()
            < e1.send->0.td_nodes()),
    ensures
        ({
            let a = s0.entries@;
            let t = a.update(i, ne);
            let rtr = match ne.recv {
                Some(r) => s0.rtr@.insert(ne.id, r.trace()),
                None => s0.rtr@,
            };
            &&& entries_ok(t, s0.ids, s0.rx_bidi, s0.rx_uni, rtr, s0.removed@, s0.resets@)
            &&& records_ok(t, s0.ids, s0.rx_bidi, s0.rx_uni, rtr, s0.removed@, s0.resets@)
            &&& s0.conn_counted == s0.gone@ + sum(t, 0)
            &&& sum(t, 1) == sum(a, 1) - val(a[i], 1) + val(ne, 1)
            &&& sum(t, 1) <= sum(t, 0)
            &&& sum(t, 4) == sum(a, 4)
            &&& sum(t, 6) == sum(a, 6)
            &&& sum(t, 8) == sum(a, 8)
            &&& sum(t, 9) <= sum(a, 9)
            &&& val(ne, 11) <= val(a[i], 11)
            &&& etd(a[i]) ==> val(ne, 11) < val(a[i], 11)
            &&& sum(t, 11) == sum(a, 11) - val(a[i], 11) + val(ne, 11)
            &&& sflight(ne) == sflight(a[i])
        }),
{
    let a = s0.entries@;
    let t1 = a.update(i, e1);
    assert(entry_ok(a[i], s0.rx_bidi, s0.rx_uni));
    if a[i].recv is Some {
        s0.conn_recv.lemma_wf();
        lemma_recv_ok(s0, i, e1, 0);
        let rtr = s0.rtr@.insert(ne.id, ne.recv->0.trace());
        lemma_reap_entry(t1, i, ne, s0.ids, s0.rx_bidi, s0.rx_uni, rtr, s0.removed@, s0.resets@);
        assert(t1.update(i, ne) =~= a.update(i, ne));
        lemma_sum_update(a, i, e1, 1);
        lemma_sum_update(a, i, e1, 11);
        lemma_sum_update(a, i, e1, 9);
    } else {
        assert(t1 =~= a);
        lemma_reap_entry(a, i, ne, s0.ids, s0.rx_bidi, s0.rx_uni, s0.rtr@, s0.removed@, s0.resets@);
        assert forall|k: int| 0 <= k < a.len() implies terms_ok(#[trigger] a[k]) by {
            lemma_terms(a[k], s0.rx_bidi, s0.rx_uni);
        }
        let t = a.update(i, ne);
        assert forall|k: int| 0 <= k < t.len() implies terms_ok(#[trigger] t[k]) by {
            lemma_terms(t[k], s0.rx_bidi, s0.rx_uni);
        }
        lemma_sum_bounds(t);
        lemma_sum_update(a, i, ne, 1);
    }
}

/// `deliver_some`'s step on the queue's head, entry `i` (now `ne`): its term leaves the queue, or comes back with
/// fewer bytes pending or a lighter sending part; the other ids' terms are unchanged. `measure` falls.
proof fn lemma_head_measure(s0: Streams, s1: Streams, i: int, ne: Entry)
    requires
        s0.wf(),
        0 <= i < s0.entries@.len(),
        s0.q@.len() > 0,
        s0.q@[0] == s0.entries@[i].id,
        ne.id == s0.entries@[i].id,
        s1.entries@ == s0.entries@.update(i, ne),
        forall|j: u64| j != ne.id ==> #[trigger] s1.rx_spec(j) == s0.rx_spec(j),
        s1.q@ == (if ne.queued {
            s0.q@.drop_first().push(ne.id)
        } else {
            s0.q@.drop_first()
        }),
        recv_pending(s1.rx_spec(ne.id)) <= recv_pending(s0.rx_spec(ne.id)),
        val(ne, 11) <= val(s0.entries@[i], 11),
        ne.queued ==> recv_pending(s1.rx_spec(ne.id)) < recv_pending(s0.rx_spec(ne.id)) || val(ne, 11) < val(
            s0.entries@[i],
            11,
        ),
    ensures
        s1.measure() < s0.measure(),
{
    let qv = s0.q@;
    let x = ne.id;
    let rest = qv.drop_first();
    lemma_queue_ok(s0.entries@, s0.q);
    lemma_qinv_facts(s0.entries@, qv);
    lemma_qm_first(s0.qterm(), qv);
    assert forall|k: int| 0 <= k < rest.len() implies (s1.qterm())(#[trigger] rest[k]) == (s0.qterm())(rest[k]) by {
        assert(rest[k] == qv[k + 1]);
        assert(qv[k + 1] != qv[0]);
    }
    lemma_qm_ext(s1.qterm(), s0.qterm(), rest);
    if ne.queued {
        lemma_qm_push(s1.qterm(), rest, x);
    }
    lemma_sum_update(s0.entries@, i, ne, 11);
    lemma_sum_w_nonneg(s0.entries@);
    lemma_sum_w_nonneg(s1.entries@);
}

/// The queue's head `x` popped, its receiving part the only one changed: `rx_backlog` falls (by the head's term when
/// it leaves, by the bytes delivered when it is re-queued).
proof fn lemma_pop_measure(s0: Streams, s1: Streams, x: u64)
    requires
        s0.wf(),
        s0.q@.len() > 0,
        s0.q@[0] == x,
        forall|j: u64| j != x ==> #[trigger] s1.rx_spec(j) == s0.rx_spec(j),
        s1.q@ == s0.q@.drop_first() || (s1.q@ == s0.q@.drop_first().push(x) && recv_pending(s1.rx_spec(x))
            < recv_pending(s0.rx_spec(x))),
    ensures
        s1.rx_backlog() < s0.rx_backlog(),
{
    let qv = s0.q@;
    let rest = qv.drop_first();
    lemma_queue_ok(s0.entries@, s0.q);
    lemma_qinv_facts(s0.entries@, qv);
    lemma_qm_first(s0.qterm(), qv);
    assert forall|k: int| 0 <= k < rest.len() implies (s1.qterm())(#[trigger] rest[k]) == (s0.qterm())(rest[k]) by {
        assert(rest[k] == qv[k + 1]);
        assert(qv[k + 1] != qv[0]);
    }
    lemma_qm_ext(s1.qterm(), s0.qterm(), rest);
    if s1.q@ != rest {
        lemma_qm_push(s1.qterm(), rest, x);
    }
}

/// Same queue, same receiving parts: same `rx_backlog`.
proof fn lemma_backlog_same(s0: Streams, s1: Streams)
    requires
        s1.q@ == s0.q@,
        s1.rx_bidi == s0.rx_bidi,
        s1.rx_uni == s0.rx_uni,
        forall|j: u64| #[trigger] s1.rx_trace(j) == s0.rx_trace(j),
    ensures
        s1.rx_backlog() == s0.rx_backlog(),
{
    let qv = s0.q@;
    assert forall|k: int| 0 <= k < qv.len() implies (s1.qterm())(#[trigger] qv[k]) == (s0.qterm())(qv[k]) by {
        assert(s1.rx_trace(qv[k]) == s0.rx_trace(qv[k]));
    }
    lemma_qm_ext(s1.qterm(), s0.qterm(), qv);
}

/// Same queue, the same bytes past delivery on every receiving part: same `rx_backlog`.
proof fn lemma_backlog_pending(s0: Streams, s1: Streams)
    requires
        s1.q@ == s0.q@,
        forall|j: u64| #[trigger] recv_pending(s1.rx_spec(j)) == recv_pending(s0.rx_spec(j)),
    ensures
        s1.rx_backlog() == s0.rx_backlog(),
{
    let qv = s0.q@;
    assert forall|k: int| 0 <= k < qv.len() implies (s1.qterm())(#[trigger] qv[k]) == (s0.qterm())(qv[k]) by {
        assert(recv_pending(s1.rx_spec(qv[k])) == recv_pending(s0.rx_spec(qv[k])));
    }
    lemma_qm_ext(s1.qterm(), s0.qterm(), qv);
}

/// A step on entry `i`'s sending part that may fill its slot (a reset; `ne` after it, queued now if `enq`): the queue
/// step `lemma_swap` takes, with room for the id.
proof fn lemma_reset_enqueue(s0: Streams, i: int, ne: Entry, enq: bool)
    requires
        s0.wf(),
        0 <= i < s0.entries@.len(),
        ne.id == s0.entries@[i].id,
        ne.recv == s0.entries@[i].recv,
        etd(s0.entries@[i]) ==> etd(ne),
        enq == (!s0.entries@[i].queued && etd(ne)),
        ne.queued == (s0.entries@[i].queued || enq),
    ensures
        s0.q.wf(),
        enq ==> s0.q@.len() < IDQ_CAP,
        !enq ==> qkeep(s0.entries@[i], ne),
        enq ==> !s0.entries@[i].queued && ne.queued && etd(ne),
{
    let a = s0.entries@;
    lemma_queue_ok(a, s0.q);
    lemma_qinv_facts(a, s0.q@);
    if enq {
        lemma_entries_bound(s0);
        lemma_qcount_le(a);
        assert(IDQ_CAP == max_entries()) by (compute_only);
    }
}

/// The queue after entry `i` became `ne`: unchanged with the flag kept (`qkeep`), or the id appended as it became
/// queued.
proof fn lemma_queue_step(s0: Streams, i: int, ne: Entry, q1: IdQueue)
    requires
        s0.wf(),
        0 <= i < s0.entries@.len(),
        ne.id == s0.entries@[i].id,
        entry_ok(ne, s0.rx_bidi, s0.rx_uni),
        ({
            ||| q1 == s0.q && qkeep(s0.entries@[i], ne)
            ||| q1.wf() && q1@ == s0.q@.push(ne.id) && !s0.entries@[i].queued && ne.queued && (ne.recv is Some
                || etd(ne)) && (etd(s0.entries@[i]) ==> etd(ne))
        }),
    ensures
        queue_ok(s0.entries@.update(i, ne), q1),
{
    let a = s0.entries@;
    lemma_queue_ok(a, s0.q);
    lemma_qinv_facts(a, s0.q@);
    assert(ids_distinct(a));
    assert(entry_ok(a[i], s0.rx_bidi, s0.rx_uni));
    if eready(ne) && !ne.queued {
        assert(eready(a[i]) ==> a[i].queued);
    }
    if etd(ne) && !ne.queued {
        assert(etd(a[i]) ==> a[i].queued);
    }
    if ne.queued && q1 == s0.q {
        assert(a[i].recv is Some || etd(a[i]));
    }
    lemma_qinv_set(a, i, ne, s0.q@, q1@);
    lemma_queue_ok(a.update(i, ne), q1);
}

/// A queued id's term is at most a window plus one: its receiving part's bytes past delivery, none without one.
proof fn lemma_qterm_le(s: Streams, i: int)
    requires
        s.wf(),
        0 <= i < s.entries@.len(),
    ensures
        (s.qterm())(s.entries@[i].id) <= MAX_RECV_WINDOW + 1,
{
    let e = s.entries@[i];
    let id = e.id;
    assert(entry_ok(e, s.rx_bidi, s.rx_uni));
    if let Some(r) = e.recv {
        r.lemma_wf();
        assert(s.rx_spec(id) == r.rfc());
    } else {
        assert(!s.rtr@.contains_key(id)) by {
            s.ids.lemma_wf();
            assert(created(s.ids, id));
        }
        assert(s.rx_trace(id) == Seq::<SpecRecvIn>::empty());
        assert(s.rx_spec(id) == recv_init(s.rx_window(id)));
    }
}

/// The reset's measure: the part's weight falls by at least `kw()` when its slot takes a node, more than its queueing
/// adds; the receiving parts and the rest of the queue are as they were.
proof fn lemma_reset_measure(s0: Streams, s1: Streams, i: int, ne: Entry, enq: bool)
    requires
        s0.wf(),
        0 <= i < s0.entries@.len(),
        ne.id == s0.entries@[i].id,
        s1.entries@ == s0.entries@.update(i, ne),
        s1.rx_bidi == s0.rx_bidi,
        s1.rx_uni == s0.rx_uni,
        forall|j: u64| #[trigger] s1.rx_trace(j) == s0.rx_trace(j),
        enq ==> s1.q@ == s0.q@.push(ne.id),
        !enq ==> s1.q@ == s0.q@,
        val(ne, 11) + (if enq { kw() } else { 0int }) <= val(s0.entries@[i], 11),
    ensures
        s1.measure() <= s0.measure(),
{
    let a = s0.entries@;
    lemma_sum_update(a, i, ne, 11);
    lemma_sum_w_nonneg(a);
    lemma_sum_w_nonneg(s1.entries@);
    let qv = s0.q@;
    assert forall|k: int| 0 <= k < qv.len() implies (s1.qterm())(#[trigger] qv[k]) == (s0.qterm())(qv[k]) by {
        assert(s1.rx_trace(qv[k]) == s0.rx_trace(qv[k]));
    }
    lemma_qm_ext(s1.qterm(), s0.qterm(), qv);
    if enq {
        lemma_qm_push(s1.qterm(), qv, ne.id);
        lemma_qterm_le(s0, i);
        assert(s1.rx_spec(ne.id) == s0.rx_spec(ne.id));
    }
}

/// A queue step for entry `i`, now `ne`: queued now (`enq`, its id to be appended) if it has bytes or the FIN left,
/// or a non-empty teardown slot, and was not; the queue has room for it: every queued id is a live entry's, at most
/// `max_entries()` (`IDQ_CAP`, D13).
proof fn lemma_enqueue(s0: Streams, i: int, ne: Entry, enq: bool)
    requires
        s0.wf(),
        0 <= i < s0.entries@.len(),
        ne.id == s0.entries@[i].id,
        ne.queued ==> ne.recv is Some || etd(ne),
        enq == ((eready(ne) || etd(ne)) && !s0.entries@[i].queued),
        ne.queued == (s0.entries@[i].queued || enq),
    ensures
        s0.q.wf(),
        enq ==> s0.q@.len() < IDQ_CAP,
        qinv(s0.entries@.update(i, ne), if enq {
            s0.q@.push(ne.id)
        } else {
            s0.q@
        }),
{
    let a = s0.entries@;
    lemma_queue_ok(a, s0.q);
    lemma_qinv_facts(a, s0.q@);
    assert(ids_distinct(a));
    lemma_qinv_set(a, i, ne, s0.q@, if enq {
        s0.q@.push(ne.id)
    } else {
        s0.q@
    });
    if enq {
        lemma_entries_bound(s0);
        lemma_qcount_le(a);
        assert(IDQ_CAP == max_entries()) by (compute_only);
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

/// What feeding frame `f` to receiving part `r0` (now `r1`) did, with `room` bytes of connection
/// credit left: `on_data` (then `deliver` of at most the frame's bytes) or `on_reset`. Its error
/// and credit are those of the frame's own input.
spec fn fed(
    r0: RecvStream,
    r1: RecvStream,
    f: SpecFrame,
    room: u64,
    ev0: Seq<StreamEvent>,
    ev1: Seq<StreamEvent>,
    r: Result<u64, u64>,
) -> bool {
    let t2 = r0.trace().push(frame_recv_in(f)->0);
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
        &&& r1.trace() == r0.trace() + frame_recv_ins(f)
        &&& counted(r1.rfc()) == counted(s2)
        &&& event_views(ev1) == event_views(ev0) + r1.rfc().events.skip(s1.events.len() as int)
    }
}

/// STREAM or RESET_STREAM `f` to `rs`. The costs `on_data`, `deliver` and `on_reset` return are
/// dropped here: their composition through `Streams::on_frame` and `on_datagram` is 9b2 Task 10d's
/// (item 4, the STREAM-path cost composition); `find`'s scan is Q20's (9b4).
fn feed_recv(rs: &mut RecvStream, f: &Frame, room: u64, ev: &mut Vec<StreamEvent>) -> (r: Result<
    u64,
    u64,
>)
    requires
        old(rs).wf(),
        frame_wf(f@),
        frame_recv_in(f@) is Some,
    ensures
        fed(*old(rs), *final(rs), f@, room, old(ev)@, final(ev)@, r),
{
    let ghost r0 = *rs;
    match f {
        Frame::Stream { .. } => feed_stream(rs, f, room, ev),
        Frame::ResetStream { error_code, final_size, .. } => {
            let (r, _) = rs.on_reset(*error_code, *final_size, room, ev);
            proof {
                assert(r0.trace() + frame_recv_ins(f@) =~= r0.trace().push(frame_recv_in(f@)->0));
            }
            r
        },
        _ => Ok(0),
    }
}

/// `feed_recv` for STREAM: `on_data`, then `deliver` of at most the frame's bytes (D12).
#[verifier::spinoff_prover]
fn feed_stream(rs: &mut RecvStream, f: &Frame, room: u64, ev: &mut Vec<StreamEvent>) -> (r: Result<
    u64,
    u64,
>)
    requires
        old(rs).wf(),
        frame_wf(f@),
        f@ is Stream,
    ensures
        fed(*old(rs), *final(rs), f@, room, old(ev)@, final(ev)@, r),
        r matches Err(c) ==> match f@ {
            SpecFrame::Stream { offset, data, fin, .. } => recv_allowed_err(
                old(rs).rfc(),
                offset as nat,
                data.len(),
                fin,
                room as nat,
                c,
            ),
            _ => true,
        },
{
    let ghost r0 = *rs;
    proof {
        r0.lemma_wf();
    }
    match f {
        Frame::Stream { offset, data, fin, .. } => {
            let (r, _) = rs.on_data(*offset, data.as_slice(), *fin, room);
            if r.is_ok() {
                let ghost r1 = *rs;
                let _ = rs.deliver(data.len() as u64, ev);
                proof {
                    let i = frame_recv_in(f@)->0;
                    let d = SpecRecvIn::Deliver { max: data@.len() };
                    r1.lemma_wf();
                    lemma_recv_push(r0.id_spec(), r0.window_spec(), r1.trace(), d);
                    lemma_deliver_fields(r0.id_spec(), r1.rfc(), data@.len());
                    assert(r0.trace() + frame_recv_ins(f@) =~= r0.trace().push(i).push(d));
                }
            }
            r
        },
        _ => Ok(0),
    }
}

/// `deliver_at_head`'s step on the entry it took out: at most `budget` bytes delivered, the entry
/// queued again while bytes or the FIN are left. Returns the credit retired, the cost, and whether
/// it stays queued (split for the rlimit).
#[verifier::spinoff_prover]
fn deliver_entry(e: &mut Entry, budget: u64, ev: &mut Vec<StreamEvent>) -> (r: (u64, Ghost<nat>, bool))
    requires
        old(e).recv is Some,
        old(e).recv->0.wf(),
        budget >= 1,
    ensures
        final(e).id == old(e).id,
        final(e).send == old(e).send,
        final(e).recv is Some,
        ({
            let r0 = old(e).recv->0;
            let r1 = final(e).recv->0;
            &&& r1.wf()
            &&& r1.id_spec() == r0.id_spec()
            &&& r1.window_spec() == r0.window_spec()
            &&& r1.trace() == r0.trace().push(SpecRecvIn::Deliver { max: budget as nat })
            &&& counted(r1.rfc()) == counted(r0.rfc())
            &&& retired(r0.rfc()) + r.0 == retired(r1.rfc())
            &&& r.2 ==> recv_pending(r1.rfc()) < recv_pending(r0.rfc())
            &&& recv_pending(r1.rfc()) <= recv_pending(r0.rfc())
        }),
        r.2 == eready(*final(e)),
        final(e).queued == r.2,
        r.1@ <= c_rd() * (budget + budget as nat / (PAGE as nat) + 2) + 1,
{
    let mut rs = match e.recv.take() {
        Some(rs) => rs,
        None => RecvStream::new(0, 0),  // unreachable: required Some
    };
    let ghost rs0 = rs;
    let t0 = rs.retired_exec();
    let (_, c) = rs.deliver(budget, ev);
    proof {
        let x = rs0.id_spec();
        let w = rs0.window_spec();
        let d = SpecRecvIn::Deliver { max: budget as nat };
        rs0.lemma_wf();
        lemma_counted_monotone(x, w, rs0.trace(), d);
        lemma_recv_push(x, w, rs0.trace(), d);
        lemma_deliver_fields(x, rs0.rfc(), budget as nat);
        lemma_deliver_progress(x, rs0.rfc(), budget as nat);
    }
    let t1 = rs.retired_exec();
    let ready = rs.has_ready();
    e.recv = Some(rs);
    e.queued = ready;
    (t1 - t0, c, ready)
}

/// `apply_recv`'s step on the entry it took out: the frame to its receiving part, then the queue
/// flag (D13: an entry with bytes or the FIN left undelivered is queued). Returns the frame's
/// result, the credit the part retired, and whether the entry was newly queued (split for the
/// rlimit).
#[verifier::spinoff_prover]
fn feed_entry(e: &mut Entry, f: &Frame, room: u64, ev: &mut Vec<StreamEvent>) -> (r: (
    Result<u64, u64>,
    u64,
    bool,
))
    requires
        old(e).recv is Some,
        old(e).recv->0.wf(),
        frame_wf(f@),
        frame_recv_in(f@) is Some,
        eready(*old(e)) ==> old(e).queued,
    ensures
        final(e).id == old(e).id,
        final(e).send == old(e).send,
        final(e).recv is Some,
        fed(old(e).recv->0, final(e).recv->0, f@, room, old(ev)@, final(ev)@, r.0),
        retired(old(e).recv->0.rfc()) + r.1 == retired(final(e).recv->0.rfc()),
        r.0 matches Ok(n) ==> counted(old(e).recv->0.rfc()) + n == counted(final(e).recv->0.rfc()),
        r.2 == (eready(*final(e)) && !old(e).queued),
        final(e).queued == (old(e).queued || r.2),
        r.0 is Err ==> *final(e) == *old(e),
        // A STREAM frame's errors are RFC 9000's (`on_data`); a RESET_STREAM's are `on_reset`'s.
        r.0 matches Err(c) ==> match f@ {
            SpecFrame::Stream { offset, data, fin, .. } => recv_allowed_err(
                old(e).recv->0.rfc(),
                offset as nat,
                data.len(),
                fin,
                room as nat,
                c,
            ),
            _ => true,
        },
{
    let mut rs = match e.recv.take() {
        Some(rs) => rs,
        None => RecvStream::new(0, 0),  // unreachable: required Some
    };
    let ghost rs0 = rs;
    let t0 = rs.retired_exec();
    let res = match f {
        Frame::Stream { .. } => feed_stream(&mut rs, f, room, ev),
        _ => feed_recv(&mut rs, f, room, ev),
    };
    proof {
        let id = rs0.id_spec();
        let w = rs0.window_spec();
        let i = frame_recv_in(f@)->0;
        let t2 = rs0.trace().push(i);
        if res is Ok {
            lemma_counted_monotone(id, w, rs0.trace(), i);
            if f@ is Stream {
                lemma_counted_monotone(id, w, t2, frame_recv_ins(f@)[1]);
                assert(rs.trace() =~= t2.push(frame_recv_ins(f@)[1]));
            } else {
                assert(rs.trace() =~= t2);
            }
        }
    }
    let t1 = rs.retired_exec();
    let ready = rs.has_ready();
    e.recv = Some(rs);
    let enq = ready && !e.queued;
    if enq {
        e.queued = true;
    }
    (res, t1 - t0, enq)
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
            &&& sum(t, 9) == sum(s0.entries@, 9)
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
    lemma_sum_update(a, i, ne, 9);
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
        forall|j: u64| #[trigger] s1.tx_flight(j) == s0.tx_flight(j),
        post_rest(s1, s2, f, ev0, ev1, r),
    ensures
        post_rest(s0, s2, f, ev0, ev1, r),
        rx_outcome(s1, f) == rx_outcome(s0, f),
{
    assert forall|j: u64| !#[trigger] s2.send_reset(j) implies s2.tx_flight(j) == s0.tx_flight(j) && s2.send_reset(j)
        == s0.send_reset(j) by {
        assert(s1.send_reset(j) == s0.send_reset(j));
        assert(s1.tx_flight(j) == s0.tx_flight(j));
    }
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
        forall|j: u64| #[trigger] s2.tx_flight(j) == s1.tx_flight(j),
        post_rest(s0, s1, f, ev0, ev1, r),
    ensures
        post_rest(s0, s2, f, ev0, ev1, r),
{
    assert forall|j: u64| !#[trigger] s2.send_reset(j) implies s2.tx_flight(j) == s0.tx_flight(j) && s2.send_reset(j)
        == s0.send_reset(j) by {
        assert(s1.send_reset(j) == s2.send_reset(j));
        assert(s2.tx_flight(j) == s1.tx_flight(j));
    }
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
        tx_kept_but(s1, s2, None),
    ensures
        post_rest(s0, s2, f, ev0, ev1, r),
{
    assert forall|j: u64| !#[trigger] s2.send_reset(j) implies s2.tx_flight(j) == s0.tx_flight(j) && s2.send_reset(j)
        == s0.send_reset(j) by {
        assert(s1.send_reset(j) == s2.send_reset(j));
    }
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

/// `poll_max_data` committed MAX_DATA (`s1` to `s2`, only `conn_recv` changed, its limit not lowered): the polling
/// state is still kept (split from `poll_max_data` for the rlimit).
proof fn lemma_max_data_kept(s0: Streams, s1: Streams, s2: Streams, n: int, out: Seq<Frame>)
    requires
        kept(s0, s1),
        sends_same(s0, s1),
        out_tx(s1, n, out),
        s2.conn_recv.wf(),
        s1.conn_recv.limit_spec() <= s2.conn_recv.limit_spec(),
        s2.conn_recv.consumed_spec() == s1.conn_recv.consumed_spec(),
        s2.conn_recv.window_spec() == s1.conn_recv.window_spec(),
        s2.conn_recv.cap_spec() == s1.conn_recv.cap_spec(),
        s2 == (Streams { conn_recv: s2.conn_recv, ..s1 }),
    ensures
        kept(s0, s2),
        sends_same(s0, s2),
        out_tx(s2, n, out),
{
    assert(forall|j: u64| #[trigger] s2.rx_spec(j) == s1.rx_spec(j));
}

/// `poll_max_streams` committed this direction's MAX_STREAMS (`s1` to `s2`, only `ids`
/// changed): the polling state is still kept (split from `poll_max_streams` for the rlimit).
#[verifier::spinoff_prover]
proof fn lemma_max_streams_kept(
    s0: Streams,
    s1: Streams,
    s2: Streams,
    bidi: bool,
    n: int,
    out: Seq<Frame>,
)
    requires
        kept(s0, s1),
        sends_same(s0, s1),
        out_tx(s1, n, out),
        s2.ids.wf(),
        forall|b: bool| #[trigger] s2.ids.peer_opened_spec(b) == s1.ids.peer_opened_spec(b),
        s2.ids.peer_credit_spec(!bidi) == s1.ids.peer_credit_spec(!bidi),
        s2.ids.local_uni_spec() == s1.ids.local_uni_spec(),
        ({
            let c0 = s1.ids.peer_credit_spec(bidi);
            let c1 = s2.ids.peer_credit_spec(bidi);
            &&& c1.consumed_spec() == c0.consumed_spec()
            &&& c1.window_spec() == c0.window_spec()
        }),
        s2 == (Streams { ids: s2.ids, ..s1 }),
    ensures
        kept(s0, s2),
        sends_same(s0, s2),
        out_tx(s2, n, out),
{
    assert forall|b: bool|
        {
            &&& #[trigger] s2.ids.peer_opened_spec(b) == s1.ids.peer_opened_spec(b)
            &&& s2.ids.peer_credit_spec(b).consumed_spec() == s1.ids.peer_credit_spec(
                b,
            ).consumed_spec()
            &&& s2.ids.peer_credit_spec(b).window_spec() == s1.ids.peer_credit_spec(
                b,
            ).window_spec()
        } by {
        if b != bidi {
            assert(b == !bidi);
        }
    }
    lemma_ids_frame(s1, s2);
    assert(forall|j: u64| #[trigger] s2.rx_spec(j) == s1.rx_spec(j));
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
        qkeep(s0.entries@[i], ne) ==> queue_ok(s0.entries@.update(i, ne), s0.q),
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
    if qkeep(a[i], ne) {
        lemma_queue_ok(a, s0.q);
        lemma_qinv_facts(a, s0.q@);
        assert(ids_distinct(a));
        if eready(ne) {
            assert(eready(a[i]) ==> a[i].queued);
        }
        if etd(ne) {
            assert(etd(a[i]) ==> a[i].queued);
        }
        if ne.queued {
            assert(a[i].recv is Some || etd(a[i]));
            assert(entry_ok(ne, s0.rx_bidi, s0.rx_uni));
        }
        lemma_qinv_set(a, i, ne, s0.q@, s0.q@);
        lemma_queue_ok(t, s0.q);
    }
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
        if k != i {
            assert(t[k] == a[k]);
            assert(t[k].id != id);
        }
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
        !e.queued,
        e.recv matches Some(r) ==> terminal(r.rfc().state),
        s1.entries@ == s0.entries@.remove(i),
        s1.q == s0.q,
        s1.conn_recv == s0.conn_recv,
        s1.conn_counted == s0.conn_counted,
        s1.conn_send == s0.conn_send,
        s1.rx_conn == s0.rx_conn,
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
        s1.tx_held() <= s0.tx_held(),
{
    let a = s0.entries@;
    let t = s1.entries@;
    let id = e.id;
    s0.ids.lemma_wf();
    s1.ids.lemma_wf();
    lemma_queue_ok(a, s0.q);
    lemma_qinv_remove(a, i, s0.q@);
    lemma_queue_ok(t, s1.q);
    assert(entry_ok(e, s0.rx_bidi, s0.rx_uni));
    lemma_sum_remove(a, i, 0);
    lemma_sum_remove(a, i, 1);
    lemma_sum_remove(a, i, 4);
    lemma_sum_remove(a, i, 6);
    lemma_sum_remove(a, i, 8);
    lemma_sum_remove(a, i, 9);
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
        e.send matches Some(p) ==> p.wf() && p.reset_spec() is None && p.sent_end() == 0
            && p.held_spec() == 0 && p.td_nodes() == 0 && p.td_window() == 0,
        s1.entries@ == s0.entries@.push(e),
        s1.rtr@ == s0.rtr@.insert(x, Seq::<SpecRecvIn>::empty()),
        s1.q == s0.q,
        !e.queued,
        s1.conn_recv == s0.conn_recv,
        s1.conn_counted == s0.conn_counted,
        s1.conn_send == s0.conn_send,
        s1.rx_conn == s0.rx_conn,
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
        s1.tx_held() == s0.tx_held(),
{
    let b = x % 4 == 0;
    let a = s0.entries@;
    let t = s1.entries@;
    s0.ids.lemma_wf();
    s1.ids.lemma_wf();
    let r = e.recv->0;
    r.lemma_wf();
    lemma_recv_inv(x, r.window_spec(), Seq::empty());
    // Nothing to deliver yet: the queue is unchanged.
    let m0 = rfc_received(Seq::<(nat, Seq<u8>)>::empty());
    assert(m0 =~= Map::<nat, u8>::empty());
    lemma_contiguous_is(m0, 0);
    assert(!eready(e));
    lemma_queue_ok(a, s0.q);
    lemma_qinv_push(a, e, s0.q@);
    lemma_queue_ok(t, s1.q);
    // The new entry counts nothing yet.
    assert(val(e, 0) == 0 && val(e, 1) == 0 && val(e, 2) == 0 && val(e, 3) == 0);
    assert(val(e, kq(b)) == 1 && val(e, kq(!b)) == 0 && val(e, 8) == 0 && val(e, 9) == 0);
    lemma_sum_push(a, e, 9);
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
        _ => is_stream_layer_frame(f),
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

pub proof fn lemma_frames_bytes_push(fs: Seq<SpecFrame>, f: SpecFrame)
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
        piece_of(f@) is None,
        no_piece(old(out)@, pre.len() as int),
    ensures
        out_ok(s0, pre, budget, final(out)@, *final(room)),
        out_tx(cur, pre.len() as int, final(out)@),
        no_piece(final(out)@, pre.len() as int),
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

/// The fit rule: the best length over 1-, 2-, 4- and 8-byte length fields; 0 (a lone FIN) when
/// only `hdr + 1` fits (split from `poll_stream` for the rlimit).
fn best_fit(room: usize, hdr: usize, want: u64) -> (best: u64)
    requires
        hdr + 1 <= room,
    ensures
        best <= VARINT_MAX,
        hdr + rfc_varint_min_len(best) + best <= room,
{
    let mut best: u64 = 0;
    let ghost mut bw: int = 1;
    if let Some(n) = fit(room, hdr, 1, want) {
        if n > best {
            best = n;
            proof {
                bw = 1;
            }
        }
    }
    if let Some(n) = fit(room, hdr, 2, want) {
        if n > best {
            best = n;
            proof {
                bw = 2;
            }
        }
    }
    if let Some(n) = fit(room, hdr, 4, want) {
        if n > best {
            best = n;
            proof {
                bw = 4;
            }
        }
    }
    if let Some(n) = fit(room, hdr, 8, want) {
        if n > best {
            best = n;
            proof {
                bw = 8;
            }
        }
    }
    assert(hdr + bw + best <= room && rfc_varint_min_len(best) <= bw);
    best
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
#[verifier::spinoff_prover]
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
        final(p).td_nodes() == old(p).td_nodes(),
        final(p).td_window() == old(p).td_window(),
        final(p).wf(),
        final(cs).wf(),
        final(p).reset_spec() == old(p).reset_spec(),
        final(cs).max() == old(cs).max(),
        final(p).sent_end() - old(p).sent_end() == final(cs).used() - old(cs).used(),
        final(p).sent_end() >= old(p).sent_end(),
        final(p).held_spec() <= old(p).held_spec(),
        out_ok(s0, pre, budget, final(out)@, *final(room)),
        final(out)@.len() >= old(out)@.len(),
        final(out)@.subrange(0, old(out)@.len() as int) == old(out)@,
        streamed(final(out)@, old(out)@.len() as int, id, final(p).sent_end()),
        gained(old(p).flight_spec(), final(p).flight_spec(), frames_view(final(out)@.skip(old(out)@.len() as int)), id),
{
    hide(out_ok);
    let ghost p0 = *p;
    let ghost c0 = *cs;
    let ghost o0 = out@;
    proof {
        assert(out@.subrange(0, o0.len() as int) =~= o0);
        assert(frames_view(o0.skip(o0.len() as int)) =~= Seq::<SpecFrame>::empty());
        lemma_gained_empty(p0.flight_spec(), id);
    }
    loop
        invariant
            p.td_nodes() == p0.td_nodes(),
            p.td_window() == p0.td_window(),
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
            p.held_spec() <= p0.held_spec(),
            out@.len() >= o0.len(),
            out@.subrange(0, o0.len() as int) == o0,
            streamed(out@, o0.len() as int, id, p.sent_end()),
            gained(p0.flight_spec(), p.flight_spec(), frames_view(out@.skip(o0.len() as int)), id),
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
        let best = best_fit(*room, hdr, p.want());
        let ghost ps = p.sent_end();
        let ghost ob = out@;
        let ghost pf = p.flight_spec();
        if !poll_chunk(p, id, off, hdr, best, cs, room, out, Ghost(s0), Ghost(pre), Ghost(budget)) {
            break;
        }
        proof {
            lemma_streamed_push(ob, o0, id, ps, p.sent_end(), out@.last());
            assert(ob.push(out@.last()) =~= out@);
            assert(frames_view(out@.skip(o0.len() as int)) =~= frames_view(ob.skip(o0.len() as int)) + seq![
                out@.last()@,
            ]);
            lemma_gained_trans(p0.flight_spec(), pf, p.flight_spec(), frames_view(ob.skip(o0.len() as int)), seq![
                out@.last()@,
            ], id);
        }
    }
}

/// One `poll_data` of `p` at `off`, sized `best`, appended to `out` as a STREAM frame of stream `id` (split from
/// `poll_stream` for the rlimit). `false`: nothing sent, nothing changed.
#[verifier::spinoff_prover]
fn poll_chunk(
    p: &mut SendStream,
    id: u64,
    off: u64,
    hdr: usize,
    best: u64,
    cs: &mut SendCredit,
    room: &mut usize,
    out: &mut Vec<Frame>,
    Ghost(s0): Ghost<Streams>,
    Ghost(pre): Ghost<Seq<Frame>>,
    Ghost(budget): Ghost<nat>,
) -> (sent: bool)
    requires
        old(p).wf(),
        old(cs).wf(),
        id <= VARINT_MAX,
        match s0.tx_part(id) {
            Some(q) => !no_data(q.state()),
            None => false,
        },
        out_ok(s0, pre, budget, old(out)@, *old(room)),
        old(p).next_off() == Some(off),
        hdr == 1 + rfc_varint_min_len(id) + if off > 0 {
            rfc_varint_min_len(off)
        } else {
            0
        },
        best <= VARINT_MAX,
        hdr + rfc_varint_min_len(best) + best <= *old(room),
    ensures
        final(p).td_nodes() == old(p).td_nodes(),
        final(p).td_window() == old(p).td_window(),
        final(p).wf(),
        final(cs).wf(),
        final(p).reset_spec() == old(p).reset_spec(),
        final(cs).max() == old(cs).max(),
        final(p).sent_end() - old(p).sent_end() == final(cs).used() - old(cs).used(),
        final(p).sent_end() >= old(p).sent_end(),
        final(p).held_spec() <= old(p).held_spec(),
        out_ok(s0, pre, budget, final(out)@, *final(room)),
        !sent ==> final(out)@ == old(out)@ && *final(p) == *old(p),
        sent ==> *final(room) < *old(room) && final(out)@.len() == old(out)@.len() + 1 && final(out)@.drop_last()
            == old(out)@ && (final(out)@.last()@ matches SpecFrame::Stream { stream_id, offset, data, .. }
            && stream_id == id && offset + data.len() <= final(p).sent_end()),
        sent ==> gained(old(p).flight_spec(), final(p).flight_spec(), seq![final(out)@.last()@], id),
{
    hide(out_ok);
    proof {
        cs.lemma_wf();
    }
    let ghost p0 = *p;
    match p.poll_data(best, cs.available()) {
        None => false,
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
                assert(f@ == SpecFrame::Stream { stream_id: id, offset: cv.off, data: cv.data, fin: cv.fin });
                lemma_out_push(s0, pre, budget, out@, *room, f, (*room - len) as usize);
            }
            *room = *room - len;
            let ghost ob = out@;
            out.push(f);
            proof {
                assert(out@.drop_last() =~= ob);
                p0.lemma_wf();
                lemma_gained_one(p0.flight_spec(), p.flight_spec(), out@.last()@, id);
            }
            true
        },
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
    &&& s.rx_conn == s0.rx_conn
    &&& s.q == s0.q
    &&& s.tx_held() <= s0.tx_held()
    &&& s.entries@.len() == s0.entries@.len()
    &&& forall|k: int|
        0 <= k < s.entries@.len() ==> (#[trigger] s.entries@[k]).id == s0.entries@[k].id
    &&& forall|b: bool| #[trigger] s.ids.peer_opened_spec(b) == s0.ids.peer_opened_spec(b)
    &&& forall|j: u64| #[trigger]
        s.rx_spec(j).state == s0.rx_spec(j).state && s.rx_spec(j).stopped == s0.rx_spec(
            j,
        ).stopped && s.rx_spec(j).events == s0.rx_spec(j).events
}

/// The pieces in flight of an entry's sending part.
spec fn sflight(e: Entry) -> Option<Set<(u64, u64)>> {
    match e.send {
        Some(p) => Some(p.flight_spec()),
        None => None,
    }
}

/// Every sending part is in the state it had at the start, with the same pieces in flight.
spec fn sends_same(s0: Streams, s: Streams) -> bool {
    &&& forall|k: int|
        0 <= k < s.entries@.len() ==> sstate(#[trigger] s.entries@[k]) == sstate(s0.entries@[k])
    &&& forall|k: int|
        0 <= k < s.entries@.len() ==> sflight(#[trigger] s.entries@[k]) == sflight(s0.entries@[k])
}

/// No frame of `out` from `n` on has a piece: the control frames (D10 (b)).
spec fn no_piece(out: Seq<Frame>, n: int) -> bool {
    forall|k: int| n <= k < out.len() ==> piece_of(#[trigger] out[k]@) is None
}

#[verifier::spinoff_prover]
proof fn lemma_no_piece(out: Seq<Frame>, n: int)
    requires
        0 <= n <= out.len(),
        no_piece(out, n),
    ensures
        frame_pieces(frames_view(out.skip(n))) == Multiset::<PieceKey>::empty(),
{
    let v = frames_view(out.skip(n));
    assert forall|i: int| 0 <= i < v.len() implies piece_of(#[trigger] v[i]) is None by {
        assert(v[i] == out[n + i]@);
    }
    lemma_frame_pieces_none(v);
}

/// `sends_same` with the same IDs at each index: every stream's flight as at the start.
#[verifier::spinoff_prover]
proof fn lemma_flights_same(s0: Streams, s: Streams)
    requires
        kept(s0, s),
        sends_same(s0, s),
    ensures
        forall|j: u64| #[trigger] s.tx_flight(j) == s0.tx_flight(j),
{
    assert forall|j: u64| #[trigger] s.tx_flight(j) == s0.tx_flight(j) by {
        if has_id(s.entries@, j) {
            let k = choose|k: int| 0 <= k < s.entries@.len() && (#[trigger] s.entries@[k]).id == j;
            lemma_part_at(s, k);
            lemma_part_at(s0, k);
            assert(sflight(s.entries@[k]) == sflight(s0.entries@[k]));
        } else if has_id(s0.entries@, j) {
            let k = choose|k: int| 0 <= k < s0.entries@.len() && (#[trigger] s0.entries@[k]).id == j;
            assert(s.entries@[k].id == j);
        }
    }
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
        recv_ready(r1.rfc()) == recv_ready(r0.rfc()),
        recv_pending(r1.rfc()) == recv_pending(r0.rfc()),
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
        val(ne, 9) <= val(s0.entries@[i], 9) || sum(s0.entries@, 9) - val(s0.entries@[i], 9) + val(
            ne,
            9,
        ) <= MAX_SEND_BUFFER,
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
        s1.rx_conn == s0.rx_conn,
        s1.rx_bidi == s0.rx_bidi,
        s1.rx_uni == s0.rx_uni,
        s1.tx_bidi == s0.tx_bidi,
        s1.tx_uni == s0.tx_uni,
        s1.failed == s0.failed,
        s1.removed == s0.removed,
        s1.gone == s0.gone,
        s1.tx_gone == s0.tx_gone,
        // The queue: as it was, or the entry's id appended as it becomes queued (a reset's slot, D10 (e)).
        ({
            ||| s1.q == s0.q && qkeep(s0.entries@[i], ne)
            ||| s1.q.wf() && s1.q@ == s0.q@.push(ne.id) && !s0.entries@[i].queued && ne.queued && (ne.recv is Some
                || etd(ne)) && (etd(s0.entries@[i]) ==> etd(ne))
        }),
    ensures
        s1.wf(),
        s1.tx_held() == s0.tx_held() - val(s0.entries@[i], 9) + val(ne, 9),
        s1.td_weight() == s0.td_weight() - val(s0.entries@[i], 11) + val(ne, 11),
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
    lemma_sum_update(a, i, ne, 9);
    lemma_sum_update(a, i, ne, 11);
    lemma_sum_w_nonneg(s1.entries@);
    lemma_sum_w_nonneg(a);
    assert(val(ne, 4) == val(a[i], 4) && val(ne, 6) == val(a[i], 6));
    s0.ids.lemma_wf();
    lemma_queue_step(s0, i, ne, s1.q);
}

/// `recv_op_at`'s proof once entry `i` (`e0`) is back as `ne`, its receiving part moved by one control operation
/// (`lemma_ctl`'s facts; `ctl_only`: no Credit input): `wf`, `kept`, `out_tx` and the traces (split for the rlimit).
#[verifier::spinoff_prover]
proof fn lemma_recv_op_post(
    s0: Streams,
    s1: Streams,
    s2: Streams,
    i: int,
    e0: Entry,
    ne: Entry,
    n: int,
    o: Seq<Frame>,
    ctl_only: bool,
)
    requires
        kept(s0, s1),
        0 <= i < s1.entries@.len(),
        out_tx(s1, n, o),
        e0 == s1.entries@[i],
        s2.entries@ == s1.entries@.update(i, ne),
        ne.id == e0.id,
        ne.send == e0.send,
        ne.queued == e0.queued,
        ne.recv is Some == e0.recv is Some,
        e0.recv is None ==> s2.rtr@ == s1.rtr@,
        ne.recv matches Some(r) ==> {
            let r0 = e0.recv->0;
            &&& s2.rtr@ == s1.rtr@.insert(ne.id, r.trace())
            &&& r.wf()
            &&& r.id_spec() == r0.id_spec()
            &&& r.window_spec() == r0.window_spec()
            &&& r.rfc().state == r0.rfc().state
            &&& r.rfc().events == r0.rfc().events
            &&& r.rfc().stopped == r0.rfc().stopped
            &&& counted(r.rfc()) == counted(r0.rfc())
            &&& retired(r.rfc()) == retired(r0.rfc())
            &&& recv_ready(r.rfc()) == recv_ready(r0.rfc())
            &&& ctl_only ==> r.trace() == r0.trace()
        },
        s2 == (Streams { entries: s2.entries, rtr: s2.rtr, ..s1 }),
    ensures
        out_tx(s2, n, o),
        kept(s0, s2),
        sends_same(s0, s1) ==> sends_same(s0, s2),
        forall|j: u64| j != e0.id ==> #[trigger] s2.rx_trace(j) == s1.rx_trace(j),
        ctl_only ==> forall|j: u64| #[trigger] s2.rx_trace(j) == s1.rx_trace(j),
{
    let id = e0.id;
    assert(entry_ok(e0, s1.rx_bidi, s1.rx_uni));
    lemma_swap(s1, s2, i, ne);
    lemma_swap_kept(s0, s1, s2, i, ne);
    lemma_tx_grows(s1, s2, i, n, o);
    if ctl_only {
        assert forall|j: u64| #[trigger] s2.rx_trace(j) == s1.rx_trace(j) by {
            if j == id && ne.recv is Some {
                assert(s1.rtr@[id] == e0.recv->0.trace());
            }
        }
    }
}

/// `lemma_swap` during `poll_frames`: `kept` and `sends_same` carry over when the new entry's
/// receive side and send state are as before (up to a Credit input).
proof fn lemma_swap_kept(s0: Streams, s1: Streams, s2: Streams, i: int, ne: Entry)
    requires
        kept(s0, s1),
        0 <= i < s1.entries@.len(),
        ne.id == s1.entries@[i].id,
        s2.resets == s1.resets,
        s2.q == s1.q,
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
        s2.rx_conn == s1.rx_conn,
        s2.tx_held() <= s1.tx_held(),
    ensures
        kept(s0, s2),
        sends_same(s0, s1) && sstate(ne) == sstate(s1.entries@[i]) && sflight(ne) == sflight(s1.entries@[i])
            ==> sends_same(s0, s2),
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
    if sends_same(s0, s1) && sstate(ne) == sstate(s1.entries@[i]) && sflight(ne) == sflight(s1.entries@[i]) {
        assert forall|k: int| 0 <= k < s2.entries@.len() implies sstate(#[trigger] s2.entries@[k])
            == sstate(s0.entries@[k]) by {
            if k != i {
                assert(s2.entries@[k] == s1.entries@[k]);
            }
        }
        assert forall|k: int| 0 <= k < s2.entries@.len() implies sflight(#[trigger] s2.entries@[k])
            == sflight(s0.entries@[k]) by {
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
        &&& id / 4 < MAX_OWN_UNI
    }

    /// How many more bytes `write` accepts on stream `id`: the most `d` that keeps the send queues'
    /// reservations within `MAX_SEND_BUFFER` (`id`'s part's `room_spec`, the other parts' reservations
    /// set aside; for a stream with no sending part, an empty queue's).
    pub closed spec fn send_room_spec(&self, id: u64) -> int {
        let b = MAX_SEND_BUFFER - self.tx_held();
        match self.tx_part(id) {
            Some(p) => p.room_spec((b + p.held_spec()) as nat) as int,
            None => res_room(b as nat, 0) as int,
        }
    }

    pub fn send_room(&self, id: u64) -> (r: u64)
        requires
            self.wf(),
        ensures
            r as int == self.send_room_spec(id),
    {
        let mut acc: u64 = 0;
        let mut i: usize = 0;
        proof {
            assert(self.entries@.take(0) =~= Seq::<Entry>::empty());
            lemma_sum_prefix_le(self.entries@, 0);
        }
        while i < self.entries.len()
            invariant
                self.wf(),
                i <= self.entries@.len(),
                acc == sum(self.entries@.take(i as int), 9),
                acc <= self.tx_held(),
            decreases self.entries@.len() - i,
        {
            proof {
                assert(entry_ok(self.entries@[i as int], self.rx_bidi, self.rx_uni));
                lemma_sum_take(self.entries@, i as int, 9);
                lemma_sum_prefix_le(self.entries@, i as int + 1);
            }
            let b = match &self.entries[i].send {
                Some(p) => p.reserved(),
                None => 0,
            };
            acc = acc + b;
            i += 1;
        }
        proof {
            assert(self.entries@.take(i as int) =~= self.entries@);
        }
        let free = MAX_SEND_BUFFER - acc;
        if let Some(k) = self.find(id) {
            if let Some(p) = &self.entries[k].send {
                proof {
                    lemma_part_at(*self, k as int);
                    lemma_sum_buf_le(self.entries@, k as int);
                    assert(entry_ok(self.entries@[k as int], self.rx_bidi, self.rx_uni));
                }
                return p.room(free + p.held());
            }
            proof {
                lemma_part_at(*self, k as int);
            }
        }
        if free >= 128 {
            free / 6
        } else {
            0
        }
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
            } && data@.len() <= old(self).send_room_spec(id),
            r is Err ==> *final(self) == *old(self),
            final(self).conn_recv_spec().window_spec() == old(self).conn_recv_spec().window_spec(),
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
            // D10 (b): no flight changes, a new part's included (re-review F2, F3).
            forall|j: u64| #[trigger] final(self).tx_flight(j) == old(self).tx_flight(j),
            tx_kept_but(*old(self), *final(self), None),
            final(self).measure() == old(self).measure(),
    {
        // Before any swap, so a refusal changes nothing.
        if data.len() as u64 > self.send_room(id) {
            return Err(());
        }
        let ghost s0 = *self;
        let r = match self.find(id) {
            Some(i) => self.write_at(i, data, fin),
            None => self.write_new(id, data, fin),
        };
        proof {
            lemma_kept_of_flights(s0, *self);
            lemma_backlog_same(s0, *self);
        }
        r
    }

    fn write_at(&mut self, i: usize, data: &[u8], fin: bool) -> (r: Result<(), ()>)
        requires
            old(self).wf(),
            i < old(self).entries@.len(),
            data@.len() <= old(self).send_room_spec(old(self).entries@[i as int].id),
        ensures
            ({
                let id = old(self).entries@[i as int].id;
                &&& final(self).wf()
                &&& final(self).failed() == old(self).failed()
                &&& final(self).rx_conn == old(self).rx_conn
                &&& final(self).q == old(self).q
                &&& final(self).rx_bidi == old(self).rx_bidi
                &&& final(self).rx_uni == old(self).rx_uni
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
                &&& forall|j: u64| #[trigger] final(self).tx_flight(j) == old(self).tx_flight(j)
                &&& final(self).td_weight() == old(self).td_weight()
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
        proof {
            let p0 = s0.entries@[i as int].send->0;
            lemma_sum_buf_le(s0.entries@, i as int);
            assert(MAX_SEND_BUFFER <= byteq::queue::MAX_QUEUE) by (compute_only);
            p0.lemma_room((MAX_SEND_BUFFER - s0.tx_held() + p0.held_spec()) as nat, data@.len() as nat);
            p0.lemma_held();
        }
        let mut e = Entry { id: 0, recv: None, send: None, queued: false };
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
            assert forall|j: u64| #[trigger] self.tx_flight(j) == s0.tx_flight(j) by {
                if j != id {
                    lemma_part_other(s0, *self, i as int, j);
                }
            }
        }
        Ok(())
    }

    fn write_new(&mut self, id: u64, data: &[u8], fin: bool) -> (r: Result<(), ()>)
        requires
            old(self).wf(),
            !has_id(old(self).entries@, id),
            data@.len() <= res_room((MAX_SEND_BUFFER - old(self).tx_held()) as nat, 0),
        ensures
            final(self).wf(),
            final(self).td_weight() == old(self).td_weight(),
            final(self).failed() == old(self).failed(),
            final(self).rx_conn == old(self).rx_conn,
            final(self).q == old(self).q,
            final(self).rx_bidi == old(self).rx_bidi,
            final(self).rx_uni == old(self).rx_uni,
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
            forall|j: u64| #[trigger] final(self).tx_flight(j) == old(self).tx_flight(j),
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
        proof {
            lemma_sum_buf_nonneg(s0.entries@);
            assert(MAX_SEND_BUFFER <= byteq::queue::MAX_QUEUE) by (compute_only);
            p.lemma_room((MAX_SEND_BUFFER - s0.tx_held()) as nat, data@.len() as nat);
        }
        let _ = p.write(data, fin);
        let e = Entry { id, recv: None, send: Some(p), queued: false };
        self.entries.push(e);
        proof {
            lemma_wt(0, 0, 0, 0);
            lemma_push_local(s0, *self, e);
            lemma_part_at(*self, s0.entries@.len() as int);
            assert(self.entries@[s0.entries@.len() as int] == e);
            assert forall|j: u64| #[trigger] self.tx_flight(j) == s0.tx_flight(j) by {
                if j != id && has_id(self.entries@, j) {
                    let k = choose|k: int| 0 <= k < self.entries@.len() && (#[trigger] self.entries@[k]).id == j;
                    assert(k < s0.entries@.len());
                    assert(self.entries@[k] == s0.entries@[k]);
                    lemma_part_at(*self, k);
                    lemma_part_at(s0, k);
                } else if j != id && has_id(s0.entries@, j) {
                    let k = choose|k: int| 0 <= k < s0.entries@.len() && (#[trigger] s0.entries@[k]).id == j;
                    assert(self.entries@[k] == s0.entries@[k]);
                }
            }
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
            final(self).tx_held() <= old(self).tx_held(),
            final(self).conn_recv_spec().window_spec() == old(self).conn_recv_spec().window_spec(),
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
            // D10 (b): only `id` may change, and then it is reset (its flight emptied).
            tx_kept_but(*old(self), *final(self), None),
            forall|j: u64| #[trigger] old(self).send_reset(j) ==> final(self).send_reset(j),
            // The part's sets move to its slot (halving their weight) and it is queued for `deliver_some`'s reaping.
            final(self).measure() <= old(self).measure(),
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
                let mut e = Entry { id: 0, recv: None, send: None, queued: false };
                self.entries.set_and_swap(i, &mut e);
                let ghost e0 = e;
                if let Some(mut p) = e.send.take() {
                    let _ = p.reset(code);
                    e.send = Some(p);
                }
                // A non-empty slot is queued, for `deliver_some` to reap (D10 (e)).
                let enq = !e.queued && match &e.send {
                    Some(p) => p.has_td(),
                    None => false,
                };
                if enq {
                    e.queued = true;
                }
                let ghost ne = e;
                proof {
                    assert(e0 == s0.entries@[i as int]);
                    assert(entry_ok(e0, s0.rx_bidi, s0.rx_uni));
                    e0.send->0.lemma_td();
                    e0.send->0.lemma_held();
                    lemma_res_mono(ne.send->0.td_window(), e0.send->0.peak_spec());
                    assert(val(ne, 9) <= val(e0, 9));
                    lemma_wt(
                        ne.send->0.ranges_held(),
                        ne.send->0.td_nodes(),
                        e0.send->0.ranges_held(),
                        e0.send->0.td_nodes(),
                    );
                    assert(val(ne, 11) + (if enq { kw() } else { 0int }) <= val(e0, 11));
                    lemma_reset_enqueue(s0, i as int, ne, enq);
                }
                self.entries.set_and_swap(i, &mut e);
                if enq {
                    self.q.push(id);
                }
                self.resets = Ghost(self.resets@.insert(id, code));
                proof {
                    assert(self.entries@ == s0.entries@.update(i as int, ne));
                    assert(ne.recv == s0.entries@[i as int].recv);
                    if let Some(r) = ne.recv {
                        assert(s0.rtr@.insert(id, r.trace()) =~= s0.rtr@);
                    }
                    lemma_swap(s0, *self, i as int, ne);
                    assert forall|j: u64| #[trigger] self.rx_trace(j) == s0.rx_trace(j) by {}
                    assert forall|j: u64| j != id implies #[trigger] self.tx_flight(j) == s0.tx_flight(j) by {
                        lemma_part_other(s0, *self, i as int, j);
                    }
                    assert(self.send_reset(id));
                    lemma_reset_measure(s0, *self, i as int, ne, enq);
                }
            }
        }
    }

    /// Stream `id`'s sending part, if any, is flushed (D10 (c)): its bytes written so far may go as a short piece.
    pub fn flush(&mut self, id: u64)
        requires
            old(self).wf(),
            !old(self).failed(),
        ensures
            final(self).wf(),
            !final(self).failed(),
            final(self).tx_held() == old(self).tx_held(),
            final(self).conn_recv_spec().window_spec() == old(self).conn_recv_spec().window_spec(),
            match old(self).tx_part(id) {
                Some(p) => final(self).tx_part(id) matches Some(q) && q.flush_point() == q.all_written().len()
                    && q.all_written() == p.all_written() && q.fin_written_spec() == p.fin_written_spec()
                    && q.state() == p.state() && q.sent_end() == p.sent_end() && q.reset_spec() == p.reset_spec()
                    && q.held_spec() == p.held_spec() && q.flight_spec() == p.flight_spec(),
                None => final(self).tx_part(id) is None,
            },
            forall|j: u64| j != id ==> #[trigger] final(self).tx_part(j) == old(self).tx_part(j),
            forall|j: u64| #[trigger] final(self).tx_flight(j) == old(self).tx_flight(j),
            tx_kept_but(*old(self), *final(self), None),
            forall|j: u64| #[trigger] final(self).send_room_spec(j) == old(self).send_room_spec(j),
            forall|j: u64| #[trigger] final(self).reset_code(j) == old(self).reset_code(j),
            forall|j: u64| #[trigger] final(self).rx_trace(j) == old(self).rx_trace(j),
            forall|j: u64| #[trigger] final(self).is_removed(j) == old(self).is_removed(j),
            final(self).measure() == old(self).measure(),
    {
        let ghost s0 = *self;
        if let Some(i) = self.find(id) {
            proof {
                lemma_part_at(s0, i as int);
                assert(entry_ok(s0.entries@[i as int], s0.rx_bidi, s0.rx_uni));
            }
            let mut e = Entry { id: 0, recv: None, send: None, queued: false };
            self.entries.set_and_swap(i, &mut e);
            if let Some(mut p) = e.send.take() {
                p.flush();
                e.send = Some(p);
            }
            let ghost ne = e;
            self.entries.set_and_swap(i, &mut e);
            proof {
                assert(self.entries@ == s0.entries@.update(i as int, ne));
                lemma_swap_same_rx(s0, *self, i as int, ne);
                lemma_part_at(*self, i as int);
                assert forall|j: u64| j != id implies #[trigger] self.tx_part(j) == s0.tx_part(j) by {
                    lemma_part_other(s0, *self, i as int, j);
                }
                assert(self.tx_held() == s0.tx_held()) by {
                    lemma_held_same(s0, *self, i as int);
                }
                assert forall|j: u64| #[trigger] self.send_room_spec(j) == s0.send_room_spec(j) by {
                    if j != id {
                        lemma_part_other(s0, *self, i as int, j);
                    }
                }
                assert forall|j: u64| #[trigger] self.tx_flight(j) == s0.tx_flight(j) by {
                    if j != id {
                        lemma_part_other(s0, *self, i as int, j);
                    }
                }
            }
        }
        proof {
            lemma_kept_of_flights(s0, *self);
            lemma_backlog_same(s0, *self);
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
            final(self).tx_held() <= old(self).tx_held(),
            final(self).conn_recv_spec().window_spec() == old(self).conn_recv_spec().window_spec(),
            forall|j: u64| j != id ==> #[trigger] final(self).rx_trace(j) == old(self).rx_trace(j),
            final(self).rx_trace(id) == old(self).rx_trace(id) || final(self).rx_trace(id) == old(
                self,
            ).rx_trace(id).push(SpecRecvIn::Stop),
            // Only while data may still arrive (Recv or Size Known; `RecvStream::stop`, §3.5).
            old(self).rx_live(id) && (old(self).rx_spec(id).state is Recv || old(self).rx_spec(id).state is SizeKnown)
                ==> final(self).rx_spec(id).stopped,
            forall|j: u64| #[trigger] final(self).reset_code(j) == old(self).reset_code(j),
            forall|j: u64| #[trigger] final(self).is_removed(j) == old(self).is_removed(j),
            forall|j: u64| #[trigger] final(self).tx_flight(j) == old(self).tx_flight(j),
            tx_kept_but(*old(self), *final(self), None),
            final(self).measure() == old(self).measure(),
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
                let mut e = Entry { id: 0, recv: None, send: None, queued: false };
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
                    lemma_part_at(s0, i as int);
                    lemma_part_at(*self, i as int);
                    assert forall|j: u64| #[trigger] self.tx_flight(j) == s0.tx_flight(j) by {
                        if j != id {
                            lemma_part_other(s0, *self, i as int, j);
                        }
                    }
                    assert forall|j: u64| #[trigger] recv_pending(self.rx_spec(j)) == recv_pending(
                        s0.rx_spec(j),
                    ) by {
                        if j != id {
                            assert(self.rx_trace(j) == s0.rx_trace(j));
                        }
                    }
                    lemma_backlog_pending(s0, *self);
                }
            }
        }
        proof {
            lemma_kept_of_flights(s0, *self);
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
            final(self).tx_held() <= old(self).tx_held(),
            final(self).conn_recv_spec().window_spec() == old(self).conn_recv_spec().window_spec(),
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
            // D10 (b): each stream's flight gains exactly the pieces of the STREAM frames returned for it.
            tx_gained(*old(self), *final(self), frames_view(final(out)@.skip(old(out)@.len() as int))),
            forall|j: u64| #[trigger] final(self).send_reset(j) == old(self).send_reset(j),
    {
        let ghost s0 = *self;
        let ghost pre = out@;
        let ghost b = budget as nat;
        let mut room = budget;
        proof {
            lemma_out_init(s0, pre, b, room);
        }
        self.poll_control(&mut room, out, Ghost(s0), Ghost(pre), Ghost(b));
        let ghost sm = *self;
        let ghost om = out@;
        proof {
            lemma_flights_same(s0, sm);
            assert(pre.len() <= om.len() && om.subrange(0, pre.len() as int) == pre);
            lemma_no_piece(om, pre.len() as int);
            lemma_tx_gained_same(s0, sm, frames_view(om.skip(pre.len() as int)));
        }
        self.poll_streams(&mut room, out, Ghost(s0), Ghost(pre), Ghost(b));
        proof {
            lemma_poll_post(s0, *self, pre, b, out@, room);
            lemma_skip_split(pre, om, out@);
            lemma_tx_gained_trans(s0, sm, *self, frames_view(om.skip(pre.len() as int)), frames_view(
                out@.skip(om.len() as int),
            ));
            assert forall|j: u64| #[trigger] self.send_reset(j) == s0.send_reset(j) by {
                assert(self.reset_code(j) == s0.reset_code(j));
            }
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
            no_piece(old(out)@, pre.len() as int),
        ensures
            kept(s0, *final(self)),
            sends_same(s0, *final(self)),
            out_ok(s0, pre, budget, final(out)@, *final(room)),
            out_tx(*final(self), pre.len() as int, final(out)@),
            no_piece(final(out)@, pre.len() as int),
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
            no_piece(old(out)@, pre.len() as int),
        ensures
            kept(s0, *final(self)),
            sends_same(s0, *final(self)),
            out_ok(s0, pre, budget, final(out)@, *final(room)),
            out_tx(*final(self), pre.len() as int, final(out)@),
            no_piece(final(out)@, pre.len() as int),
    {
        let mut i: usize = 0;
        while i < self.entries.len()
            invariant
                kept(s0, *self),
                sends_same(s0, *self),
                out_ok(s0, pre, budget, out@, *room),
                out_tx(*self, pre.len() as int, out@),
                no_piece(out@, pre.len() as int),
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
        let mut e = Entry { id: 0, recv: None, send: None, queued: false };
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
            no_piece(old(out)@, pre.len() as int),
        ensures
            kept(s0, *final(self)),
            sends_same(s0, *final(self)),
            out_ok(s0, pre, budget, final(out)@, *final(room)),
            out_tx(*final(self), pre.len() as int, final(out)@),
            no_piece(final(out)@, pre.len() as int),
    {
        let mut i: usize = 0;
        while i < self.entries.len()
            invariant
                kept(s0, *self),
                sends_same(s0, *self),
                out_ok(s0, pre, budget, out@, *room),
                out_tx(*self, pre.len() as int, out@),
                no_piece(out@, pre.len() as int),
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
        let mut e = Entry { id: 0, recv: None, send: None, queued: false };
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
            lemma_recv_op_post(s0, s1, *self, i as int, e0, ne, n, o, op != 1);
        }
    }

    /// The pending MAX_DATA.
    #[verifier::spinoff_prover]
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
            no_piece(old(out)@, pre.len() as int),
        ensures
            kept(s0, *final(self)),
            sends_same(s0, *final(self)),
            out_ok(s0, pre, budget, final(out)@, *final(room)),
            out_tx(*final(self), pre.len() as int, final(out)@),
            no_piece(final(out)@, pre.len() as int),
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
                    lemma_max_data_kept(s0, s1, *self, pre.len() as int, out@);
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
            no_piece(old(out)@, pre.len() as int),
        ensures
            kept(s0, *final(self)),
            sends_same(s0, *final(self)),
            out_ok(s0, pre, budget, final(out)@, *final(room)),
            out_tx(*final(self), pre.len() as int, final(out)@),
            no_piece(final(out)@, pre.len() as int),
    {
        let mut i: usize = 0;
        while i < self.entries.len()
            invariant
                kept(s0, *self),
                sends_same(s0, *self),
                out_ok(s0, pre, budget, out@, *room),
                out_tx(*self, pre.len() as int, out@),
                no_piece(out@, pre.len() as int),
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
            no_piece(old(out)@, pre.len() as int),
        ensures
            kept(s0, *final(self)),
            sends_same(s0, *final(self)),
            out_ok(s0, pre, budget, final(out)@, *final(room)),
            out_tx(*final(self), pre.len() as int, final(out)@),
            no_piece(final(out)@, pre.len() as int),
    {
        if let Some(v) = self.ids.pending_max_streams(bidi) {
            let f = Frame::MaxStreams { bidi, max: v };
            if emit(f, room, out, Ghost(s0), Ghost(pre), Ghost(budget), Ghost(*self)) {
                let ghost s1 = *self;
                self.ids.commit_max_streams(bidi);
                proof {
                    lemma_max_streams_kept(s0, s1, *self, bidi, pre.len() as int, out@);
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
            tx_gained(*old(self), *final(self), frames_view(final(out)@.skip(old(out)@.len() as int))),
            final(out)@.len() >= old(out)@.len(),
            final(out)@.subrange(0, old(out)@.len() as int) == old(out)@,
    {
        hide(out_ok);
        let ghost sa = *self;
        let ghost oa = out@;
        proof {
            assert(frames_view(oa.skip(oa.len() as int)) =~= Seq::<SpecFrame>::empty());
            lemma_frame_pieces_none(Seq::<SpecFrame>::empty());
            lemma_tx_gained_same(sa, sa, Seq::<SpecFrame>::empty());
            assert(oa.subrange(0, oa.len() as int) =~= oa);
        }
        let mut i: usize = 0;
        while i < self.entries.len()
            invariant
                tx_gained(sa, *self, frames_view(out@.skip(oa.len() as int))),
                out@.len() >= oa.len(),
                out@.subrange(0, oa.len() as int) == oa,
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
                let ghost sb = *self;
                let ghost ob = out@;
                self.poll_stream_at(i, room, out, Ghost(s0), Ghost(pre), Ghost(budget));
                proof {
                    lemma_skip_split(oa, ob, out@);
                    lemma_tx_gained_trans(sa, sb, *self, frames_view(ob.skip(oa.len() as int)), frames_view(
                        out@.skip(ob.len() as int),
                    ));
                }
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
            tx_gained(*old(self), *final(self), frames_view(final(out)@.skip(old(out)@.len() as int))),
            final(out)@.len() >= old(out)@.len(),
            final(out)@.subrange(0, old(out)@.len() as int) == old(out)@,
    {
        hide(out_ok);
        let ghost s1 = *self;
        proof {
            assert(pre.len() <= out@.len()) by {
                reveal(out_ok);
            }
            lemma_id_bound(s1, i as int);
            lemma_part_at(s0, i as int);
            assert(s0.entries@[i as int].id == s1.entries@[i as int].id);
        }
        let id = self.entries[i].id;
        let ghost o0 = out@;
        let mut e = Entry { id: 0, recv: None, send: None, queued: false };
        self.entries.set_and_swap(i, &mut e);
        let ghost e0 = e;
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
            lemma_tx_gained_at(s1, *self, i as int, ne, frames_view(out@.skip(o0.len() as int)));
        }
    }

    /// Frame `f`, returned by `poll_frames`, was acknowledged. A sending part's ack may end the
    /// stream, which is then removed (§4.4: flow control state is kept until then).
    pub fn on_frame_acked(&mut self, f: &Frame)
        requires
            old(self).wf(),
            !old(self).failed(),
            // D10 (b): a STREAM frame's piece is in flight unless its part was reset (conn's `pieces_ok`).
            piece_in_flight(*old(self), f@),
        ensures
            final(self).wf(),
            !final(self).failed(),
            final(self).tx_held() <= old(self).tx_held(),
            final(self).conn_recv_spec().window_spec() == old(self).conn_recv_spec().window_spec(),
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
            piece_removed(*old(self), *final(self), f@),
            tx_kept_but(*old(self), *final(self), piece_stream(f@)),
            forall|j: u64| #[trigger] final(self).send_reset(j) == old(self).send_reset(j),
    {
        let ghost s0 = *self;
        match f {
            Frame::Stream { stream_id, offset, data, fin } => {
                self.send_op(*stream_id, 0, *offset, data.len() as u64, *fin);
            },
            Frame::ResetStream { stream_id, .. } => {
                self.send_op(*stream_id, 1, 0, 0, false);
            },
            _ => {
                proof {
                    assert(tx_kept_but(s0, *self, None));
                }
            },
        }
    }

    /// Frame `f`, returned by `poll_frames`, was lost: lost STREAM bytes are queued again
    /// (unless the stream was reset since), RESET_STREAM and STOP_SENDING resent unchanged,
    /// and credit frames resent with the current value (§13.3).
    pub fn on_frame_lost(&mut self, f: &Frame)
        requires
            old(self).wf(),
            !old(self).failed(),
            // D10 (b): a STREAM frame's piece is in flight unless its part was reset (conn's `pieces_ok`).
            piece_in_flight(*old(self), f@),
        ensures
            final(self).wf(),
            !final(self).failed(),
            final(self).tx_held() <= old(self).tx_held(),
            final(self).conn_recv_spec().window_spec() == old(self).conn_recv_spec().window_spec(),
            forall|j: u64| #[trigger] final(self).reset_code(j) == old(self).reset_code(j),
            forall|j: u64| #[trigger] final(self).rx_trace(j) == old(self).rx_trace(j),
            forall|j: u64| #[trigger] final(self).is_removed(j) == old(self).is_removed(j),
            piece_removed(*old(self), *final(self), f@),
            tx_kept_but(*old(self), *final(self), piece_stream(f@)),
            forall|j: u64| #[trigger] final(self).send_reset(j) == old(self).send_reset(j),
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
                    assert(tx_kept_but(s0, *self, None));
                }
            },
            Frame::MaxStreams { bidi, .. } => {
                self.ids.max_streams_lost(*bidi);
                proof {
                    lemma_ids_frame(s0, *self);
                    assert(forall|j: u64| #[trigger] self.rx_trace(j) == s0.rx_trace(j));
                    assert(tx_kept_but(s0, *self, None));
                }
            },
            _ => {
                proof {
                    assert(tx_kept_but(s0, *self, None));
                }
            },
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
            final(self).tx_held() <= old(self).tx_held(),
            final(self).rx_conn == old(self).rx_conn,
            forall|j: u64| #[trigger] final(self).reset_code(j) == old(self).reset_code(j),
            forall|j: u64| #[trigger] final(self).rx_trace(j) == old(self).rx_trace(j),
            forall|j: u64| #[trigger] final(self).is_removed(j) == old(self).is_removed(j),
            forall|j: u64| #[trigger] final(self).tx_flight(j) == old(self).tx_flight(j),
            final(self).resets == old(self).resets,
    {
        let ghost s0 = *self;
        if let Some(i) = self.find(id) {
            proof {
                assert(kept(s0, s0));
                assert(sends_same(s0, s0));
            }
            self.recv_op_at(i, op, Ghost(s0), Ghost(0), Ghost(Seq::<Frame>::empty()));
            proof {
                lemma_flights_same(s0, *self);
            }
        }
    }

    /// An ack or loss on stream `id`'s sending part: op 0 data acked, 1 reset acked (each
    /// followed by `gc`), 2 data lost, 3 reset lost.
    fn send_op(&mut self, id: u64, op: u8, off: u64, len: u64, fin: bool)
        requires
            old(self).wf(),
            (op == 0 || op == 2) && len > 0 && !old(self).send_reset(id) ==> off + len <= VARINT_MAX && old(
                self,
            ).tx_flight(id).contains((off, (off + len) as u64)),
        ensures
            final(self).wf(),
            final(self).failed == old(self).failed,
            final(self).tx_held() <= old(self).tx_held(),
            final(self).rx_conn == old(self).rx_conn,
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
            (op == 0 || op == 2) && len > 0 && !old(self).send_reset(id) ==> final(self).tx_flight(id) == old(
                self,
            ).tx_flight(id).remove((off, (off + len) as u64)),
            tx_kept_but(
                *old(self),
                *final(self),
                if (op == 0 || op == 2) && len > 0 {
                    Some(id)
                } else {
                    None
                },
            ),
            final(self).resets == old(self).resets,
    {
        let ghost s0 = *self;
        if let Some(i) = self.find(id) {
            self.send_op_at(i, op, off, len, fin);
            if op < 2 {
                let ghost s1 = *self;
                self.gc(i);
                proof {
                    assert(self.send_reset(id) == s1.send_reset(id));
                    assert(!self.send_reset(id) ==> self.tx_flight(id) == s1.tx_flight(id));
                    assert forall|j: u64| !#[trigger] self.send_reset(j) implies self.send_reset(j) == s1.send_reset(j)
                        && self.tx_flight(j) == s1.tx_flight(j) by {}
                }
            }
        } else {
            proof {
                assert(self.tx_flight(id) == Set::<(u64, u64)>::empty());
            }
        }
    }

    /// `send_op` on entry `i`, before its `gc` (split from it for the rlimit).
    #[verifier::spinoff_prover]
    fn send_op_at(&mut self, i: usize, op: u8, off: u64, len: u64, fin: bool)
        requires
            old(self).wf(),
            i < old(self).entries@.len(),
            (op == 0 || op == 2) && len > 0 && !old(self).send_reset(old(self).entries@[i as int].id) ==> off + len
                <= VARINT_MAX && old(self).tx_flight(old(self).entries@[i as int].id).contains(
                (off, (off + len) as u64),
            ),
        ensures
            final(self).wf(),
            final(self).entries@.len() == old(self).entries@.len(),
            final(self).entries@[i as int].id == old(self).entries@[i as int].id,
            final(self).failed == old(self).failed,
            final(self).tx_held() <= old(self).tx_held(),
            final(self).rx_conn == old(self).rx_conn,
            final(self).ids == old(self).ids,
            final(self).removed == old(self).removed,
            final(self).resets == old(self).resets,
            final(self).same_traces(*old(self)),
            forall|j: u64| #[trigger] final(self).reset_code(j) == old(self).reset_code(j),
            forall|j: u64| #[trigger] final(self).rx_trace(j) == old(self).rx_trace(j),
            forall|j: u64| #[trigger] final(self).is_removed(j) == old(self).is_removed(j),
            forall|b: bool| #[trigger] final(self).peer_closed(b) == old(self).peer_closed(b),
            (op == 0 || op == 2) && len > 0 && !old(self).send_reset(old(self).entries@[i as int].id)
                ==> final(self).tx_flight(old(self).entries@[i as int].id) == old(self).tx_flight(
                old(self).entries@[i as int].id,
            ).remove((off, (off + len) as u64)),
            tx_kept_but(
                *old(self),
                *final(self),
                if (op == 0 || op == 2) && len > 0 {
                    Some(old(self).entries@[i as int].id)
                } else {
                    None
                },
            ),
    {
        let ghost s0 = *self;
        let mut e = Entry { id: 0, recv: None, send: None, queued: false };
        self.entries.set_and_swap(i, &mut e);
        proof {
            assert(entry_ok(e, s0.rx_bidi, s0.rx_uni));
        }
        let ghost e0 = e;
        if let Some(mut p) = e.send.take() {
            proof {
                lemma_part_at(s0, i as int);
                p.lemma_wf();
                p.lemma_flight_idle();
                p.lemma_in_flight(off, len);
            }
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
            lemma_send_op_flight(s0, *self, i as int, e0, ne, op, off, len);
        }
    }
}

/// Another id's sending part is untouched by a swap at `i`.
proof fn lemma_part_other(s0: Streams, s1: Streams, i: int, j: u64)
    requires
        s0.wf(),
        s1.wf(),
        0 <= i < s0.entries@.len(),
        s1.entries@ == s0.entries@.update(i, s1.entries@[i]),
        s1.entries@[i].id == s0.entries@[i].id,
        j != s0.entries@[i].id,
    ensures
        s1.tx_part(j) == s0.tx_part(j),
{
    if has_id(s0.entries@, j) {
        let k = choose|k: int| 0 <= k < s0.entries@.len() && (#[trigger] s0.entries@[k]).id == j;
        assert(s1.entries@[k] == s0.entries@[k]);
        lemma_part_at(s0, k);
        lemma_part_at(s1, k);
    } else {
        assert(!has_id(s1.entries@, j)) by {
            if has_id(s1.entries@, j) {
                let k = choose|k: int| 0 <= k < s1.entries@.len() && (#[trigger] s1.entries@[k]).id == j;
                assert(s1.entries@[k] == s0.entries@[k]);
            }
        }
    }
}

/// A swap at `i` that keeps the part's reservation keeps the connection's sum.
proof fn lemma_held_same(s0: Streams, s1: Streams, i: int)
    requires
        0 <= i < s0.entries@.len(),
        s1.entries@ == s0.entries@.update(i, s1.entries@[i]),
        val(s1.entries@[i], 9) == val(s0.entries@[i], 9),
    ensures
        s1.tx_held() == s0.tx_held(),
{
    lemma_sum_update(s0.entries@, i, s1.entries@[i], 9);
}

/// `lemma_swap` for an entry whose receiving part is unchanged and whose sending part kept its
/// bytes sent and its reset: no record changes.
proof fn lemma_swap_same_rx(s0: Streams, s1: Streams, i: int, ne: Entry)
    requires
        s0.wf(),
        0 <= i < s0.entries@.len(),
        ne.id == s0.entries@[i].id,
        ne.recv == s0.entries@[i].recv,
        ne.queued == s0.entries@[i].queued,
        ne.send is Some == s0.entries@[i].send is Some,
        ne.send matches Some(p) ==> p.wf() && p.sent_end() == s0.entries@[i].send->0.sent_end()
            && p.reset_spec() == s0.entries@[i].send->0.reset_spec() && p.held_spec()
            <= s0.entries@[i].send->0.held_spec() && p.td_nodes() == s0.entries@[i].send->0.td_nodes()
            && p.td_window() == s0.entries@[i].send->0.td_window(),
        s1.entries@ == s0.entries@.update(i, ne),
        s1 == (Streams { entries: s1.entries, ..s0 }),
    ensures
        s1.wf(),
        s1.tx_held() <= s0.tx_held(),
        s1.td_weight() == s0.td_weight() - val(s0.entries@[i], 11) + val(ne, 11),
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
        !e.queued,
        e.send matches Some(p) && p.wf() && p.reset_spec() is None && p.sent_end() == 0 && p.td_nodes() == 0,
        sum(s0.entries@, 9) + val(e, 9) <= MAX_SEND_BUFFER,
        s1.entries@ == s0.entries@.push(e),
        s1 == (Streams { entries: s1.entries, ids: s1.ids, ..s0 }),
    ensures
        s1.wf(),
        forall|j: u64| #[trigger] s1.rx_trace(j) == s0.rx_trace(j),
        s1.tx_held() == s0.tx_held() + val(e, 9),
        s1.td_weight() == s0.td_weight() + val(e, 11),
{
    lemma_sum_push(s0.entries@, e, 11);
    lemma_sum_w_nonneg(s0.entries@);
    if let Some(p) = e.send {
        lemma_wt(p.ranges_held(), p.td_nodes(), 0, 0);
    }
    let a = s0.entries@;
    let t = s1.entries@;
    lemma_queue_ok(a, s0.q);
    lemma_qinv_push(a, e, s0.q@);
    lemma_queue_ok(t, s1.q);
    s0.ids.lemma_wf();
    s1.ids.lemma_wf();
    lemma_sum_push(a, e, 9);
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

impl Streams {
    /// Test support: the send queues' allocated capacity (`SendStream::buf_capacity`), summed.
    #[doc(hidden)]
    pub fn send_capacity(&self) -> usize {
        self.entries.iter().filter_map(|e| e.send.as_ref()).map(SendStream::buf_capacity).sum()
    }

    /// Test support: stream `id`'s sending part's acked, lost and in-flight counts.
    #[doc(hidden)]
    pub fn send_range_counts(&self, id: u64) -> Option<(usize, usize, usize)> {
        for e in &self.entries {
            if e.id == id {
                return e.send.as_ref().map(SendStream::range_counts);
            }
        }
        None
    }

    /// Test support: stream `id`'s sending part's bytes buffered, the window its range bound is in (D10 (d)).
    #[doc(hidden)]
    pub fn send_buffered(&self, id: u64) -> Option<usize> {
        for e in &self.entries {
            if e.id == id {
                return e.send.as_ref().map(SendStream::buffered);
            }
        }
        None
    }

    /// Test support: the nodes in stream `id`'s sending part's teardown slot (D10 (e)).
    #[doc(hidden)]
    pub fn send_td_len(&self, id: u64) -> Option<usize> {
        for e in &self.entries {
            if e.id == id {
                return e.send.as_ref().map(SendStream::td_len);
            }
        }
        None
    }
}

impl DeadStreams {
    /// Test support: the entries left.
    #[doc(hidden)]
    pub fn entries_left(&self) -> usize {
        self.entries.len()
    }
}
