//! Proof-only check that the invariants of `flow`, `stream_id`, `reassembly`, `recv_stream` and
//! `send_stream` are usable from another module through `lemma_wf` alone (their `wf` and
//! accessors are closed).
use vstd::prelude::*;
// Used only in ghost code, which a plain `cargo build` erases.
#[allow(unused_imports)]
use crate::codes::*;
#[allow(unused_imports)]
use crate::flow::*;
#[allow(unused_imports)]
use crate::reassembly::*;
#[allow(unused_imports)]
use crate::recv_stream::*;
#[allow(unused_imports)]
use crate::send_stream::*;
#[allow(unused_imports)]
use crate::stream_id::*;
#[allow(unused_imports)]
use wire::varint::*;

verus! {

proof fn recv_credit_exports(c: RecvCredit)
    requires
        c.wf(),
{
    c.lemma_wf();
    assert(c.limit() <= c.consumed() + c.window_spec());
    assert(c.pending() matches Some(v) ==> c.limit() <= v <= c.consumed() + c.window_spec());
}

proof fn stream_ids_exports(s: StreamIds)
    requires
        s.wf(),
{
    s.lemma_wf();
    assert(s.peer_limit(true) <= MAX_STREAMS_LIMIT);
    assert(s.peer_credit_spec(true).consumed_spec() <= s.peer_opened_spec(true));
    assert(s.pending_max_streams(false) matches Some(v) ==> v <= MAX_STREAMS_LIMIT);
    // R3's live-stream bound: opened - closed <= limit - closed <= window.
    assert(s.peer_opened_spec(true) - s.peer_credit_spec(true).consumed_spec()
        <= s.peer_credit_spec(true).window_spec());
    assert(s.peer_opened_spec(false) - s.peer_credit_spec(false).consumed_spec()
        <= s.peer_credit_spec(false).window_spec());
    assert(s.local_uni_limit() <= MAX_STREAMS_LIMIT);
    assert(s.local_uni_spec().used_spec() <= s.local_uni_limit());
}

proof fn reassembly_exports(r: Reassembly)
    requires
        r.wf(),
{
    r.lemma_wf();
    assert(r.base() + r.buf_len() <= VARINT_MAX);
    assert(r.base() <= rfc_contiguous(rfc_received(r.inserted())));
    // Memory: each of `buf`/`have` holds at most twice the logical buffered length.
    assert(r.phys_len() <= 2 * r.buf_len());
}

proof fn recv_stream_exports(r: RecvStream)
    requires
        r.wf(),
{
    r.lemma_wf();
    let s = r.rfc();
    // The per-stream buffer bounds, against the stream limit and against connection credit.
    assert(r.buffered_len() <= s.limit - s.delivered);
    assert(r.buffered_len() <= counted(s) - retired(s));
    // Memory (length, not capacity): each reassembly vec holds at most twice that.
    assert(r.buffered_phys() <= 2 * r.buffered_len());
    assert(s.delivered <= s.high <= counted(s) <= s.limit <= VARINT_MAX);
    assert(recv_events_ok(s.events, r.id_spec()));
    lemma_retired_le_counted(r.id_spec(), r.window_spec(), r.trace());
}

proof fn send_stream_exports(s: SendStream)
    requires
        s.wf(),
{
    s.lemma_wf();
    // No data beyond the peer's limit or the final size; the buffer holds only unacked bytes.
    assert(s.sent_end() <= s.max());
    assert(s.sent_end() <= s.all_written().len() <= VARINT_MAX);
    assert(!is_reset(s.state()) ==> s.buffered_spec() == s.all_written().len()
        - s.acked_base_spec());
    assert(s.next_off() matches Some(o) ==> o <= s.all_written().len());
    // Memory (length, not capacity): at most twice the bytes past the acknowledged prefix.
    assert(s.buffered_spec() <= 2 * (s.all_written().len() - s.acked_point_spec()));
    assert(s.pending_reset() matches Some(r) ==> r.1 == s.sent_end() && r.0 <= VARINT_MAX);
}

} // verus!
