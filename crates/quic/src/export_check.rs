//! Proof-only check that the invariants of `flow`, `stream_id` and `reassembly` are usable
//! from another module through `lemma_wf` alone (their `wf` and accessors are closed).
use vstd::prelude::*;
// Used only in ghost code, which a plain `cargo build` erases.
#[allow(unused_imports)]
use crate::codes::*;
#[allow(unused_imports)]
use crate::flow::*;
#[allow(unused_imports)]
use crate::reassembly::*;
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

} // verus!
