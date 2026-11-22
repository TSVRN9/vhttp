//! Order independence of a receiving part over the frame path's traces (9b2 Task 11; Task 10 review M3).
//! `recv_stream::theorem_recv_order_free` covers STREAM-only traces, which deliver nothing under lazy delivery (9b2
//! D12). The frame path (`Streams::on_frame`) feeds a part `Data` and then `Deliver`, `pump_backlog` feeds it
//! `Deliver`, and flow control and the application feed it `Credit` and `Stop`. `theorem_recv_frame_order_free` is the
//! same statement over every trace of those inputs, a RESET_STREAM excepted, plus what was delivered: always the
//! stream's own prefix, and all of it once the FIN is delivered.
use vstd::prelude::*;
#[allow(unused_imports)]
use crate::reassembly::*;
#[allow(unused_imports)]
use crate::recv_stream::*;

verus! {

/// A trace with no RESET_STREAM: STREAM frames, deliveries, credit and a local STOP_SENDING.
pub open spec fn no_reset(t: Seq<SpecRecvIn>) -> bool {
    forall|j: int| #![trigger t[j]] 0 <= j < t.len() ==> !(t[j] is Reset)
}

/// Every range received carries bytes of `s` at its offset.
pub open spec fn ins_of(ins: Seq<(nat, Seq<u8>)>, s: Seq<u8>) -> bool {
    forall|j: int|
        #![trigger ins[j]]
        0 <= j < ins.len() ==> ins[j].0 + ins[j].1.len() <= s.len() && ins[j].1 == s.subrange(
            ins[j].0 as int,
            (ins[j].0 + ins[j].1.len()) as int,
        )
}

/// All data received: "Data Recvd", or "Data Read" once it was delivered.
pub open spec fn all_received(st: SpecRecv) -> bool {
    st.state is DataRecvd || st.state is DataRead
}

/// One more range covers what the old ones did and its own offsets.
proof fn lemma_covered_push(ins: Seq<(nat, Seq<u8>)>, x: (nat, Seq<u8>))
    ensures
        forall|o: nat| #[trigger]
            covered(ins.push(x), o) <==> covered(ins, o) || x.0 <= o < x.0 + x.1.len(),
{
    let q = ins.push(x);
    assert forall|o: nat| #[trigger]
        covered(q, o) <==> covered(ins, o) || x.0 <= o < x.0 + x.1.len() by {
        if covered(ins, o) {
            let j = choose|j: int| #![trigger ins[j]] 0 <= j < ins.len() && ins[j].0 <= o < ins[j].0 + ins[j].1.len();
            assert(q[j] == ins[j]);
        }
        if x.0 <= o < x.0 + x.1.len() {
            assert(q[ins.len() as int] == x);
        }
        if covered(q, o) {
            let j = choose|j: int| #![trigger q[j]] 0 <= j < q.len() && q[j].0 <= o < q[j].0 + q[j].1.len();
            if j < ins.len() {
                assert(q[j] == ins[j]);
            }
        }
    }
}

/// A consistent trace covers only offsets below `s`'s length.
proof fn lemma_covered_lt(t: Seq<SpecRecvIn>, s: Seq<u8>)
    requires
        all_consistent(t, s),
    ensures
        forall|o: nat| #[trigger] covered(pairs(t), o) ==> o < s.len(),
{
    assert forall|o: nat| #[trigger] covered(pairs(t), o) implies o < s.len() by {
        let p = pairs(t);
        let j = choose|j: int| #![trigger p[j]] 0 <= j < p.len() && p[j].0 <= o < p[j].0 + p[j].1.len();
        assert(p[j] == pair_of(t[j]));
        assert(consistent_with(t[j], s));
    }
}

/// What a consistent trace with no RESET_STREAM has received: ranges of `s`, within the trace's ranges, and all of them
/// until delivery reaches the FIN ("Data Read" ignores later frames); the final size is `s`'s once a FIN arrived.
#[verifier::spinoff_prover]
proof fn lemma_frame_trace_ind(id: u64, window: u64, t: Seq<SpecRecvIn>, s: Seq<u8>)
    requires
        no_reset(t),
        all_consistent(t, s),
        rfc_recv(id, window, t).err is None,
    ensures
        ({
            let st = rfc_recv(id, window, t);
            &&& !(st.state is ResetRead)
            &&& st.final_size == if has_fin(t) {
                Some(s.len())
            } else {
                None::<nat>
            }
            &&& ins_of(st.ins, s)
            &&& forall|o: nat| #[trigger] covered(st.ins, o) ==> covered(pairs(t), o)
            &&& !terminal(st.state) ==> forall|o: nat| #[trigger] covered(pairs(t), o) ==> covered(st.ins, o)
        }),
    decreases t.len(),
{
    if t.len() == 0 {
        assert(pairs(t) =~= Seq::<(nat, Seq<u8>)>::empty());
        return;
    }
    let p = t.drop_last();
    let i = t.last();
    assert(p.push(i) =~= t);
    lemma_recv_push(id, window, p, i);
    lemma_recv_inv(id, window, p);
    assert forall|j: int| #![trigger p[j]] 0 <= j < p.len() implies !(p[j] is Reset) && consistent_with(p[j], s) by {
        assert(p[j] == t[j]);
    }
    lemma_frame_trace_ind(id, window, p, s);
    assert(t[t.len() - 1] == i);
    assert(!(i is Reset) && consistent_with(i, s));
    let sp = rfc_recv(id, window, p);
    let st = rfc_recv(id, window, t);
    // has_fin(t) is has_fin(p) or a FIN in i.
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
    assert(pairs(t) =~= pairs(p).push(pair_of(i)));
    lemma_covered_push(pairs(p), pair_of(i));
    match i {
        SpecRecvIn::Data { off, data, fin } => {
            if !terminal(sp.state) {
                assert(st.ins == sp.ins.push((off, data)));
                lemma_covered_push(sp.ins, (off, data));
                assert forall|j: int| #![trigger st.ins[j]] 0 <= j < st.ins.len() implies st.ins[j].0
                    + st.ins[j].1.len() <= s.len() && st.ins[j].1 == s.subrange(
                    st.ins[j].0 as int,
                    (st.ins[j].0 + st.ins[j].1.len()) as int,
                ) by {
                    if j < sp.ins.len() {
                        assert(st.ins[j] == sp.ins[j]);
                    }
                }
            }
        },
        SpecRecvIn::Deliver { max } => {
            lemma_deliver_fields(id, sp, max);
        },
        _ => {},
    }
}

/// One trace's facts, in terms of its covered offsets: the contiguous prefix `n` is the least offset the trace does not
/// cover, the bytes received up to it are `s`'s, the delivered bytes are `s`'s prefix, all data is received exactly when
/// a FIN arrived and `n` is `s`'s length, and "Data Read" means all of `s` was delivered.
#[verifier::spinoff_prover]
proof fn lemma_frame_trace(id: u64, window: u64, t: Seq<SpecRecvIn>, s: Seq<u8>)
    requires
        no_reset(t),
        all_consistent(t, s),
        rfc_recv(id, window, t).err is None,
    ensures
        ({
            let st = rfc_recv(id, window, t);
            let m = rfc_received(st.ins);
            let n = rfc_contiguous(m);
            &&& n <= s.len()
            &&& rfc_prefix(m, n) == s.take(n as int)
            &&& data_of(st.events) == s.take(st.delivered as int)
            &&& st.state is DataRead ==> st.delivered == s.len()
            &&& all_received(st) == (has_fin(t) && n == s.len())
            &&& !covered(pairs(t), n)
            &&& forall|j: nat| j < n ==> #[trigger] covered(pairs(t), j)
        }),
{
    lemma_frame_trace_ind(id, window, t, s);
    lemma_recv_inv(id, window, t);
    lemma_covered_lt(t, s);
    let st = rfc_recv(id, window, t);
    let m = rfc_received(st.ins);
    theorem_reassembly_order_free(st.ins, s);
    lemma_contiguous_exists(m);
    assert(!m.contains_key(s.len()));
    lemma_contiguous_le(m, s.len());
    let n = rfc_contiguous(m);
    let d = st.delivered;
    assert forall|j: nat| j < n implies #[trigger] covered(pairs(t), j) by {
        assert(m.contains_key(j));
    }
    // The delivered bytes are the first `d` of the contiguous prefix, which is `s`'s.
    assert(rfc_prefix(m, d) =~= s.take(d as int)) by {
        assert forall|k: int| 0 <= k < d implies #[trigger] rfc_prefix(m, d)[k] == s.take(d as int)[k] by {
            assert(rfc_prefix(m, n)[k] == s.take(n as int)[k]);
        }
    }
    if st.state is DataRead {
        assert(n == s.len());
    } else {
        assert(!covered(st.ins, n));
    }
}

/// Order independence for a receiving part fed by the frame path. Two consistent traces with no RESET_STREAM that hold
/// the same inputs (STREAM frames, deliveries, credit, STOP_SENDING), in any order and with any duplication, agree on
/// what was received in order (the contiguous prefix, which is `s`'s) and on whether all data was received ("Data
/// Recvd" or, once delivered, "Data Read"); in each, the bytes delivered so far are `s`'s prefix, in any chunking, and
/// a delivered FIN means all of `s` was delivered. (What was delivered depends on where the deliveries fall, so it is
/// not order-free; "Data Recvd" alone is not either: a delivery before the last frame leaves it, one after moves on.)
#[verifier::spinoff_prover]
pub proof fn theorem_recv_frame_order_free(
    id: u64,
    window: u64,
    t1: Seq<SpecRecvIn>,
    t2: Seq<SpecRecvIn>,
    s: Seq<u8>,
)
    requires
        no_reset(t1),
        no_reset(t2),
        t1.to_multiset() == t2.to_multiset(),
        all_consistent(t1, s),
        all_consistent(t2, s),
        rfc_recv(id, window, t1).err is None,
        rfc_recv(id, window, t2).err is None,
    ensures
        rfc_contiguous(rfc_received(rfc_recv(id, window, t1).ins)) == rfc_contiguous(
            rfc_received(rfc_recv(id, window, t2).ins),
        ),
        rfc_prefix(
            rfc_received(rfc_recv(id, window, t1).ins),
            rfc_contiguous(rfc_received(rfc_recv(id, window, t1).ins)),
        ) == s.take(rfc_contiguous(rfc_received(rfc_recv(id, window, t1).ins)) as int),
        all_received(rfc_recv(id, window, t1)) == all_received(rfc_recv(id, window, t2)),
        data_of(rfc_recv(id, window, t1).events) == s.take(rfc_recv(id, window, t1).delivered as int),
        data_of(rfc_recv(id, window, t2).events) == s.take(rfc_recv(id, window, t2).delivered as int),
        rfc_recv(id, window, t1).state is DataRead ==> rfc_recv(id, window, t1).delivered == s.len(),
        rfc_recv(id, window, t2).state is DataRead ==> rfc_recv(id, window, t2).delivered == s.len(),
{
    lemma_frame_trace(id, window, t1, s);
    lemma_frame_trace(id, window, t2, s);
    lemma_same_covered(t1, t2);
    lemma_same_covered(t2, t1);
    let n1 = rfc_contiguous(rfc_received(rfc_recv(id, window, t1).ins));
    let n2 = rfc_contiguous(rfc_received(rfc_recv(id, window, t2).ins));
    // Each is the least offset its trace does not cover, and both traces cover the same offsets.
    if n1 < n2 {
        assert(covered(pairs(t2), n1));
    }
    if n2 < n1 {
        assert(covered(pairs(t1), n2));
    }
}

/// An element of `t1` is an element of `t2` (as `recv_stream`'s private `lemma_in_both`).
proof fn lemma_in_multiset(t1: Seq<SpecRecvIn>, t2: Seq<SpecRecvIn>, j: int)
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

/// Every offset `t1` covers, and its FIN, are in `t2` too.
proof fn lemma_same_covered(t1: Seq<SpecRecvIn>, t2: Seq<SpecRecvIn>)
    requires
        t1.to_multiset() == t2.to_multiset(),
    ensures
        forall|o: nat| #[trigger] covered(pairs(t1), o) ==> covered(pairs(t2), o),
        has_fin(t1) ==> has_fin(t2),
{
    assert forall|o: nat| #[trigger] covered(pairs(t1), o) implies covered(pairs(t2), o) by {
        let p1 = pairs(t1);
        let j = choose|j: int| #![trigger p1[j]] 0 <= j < p1.len() && p1[j].0 <= o < p1[j].0 + p1[j].1.len();
        lemma_in_multiset(t1, t2, j);
        let q = choose|q: int| 0 <= q < t2.len() && t2[q] == t1[j];
        assert(pairs(t2)[q] == p1[j]);
    }
    if has_fin(t1) {
        let j = choose|j: int| 0 <= j < t1.len() && is_fin_in(#[trigger] t1[j]);
        lemma_in_multiset(t1, t2, j);
        let q = choose|q: int| 0 <= q < t2.len() && t2[q] == t1[j];
        assert(is_fin_in(t2[q]));
    }
}

} // verus!
