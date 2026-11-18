//! The sending part of a stream (RFC 9000 §3.1): buffered application data sent in STREAM
//! chunks under the peer's stream data limit (§4.1), retransmitted unchanged when lost (§2.2),
//! and abandoned with RESET_STREAM (§3.3, §3.5).
use vstd::prelude::*;
use vstd::slice::{slice_subrange, slice_to_vec};
use byteq::queue::ByteQueue;
use crate::flow::*;
use crate::ranges::*;
use wire::varint::*;

verus! {

/// Figure 2's send states.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum SendState {
    Ready,
    Send,
    DataSent,
    DataRecvd,
    ResetSent,
    ResetRecvd,
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-3.1
//# Sending the first STREAM or STREAM_DATA_BLOCKED frame causes a
//# sending part of a stream to enter the "Send" state.
//= https://www.rfc-editor.org/rfc/rfc9000#section-3.1
//# After the application indicates that all stream data has been sent
//# and a STREAM frame containing the FIN bit is sent, the sending part
//# of the stream enters the "Data Sent" state.
//= https://www.rfc-editor.org/rfc/rfc9000#section-3.1
//# Once all stream data has been successfully acknowledged, the sending
//# part of the stream enters the "Data Recvd" state, which is a terminal
//# state.
//= https://www.rfc-editor.org/rfc/rfc9000#section-3.1
//# From any state that is one of "Ready", "Send", or "Data Sent", an
//# application can signal that it wishes to abandon transmission of
//# stream data.  Alternatively, an endpoint might receive a STOP_SENDING
//# frame from its peer.  In either case, the endpoint sends a
//# RESET_STREAM frame, which causes the stream to enter the "Reset Sent"
//# state.
//= https://www.rfc-editor.org/rfc/rfc9000#section-3.1
//# Once a packet containing a RESET_STREAM has been acknowledged, the
//# sending part of the stream enters the "Reset Recvd" state, which is a
//# terminal state.
/// Figure 2's edges.
pub open spec fn send_edge(a: SendState, b: SendState) -> bool {
    ||| a is Ready && b is Send
    ||| a is Send && b is DataSent
    ||| a is DataSent && b is DataRecvd
    ||| (a is Ready || a is Send || a is DataSent) && b is ResetSent
    ||| a is ResetSent && b is ResetRecvd
}

/// One call moves along at most two edges: one emission may take Ready to Send to Data Sent.
pub open spec fn send_step_ok(a: SendState, b: SendState) -> bool {
    a == b || send_edge(a, b) || exists|c: SendState| send_edge(a, c) && send_edge(c, b)
}

/// One STREAM frame's worth of data: `new_bytes` of it were never sent before.
#[derive(Debug, PartialEq, Eq)]
pub struct Chunk {
    pub off: u64,
    pub data: Vec<u8>,
    pub fin: bool,
    pub new_bytes: u64,
}

pub struct SpecChunk {
    pub off: u64,
    pub data: Seq<u8>,
    pub fin: bool,
    pub new_bytes: u64,
}

impl View for Chunk {
    type V = SpecChunk;

    open spec fn view(&self) -> SpecChunk {
        SpecChunk { off: self.off, data: self.data@, fin: self.fin, new_bytes: self.new_bytes }
    }
}

/// The cost constants of the ACK, loss and poll workers: `c_ss1() · (h + 1) + c_ss2() · MAX_FLUSH` (D10 (e)).
pub open spec fn c_ss1() -> nat {
    400
}

pub open spec fn c_ss2() -> nat {
    10
}

/// D10 (a), (d) over the views of a part not reset: the acked, lost and in-flight sets lie in `[ab, se)`, pairwise
/// apart, and cover it; the open slots ascend, each ending in `(ab, se]`; every item is at least `FLOOR` long or holds
/// a whole open slot. Opaque: revealed only by the lemmas below.
#[verifier::opaque]
pub open spec fn parts(
    a: Seq<(u64, u64)>,
    l: Seq<(u64, u64)>,
    f: Seq<(u64, u64)>,
    sp: Seq<(u64, u64)>,
    ab: u64,
    se: u64,
) -> bool {
    &&& in_bounds(a, ab, se)
    &&& in_bounds(l, ab, se)
    &&& in_bounds(f, ab, se)
    &&& apart(a, l)
    &&& apart(a, f)
    &&& apart(l, f)
    &&& forall|x: nat|
        #![trigger covers(a, x)]
        #![trigger covers(l, x)]
        #![trigger covers(f, x)]
        ab <= x < se ==> covers(a, x) || covers(l, x) || covers(f, x)
    &&& disjoint(sp)
    &&& forall|k: int| 0 <= k < sp.len() ==> ab < #[trigger] sp[k].1 <= se
    &&& items_ok(a, sp)
    &&& items_ok(l, sp)
    &&& items_ok(f, sp)
}

/// No acked range starts at `ab`: one `drop_front` per ACK takes the whole acknowledged prefix (Task 8 review Minor 3).
pub open spec fn starts_past(a: Seq<(u64, u64)>, ab: u64) -> bool {
    forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i].0 > ab
}

/// A range of `v` lies in `[lo, hi)`, so its bytes do.
proof fn lemma_covers_in(v: Seq<(u64, u64)>, lo: u64, hi: u64)
    requires
        in_bounds(v, lo, hi),
    ensures
        forall|x: nat| #[trigger] covers(v, x) ==> lo <= x < hi,
{
    assert forall|x: nat| #[trigger] covers(v, x) implies lo <= x < hi by {
        let i = choose|i: int| 0 <= i < v.len() && #[trigger] inr(v[i], x);
        assert(lo <= v[i].0 < v[i].1 <= hi);
    }
}

/// Each range of `w` is a range of `v` or `q`: `w` is in bounds and its items ok when those of `v` and `q` are.
proof fn lemma_sub(v: Seq<(u64, u64)>, w: Seq<(u64, u64)>, q: (u64, u64), sp: Seq<(u64, u64)>, lo: u64, hi: u64)
    requires
        forall|p: (u64, u64)| #[trigger] w.contains(p) ==> v.contains(p) || p == q,
        in_bounds(v, lo, hi),
        items_ok(v, sp),
        lo <= q.0 < q.1 <= hi,
        item_ok(q, sp),
    ensures
        in_bounds(w, lo, hi),
        items_ok(w, sp),
{
    assert forall|i: int| 0 <= i < w.len() implies lo <= #[trigger] w[i].0 < w[i].1 <= hi && item_ok(w[i], sp) by {
        assert(w.contains(w[i]));
        if v.contains(w[i]) {
            let j = choose|j: int| 0 <= j < v.len() && v[j] == w[i];
            assert(item_ok(v[j], sp));
        }
    }
}

/// An item holding an ok item is ok.
proof fn lemma_item_grow(p: (u64, u64), q: (u64, u64), sp: Seq<(u64, u64)>)
    requires
        item_ok(p, sp),
        q.0 <= p.0,
        p.1 <= q.1,
        p.0 < p.1,
    ensures
        item_ok(q, sp),
{
    if !(p.1 - p.0 >= FLOOR) {
        let j = choose|j: int| 0 <= j < sp.len() && p.0 <= #[trigger] sp[j].0 && sp[j].1 <= p.1;
        assert(q.0 <= sp[j].0 && sp[j].1 <= q.1);
    }
}

/// An ok item stays ok against `sp` with slots added after.
proof fn lemma_items_push(v: Seq<(u64, u64)>, sp: Seq<(u64, u64)>, sp2: Seq<(u64, u64)>)
    requires
        items_ok(v, sp),
        sp.len() <= sp2.len(),
        forall|k: int| 0 <= k < sp.len() ==> #[trigger] sp2[k] == sp[k],
    ensures
        items_ok(v, sp2),
{
    assert forall|i: int| 0 <= i < v.len() implies #[trigger] item_ok(v[i], sp2) by {
        assert(item_ok(v[i], sp));
        if !(v[i].1 - v[i].0 >= FLOOR) {
            let j = choose|j: int| 0 <= j < sp.len() && v[i].0 <= #[trigger] sp[j].0 && sp[j].1 <= v[i].1;
            assert(sp2[j] == sp[j]);
        }
    }
}

/// D10 (d): the bound, from `parts` (`lemma_bound`).
proof fn lemma_parts_bound(
    a: Seq<(u64, u64)>,
    l: Seq<(u64, u64)>,
    f: Seq<(u64, u64)>,
    sp: Seq<(u64, u64)>,
    ab: u64,
    se: u64,
)
    requires
        parts(a, l, f, sp, ab, se),
        disjoint(a),
        disjoint(l),
        disjoint(f),
    ensures
        a.len() + l.len() + f.len() <= ((se - ab) as nat) / (FLOOR as nat) + sp.len(),
{
    reveal(parts);
    lemma_bound(a, l, f, sp, ab, se);
}

/// A new piece `[se, e2)` past every item: in flight, with its own slot if short.
proof fn lemma_new_piece(
    a: Seq<(u64, u64)>,
    l: Seq<(u64, u64)>,
    f: Seq<(u64, u64)>,
    f2: Seq<(u64, u64)>,
    sp: Seq<(u64, u64)>,
    sp2: Seq<(u64, u64)>,
    ab: u64,
    se: u64,
    e2: u64,
)
    requires
        parts(a, l, f, sp, ab, se),
        ab <= se < e2,
        forall|x: nat| #[trigger] covers(f2, x) <==> covers(f, x) || (se <= x && x < e2),
        forall|p: (u64, u64)| #[trigger] f2.contains(p) <==> f.contains(p) || p == (se, e2),
        sp2 == sp.push((se, e2)) || (sp2 == sp && e2 - se >= FLOOR),
    ensures
        parts(a, l, f2, sp2, ab, e2),
{
    reveal(parts);
    lemma_covers_in(a, ab, se);
    lemma_covers_in(l, ab, se);
    lemma_covers_in(f, ab, se);
    assert forall|k: int| 0 <= k < sp.len() implies #[trigger] sp2[k] == sp[k] by {}
    lemma_items_push(a, sp, sp2);
    lemma_items_push(l, sp, sp2);
    lemma_items_push(f, sp, sp2);
    assert(item_ok((se, e2), sp2)) by {
        if sp2 != sp {
            assert(sp2[sp.len() as int] == (se, e2));
        }
    }
    lemma_sub(f, f2, (se, e2), sp2, ab, e2);
    assert(in_bounds(a, ab, e2));
    assert(in_bounds(l, ab, e2));
    assert(in_bounds(f, ab, e2));
    assert(disjoint(sp2)) by {
        assert forall|i: int, j: int| 0 <= i < j < sp2.len() implies #[trigger] sp2[i].1 <= #[trigger] sp2[j].0 by {
            if j == sp.len() {
                assert(sp2[i] == sp[i]);
            }
        }
    }
}

/// A resent piece `[s, s + k)` off the first lost range `[s, e)`: whole, or a cut leaving both parts at least FLOOR.
proof fn lemma_resend(
    a: Seq<(u64, u64)>,
    l: Seq<(u64, u64)>,
    l2: Seq<(u64, u64)>,
    f: Seq<(u64, u64)>,
    f2: Seq<(u64, u64)>,
    sp: Seq<(u64, u64)>,
    ab: u64,
    se: u64,
    k: u64,
)
    requires
        parts(a, l, f, sp, ab, se),
        disjoint(l),
        l.len() > 0,
        0 < k <= l[0].1 - l[0].0,
        k == l[0].1 - l[0].0 || (k >= FLOOR && l[0].1 - l[0].0 - k >= FLOOR),
        forall|x: nat| #[trigger] covers(l2, x) <==> covers(l, x) && !(l[0].0 <= x && x < l[0].0 + k),
        l2 == (if k == l[0].1 - l[0].0 {
            l.skip(1)
        } else {
            l.update(0, ((l[0].0 + k) as u64, l[0].1))
        }),
        forall|x: nat| #[trigger] covers(f2, x) <==> covers(f, x) || (l[0].0 <= x && x < l[0].0 + k),
        forall|p: (u64, u64)| #[trigger] f2.contains(p) <==> f.contains(p) || p == (l[0].0, (l[0].0 + k) as u64),
    ensures
        parts(a, l2, f2, sp, ab, se),
{
    reveal(parts);
    let (s, e) = l[0];
    let q = (s, (s + k) as u64);
    assert(inr(l[0], s as nat));
    assert(item_ok(l[0], sp));
    assert(item_ok(q, sp));
    lemma_sub(f, f2, q, sp, ab, se);
    assert forall|i: int| 0 <= i < l2.len() implies ab <= #[trigger] l2[i].0 < l2[i].1 <= se && item_ok(l2[i], sp) by {
        if k == e - s {
            assert(l2[i] == l[i + 1]);
            assert(item_ok(l[i + 1], sp));
        } else if i > 0 {
            assert(l2[i] == l[i]);
            assert(item_ok(l[i], sp));
        }
    }
    assert forall|x: nat| #![trigger covers(a, x), covers(f2, x)] !(covers(a, x) && covers(f2, x)) by {
        if covers(f2, x) && !covers(f, x) {
            assert(inr(l[0], x));
            assert(covers(l, x));
        }
    }
    assert forall|x: nat| #![trigger covers(l2, x), covers(f2, x)] !(covers(l2, x) && covers(f2, x)) by {
        if covers(l2, x) {
            assert(covers(l, x));
        }
    }
    assert forall|x: nat| #![trigger covers(a, x), covers(l2, x)] !(covers(a, x) && covers(l2, x)) by {
        if covers(l2, x) {
            assert(covers(l, x));
        }
    }
    assert forall|x: nat|
        #![trigger covers(a, x)]
        #![trigger covers(l2, x)]
        #![trigger covers(f2, x)]
        ab <= x < se implies covers(a, x) || covers(l2, x) || covers(f2, x) by {
        if covers(l, x) {
        }
    }
}

/// No byte of an in-flight piece is acked or lost.
proof fn lemma_piece_free(
    a: Seq<(u64, u64)>,
    l: Seq<(u64, u64)>,
    f: Seq<(u64, u64)>,
    sp: Seq<(u64, u64)>,
    ab: u64,
    se: u64,
    o: u64,
    e: u64,
)
    requires
        parts(a, l, f, sp, ab, se),
        f.contains((o, e)),
    ensures
        ab <= o < e <= se,
        forall|x: nat| o <= x < e ==> !covers(a, x) && !covers(l, x),
        item_ok((o, e), sp),
{
    reveal(parts);
    let i = choose|i: int| 0 <= i < f.len() && f[i] == (o, e);
    assert(item_ok(f[i], sp));
    assert forall|x: nat| o <= x < e implies !covers(a, x) && !covers(l, x) by {
        assert(inr(f[i], x));
        assert(covers(f, x));
    }
}

/// The piece `(o, e)` leaves flight and joins the merged set `v`, as `w` (the merged range `(am, bm)`); `u` is the
/// third set. Shared by ACK (`v` acked) and loss (`v` lost).
proof fn lemma_move(
    v: Seq<(u64, u64)>,
    w: Seq<(u64, u64)>,
    u: Seq<(u64, u64)>,
    f: Seq<(u64, u64)>,
    f2: Seq<(u64, u64)>,
    sp: Seq<(u64, u64)>,
    ab: u64,
    se: u64,
    o: u64,
    e: u64,
    am: u64,
    bm: u64,
)
    requires
        in_bounds(v, ab, se),
        in_bounds(u, ab, se),
        in_bounds(f, ab, se),
        apart(v, u),
        apart(v, f),
        apart(u, f),
        forall|x: nat|
            #![trigger covers(v, x)]
            #![trigger covers(u, x)]
            #![trigger covers(f, x)]
            ab <= x < se ==> covers(v, x) || covers(u, x) || covers(f, x),
        items_ok(v, sp),
        items_ok(f, sp),
        f.contains((o, e)),
        ab <= o < e <= se,
        item_ok((o, e), sp),
        forall|x: nat| #[trigger] covers(f2, x) <==> covers(f, x) && !(o <= x && x < e),
        forall|p: (u64, u64)| #[trigger] f2.contains(p) <==> f.contains(p) && p != (o, e),
        forall|x: nat| #[trigger] covers(w, x) <==> covers(v, x) || (o <= x && x < e),
        w.contains((am, bm)),
        am <= o,
        e <= bm,
        am == o || v.contains((am, o)),
        bm == e || v.contains((e, bm)),
        forall|p: (u64, u64)| #[trigger] w.contains(p) && p != (am, bm) ==> v.contains(p),
    ensures
        in_bounds(w, ab, se),
        in_bounds(f2, ab, se),
        apart(w, u),
        apart(w, f2),
        apart(u, f2),
        forall|x: nat|
            #![trigger covers(w, x)]
            #![trigger covers(u, x)]
            #![trigger covers(f2, x)]
            ab <= x < se ==> covers(w, x) || covers(u, x) || covers(f2, x),
        items_ok(w, sp),
        items_ok(f2, sp),
        ab <= am,
{
    let q = (am, bm);
    if am != o {
        let j = choose|j: int| 0 <= j < v.len() && v[j] == (am, o);
        assert(ab <= v[j].0);
    }
    if bm != e {
        let j = choose|j: int| 0 <= j < v.len() && v[j] == (e, bm);
        assert(v[j].1 <= se);
    }
    lemma_item_grow((o, e), q, sp);
    lemma_sub(v, w, q, sp, ab, se);
    lemma_sub(f, f2, (o, e), sp, ab, se);
    let i = choose|i: int| 0 <= i < f.len() && f[i] == (o, e);
    assert forall|x: nat| o <= x < e implies covers(f, x) by {
        assert(inr(f[i], x));
    }
    assert forall|x: nat| #![trigger covers(w, x), covers(u, x)] !(covers(w, x) && covers(u, x)) by {
        if covers(w, x) && !covers(v, x) {
            assert(covers(f, x));
        }
    }
    assert forall|x: nat| #![trigger covers(w, x), covers(f2, x)] !(covers(w, x) && covers(f2, x)) by {
        if covers(f2, x) {
            assert(covers(f, x));
        }
    }
    assert forall|x: nat| #![trigger covers(u, x), covers(f2, x)] !(covers(u, x) && covers(f2, x)) by {
        if covers(f2, x) {
            assert(covers(f, x));
        }
    }
    assert forall|x: nat|
        #![trigger covers(w, x)]
        #![trigger covers(u, x)]
        #![trigger covers(f2, x)]
        ab <= x < se implies covers(w, x) || covers(u, x) || covers(f2, x) by {
        if covers(v, x) {
        }
        if covers(f, x) {
        }
    }
}

/// An ACK moves the piece to `acked` (`a2`, its merged range `(am, bm)`); the start clause holds but for `(am, bm)`.
proof fn lemma_ack(
    a: Seq<(u64, u64)>,
    a2: Seq<(u64, u64)>,
    l: Seq<(u64, u64)>,
    f: Seq<(u64, u64)>,
    f2: Seq<(u64, u64)>,
    sp: Seq<(u64, u64)>,
    ab: u64,
    se: u64,
    o: u64,
    e: u64,
    am: u64,
    bm: u64,
)
    requires
        parts(a, l, f, sp, ab, se),
        starts_past(a, ab),
        f.contains((o, e)),
        forall|x: nat| #[trigger] covers(f2, x) <==> covers(f, x) && !(o <= x && x < e),
        forall|p: (u64, u64)| #[trigger] f2.contains(p) <==> f.contains(p) && p != (o, e),
        forall|x: nat| #[trigger] covers(a2, x) <==> covers(a, x) || (o <= x && x < e),
        a2.contains((am, bm)),
        am <= o,
        e <= bm,
        am == o || a.contains((am, o)),
        bm == e || a.contains((e, bm)),
        forall|p: (u64, u64)| #[trigger] a2.contains(p) && p != (am, bm) ==> a.contains(p),
    ensures
        parts(a2, l, f2, sp, ab, se),
        ab <= am,
        am > ab ==> starts_past(a2, ab),
        forall|p: (u64, u64)| #[trigger] a2.contains(p) && p != (am, bm) ==> p.0 > ab,
{
    lemma_piece_free(a, l, f, sp, ab, se, o, e);
    reveal(parts);
    lemma_move(a, a2, l, f, f2, sp, ab, se, o, e, am, bm);
    assert forall|p: (u64, u64)| #[trigger] a2.contains(p) && p != (am, bm) implies p.0 > ab by {
        let j = choose|j: int| 0 <= j < a.len() && a[j] == p;
        assert(a[j].0 > ab);
    }
    if am > ab {
        assert forall|i: int| 0 <= i < a2.len() implies #[trigger] a2[i].0 > ab by {
            assert(a2.contains(a2[i]));
        }
    }
}

/// A loss moves the piece to `lost` (`l2`, its merged range `(am, bm)`).
proof fn lemma_lose(
    a: Seq<(u64, u64)>,
    l: Seq<(u64, u64)>,
    l2: Seq<(u64, u64)>,
    f: Seq<(u64, u64)>,
    f2: Seq<(u64, u64)>,
    sp: Seq<(u64, u64)>,
    ab: u64,
    se: u64,
    o: u64,
    e: u64,
    am: u64,
    bm: u64,
)
    requires
        parts(a, l, f, sp, ab, se),
        f.contains((o, e)),
        forall|x: nat| #[trigger] covers(f2, x) <==> covers(f, x) && !(o <= x && x < e),
        forall|p: (u64, u64)| #[trigger] f2.contains(p) <==> f.contains(p) && p != (o, e),
        forall|x: nat| #[trigger] covers(l2, x) <==> covers(l, x) || (o <= x && x < e),
        l2.contains((am, bm)),
        am <= o,
        e <= bm,
        am == o || l.contains((am, o)),
        bm == e || l.contains((e, bm)),
        forall|p: (u64, u64)| #[trigger] l2.contains(p) && p != (am, bm) ==> l.contains(p),
    ensures
        parts(a, l2, f2, sp, ab, se),
{
    lemma_piece_free(a, l, f, sp, ab, se, o, e);
    reveal(parts);
    lemma_move(l, l2, a, f, f2, sp, ab, se, o, e, am, bm);
}

/// Two distinct ranges of a merged sequence: one ends before the other starts.
proof fn lemma_merged_pair(v: Seq<(u64, u64)>, p: (u64, u64), q: (u64, u64))
    requires
        merged(v),
        v.contains(p),
        v.contains(q),
        p != q,
    ensures
        p.1 < q.0 || q.1 < p.0,
{
    let i = choose|i: int| 0 <= i < v.len() && v[i] == p;
    let j = choose|j: int| 0 <= j < v.len() && v[j] == q;
    if i < j {
        assert(v[i].1 < v[j].0);
    } else {
        assert(v[j].1 < v[i].0);
    }
}

/// The acked prefix `(ab, b)` leaves `acked` (`a3`), `acked_base` moves to `b`, and the slots ending at or below `b`
/// (the first `c`) close.
proof fn lemma_drop(
    a2: Seq<(u64, u64)>,
    a3: Seq<(u64, u64)>,
    l: Seq<(u64, u64)>,
    f: Seq<(u64, u64)>,
    sp: Seq<(u64, u64)>,
    sp3: Seq<(u64, u64)>,
    ab: u64,
    b: u64,
    se: u64,
    c: int,
)
    requires
        parts(a2, l, f, sp, ab, se),
        merged(a2),
        a2.contains((ab, b)),
        forall|p: (u64, u64)| #[trigger] a2.contains(p) && p != (ab, b) ==> p.0 > ab,
        forall|x: nat| #[trigger] covers(a3, x) <==> covers(a2, x) && !(ab <= x && x < b),
        forall|p: (u64, u64)| #[trigger] a3.contains(p) ==> a2.contains(p) && p != (ab, b),
        0 <= c <= sp.len(),
        forall|k: int| 0 <= k < c ==> #[trigger] sp[k].1 <= b,
        forall|k: int| c <= k < sp.len() ==> #[trigger] sp[k].1 > b,
        sp3 == sp.skip(c),
    ensures
        parts(a3, l, f, sp3, b, se),
        starts_past(a3, b),
        ab < b <= se,
{
    reveal(parts);
    let i0 = choose|i: int| 0 <= i < a2.len() && a2[i] == (ab, b);
    assert(a2[i0].0 < a2[i0].1 <= se);
    assert forall|x: nat| ab <= x < b implies covers(a2, x) by {
        assert(inr(a2[i0], x));
    }
    // What stays lies at or past b, so in `[b, se)`, and holds only slots ending past b.
    assert forall|i: int| 0 <= i < a3.len() implies #[trigger] a3[i].0 > b && a3[i].1 <= se && a3[i].0 < a3[i].1 && item_ok(
        a3[i],
        sp,
    ) by {
        assert(a3.contains(a3[i]));
        let j = choose|j: int| 0 <= j < a2.len() && a2[j] == a3[i];
        assert(a2.contains(a3[i]));
        lemma_merged_pair(a2, a3[i], (ab, b));
        assert(item_ok(a2[j], sp));
    }
    assert forall|i: int| 0 <= i < l.len() implies #[trigger] l[i].0 >= b by {
        if l[i].0 < b {
            assert(inr(l[i], l[i].0 as nat));
            assert(covers(l, l[i].0 as nat) && covers(a2, l[i].0 as nat));
        }
    }
    assert forall|i: int| 0 <= i < f.len() implies #[trigger] f[i].0 >= b by {
        if f[i].0 < b {
            assert(inr(f[i], f[i].0 as nat));
            assert(covers(f, f[i].0 as nat) && covers(a2, f[i].0 as nat));
        }
    }
    // An item past b holds no closed slot.
    assert forall|it: (u64, u64)| it.0 >= b && it.0 < it.1 && #[trigger] item_ok(it, sp) implies item_ok(it, sp3) by {
        if !(it.1 - it.0 >= FLOOR) {
            let j = choose|j: int| 0 <= j < sp.len() && it.0 <= #[trigger] sp[j].0 && sp[j].1 <= it.1;
            assert(sp[j].0 < sp[j].1);
            assert(j >= c);
            assert(sp3[j - c] == sp[j]);
        }
    }
    assert forall|i: int| 0 <= i < a3.len() implies #[trigger] item_ok(a3[i], sp3) by {
        assert(item_ok(a3[i], sp));
    }
    assert forall|i: int| 0 <= i < l.len() implies #[trigger] item_ok(l[i], sp3) by {
        assert(item_ok(l[i], sp));
    }
    assert forall|i: int| 0 <= i < f.len() implies #[trigger] item_ok(f[i], sp3) by {
        assert(item_ok(f[i], sp));
    }
    assert forall|x: nat| #![trigger covers(a3, x), covers(l, x)] !(covers(a3, x) && covers(l, x)) by {}
    assert forall|x: nat| #![trigger covers(a3, x), covers(f, x)] !(covers(a3, x) && covers(f, x)) by {}
    assert forall|x: nat|
        #![trigger covers(a3, x)]
        #![trigger covers(l, x)]
        #![trigger covers(f, x)]
        b <= x < se implies covers(a3, x) || covers(l, x) || covers(f, x) by {
        if covers(a2, x) {
        }
    }
    assert(disjoint(sp3)) by {
        assert forall|i: int, j: int| 0 <= i < j < sp3.len() implies #[trigger] sp3[i].1 <= #[trigger] sp3[j].0 by {
            assert(sp3[i] == sp[i + c] && sp3[j] == sp[j + c]);
        }
        assert forall|i: int| 0 <= i < sp3.len() implies #[trigger] sp3[i].0 < sp3[i].1 by {
            assert(sp3[i] == sp[i + c]);
        }
    }
    assert forall|k: int| 0 <= k < sp3.len() implies b < #[trigger] sp3[k].1 <= se by {
        assert(sp3[k] == sp[k + c]);
    }
}

/// `parts`' bounds, outside its opaque body.
proof fn lemma_parts_end(
    a: Seq<(u64, u64)>,
    l: Seq<(u64, u64)>,
    f: Seq<(u64, u64)>,
    sp: Seq<(u64, u64)>,
    ab: u64,
    se: u64,
)
    requires
        parts(a, l, f, sp, ab, se),
    ensures
        in_bounds(a, ab, se),
        in_bounds(l, ab, se),
        in_bounds(f, ab, se),
        forall|x: nat| #[trigger] covers(f, x) ==> ab <= x < se,
        disjoint(sp),
        forall|k: int| 0 <= k < sp.len() ==> ab < #[trigger] sp[k].1 <= se,
{
    reveal(parts);
    lemma_covers_in(f, ab, se);
}

/// The head `[l[0].0, end)` of the first lost range holds no byte in flight.
proof fn lemma_piece_space(
    a: Seq<(u64, u64)>,
    l: Seq<(u64, u64)>,
    f: Seq<(u64, u64)>,
    sp: Seq<(u64, u64)>,
    ab: u64,
    se: u64,
    end: u64,
)
    requires
        parts(a, l, f, sp, ab, se),
        l.len() > 0,
        l[0].0 < end <= l[0].1,
    ensures
        ab <= l[0].0,
        l[0].1 <= se,
        forall|x: nat| l[0].0 <= x < end ==> !covers(f, x),
{
    reveal(parts);
    assert forall|x: nat| l[0].0 <= x < end implies !covers(f, x) by {
        assert(inr(l[0], x));
        assert(covers(l, x));
    }
}

/// The bytes `retransmit` takes off a lost range of `r` (D10 (c)): all of it if it fits in `m`, else `min(m, r −
/// FLOOR)` when both parts stay at least `FLOOR`, else none (split from `retransmit` for the rlimit).
fn resend_len(r: u64, m: u64) -> (k: Option<u64>)
    ensures
        k is None ==> r > m && (r < 2 * FLOOR || m < FLOOR),
        k matches Some(k) ==> 0 < k <= r || r == 0,
        k matches Some(k) ==> k <= m,
        k matches Some(k) ==> k == r || (k >= FLOOR && r - k >= FLOOR),
{
    if r <= m {
        Some(r)
    } else if r >= 2 * FLOOR && m >= FLOOR {
        if m < r - FLOOR {
            Some(m)
        } else {
            Some(r - FLOOR)
        }
    } else {
        None
    }
}

/// `poll_data` sends new data only while the acked and lost sets hold fewer ranges than this in all. A throttle on new
/// data only, not the bound: the bound is `wf`'s, from piece edges (D10 (d)).
pub const MAX_SEND_RANGES: usize = 64;

/// The reservation a send queue of peak `pk` holds against `MAX_SEND_BUFFER` (owner decision
/// 2026-11-17, option (b)): none while empty, else `2·max(MIN_CAP, 3·pk)` = `max(128, 6·pk)`, which
/// bounds both of its buffers while it migrates (`ByteQueue::lemma_wf`).
pub open spec fn res_of(pk: nat) -> nat {
    if pk == 0 {
        0
    } else if 6 * pk < 128 {
        128
    } else {
        6 * pk
    }
}

/// The most bytes a write may take into a queue of length `len` with `b` bytes of reservation to
/// spend: its peak may reach `b/6` (none below 128).
pub open spec fn res_room(b: nat, len: nat) -> nat {
    if b >= 128 && b / 6 >= len {
        (b / 6 - len) as nat
    } else {
        0
    }
}

/// The sending part of one stream.
pub struct SendStream {
    state: SendState,
    /// The bytes `[acked_base, written)`.
    buf: ByteQueue,
    /// `buf`'s peak, kept in exec for the reservation.
    peak: u64,
    acked_base: u64,
    written: u64,
    sent_end: u64,
    fin_written: bool,
    fin_acked: bool,
    /// Acknowledged bytes past `acked_base`, merged (D10 (a)).
    acked: RangeSet,
    /// Bytes declared lost and not yet resent, merged.
    lost: RangeSet,
    /// The pieces sent and neither acknowledged nor lost, each exactly as `poll_data` returned it.
    flight: PieceSet,
    /// The open slots: the short new pieces sent, `slots[..nslots]`, until `acked_base` reaches their end (D10 (c)).
    slots: [(u64, u64); 4],
    nslots: usize,
    /// The flush point: new bytes below it go out as a short piece (D10 (c)).
    flush_to: u64,
    fin_lost: bool,
    credit: SendCredit,
    /// The RESET_STREAM's error code and final size, once reset.
    reset: Option<(u64, u64)>,
    reset_pending: bool,
    all_written: Ghost<Seq<u8>>,
}

pub open spec fn is_reset(a: SendState) -> bool {
    a is ResetSent || a is ResetRecvd
}

/// No STREAM frames are sent from these states (§3.3).
pub open spec fn no_data(a: SendState) -> bool {
    a is DataRecvd || is_reset(a)
}

/// What a returned chunk guarantees, between the stream before (`s1`) and after (`s2`).
pub open spec fn chunk_ok(
    s1: SendStream,
    s2: SendStream,
    c: SpecChunk,
    max_len: u64,
    conn_avail: u64,
) -> bool {
    let end = c.off + c.data.len();
    &&& end <= s1.all_written().len()
    &&& c.data == s1.all_written().subrange(c.off as int, end)
    &&& c.fin ==> end == s1.all_written().len() && s1.fin_written_spec()
    &&& c.data.len() > 0 || c.fin
    &&& c.data.len() <= max_len
    &&& c.new_bytes <= conn_avail
    &&& s2.sent_end() == s1.sent_end() + c.new_bytes
    &&& end <= s2.sent_end()
    &&& s1.next_off() == Some(c.off)
    &&& !(s2.state() is Ready)
}

impl SendStream {
    /// Every byte the application has written, in order.
    pub closed spec fn all_written(&self) -> Seq<u8> {
        self.all_written@
    }

    pub closed spec fn state(&self) -> SendState {
        self.state
    }

    pub closed spec fn fin_written_spec(&self) -> bool {
        self.fin_written
    }

    pub closed spec fn acked_base_spec(&self) -> u64 {
        self.acked_base
    }

    pub closed spec fn fin_acked_spec(&self) -> bool {
        self.fin_acked
    }

    /// The RESET_STREAM's `(code, final size)`, once reset.
    pub closed spec fn reset_spec(&self) -> Option<(u64, u64)> {
        self.reset
    }

    /// The end of the acknowledged prefix: each ACK drops it from the buffer at once, so it is the
    /// buffer's start (that no acked range starts there is Task 8a's `wf` clause, on merged sets).
    pub closed spec fn acked_point_spec(&self) -> u64 {
        self.acked_base
    }

    pub closed spec fn buffered_spec(&self) -> nat {
        self.buf@.len()
    }

    /// The largest length plus write since the queue was last empty.
    pub closed spec fn peak_spec(&self) -> nat {
        self.peak as nat
    }

    /// The reservation the stream holds against `MAX_SEND_BUFFER` (`res_of` its peak); its queue's buffers are within
    /// it (`lemma_held`), so the connection's sum bounds memory (carryover mem-9b2-send-cap).
    pub closed spec fn held_spec(&self) -> nat {
        res_of(self.peak as nat)
    }

    /// The bytes the send queue's buffers requested from the allocator (both while it migrates).
    pub closed spec fn capacity_spec(&self) -> nat {
        self.buf.requested()
    }

    /// The most bytes a `write` may take with the reservation within `b`.
    pub closed spec fn room_spec(&self, b: nat) -> nat {
        res_room(b, self.buf@.len())
    }

    /// Ranges held in the acked and lost sets.
    pub closed spec fn range_count(&self) -> nat {
        self.acked@.len() + self.lost@.len()
    }

    /// Ranges and pieces held in the three sets: one tree node each.
    pub closed spec fn ranges_held(&self) -> nat {
        self.acked@.len() + self.lost@.len() + self.flight@.len()
    }

    /// The largest of the three trees' heights: per-call costs are in it (D10 (e)).
    pub closed spec fn ht(&self) -> nat {
        let (a, l, f) = (self.acked.ht(), self.lost.ht(), self.flight.ht());
        if a >= l && a >= f {
            a
        } else if l >= f {
            l
        } else {
            f
        }
    }

    /// `[off, off + len)` is a piece in flight, exactly.
    pub closed spec fn in_flight(&self, off: u64, len: u64) -> bool {
        off + len <= VARINT_MAX && self.flight@.contains((off, (off + len) as u64))
    }

    /// The pieces in flight (Task 8b's `tx_flight` reads it).
    pub closed spec fn flight_spec(&self) -> Set<(u64, u64)> {
        self.flight@.to_set()
    }

    /// The flush point: new bytes below it go out as a short piece.
    pub closed spec fn flush_point(&self) -> u64 {
        self.flush_to
    }

    /// The open slots.
    closed spec fn open_slots(&self) -> Seq<(u64, u64)> {
        self.slots@.subrange(0, self.nslots as int)
    }

    /// The three sets (D10 (a), (d)): the partition, the start clause, the slots and the bound.
    closed spec fn sets_ok(&self) -> bool {
        &&& self.acked.wf()
        &&& self.lost.wf()
        &&& self.flight.wf()
        &&& self.nslots <= MAX_FLUSH
        &&& !is_reset(self.state) ==> parts(
            self.acked@,
            self.lost@,
            self.flight@,
            self.open_slots(),
            self.acked_base,
            self.sent_end,
        ) && starts_past(self.acked@, self.acked_base)
        &&& is_reset(self.state) ==> self.acked@.len() == 0 && self.lost@.len() == 0 && self.flight@.len() == 0
            && self.nslots == 0
        &&& self.ranges_held() <= ((self.sent_end - self.acked_base) as nat) / (FLOOR as nat) + self.nslots
    }

    pub closed spec fn sent_end_spec(&self) -> u64 {
        self.sent_end
    }

    pub closed spec fn max_spec(&self) -> u64 {
        self.credit.max_spec()
    }

    /// A FIN is still to be sent: not yet, or again after a loss.
    pub closed spec fn fin_owed(&self) -> bool {
        self.fin_written && (self.state is DataSent ==> self.fin_lost)
    }

    pub closed spec fn next_off_spec(&self) -> Option<u64> {
        if no_data(self.state) {
            None
        } else if self.lost@.len() > 0 {
            Some(self.lost@[0].0)
        } else if self.sent_end < self.written || self.fin_owed() {
            Some(self.sent_end)
        } else {
            None
        }
    }

    pub closed spec fn pending_reset_spec(&self) -> Option<(u64, u64)> {
        if self.reset_pending && self.state is ResetSent {
            self.reset
        } else {
            None
        }
    }

    /// `wf` but the sets and the clauses `on_data_acked` restores only at its end.
    closed spec fn core(&self) -> bool {
        &&& self.buf.wf()
        &&& self.peak == self.buf.peak()
        &&& self.credit.wf()
        &&& self.credit.used_spec() == self.sent_end
        &&& self.sent_end <= self.credit.max_spec()
        &&& self.sent_end <= self.written
        &&& self.written == self.all_written@.len()
        &&& self.written <= VARINT_MAX
        &&& self.acked_base <= self.sent_end
        &&& !is_reset(self.state) ==> self.buf@ == self.all_written@.subrange(
            self.acked_base as int,
            self.written as int,
        )
        &&& is_reset(self.state) ==> self.buf@.len() == 0 && !self.fin_lost && !self.fin_acked
        &&& self.state is Ready ==> self.sent_end == 0
        &&& (self.state is DataSent || self.state is DataRecvd) ==> self.fin_written
            && self.sent_end == self.written
        &&& self.fin_lost ==> self.state is DataSent && !self.fin_acked
        &&& self.fin_acked ==> self.state is DataSent || self.state is DataRecvd
        &&& self.state is DataRecvd ==> self.acked_base == self.written && self.fin_acked
        &&& (self.reset is Some <==> is_reset(self.state))
        &&& self.reset matches Some(r) ==> r.0 <= VARINT_MAX && r.1 == self.sent_end
        &&& self.reset_pending ==> self.state is ResetSent
    }

    pub closed spec fn wf(&self) -> bool {
        &&& self.core()
        &&& self.sets_ok()
        &&& self.flush_to <= self.written
        &&& self.state is DataSent ==> !(self.acked_base == self.written && self.fin_acked)
        // Memory: the buffer holds exactly the bytes past the acknowledged prefix (none once reset).
        &&& !is_reset(self.state) ==> self.buf@.len() == self.written - self.acked_base
    }

    /// The invariant, in terms of the accessors.
    pub proof fn lemma_wf(&self)
        requires
            self.wf(),
        ensures
            self.sent_end() <= self.max(),
            self.sent_end() <= self.all_written().len() <= VARINT_MAX,
            self.acked_base_spec() <= self.sent_end(),
            self.buffered_spec() == if is_reset(self.state()) {
                0
            } else {
                self.all_written().len() - self.acked_base_spec()
            },
            self.state() is Ready ==> self.sent_end() == 0,
            (self.state() is DataSent || self.state() is DataRecvd) ==> self.fin_written_spec()
                && self.sent_end() == self.all_written().len(),
            self.state() is DataSent ==> !(self.acked_base_spec() == self.all_written().len()
                && self.fin_acked_spec()),
            self.state() is DataRecvd ==> self.acked_base_spec() == self.all_written().len()
                && self.fin_acked_spec(),
            self.reset_spec() is Some <==> is_reset(self.state()),
            self.reset_spec() matches Some(r) ==> r.0 <= VARINT_MAX && r.1 == self.sent_end(),
            self.pending_reset() is Some ==> self.state() is ResetSent && self.pending_reset()
                == self.reset_spec(),
            self.next_off() matches Some(o) ==> o <= self.all_written().len(),
            self.acked_base_spec() <= self.acked_point_spec() <= self.all_written().len(),
            self.buffered_spec() <= 2 * (self.all_written().len() - self.acked_point_spec()),
            self.acked_point_spec() == self.all_written().len() <==> self.acked_base_spec()
                == self.all_written().len(),
            // D10 (d)/(f): at most `W / FLOOR + MAX_FLUSH` nodes, `W` the bytes buffered.
            self.ranges_held() <= self.buffered_spec() / (FLOOR as nat) + MAX_FLUSH,
            self.flush_point() <= self.all_written().len(),
    {
        self.credit.lemma_wf();
        if !is_reset(self.state) {
            lemma_parts_end(self.acked@, self.lost@, self.flight@, self.open_slots(), self.acked_base, self.sent_end);
            if self.lost@.len() > 0 {
                assert(self.lost@[0].0 < self.sent_end);
            }
            vstd::arithmetic::div_mod::lemma_div_is_ordered(
                (self.sent_end - self.acked_base) as int,
                self.buf@.len() as int,
                FLOOR as int,
            );
        }
    }

    /// The queue's buffers are within the reservation, the second buffer of a migration included.
    pub proof fn lemma_held(&self)
        requires
            self.wf(),
        ensures
            self.buffered_spec() <= self.peak_spec(),
            self.capacity_spec() <= self.held_spec(),
            self.peak_spec() == 0 ==> self.buffered_spec() == 0,
    {
        self.buf.lemma_wf();
    }

    /// A write of at most `room_spec(b)` bytes leaves the reservation within `b`, its peak `max(peak, len + d)`; one of
    /// `room_spec(b) + 1` bytes would not.
    pub proof fn lemma_room(&self, b: nat, d: nat)
        requires
            self.wf(),
            self.held_spec() <= b,
        ensures
            d <= self.room_spec(b) ==> self.buffered_spec() + d <= b && res_of(
                vstd::math::max(self.peak_spec() as int, (self.buffered_spec() + d) as int) as nat,
            ) <= b,
            d == self.room_spec(b) + 1 ==> res_of(
                vstd::math::max(self.peak_spec() as int, (self.buffered_spec() + d) as int) as nat,
            ) > b,
            self.room_spec(b) <= b,
    {
        self.lemma_held();
    }

    pub fn held(&self) -> (r: u64)
        requires
            self.wf(),
        ensures
            r == self.held_spec(),
    {
        proof {
            self.buf.lemma_wf();
        }
        if self.peak == 0 {
            0
        } else if 6 * self.peak < 128 {
            128
        } else {
            6 * self.peak
        }
    }

    pub fn room(&self, b: u64) -> (r: u64)
        requires
            self.wf(),
        ensures
            r == self.room_spec(b as nat),
    {
        let len = self.buf.len() as u64;
        if b >= 128 && b / 6 >= len {
            b / 6 - len
        } else {
            0
        }
    }

    /// The send buffer's length: the bytes written past `acked_base`, none once reset.
    pub fn buffered(&self) -> (r: usize)
        requires
            self.wf(),
        ensures
            r == self.buffered_spec(),
    {
        self.buf.len()
    }

    pub proof fn lemma_buffered(&self)
        requires
            self.wf(),
        ensures
            self.buffered_spec() == if is_reset(self.state()) {
                0
            } else {
                (self.all_written().len() - self.acked_base_spec()) as nat
            },
    {
        self.lemma_wf();
    }

    pub fn new(max: u64) -> (r: SendStream)
        ensures
            r.wf(),
            r.state() is Ready,
            r.all_written() == Seq::<u8>::empty(),
            !r.fin_written_spec(),
            r.sent_end() == 0,
            r.max() == max,
            r.reset_spec() is None,
            r.buffered_spec() == 0,
            r.held_spec() == 0,
            r.peak_spec() == 0,
            r.flight_spec() == Set::<(u64, u64)>::empty(),
            r.flush_point() == 0,
    {
        let r = SendStream {
            state: SendState::Ready,
            buf: ByteQueue::new(),
            peak: 0,
            acked_base: 0,
            written: 0,
            sent_end: 0,
            fin_written: false,
            fin_acked: false,
            acked: RangeSet::new(),
            lost: RangeSet::new(),
            flight: PieceSet::new(),
            slots: [(0, 0), (0, 0), (0, 0), (0, 0)],
            nslots: 0,
            flush_to: 0,
            fin_lost: false,
            credit: SendCredit::new(max),
            reset: None,
            reset_pending: false,
            all_written: Ghost(Seq::empty()),
        };
        proof {
            assert(r.buf@ =~= r.all_written@.subrange(0, 0));
            reveal(parts);
            assert(r.open_slots() =~= Seq::<(u64, u64)>::empty());
            r.flight@.to_set_ensures();
            assert(r.flight_spec() =~= Set::<(u64, u64)>::empty());
        }
        r
    }

    pub fn state_exec(&self) -> (r: SendState)
        ensures
            r == self.state(),
    {
        self.state
    }

    #[verifier::when_used_as_spec(sent_end_spec)]
    pub fn sent_end(&self) -> (r: u64)
        ensures
            r == self.sent_end_spec(),
    {
        self.sent_end
    }

    /// The peer's stream data limit.
    #[verifier::when_used_as_spec(max_spec)]
    pub fn max(&self) -> (r: u64)
        ensures
            r == self.max_spec(),
    {
        self.credit.max()
    }

    pub fn is_terminal(&self) -> (r: bool)
        ensures
            r == (self.state() is DataRecvd || self.state() is ResetRecvd),
    {
        match self.state {
            SendState::DataRecvd | SendState::ResetRecvd => true,
            _ => false,
        }
    }

    /// Appends application data, with the FIN if `fin`.
    pub fn write(&mut self, data: &[u8], fin: bool) -> (r: Result<(), ()>)
        requires
            old(self).wf(),
            old(self).buffered_spec() + data@.len() <= byteq::queue::MAX_QUEUE,
        ensures
            final(self).wf(),
            send_step_ok(old(self).state(), final(self).state()),
            r is Err <==> (!(old(self).state() is Ready || old(self).state() is Send)
                || old(self).fin_written_spec() || old(self).all_written().len() + data@.len()
                > VARINT_MAX),
            r is Err ==> *final(self) == *old(self),
            r is Ok ==> final(self).buffered_spec() == old(self).buffered_spec() + data@.len(),
            r is Ok ==> final(self).peak_spec() == vstd::math::max(
                old(self).peak_spec() as int,
                (old(self).buffered_spec() + data@.len()) as int,
            ),
            r is Ok ==> final(self).held_spec() == res_of(
                vstd::math::max(old(self).peak_spec() as int, (old(self).buffered_spec() + data@.len()) as int) as nat,
            ),
            r is Ok ==> {
                &&& final(self).all_written() == old(self).all_written() + data@
                &&& final(self).fin_written_spec() == fin
                &&& final(self).state() == old(self).state()
                &&& final(self).sent_end() == old(self).sent_end()
                &&& final(self).max() == old(self).max()
                &&& final(self).reset_spec() == old(self).reset_spec()
            },
    {
        let open = match self.state {
            SendState::Ready | SendState::Send => true,
            _ => false,
        };
        if !open || self.fin_written || data.len() as u64 > VARINT_MAX - self.written {
            return Err(());
        }
        let ghost aw = self.all_written@;
        let len = self.buf.len() as u64;
        let Ghost(w) = self.buf.push_slice(data);
        assert(w <= 7 * data@.len() + 4);
        if len + data.len() as u64 > self.peak {
            self.peak = len + data.len() as u64;
        }
        self.written = self.written + data.len() as u64;
        self.all_written = Ghost(aw + data@);
        self.fin_written = fin;
        proof {
            assert(self.buf@ =~= self.all_written@.subrange(
                self.acked_base as int,
                self.written as int,
            ));
        }
        Ok(())
    }

    /// Sets the flush point at the bytes written: new bytes below it go out as a short piece (D10 (c)). O(1).
    pub fn flush(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).flush_point() == final(self).all_written().len(),
            final(self).state() == old(self).state(),
            final(self).all_written() == old(self).all_written(),
            final(self).fin_written_spec() == old(self).fin_written_spec(),
            final(self).acked_base_spec() == old(self).acked_base_spec(),
            final(self).fin_acked_spec() == old(self).fin_acked_spec(),
            final(self).reset_spec() == old(self).reset_spec(),
            final(self).buffered_spec() == old(self).buffered_spec(),
            final(self).peak_spec() == old(self).peak_spec(),
            final(self).held_spec() == old(self).held_spec(),
            final(self).capacity_spec() == old(self).capacity_spec(),
            forall|b: nat| #[trigger] final(self).room_spec(b) == old(self).room_spec(b),
            final(self).range_count() == old(self).range_count(),
            final(self).ranges_held() == old(self).ranges_held(),
            final(self).sent_end() == old(self).sent_end(),
            final(self).max() == old(self).max(),
            final(self).next_off() == old(self).next_off(),
            final(self).pending_reset() == old(self).pending_reset(),
            final(self).flight_spec() == old(self).flight_spec(),
    {
        self.flush_to = self.written;
    }

    /// The next chunk to send, at most `max_len` bytes, with `conn_avail` bytes of connection
    /// credit left: lost ranges first, then new data, then a lone FIN.
    pub fn poll_data(&mut self, max_len: u64, conn_avail: u64) -> (r: Option<Chunk>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            send_step_ok(old(self).state(), final(self).state()),
            final(self).all_written() == old(self).all_written(),
            final(self).fin_written_spec() == old(self).fin_written_spec(),
            final(self).max() == old(self).max(),
            final(self).reset_spec() == old(self).reset_spec(),
            final(self).pending_reset() == old(self).pending_reset(),
            no_data(old(self).state()) ==> r is None,
            r is None ==> *final(self) == *old(self),
            r matches Some(c) ==> chunk_ok(*old(self), *final(self), c@, max_len, conn_avail),
            final(self).buffered_spec() <= old(self).buffered_spec(),
            final(self).held_spec() <= old(self).held_spec(),
            r matches Some(c) && c@.off >= old(self).sent_end_spec() && c@.data.len() > 0
                ==> old(self).range_count() < MAX_SEND_RANGES,
            r matches Some(c) ==> (c@.data.len() > 0 ==> final(self).flight_spec() == old(self).flight_spec().insert(
                (c@.off, (c@.off + c@.data.len()) as u64),
            )),
            (r is None || r->0@.data.len() == 0) ==> final(self).flight_spec() == old(self).flight_spec(),
            final(self).flush_point() == old(self).flush_point(),
    {
        let (r, Ghost(c)) = self.poll_data_w(max_len, conn_avail);
        proof {
            assert(c <= c_ss1() * (old(self).ht() + 1) + c_ss2() * MAX_FLUSH + max_len);
        }
        r
    }

    /// `poll_data`, with its cost: one tree op per set touched and one unit per byte copied.
    fn poll_data_w(&mut self, max_len: u64, conn_avail: u64) -> (r: (Option<Chunk>, Ghost<nat>))
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            send_step_ok(old(self).state(), final(self).state()),
            final(self).all_written() == old(self).all_written(),
            final(self).fin_written_spec() == old(self).fin_written_spec(),
            final(self).max() == old(self).max(),
            final(self).reset_spec() == old(self).reset_spec(),
            final(self).pending_reset() == old(self).pending_reset(),
            no_data(old(self).state()) ==> r.0 is None,
            r.0 is None ==> *final(self) == *old(self),
            r.0 matches Some(c) ==> chunk_ok(*old(self), *final(self), c@, max_len, conn_avail),
            final(self).buffered_spec() <= old(self).buffered_spec(),
            final(self).held_spec() <= old(self).held_spec(),
            r.0 matches Some(c) && c@.off >= old(self).sent_end_spec() && c@.data.len() > 0
                ==> old(self).range_count() < MAX_SEND_RANGES,
            r.0 matches Some(c) ==> (c@.data.len() > 0 ==> final(self).flight_spec() == old(self).flight_spec().insert(
                (c@.off, (c@.off + c@.data.len()) as u64),
            )),
            (r.0 is None || r.0->0@.data.len() == 0) ==> final(self).flight_spec() == old(self).flight_spec(),
            final(self).flush_point() == old(self).flush_point(),
            r.1@ <= c_ss1() * (old(self).ht() + 1) + c_ss2() * MAX_FLUSH + max_len,
    {
        let ghost mut work: nat = 0;
        match self.state {
            //= https://www.rfc-editor.org/rfc/rfc9000#section-3.3
            //# A sender MUST NOT send any of these frames from a terminal state
            //# ("Data Recvd" or "Reset Recvd").
            //= https://www.rfc-editor.org/rfc/rfc9000#section-3.3
            //# A sender MUST NOT send a STREAM or
            //# STREAM_DATA_BLOCKED frame for a stream in the "Reset Sent" state or
            //# any terminal state -- that is, after sending a RESET_STREAM frame.
            SendState::DataRecvd | SendState::ResetSent | SendState::ResetRecvd => return (None, Ghost(work)),
            _ => {},
        }
        proof {
            assert(c_ss1() == 400 && c_ss2() == 10);
            self.acked.lemma_wf();
            self.lost.lemma_wf();
        }
        if self.lost.len() > 0 {
            let (r, Ghost(c)) = self.retransmit(max_len);
            proof {
                work = work + c;
            }
            (r, Ghost(work))
        } else {
            // The new-data gate (3d D4), a throttle only: a lone FIN still goes.
            let new_ok = self.acked.len() < MAX_SEND_RANGES as u64 && self.lost.len() < MAX_SEND_RANGES as u64
                - self.acked.len();
            let (r, Ghost(c)) = self.send_new(max_len, conn_avail, new_ok);
            proof {
                work = work + c;
            }
            (r, Ghost(work))
        }
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-2.2
    //# The data at a given offset MUST NOT change if it is sent
    //# multiple times
    //
    //= https://www.rfc-editor.org/rfc/rfc9000#section-13.3
    //# Application data sent in STREAM frames is retransmitted in new STREAM
    //# frames unless the endpoint has sent a RESET_STREAM for that stream.
    /// The start of the first lost range `[s, e)` again, from the buffer of written bytes: the whole range if it fits,
    /// else a cut leaving both parts at least `FLOOR` (D10 (c)), else nothing; never new data past it.
    fn retransmit(&mut self, max_len: u64) -> (r: (Option<Chunk>, Ghost<nat>))
        requires
            old(self).wf(),
            old(self).lost@.len() > 0,
            !no_data(old(self).state),
        ensures
            final(self).wf(),
            send_step_ok(old(self).state(), final(self).state()),
            final(self).all_written() == old(self).all_written(),
            final(self).fin_written_spec() == old(self).fin_written_spec(),
            final(self).max() == old(self).max(),
            final(self).reset_spec() == old(self).reset_spec(),
            final(self).pending_reset() == old(self).pending_reset(),
            r.0 is None ==> *final(self) == *old(self),
            r.0 matches Some(c) ==> chunk_ok(*old(self), *final(self), c@, max_len, 0),
            final(self).buffered_spec() == old(self).buffered_spec(),
            final(self).held_spec() == old(self).held_spec(),
            r.0 matches Some(c) ==> c@.off < old(self).sent_end_spec(),
            r.0 matches Some(c) ==> c@.data.len() > 0,
            r.0 matches Some(c) ==> final(self).flight_spec() == old(self).flight_spec().insert(
                (c@.off, (c@.off + c@.data.len()) as u64),
            ),
            final(self).flush_point() == old(self).flush_point(),
            ({
                let (s, e) = old(self).lost@[0];
                &&& r.0 is None ==> e - s > max_len && (e - s < 2 * FLOOR || max_len < FLOOR)
                &&& r.0 matches Some(c) ==> c@.data.len() == e - s || (c@.data.len() >= FLOOR && e - s
                    - c@.data.len() >= FLOOR)
            }),
            r.1@ <= c_ss1() * (old(self).ht() + 1) + max_len,
    {
        let ghost mut work: nat = 0;
        let ghost s0 = *self;
        proof {
            assert(c_rs() == 100 && c_ss1() == 400);
            assert(s0.flight.ht() <= s0.ht() && s0.lost.ht() <= s0.ht());
            self.lost.lemma_wf();
            self.flight.lemma_wf();
            self.acked.lemma_wf();
        }
        let (lf, Ghost(c0)) = self.lost.first();
        proof {
            work = work + c0;
        }
        let (s, e) = match lf {
            Some(p) => p,
            None => return (None, Ghost(work)),
        };
        let k = match resend_len(e - s, max_len) {
            Some(k) => k,
            None => return (None, Ghost(work)),
        };
        let end = s + k;
        let ghost aw = self.all_written@;
        let ghost ab = self.acked_base;
        proof {
            assert(s0.lost@[0] == (s, e));
            lemma_piece_space(s0.acked@, s0.lost@, s0.flight@, s0.open_slots(), ab, s0.sent_end, end);
        }
        let data = slice_to_vec(
            slice_subrange(
                self.buf.as_slice(),
                (s - self.acked_base) as usize,
                (end - self.acked_base) as usize,
            ),
        );
        proof {
            assert(data@ =~= aw.subrange(s as int, end as int));
            work = work + k as nat;
        }
        let Ghost(c1) = self.resend_piece(k);
        proof {
            work = work + c1;
        }
        let fin = end == self.written && self.fin_written;
        if fin {
            self.fin_lost = false;
            self.state = SendState::DataSent;
        }
        (Some(Chunk { off: s, data, fin, new_bytes: 0 }), Ghost(work))
    }

    /// `[s, s + k)` off the first lost range `[s, e)` goes in flight: `k` the whole range, or a cut leaving both parts
    /// at least `FLOOR` (split from `retransmit` for the rlimit).
    fn resend_piece(&mut self, k: u64) -> (r: Ghost<nat>)
        requires
            old(self).wf(),
            !is_reset(old(self).state),
            old(self).lost@.len() > 0,
            0 < k <= old(self).lost@[0].1 - old(self).lost@[0].0,
            k == old(self).lost@[0].1 - old(self).lost@[0].0 || (k >= FLOOR && old(self).lost@[0].1 - old(
                self,
            ).lost@[0].0 - k >= FLOOR),
        ensures
            *final(self) == (SendStream { lost: final(self).lost, flight: final(self).flight, ..*old(self) }),
            final(self).sets_ok(),
            final(self).flight_spec() == old(self).flight_spec().insert(
                (old(self).lost@[0].0, (old(self).lost@[0].0 + k) as u64),
            ),
            r@ <= c_rs() * (old(self).lost.ht() + 1) + c_rs() * (old(self).lost.ht() + 1) + c_rs() * (old(
                self,
            ).flight.ht() + 1),
    {
        let ghost mut work: nat = 0;
        let ghost s0 = *self;
        proof {
            self.lost.lemma_wf();
            self.flight.lemma_wf();
            self.acked.lemma_wf();
        }
        let (lf, Ghost(c0)) = self.lost.first();
        proof {
            work = work + c0;
        }
        let s = match lf {
            Some(p) => p.0,
            None => return Ghost(work),
        };
        proof {
            lemma_piece_space(s0.acked@, s0.lost@, s0.flight@, s0.open_slots(), s0.acked_base, s0.sent_end, (s
                + k) as u64);
        }
        let Ghost(c1) = self.lost.take_first(k);
        let Ghost(c2) = self.flight.insert_piece(s, s + k);
        proof {
            work = work + c1 + c2;
            lemma_resend(s0.acked@, s0.lost@, self.lost@, s0.flight@, self.flight@, s0.open_slots(), s0.acked_base, s0.sent_end, k);
            self.lost.lemma_wf();
            self.flight.lemma_wf();
            lemma_parts_bound(self.acked@, self.lost@, self.flight@, self.open_slots(), s0.acked_base, s0.sent_end);
            self.flight@.to_set_ensures();
            s0.flight@.to_set_ensures();
            assert(self.flight_spec() =~= s0.flight_spec().insert((s, (s + k) as u64)));
        }
        Ghost(work)
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-4.5
    //# An endpoint MUST NOT send data on a stream at or beyond the final
    //# size.
    /// New bytes from `sent_end`, within every limit and only if `new_ok`, coalesced (D10 (c)): `a` bytes sendable,
    /// a piece of `min(a, max_len)` if `a` and it are at least `FLOOR`; below `FLOOR` a short piece to a credit cut,
    /// the FIN's end or the flush point, if it fits and a slot is free; else a lone FIN that is owed.
    fn send_new(&mut self, max_len: u64, conn_avail: u64, new_ok: bool) -> (r: (Option<Chunk>, Ghost<nat>))
        requires
            old(self).wf(),
            old(self).lost@.len() == 0,
            !no_data(old(self).state),
        ensures
            final(self).wf(),
            send_step_ok(old(self).state(), final(self).state()),
            final(self).all_written() == old(self).all_written(),
            final(self).fin_written_spec() == old(self).fin_written_spec(),
            final(self).max() == old(self).max(),
            final(self).reset_spec() == old(self).reset_spec(),
            final(self).pending_reset() == old(self).pending_reset(),
            r.0 is None ==> *final(self) == *old(self),
            r.0 matches Some(c) ==> chunk_ok(*old(self), *final(self), c@, max_len, conn_avail),
            final(self).buffered_spec() == old(self).buffered_spec(),
            final(self).held_spec() == old(self).held_spec(),
            r.0 matches Some(c) && c@.data.len() > 0 ==> new_ok,
            r.0 matches Some(c) ==> (c@.data.len() > 0 ==> final(self).flight_spec() == old(self).flight_spec().insert(
                (c@.off, (c@.off + c@.data.len()) as u64),
            )),
            (r.0 is None || r.0->0@.data.len() == 0) ==> final(self).flight_spec() == old(self).flight_spec(),
            final(self).flush_point() == old(self).flush_point(),
            r.1@ <= c_ss1() * (old(self).ht() + 1) + c_ss2() * MAX_FLUSH + max_len,
    {
        let ghost mut work: nat = 0;
        let ghost s0 = *self;
        proof {
            assert(c_rs() == 100 && c_ss1() == 400 && c_ss2() == 10);
            assert(s0.flight.ht() <= s0.ht());
            self.credit.lemma_wf();
        }
        let off = self.sent_end;
        let (len, short) = self.new_len(max_len, conn_avail, new_ok);
        let end = off + len;
        let owed = self.fin_written && match self.state {
            SendState::DataSent => self.fin_lost,
            _ => true,
        };
        let fin = end == self.written && owed;
        if len == 0 && !fin {
            return (None, Ghost(work));
        }
        let ghost aw = self.all_written@;
        let ghost old_state = self.state;
        let data = slice_to_vec(
            slice_subrange(
                self.buf.as_slice(),
                (off - self.acked_base) as usize,
                (end - self.acked_base) as usize,
            ),
        );
        proof {
            assert(data@ =~= aw.subrange(off as int, end as int));
            work = work + len as nat;
        }
        if len > 0 {
            let Ghost(c1) = self.push_piece(end, short);
            proof {
                work = work + c1;
            }
        }
        if fin {
            self.fin_lost = false;
            self.state = SendState::DataSent;
        } else {
            self.state = SendState::Send;
        }
        proof {
            self.credit.lemma_wf();
            if old_state is Ready && fin {
                assert(send_edge(SendState::Ready, SendState::Send) && send_edge(
                    SendState::Send,
                    SendState::DataSent,
                ));
            }
        }
        (Some(Chunk { off, data, fin, new_bytes: len }), Ghost(work))
    }

    /// The new bytes `send_new` sends (D10 (c)): `a` sendable, a piece of `min(a, max_len)` if `a` and it are at
    /// least `FLOOR`; below `FLOOR` a short piece (`r.1`) to a credit cut, the FIN's end or the flush point, if it fits
    /// and a slot is free; else none.
    fn new_len(&self, max_len: u64, conn_avail: u64, new_ok: bool) -> (r: (u64, bool))
        requires
            self.wf(),
        ensures
            r.0 <= self.written - self.sent_end,
            r.0 <= self.credit.available_spec(),
            r.0 <= conn_avail,
            r.0 <= max_len,
            r.0 > 0 ==> new_ok,
            r.0 > 0 ==> r.0 >= FLOOR || (r.1 && self.nslots < MAX_FLUSH),
            r.1 ==> r.0 > 0,
    {
        proof {
            self.credit.lemma_wf();
        }
        let off = self.sent_end;
        let mut a = self.written - off;
        if !new_ok {
            a = 0;
        }
        let avail = self.credit.available();
        if a > avail {
            a = avail;
        }
        if a > conn_avail {
            a = conn_avail;
        }
        if a >= FLOOR {
            let len = if a < max_len {
                a
            } else {
                max_len
            };
            if len < FLOOR {
                (0, false)
            } else {
                (len, false)
            }
        } else if a > 0 {
            // A credit cut, the FIN's end or a flush point ends a short piece; flushed bytes never wait behind an
            // unflushed tail (review M1).
            let e = if a < self.written - off || (off + a == self.written && self.fin_written) || off + a
                <= self.flush_to {
                off + a
            } else if off < self.flush_to {
                self.flush_to
            } else {
                off
            };
            if e > off && e - off <= max_len && self.nslots < MAX_FLUSH {
                (e - off, true)
            } else {
                (0, false)
            }
        } else {
            (0, false)
        }
    }

    /// The new piece `[sent_end, end)` goes in flight, opening a slot if `short` (split from `send_new` for the
    /// rlimit).
    fn push_piece(&mut self, end: u64, short: bool) -> (r: Ghost<nat>)
        requires
            old(self).wf(),
            !no_data(old(self).state),
            old(self).sent_end < end <= old(self).written,
            end - old(self).sent_end <= old(self).credit.available_spec(),
            end - old(self).sent_end >= FLOOR || (short && old(self).nslots < MAX_FLUSH),
        ensures
            *final(self) == (SendStream {
                flight: final(self).flight,
                slots: final(self).slots,
                nslots: final(self).nslots,
                credit: final(self).credit,
                sent_end: end,
                ..*old(self)
            }),
            final(self).sets_ok(),
            final(self).credit.wf(),
            final(self).credit.used_spec() == end,
            final(self).credit.max_spec() == old(self).credit.max_spec(),
            final(self).flight_spec() == old(self).flight_spec().insert((old(self).sent_end, end)),
            r@ <= c_rs() * (old(self).flight.ht() + 1),
    {
        let ghost mut work: nat = 0;
        let ghost s0 = *self;
        let off = self.sent_end;
        proof {
            self.flight.lemma_wf();
            self.acked.lemma_wf();
            self.lost.lemma_wf();
            self.credit.lemma_wf();
            lemma_parts_end(s0.acked@, s0.lost@, s0.flight@, s0.open_slots(), s0.acked_base, off);
        }
        let Ghost(c1) = self.flight.insert_piece(off, end);
        proof {
            work = work + c1;
        }
        let ghost sp0 = s0.open_slots();
        if short && end - off < FLOOR {
            self.slots[self.nslots] = (off, end);
            self.nslots = self.nslots + 1;
        }
        self.credit.consume(end - off);
        self.sent_end = end;
        proof {
            let sp = self.open_slots();
            assert(sp =~= sp0.push((off, end)) || sp =~= sp0);
            assert(sp != sp0 ==> sp =~= sp0.push((off, end)));
            lemma_new_piece(s0.acked@, s0.lost@, s0.flight@, self.flight@, sp0, sp, s0.acked_base, off, end);
            self.flight.lemma_wf();
            lemma_parts_bound(self.acked@, self.lost@, self.flight@, sp, self.acked_base, end);
            self.flight@.to_set_ensures();
            s0.flight@.to_set_ensures();
            assert(self.flight_spec() =~= s0.flight_spec().insert((off, end)));
        }
        Ghost(work)
    }

    /// The offset `poll_data` would send at next, if it sends anything. `Some` does not mean
    /// `poll_data` will send: credit may be 0, or the room short of the floor. Loop on `poll_data`'s result, not on this.
    #[verifier::when_used_as_spec(next_off_spec)]
    pub fn next_off(&self) -> (r: Option<u64>)
        requires
            self.wf(),
        ensures
            r == self.next_off_spec(),
            r matches Some(o) ==> o <= self.all_written().len(),
    {
        match self.state {
            SendState::DataRecvd | SendState::ResetSent | SendState::ResetRecvd => return None,
            _ => {},
        }
        let (lf, Ghost(c)) = self.lost.first();
        proof {
            assert(c <= c_rs() * (self.lost.ht() + 1));
            if self.lost@.len() > 0 {
                lemma_parts_end(self.acked@, self.lost@, self.flight@, self.open_slots(), self.acked_base, self.sent_end);
                assert(self.lost@[0].0 < self.sent_end);
            }
        }
        if let Some((s, _)) = lf {
            return Some(s);
        }
        let owed = self.fin_written && match self.state {
            SendState::DataSent => self.fin_lost,
            _ => true,
        };
        if self.sent_end < self.written || owed {
            Some(self.sent_end)
        } else {
            None
        }
    }

    /// How many bytes `poll_data` would send next if nothing else limited it: the first lost
    /// range, else the written bytes not yet sent.
    pub fn want(&self) -> u64
        requires
            self.wf(),
    {
        let (lf, Ghost(c)) = self.lost.first();
        proof {
            assert(c <= c_rs() * (self.lost.ht() + 1));
            self.lost.lemma_wf();
        }
        match lf {
            Some((s, e)) => e - s,
            None => self.written - self.sent_end,
        }
    }

    /// Whether `write` of `n` bytes would succeed.
    pub fn writable(&self, n: usize) -> (r: bool)
        requires
            self.wf(),
        ensures
            r == ((self.state() is Ready || self.state() is Send) && !self.fin_written_spec()
                && self.all_written().len() + n <= VARINT_MAX),
    {
        let open = match self.state {
            SendState::Ready | SendState::Send => true,
            _ => false,
        };
        open && !self.fin_written && n as u64 <= VARINT_MAX - self.written
    }

    /// Abandons the stream with RESET_STREAM `code` (final size: the bytes sent). `fresh`:
    /// the stream was not already reset or fully acknowledged.
    pub fn reset(&mut self, code: u64) -> (fresh: bool)
        requires
            old(self).wf(),
            code <= VARINT_MAX,
        ensures
            final(self).wf(),
            final(self).buffered_spec() <= old(self).buffered_spec(),
            final(self).held_spec() <= old(self).held_spec(),
            send_step_ok(old(self).state(), final(self).state()),
            final(self).all_written() == old(self).all_written(),
            final(self).sent_end() == old(self).sent_end(),
            final(self).max() == old(self).max(),
            fresh == (old(self).state() is Ready || old(self).state() is Send
                || old(self).state() is DataSent),
            fresh ==> final(self).state() is ResetSent && final(self).reset_spec() == Some(
                (code, old(self).sent_end()),
            ) && final(self).pending_reset() == Some((code, old(self).sent_end()))
                && final(self).buffered_spec() == 0,
            fresh ==> final(self).flight_spec() == Set::<(u64, u64)>::empty(),
            !fresh ==> *final(self) == *old(self),
    {
        let (fresh, Ghost(c)) = self.reset_w(code);
        proof {
            assert(c <= crate::avl::c_free() * (2 * old(self).ranges_held() + 3));
        }
        fresh
    }

    /// `reset`, with its cost: the three trees freed node by node, O(nodes) until Task 10b moves them to a teardown
    /// slot in O(1) (review M3, an interim inside the phase).
    fn reset_w(&mut self, code: u64) -> (r: (bool, Ghost<nat>))
        requires
            old(self).wf(),
            code <= VARINT_MAX,
        ensures
            final(self).wf(),
            final(self).buffered_spec() <= old(self).buffered_spec(),
            final(self).held_spec() <= old(self).held_spec(),
            send_step_ok(old(self).state(), final(self).state()),
            final(self).all_written() == old(self).all_written(),
            final(self).sent_end() == old(self).sent_end(),
            final(self).max() == old(self).max(),
            r.0 == (old(self).state() is Ready || old(self).state() is Send
                || old(self).state() is DataSent),
            r.0 ==> final(self).state() is ResetSent && final(self).reset_spec() == Some(
                (code, old(self).sent_end()),
            ) && final(self).pending_reset() == Some((code, old(self).sent_end()))
                && final(self).buffered_spec() == 0,
            r.0 ==> final(self).flight_spec() == Set::<(u64, u64)>::empty(),
            !r.0 ==> *final(self) == *old(self),
            r.1@ <= crate::avl::c_free() * (2 * old(self).ranges_held() + 3),
    {
        let ghost mut work: nat = 0;
        match self.state {
            SendState::Ready | SendState::Send | SendState::DataSent => {},
            _ => return (false, Ghost(work)),
        }
        let Ghost(c1) = self.lost.clear();
        let Ghost(c2) = self.acked.clear();
        let Ghost(c3) = self.flight.clear();
        proof {
            work = work + c1 + c2 + c3;
        }
        self.state = SendState::ResetSent;
        self.reset = Some((code, self.sent_end));
        self.reset_pending = true;
        self.buf = ByteQueue::new();
        self.peak = 0;
        self.nslots = 0;
        self.fin_lost = false;
        self.fin_acked = false;
        proof {
            self.flight@.to_set_ensures();
            assert(self.flight_spec() =~= Set::<(u64, u64)>::empty());
        }
        (true, Ghost(work))
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-3.5
    //# An endpoint that receives a STOP_SENDING frame
    //# MUST send a RESET_STREAM frame if the stream is in the "Ready" or
    //# "Send" state.
    /// The peer's STOP_SENDING with `code`: reset at once, copying the code, in Ready, Send and
    /// Data Sent alike.
    pub fn on_stop_sending(&mut self, code: u64) -> (fresh: bool)
        requires
            old(self).wf(),
            code <= VARINT_MAX,
        ensures
            final(self).wf(),
            final(self).buffered_spec() <= old(self).buffered_spec(),
            final(self).held_spec() <= old(self).held_spec(),
            send_step_ok(old(self).state(), final(self).state()),
            final(self).all_written() == old(self).all_written(),
            final(self).sent_end() == old(self).sent_end(),
            final(self).max() == old(self).max(),
            fresh == (old(self).state() is Ready || old(self).state() is Send
                || old(self).state() is DataSent),
            fresh ==> final(self).state() is ResetSent && final(self).reset_spec() == Some(
                (code, old(self).sent_end()),
            ) && final(self).pending_reset() == Some((code, old(self).sent_end()))
                && final(self).buffered_spec() == 0,
            !fresh ==> *final(self) == *old(self),
    {
        self.reset(code)
    }

    /// The peer's MAX_STREAM_DATA.
    pub fn on_max_stream_data(&mut self, max: u64)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).buffered_spec() <= old(self).buffered_spec(),
            final(self).held_spec() <= old(self).held_spec(),
            final(self).state() == old(self).state(),
            final(self).all_written() == old(self).all_written(),
            final(self).fin_written_spec() == old(self).fin_written_spec(),
            final(self).sent_end() == old(self).sent_end(),
            final(self).next_off() == old(self).next_off(),
            final(self).reset_spec() == old(self).reset_spec(),
            final(self).pending_reset() == old(self).pending_reset(),
            final(self).max() == if max > old(self).max() {
                max
            } else {
                old(self).max()
            },
    {
        self.credit.on_max(max);
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-3.3
    //# A sender MUST NOT send any of these frames from a terminal state
    //# ("Data Recvd" or "Reset Recvd").
    /// The RESET_STREAM `(code, final size)` to send, if any: only in Reset Sent.
    #[verifier::when_used_as_spec(pending_reset_spec)]
    pub fn pending_reset(&self) -> (r: Option<(u64, u64)>)
        ensures
            r == self.pending_reset_spec(),
    {
        match self.state {
            SendState::ResetSent => if self.reset_pending {
                self.reset
            } else {
                None
            },
            _ => None,
        }
    }

    /// The pending RESET_STREAM was sent.
    pub fn commit_reset(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).buffered_spec() <= old(self).buffered_spec(),
            final(self).held_spec() <= old(self).held_spec(),
            final(self).state() == old(self).state(),
            final(self).all_written() == old(self).all_written(),
            final(self).sent_end() == old(self).sent_end(),
            final(self).max() == old(self).max(),
            final(self).next_off() == old(self).next_off(),
            final(self).reset_spec() == old(self).reset_spec(),
            final(self).pending_reset() is None,
    {
        self.reset_pending = false;
    }

    /// The frame carrying our RESET_STREAM was lost: send it again, unchanged (§13.3).
    pub fn on_reset_lost(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).buffered_spec() <= old(self).buffered_spec(),
            final(self).held_spec() <= old(self).held_spec(),
            final(self).state() == old(self).state(),
            final(self).all_written() == old(self).all_written(),
            final(self).sent_end() == old(self).sent_end(),
            final(self).max() == old(self).max(),
            final(self).next_off() == old(self).next_off(),
            final(self).reset_spec() == old(self).reset_spec(),
            final(self).pending_reset() == if old(self).state() is ResetSent {
                old(self).reset_spec()
            } else {
                old(self).pending_reset()
            },
    {
        if let SendState::ResetSent = self.state {
            self.reset_pending = true;
        }
    }

    /// The RESET_STREAM was acknowledged.
    pub fn on_reset_acked(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).buffered_spec() <= old(self).buffered_spec(),
            final(self).held_spec() <= old(self).held_spec(),
            send_step_ok(old(self).state(), final(self).state()),
            final(self).state() == if old(self).state() is ResetSent {
                SendState::ResetRecvd
            } else {
                old(self).state()
            },
            final(self).all_written() == old(self).all_written(),
            final(self).sent_end() == old(self).sent_end(),
            final(self).max() == old(self).max(),
            final(self).reset_spec() == old(self).reset_spec(),
            final(self).pending_reset() is None
                || final(self).pending_reset() == old(self).pending_reset(),
    {
        if let SendState::ResetSent = self.state {
            self.state = SendState::ResetRecvd;
            self.reset_pending = false;
        }
    }

    /// Closes the open slots ending at or below `b` (D10 (c)): at most `MAX_FLUSH`, the rest shifted down.
    fn close_slots(&mut self, b: u64) -> (r: (usize, Ghost<nat>))
        requires
            old(self).nslots <= MAX_FLUSH,
            disjoint(old(self).open_slots()),
        ensures
            *final(self) == (SendStream { slots: final(self).slots, nslots: final(self).nslots, ..*old(self) }),
            r.0 <= old(self).nslots,
            final(self).nslots == old(self).nslots - r.0,
            final(self).open_slots() == old(self).open_slots().skip(r.0 as int),
            forall|k: int| 0 <= k < r.0 ==> #[trigger] old(self).open_slots()[k].1 <= b,
            forall|k: int| r.0 <= k < old(self).nslots ==> #[trigger] old(self).open_slots()[k].1 > b,
            r.1@ <= 2 * MAX_FLUSH + 1,
    {
        let ghost mut work: nat = 1;
        let ghost sp = self.open_slots();
        let ghost s0 = self.slots@;
        let n = self.nslots;
        let mut c: usize = 0;
        while c < n && self.slots[c].1 <= b
            invariant
                c <= n,
                n == self.nslots,
                n <= MAX_FLUSH,
                self.slots@ == s0,
                sp == s0.subrange(0, n as int),
                forall|k: int| 0 <= k < c ==> #[trigger] sp[k].1 <= b,
                work == 1 + c,
            decreases n - c,
        {
            c = c + 1;
            proof {
                work = work + 1;
            }
        }
        proof {
            if c < n {
                assert(sp[c as int].1 > b);
                assert forall|k: int| c <= k < n implies #[trigger] sp[k].1 > b by {
                    if k > c {
                        assert(sp[c as int].1 <= sp[k].0);
                        assert(sp[k].0 < sp[k].1);
                    }
                }
            }
        }
        let mut i: usize = 0;
        while i + c < n
            invariant
                i + c <= n,
                n <= MAX_FLUSH,
                self.slots@.len() == 4,
                forall|k: int| 0 <= k < i ==> #[trigger] self.slots@[k] == s0[k + c],
                forall|k: int| i <= k < 4 ==> #[trigger] self.slots@[k] == s0[k],
                work <= 1 + c + i,
            decreases n - c - i,
        {
            let v = self.slots[i + c];
            self.slots[i] = v;
            i = i + 1;
            proof {
                work = work + 1;
            }
        }
        self.nslots = n - c;
        proof {
            assert(self.open_slots() =~= sp.skip(c as int));
        }
        (c, Ghost(work))
    }

    /// Drops the acknowledged prefix `[acked_base, b)`, the first acked range, from the set and the queue at once (no
    /// byte copied), and closes the slots it passes.
    fn drop_prefix(&mut self, b: u64) -> (r: Ghost<nat>)
        requires
            old(self).core(),
            !is_reset(old(self).state),
            old(self).acked.wf(),
            old(self).lost.wf(),
            old(self).flight.wf(),
            old(self).nslots <= MAX_FLUSH,
            old(self).flush_to <= old(self).written,
            !is_reset(old(self).state) ==> old(self).buf@.len() == old(self).written - old(self).acked_base,
            parts(
                old(self).acked@,
                old(self).lost@,
                old(self).flight@,
                old(self).open_slots(),
                old(self).acked_base,
                old(self).sent_end,
            ),
            old(self).acked@.contains((old(self).acked_base, b)),
            forall|p: (u64, u64)|
                #[trigger] old(self).acked@.contains(p) && p != (old(self).acked_base, b) ==> p.0 > old(
                    self,
                ).acked_base,
        ensures
            final(self).core(),
            final(self).sets_ok(),
            final(self).flush_to <= final(self).written,
            final(self).buf@.len() == final(self).written - final(self).acked_base,
            *final(self) == (SendStream {
                buf: final(self).buf,
                peak: final(self).peak,
                acked: final(self).acked,
                acked_base: final(self).acked_base,
                slots: final(self).slots,
                nslots: final(self).nslots,
                ..*old(self)
            }),
            final(self).acked_base == b,
            final(self).acked_base > old(self).acked_base,
            final(self).buf@.len() <= old(self).buf@.len(),
            final(self).peak <= old(self).peak,
            final(self).acked.ht() <= old(self).acked.ht() + 1,
            r@ <= c_rs() * (old(self).acked.ht() + 1) + 2 * MAX_FLUSH + 3,
    {
        let ghost mut work: nat = 0;
        let ghost s0 = *self;
        let ab = self.acked_base;
        proof {
            lemma_parts_end(s0.acked@, s0.lost@, s0.flight@, s0.open_slots(), ab, s0.sent_end);
            s0.acked.lemma_wf();
            let j = choose|j: int| 0 <= j < s0.acked@.len() && s0.acked@[j] == (ab, b);
            assert(ab < b <= s0.sent_end);
            self.buf.lemma_wf();
        }
        let Ghost(c1) = self.acked.remove_range(ab, b);
        let ghost aw = self.all_written@;
        let Ghost(c2) = self.buf.drop_front((b - ab) as usize);
        proof {
            work = work + c1 + c2;
            self.buf.lemma_wf();
        }
        if self.buf.len() == 0 {
            self.peak = 0;
        }
        self.acked_base = b;
        let (_closed, Ghost(c3)) = self.close_slots(b);
        proof {
            work = work + c3;
            assert(self.buf@ =~= aw.subrange(b as int, self.written as int));
            self.acked.lemma_wf();
            self.lost.lemma_wf();
            self.flight.lemma_wf();
            lemma_drop(
                s0.acked@,
                self.acked@,
                s0.lost@,
                s0.flight@,
                s0.open_slots(),
                self.open_slots(),
                ab,
                b,
                s0.sent_end,
                _closed as int,
            );
            lemma_parts_bound(self.acked@, self.lost@, self.flight@, self.open_slots(), b, self.sent_end);
        }
        Ghost(work)
    }

    /// The piece `[off, off + len)`, and the FIN if `fin`, was acknowledged.
    pub fn on_data_acked(&mut self, off: u64, len: u64, fin: bool)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).buffered_spec() <= old(self).buffered_spec(),
            final(self).held_spec() <= old(self).held_spec(),
            send_step_ok(old(self).state(), final(self).state()),
            final(self).all_written() == old(self).all_written(),
            final(self).fin_written_spec() == old(self).fin_written_spec(),
            final(self).sent_end() == old(self).sent_end(),
            final(self).max() == old(self).max(),
            final(self).reset_spec() == old(self).reset_spec(),
            final(self).pending_reset() == old(self).pending_reset(),
            final(self).acked_base_spec() >= old(self).acked_base_spec(),
            old(self).state() is DataSent ==> (final(self).state() is DataRecvd <==> (
                final(self).acked_base_spec() == final(self).all_written().len()
                && final(self).fin_acked_spec())),
            !(old(self).state() is DataSent) ==> final(self).state() == old(self).state(),
            (no_data(old(self).state()) || old(self).state() is Ready)
                ==> *final(self) == *old(self),
            final(self).flush_point() == old(self).flush_point(),
            len > 0 && (old(self).state() is Send || old(self).state() is DataSent) && old(self).in_flight(off, len)
                ==> final(self).flight_spec() == old(self).flight_spec().remove((off, (off + len) as u64)),
            len > 0 && !old(self).in_flight(off, len) ==> final(self).flight_spec() == old(self).flight_spec()
                && final(self).ranges_held() == old(self).ranges_held() && final(self).state() == old(self).state()
                && final(self).acked_base_spec() == old(self).acked_base_spec(),
            len == 0 ==> final(self).flight_spec() == old(self).flight_spec(),
    {
        let Ghost(c) = self.on_data_acked_w(off, len, fin);
        proof {
            assert(c <= c_ss1() * (old(self).ht() + 1) + c_ss2() * MAX_FLUSH);
        }
    }

    /// `on_data_acked`, with its cost: the piece found and removed, merged with at most two neighbours, the prefix
    /// dropped and at most `MAX_FLUSH` slots closed; independent of `len` and of the number of ranges (D10 (e)).
    fn on_data_acked_w(&mut self, off: u64, len: u64, fin: bool) -> (r: Ghost<nat>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).buffered_spec() <= old(self).buffered_spec(),
            final(self).held_spec() <= old(self).held_spec(),
            send_step_ok(old(self).state(), final(self).state()),
            final(self).all_written() == old(self).all_written(),
            final(self).fin_written_spec() == old(self).fin_written_spec(),
            final(self).sent_end() == old(self).sent_end(),
            final(self).max() == old(self).max(),
            final(self).reset_spec() == old(self).reset_spec(),
            final(self).pending_reset() == old(self).pending_reset(),
            final(self).acked_base_spec() >= old(self).acked_base_spec(),
            old(self).state() is DataSent ==> (final(self).state() is DataRecvd <==> (
                final(self).acked_base_spec() == final(self).all_written().len()
                && final(self).fin_acked_spec())),
            !(old(self).state() is DataSent) ==> final(self).state() == old(self).state(),
            (no_data(old(self).state()) || old(self).state() is Ready)
                ==> *final(self) == *old(self),
            final(self).flush_point() == old(self).flush_point(),
            len > 0 && (old(self).state() is Send || old(self).state() is DataSent) && old(self).in_flight(off, len)
                ==> final(self).flight_spec() == old(self).flight_spec().remove((off, (off + len) as u64)),
            len > 0 && !old(self).in_flight(off, len) ==> final(self).flight_spec() == old(self).flight_spec()
                && final(self).ranges_held() == old(self).ranges_held() && final(self).state() == old(self).state()
                && final(self).acked_base_spec() == old(self).acked_base_spec(),
            len == 0 ==> final(self).flight_spec() == old(self).flight_spec(),
            r@ <= c_ss1() * (old(self).ht() + 1) + c_ss2() * MAX_FLUSH,
    {
        let ghost mut work: nat = 0;
        match self.state {
            SendState::Send | SendState::DataSent => {},
            _ => return Ghost(work),
        }
        if len > 0 {
            // A piece ends at most at VARINT_MAX: a larger end is no piece.
            if off > VARINT_MAX || len > VARINT_MAX - off {
                return Ghost(work);
            }
            let (hit, Ghost(c)) = self.ack_piece(off, off + len);
            proof {
                work = work + c;
            }
            if !hit {
                return Ghost(work);
            }
        }
        if fin {
            if let SendState::DataSent = self.state {
                self.fin_acked = true;
                self.fin_lost = false;
            }
        }
        if let SendState::DataSent = self.state {
            if self.acked_base == self.written && self.fin_acked {
                self.state = SendState::DataRecvd;
            }
        }
        Ghost(work)
    }

    /// The piece `[off, end)`, if it is one in flight, leaves flight and joins `acked`; a merged range that starts at
    /// `acked_base` is dropped at once (split from `on_data_acked_w` for the rlimit).
    fn ack_piece(&mut self, off: u64, end: u64) -> (r: (bool, Ghost<nat>))
        requires
            old(self).wf(),
            old(self).state is Send || old(self).state is DataSent,
            off < end <= VARINT_MAX,
        ensures
            final(self).core(),
            final(self).sets_ok(),
            final(self).flush_to <= final(self).written,
            final(self).buf@.len() == final(self).written - final(self).acked_base,
            *final(self) == (SendStream {
                buf: final(self).buf,
                peak: final(self).peak,
                acked: final(self).acked,
                flight: final(self).flight,
                acked_base: final(self).acked_base,
                slots: final(self).slots,
                nslots: final(self).nslots,
                ..*old(self)
            }),
            final(self).acked_base >= old(self).acked_base,
            final(self).buf@.len() <= old(self).buf@.len(),
            final(self).peak <= old(self).peak,
            old(self).flight@.contains((off, end)) ==> final(self).flight_spec() == old(self).flight_spec().remove(
                (off, end),
            ),
            !old(self).flight@.contains((off, end)) ==> final(self).flight_spec() == old(self).flight_spec()
                && final(self).ranges_held() == old(self).ranges_held() && final(self).acked_base
                == old(self).acked_base,
            r.0 == old(self).flight@.contains((off, end)),
            r.1@ <= c_ss1() * (old(self).ht() + 1) + c_ss2() * MAX_FLUSH,
    {
        let ghost mut work: nat = 0;
        let ghost s0 = *self;
        proof {
            assert(c_rs() == 100 && c_ss1() == 400 && c_ss2() == 10 && crate::avl::c_free() == 1);
            assert(s0.flight.ht() <= s0.ht() && s0.acked.ht() <= s0.ht() && s0.lost.ht() <= s0.ht());
            self.flight.lemma_wf();
            self.acked.lemma_wf();
            self.lost.lemma_wf();
        }
        let (hit, Ghost(c1)) = self.flight.take_piece(off, end);
        proof {
            work = work + c1;
        }
        if !hit {
            proof {
                self.flight@.to_set_ensures();
                s0.flight@.to_set_ensures();
                assert(self.flight_spec() =~= s0.flight_spec());
            }
            return (false, Ghost(work));
        }
        proof {
            lemma_piece_free(s0.acked@, s0.lost@, s0.flight@, s0.open_slots(), s0.acked_base, s0.sent_end, off, end);
        }
        let ((am, bm), Ghost(c2)) = self.acked.add(off, end);
        proof {
            work = work + c2;
            lemma_ack(
                s0.acked@,
                self.acked@,
                s0.lost@,
                s0.flight@,
                self.flight@,
                s0.open_slots(),
                s0.acked_base,
                s0.sent_end,
                off,
                end,
                am,
                bm,
            );
            self.flight@.to_set_ensures();
            s0.flight@.to_set_ensures();
            assert(self.flight_spec() =~= s0.flight_spec().remove((off, end)));
        }
        if am == self.acked_base {
            let Ghost(c3) = self.drop_prefix(bm);
            proof {
                work = work + c3;
            }
        } else {
            proof {
                self.acked.lemma_wf();
                self.flight.lemma_wf();
                lemma_parts_bound(self.acked@, self.lost@, self.flight@, self.open_slots(), self.acked_base, self.sent_end);
            }
        }
        (true, Ghost(work))
    }

    /// The piece `[off, off + len)`, and the FIN if `fin`, was lost: queue it again.
    pub fn on_data_lost(&mut self, off: u64, len: u64, fin: bool)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).buffered_spec() <= old(self).buffered_spec(),
            final(self).held_spec() <= old(self).held_spec(),
            final(self).state() == old(self).state(),
            final(self).all_written() == old(self).all_written(),
            final(self).fin_written_spec() == old(self).fin_written_spec(),
            final(self).sent_end() == old(self).sent_end(),
            final(self).max() == old(self).max(),
            final(self).reset_spec() == old(self).reset_spec(),
            final(self).pending_reset() == old(self).pending_reset(),
            final(self).acked_base_spec() == old(self).acked_base_spec(),
            (no_data(old(self).state()) || old(self).state() is Ready)
                ==> *final(self) == *old(self),
            final(self).flush_point() == old(self).flush_point(),
            len > 0 && (old(self).state() is Send || old(self).state() is DataSent) && old(self).in_flight(off, len)
                ==> final(self).flight_spec() == old(self).flight_spec().remove((off, (off + len) as u64)),
            len > 0 && !old(self).in_flight(off, len) ==> final(self).flight_spec() == old(self).flight_spec()
                && final(self).ranges_held() == old(self).ranges_held() && final(self).state() == old(self).state()
                && final(self).acked_base_spec() == old(self).acked_base_spec(),
            len == 0 ==> final(self).flight_spec() == old(self).flight_spec(),
    {
        let Ghost(c) = self.on_data_lost_w(off, len, fin);
        proof {
            assert(c <= c_ss1() * (old(self).ht() + 1) + c_ss2() * MAX_FLUSH);
        }
    }

    /// `on_data_lost`, with its cost: the piece found and removed, merged into `lost` with at most two neighbours.
    fn on_data_lost_w(&mut self, off: u64, len: u64, fin: bool) -> (r: Ghost<nat>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).buffered_spec() <= old(self).buffered_spec(),
            final(self).held_spec() <= old(self).held_spec(),
            final(self).state() == old(self).state(),
            final(self).all_written() == old(self).all_written(),
            final(self).fin_written_spec() == old(self).fin_written_spec(),
            final(self).sent_end() == old(self).sent_end(),
            final(self).max() == old(self).max(),
            final(self).reset_spec() == old(self).reset_spec(),
            final(self).pending_reset() == old(self).pending_reset(),
            final(self).acked_base_spec() == old(self).acked_base_spec(),
            (no_data(old(self).state()) || old(self).state() is Ready)
                ==> *final(self) == *old(self),
            final(self).flush_point() == old(self).flush_point(),
            len > 0 && (old(self).state() is Send || old(self).state() is DataSent) && old(self).in_flight(off, len)
                ==> final(self).flight_spec() == old(self).flight_spec().remove((off, (off + len) as u64)),
            len > 0 && !old(self).in_flight(off, len) ==> final(self).flight_spec() == old(self).flight_spec()
                && final(self).ranges_held() == old(self).ranges_held() && final(self).state() == old(self).state()
                && final(self).acked_base_spec() == old(self).acked_base_spec(),
            len == 0 ==> final(self).flight_spec() == old(self).flight_spec(),
            r@ <= c_ss1() * (old(self).ht() + 1) + c_ss2() * MAX_FLUSH,
    {
        let ghost mut work: nat = 0;
        match self.state {
            SendState::Send | SendState::DataSent => {},
            _ => return Ghost(work),
        }
        if len > 0 {
            let ghost s0 = *self;
            proof {
                assert(c_rs() == 100 && c_ss1() == 400 && c_ss2() == 10 && crate::avl::c_free() == 1);
                assert(s0.flight.ht() <= s0.ht() && s0.acked.ht() <= s0.ht() && s0.lost.ht() <= s0.ht());
                self.flight.lemma_wf();
                self.lost.lemma_wf();
                self.acked.lemma_wf();
            }
            if off > VARINT_MAX || len > VARINT_MAX - off {
                return Ghost(work);
            }
            let (hit, Ghost(c1)) = self.flight.take_piece(off, off + len);
            proof {
                work = work + c1;
            }
            if !hit {
                proof {
                    self.flight@.to_set_ensures();
                    s0.flight@.to_set_ensures();
                    assert(self.flight_spec() =~= s0.flight_spec());
                }
                return Ghost(work);
            }
            proof {
                lemma_piece_free(s0.acked@, s0.lost@, s0.flight@, s0.open_slots(), s0.acked_base, s0.sent_end, off, (
                off + len) as u64);
            }
            let ((_am, _bm), Ghost(c2)) = self.lost.add(off, off + len);
            proof {
                work = work + c2;
                lemma_lose(
                    s0.acked@,
                    s0.lost@,
                    self.lost@,
                    s0.flight@,
                    self.flight@,
                    s0.open_slots(),
                    s0.acked_base,
                    s0.sent_end,
                    off,
                    (off + len) as u64,
                    _am,
                    _bm,
                );
                self.lost.lemma_wf();
                self.flight.lemma_wf();
                lemma_parts_bound(self.acked@, self.lost@, self.flight@, self.open_slots(), self.acked_base, self.sent_end);
                self.flight@.to_set_ensures();
                s0.flight@.to_set_ensures();
                assert(self.flight_spec() =~= s0.flight_spec().remove((off, (off + len) as u64)));
            }
        }
        if fin && !self.fin_acked {
            if let SendState::DataSent = self.state {
                self.fin_lost = true;
            }
        }
        Ghost(work)
    }
}

} // verus!

impl SendStream {
    /// Test support: the send queue's allocated capacity, both buffers while it migrates.
    #[doc(hidden)]
    pub fn buf_capacity(&self) -> usize {
        let (a, b) = self.buf.caps();
        a + b
    }

    /// Test support: the acked and lost sets' and the in-flight set's lengths.
    #[doc(hidden)]
    pub fn range_counts(&self) -> (usize, usize, usize) {
        (self.acked.to_vec().len(), self.lost.to_vec().len(), self.flight.to_vec().len())
    }

    /// Test support: the acked and lost ranges and the pieces in flight.
    #[doc(hidden)]
    pub fn range_sets(&self) -> (Vec<(u64, u64)>, Vec<(u64, u64)>, Vec<(u64, u64)>) {
        (self.acked.to_vec(), self.lost.to_vec(), self.flight.to_vec())
    }
}
