//! Byte-range sets on `quic::avl` (9b2 D10): `RangeSet`, merged ranges (sorted, disjoint, non-adjacent), and
//! `PieceSet`, disjoint pieces never merged; both keyed by start with the end as value, every op O(log n) with its
//! cost in its ensures. With `lemma_bound`, the proved bound on `SendStream`'s acked, lost and in-flight sets: items of
//! at least `FLOOR` bytes, or holding a whole open slot, number at most `W / FLOOR + slots` (D10 (d)).
use vstd::prelude::*;
// Used only in ghost code, which a plain `cargo build` erases.
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;
use crate::avl::*;
#[allow(unused_imports)]
use wire::varint::VARINT_MAX;

verus! {

/// Items shorter than this hold a whole open slot (D10 (c)): a packet always has `2·FLOOR − 1` bytes of data room.
pub const FLOOR: u64 = 256;

/// Short new pieces open at once per stream (D10 (c)).
pub const MAX_FLUSH: usize = 4;

/// The cost constant of the range and piece ops.
pub open spec fn c_rs() -> nat {
    100
}

/// Byte `x` lies in range `p`.
pub open spec fn inr(p: (u64, u64), x: nat) -> bool {
    p.0 <= x && x < p.1
}

/// Byte `x` lies in some range of `v`.
pub open spec fn covers(v: Seq<(u64, u64)>, x: nat) -> bool {
    exists|i: int| 0 <= i < v.len() && #[trigger] inr(v[i], x)
}

/// Non-empty ranges in order, none overlapping.
pub open spec fn disjoint(v: Seq<(u64, u64)>) -> bool {
    &&& forall|i: int| 0 <= i < v.len() ==> #[trigger] v[i].0 < v[i].1
    &&& forall|i: int, j: int| 0 <= i < j < v.len() ==> #[trigger] v[i].1 <= #[trigger] v[j].0
}

/// `disjoint`, and no two ranges adjacent.
pub open spec fn merged(v: Seq<(u64, u64)>) -> bool {
    &&& forall|i: int| 0 <= i < v.len() ==> #[trigger] v[i].0 < v[i].1
    &&& forall|i: int, j: int| 0 <= i < j < v.len() ==> #[trigger] v[i].1 < #[trigger] v[j].0
}

/// Every end at most `VARINT_MAX`: a set holds fewer than `2^62` ranges, as `avl::split` and `avl::join` need.
pub open spec fn capped(v: Seq<(u64, u64)>) -> bool {
    forall|i: int| 0 <= i < v.len() ==> #[trigger] v[i].1 <= VARINT_MAX
}

/// Every range is non-empty and inside `[lo, hi)`.
pub open spec fn in_bounds(v: Seq<(u64, u64)>, lo: u64, hi: u64) -> bool {
    forall|i: int| #![trigger v[i]] 0 <= i < v.len() ==> lo <= v[i].0 < v[i].1 <= hi
}

/// No byte lies in both.
pub open spec fn apart(a: Seq<(u64, u64)>, b: Seq<(u64, u64)>) -> bool {
    forall|x: nat| #![trigger covers(a, x), covers(b, x)] !(covers(a, x) && covers(b, x))
}

/// An item of at least `FLOOR` bytes, or one holding a whole slot of `sp`.
pub open spec fn item_ok(it: (u64, u64), sp: Seq<(u64, u64)>) -> bool {
    it.1 - it.0 >= FLOOR || exists|j: int| 0 <= j < sp.len() && it.0 <= #[trigger] sp[j].0 && sp[j].1 <= it.1
}

pub open spec fn items_ok(v: Seq<(u64, u64)>, sp: Seq<(u64, u64)>) -> bool {
    forall|i: int| 0 <= i < v.len() ==> #[trigger] item_ok(v[i], sp)
}

/// How many of the slots `sp` end at or below `s`: a prefix, the slots ascending.
pub open spec fn cut(sp: Seq<(u64, u64)>, s: u64) -> nat
    decreases sp.len(),
{
    if sp.len() == 0 {
        0
    } else if sp.last().1 <= s {
        sp.len()
    } else {
        cut(sp.drop_last(), s)
    }
}

proof fn lemma_cut(sp: Seq<(u64, u64)>, s: u64)
    requires
        disjoint(sp),
    ensures
        cut(sp, s) <= sp.len(),
        forall|k: int| 0 <= k < cut(sp, s) ==> #[trigger] sp[k].1 <= s,
        forall|k: int| cut(sp, s) <= k < sp.len() ==> #[trigger] sp[k].1 > s,
    decreases sp.len(),
{
    if sp.len() > 0 {
        if sp.last().1 <= s {
            assert forall|k: int| 0 <= k < sp.len() implies #[trigger] sp[k].1 <= s by {
                if k < sp.len() - 1 {
                    assert(sp[k].1 <= sp[sp.len() - 1].0);
                }
            }
        } else {
            let d = sp.drop_last();
            assert(disjoint(d));
            lemma_cut(d, s);
            assert forall|k: int| 0 <= k < cut(sp, s) implies #[trigger] sp[k].1 <= s by {
                assert(sp[k] == d[k]);
            }
            assert forall|k: int| cut(sp, s) <= k < sp.len() implies #[trigger] sp[k].1 > s by {
                if k < sp.len() - 1 {
                    assert(sp[k] == d[k]);
                }
            }
        }
    }
}

proof fn lemma_div_step(x: nat, y: nat)
    requires
        x + 256 <= y,
    ensures
        x / 256 + 1 <= y / 256,
{
    assert(x / 256 + 1 <= y / 256) by (nonlinear_arith)
        requires
            x + 256 <= y,
    ;
}

proof fn lemma_div_mono(x: nat, y: nat)
    requires
        x <= y,
    ensures
        x / 256 <= y / 256,
{
    vstd::arithmetic::div_mod::lemma_div_is_ordered(x as int, y as int, 256);
}

/// No range of `v` meets `w[k]` = `[s, e)`, `v`'s last ending at or below `e`: every range of `v` ends at or below `s`.
proof fn lemma_below(v: Seq<(u64, u64)>, w: Seq<(u64, u64)>, k: int)
    requires
        disjoint(v),
        apart(v, w),
        0 <= k < w.len(),
        w[k].0 < w[k].1,
        v.len() > 0 ==> v.last().1 <= w[k].1,
    ensures
        forall|i: int| 0 <= i < v.len() ==> #[trigger] v[i].1 <= w[k].0,
{
    let (s, e) = w[k];
    assert forall|i: int| 0 <= i < v.len() implies #[trigger] v[i].1 <= s by {
        if v[i].1 > s {
            if i < v.len() - 1 {
                assert(v[i].1 <= v[v.len() - 1].0);
            }
            let x: nat = if v[i].0 > s { v[i].0 as nat } else { s as nat };
            assert(inr(v[i], x));
            assert(inr(w[k], x));
            assert(covers(v, x) && covers(w, x));
        }
    }
}

proof fn lemma_covers_drop(v: Seq<(u64, u64)>, x: nat)
    requires
        v.len() > 0,
        covers(v.drop_last(), x),
    ensures
        covers(v, x),
{
    let i = choose|i: int| 0 <= i < v.drop_last().len() && #[trigger] inr(v.drop_last()[i], x);
    assert(v.drop_last()[i] == v[i]);
    assert(inr(v[i], x));
}

/// `lemma_bound`'s step: peel `a`'s last item, whose end is the largest of all. The rest lie below its start `s`,
/// with the slots ending at or below `s`; a long item gives `FLOOR` of the window back, a short one a slot (its own
/// slot ends past `s`).
proof fn lemma_peel(
    a: Seq<(u64, u64)>,
    l: Seq<(u64, u64)>,
    f: Seq<(u64, u64)>,
    sp: Seq<(u64, u64)>,
    lo: u64,
    hi: u64,
)
    requires
        disjoint(a),
        disjoint(l),
        disjoint(f),
        disjoint(sp),
        in_bounds(a, lo, hi),
        in_bounds(l, lo, hi),
        in_bounds(f, lo, hi),
        apart(a, l),
        apart(a, f),
        apart(l, f),
        items_ok(a, sp),
        items_ok(l, sp),
        items_ok(f, sp),
        a.len() > 0,
        l.len() > 0 ==> l.last().1 <= a.last().1,
        f.len() > 0 ==> f.last().1 <= a.last().1,
    ensures
        a.len() + l.len() + f.len() <= ((hi - lo) as nat) / (FLOOR as nat) + sp.len(),
    decreases a.len() + l.len() + f.len(), 0nat,
{
    let n = a.len() - 1;
    let (s, e) = a[n];
    let a2 = a.drop_last();
    lemma_below(l, a, n);
    lemma_below(f, a, n);
    assert forall|x: nat| #![trigger covers(a2, x), covers(l, x)] !(covers(a2, x) && covers(l, x)) by {
        if covers(a2, x) {
            lemma_covers_drop(a, x);
        }
    }
    assert forall|x: nat| #![trigger covers(a2, x), covers(f, x)] !(covers(a2, x) && covers(f, x)) by {
        if covers(a2, x) {
            lemma_covers_drop(a, x);
        }
    }
    lemma_cut(sp, s);
    let j = cut(sp, s);
    let sp2 = sp.take(j as int);
    assert forall|i: int| 0 <= i < a2.len() implies #[trigger] item_ok(a2[i], sp2) by {
        assert(a2[i] == a[i]);
        assert(a[i].1 <= a[n].0);
        assert(item_ok(a[i], sp));
        if !(a[i].1 - a[i].0 >= FLOOR) {
            let k = choose|k: int| 0 <= k < sp.len() && a[i].0 <= #[trigger] sp[k].0 && sp[k].1 <= a[i].1;
            assert(sp2[k] == sp[k]);
        }
    }
    assert forall|i: int| 0 <= i < l.len() implies #[trigger] item_ok(l[i], sp2) by {
        assert(item_ok(l[i], sp));
        if !(l[i].1 - l[i].0 >= FLOOR) {
            let k = choose|k: int| 0 <= k < sp.len() && l[i].0 <= #[trigger] sp[k].0 && sp[k].1 <= l[i].1;
            assert(sp2[k] == sp[k]);
        }
    }
    assert forall|i: int| 0 <= i < f.len() implies #[trigger] item_ok(f[i], sp2) by {
        assert(item_ok(f[i], sp));
        if !(f[i].1 - f[i].0 >= FLOOR) {
            let k = choose|k: int| 0 <= k < sp.len() && f[i].0 <= #[trigger] sp[k].0 && sp[k].1 <= f[i].1;
            assert(sp2[k] == sp[k]);
        }
    }
    assert(in_bounds(a2, lo, s)) by {
        assert forall|i: int| 0 <= i < a2.len() implies lo <= #[trigger] a2[i].0 < a2[i].1 <= s by {
            assert(a2[i] == a[i]);
            assert(a[i].1 <= a[n].0);
        }
    }
    lemma_bound(a2, l, f, sp2, lo, s);
    assert(item_ok(a[n], sp));
    if e - s >= FLOOR {
        lemma_div_step((s - lo) as nat, (hi - lo) as nat);
    } else {
        let k = choose|k: int| 0 <= k < sp.len() && s <= #[trigger] sp[k].0 && sp[k].1 <= e;
        assert(sp[k].1 > s);
        lemma_div_mono((s - lo) as nat, (hi - lo) as nat);
    }
}

/// D10 (d): pairwise apart items in `[lo, hi)`, each at least `FLOOR` long or holding a whole slot of `sp` (ascending
/// slots): at most `(hi − lo) / FLOOR` long ones, and a short one's slot is no other item's.
pub proof fn lemma_bound(
    a: Seq<(u64, u64)>,
    l: Seq<(u64, u64)>,
    f: Seq<(u64, u64)>,
    sp: Seq<(u64, u64)>,
    lo: u64,
    hi: u64,
)
    requires
        disjoint(a),
        disjoint(l),
        disjoint(f),
        disjoint(sp),
        in_bounds(a, lo, hi),
        in_bounds(l, lo, hi),
        in_bounds(f, lo, hi),
        apart(a, l),
        apart(a, f),
        apart(l, f),
        items_ok(a, sp),
        items_ok(l, sp),
        items_ok(f, sp),
    ensures
        a.len() + l.len() + f.len() <= ((hi - lo) as nat) / (FLOOR as nat) + sp.len(),
    decreases a.len() + l.len() + f.len(), 1nat,
{
    let ea: int = if a.len() > 0 { a.last().1 as int } else { -1 };
    let el: int = if l.len() > 0 { l.last().1 as int } else { -1 };
    let ef: int = if f.len() > 0 { f.last().1 as int } else { -1 };
    if a.len() + l.len() + f.len() == 0 {
    } else if ea >= el && ea >= ef {
        lemma_peel(a, l, f, sp, lo, hi);
    } else if el >= ef {
        lemma_peel(l, a, f, sp, lo, hi);
    } else {
        lemma_peel(f, a, l, sp, lo, hi);
    }
}

// ---- Sequence facts the set ops use.

/// Range `i` of a disjoint `v` starts at or past `i`, so `v` holds at most its last end ranges.
pub proof fn lemma_count(v: Seq<(u64, u64)>)
    requires
        disjoint(v),
    ensures
        forall|i: int| 0 <= i < v.len() ==> #[trigger] v[i].0 >= i,
        capped(v) ==> v.len() <= VARINT_MAX,
    decreases v.len(),
{
    if v.len() > 0 {
        let d = v.drop_last();
        assert(disjoint(d));
        lemma_count(d);
        assert forall|i: int| 0 <= i < v.len() implies #[trigger] v[i].0 >= i by {
            if i < v.len() - 1 {
                assert(v[i] == d[i]);
            } else if i > 0 {
                assert(v[i - 1] == d[i - 1]);
                assert(v[i - 1].1 <= v[i].0);
            }
        }
        assert(v[v.len() - 1].0 >= v.len() - 1);
        assert(v[v.len() - 1].0 < v[v.len() - 1].1);
        if capped(v) {
            assert(v[v.len() - 1].1 <= VARINT_MAX);
        }
    }
}

/// A capped disjoint sequence is short enough for `avl::split`, `join` and `join2`, with one more entry.
proof fn lemma_small(v: Seq<(u64, u64)>)
    requires
        disjoint(v),
        capped(v),
    ensures
        v.len() + 2 < pow2(63),
        v.len() <= VARINT_MAX,
{
    lemma_count(v);
    lemma2_to64_rest();
}

pub proof fn lemma_covers_cat(a: Seq<(u64, u64)>, b: Seq<(u64, u64)>)
    ensures
        forall|y: nat| #[trigger] covers(a + b, y) <==> covers(a, y) || covers(b, y),
{
    assert forall|y: nat| #[trigger] covers(a + b, y) <==> covers(a, y) || covers(b, y) by {
        if covers(a + b, y) {
            let i = choose|i: int| 0 <= i < (a + b).len() && #[trigger] inr((a + b)[i], y);
            if i < a.len() {
                assert(inr(a[i], y));
            } else {
                assert(inr(b[i - a.len()], y));
            }
        }
        if covers(a, y) {
            let i = choose|i: int| 0 <= i < a.len() && #[trigger] inr(a[i], y);
            assert(inr((a + b)[i], y));
        }
        if covers(b, y) {
            let i = choose|i: int| 0 <= i < b.len() && #[trigger] inr(b[i], y);
            assert(inr((a + b)[i + a.len()], y));
        }
    }
}

pub proof fn lemma_covers_one(p: (u64, u64))
    ensures
        forall|y: nat| #[trigger] covers(seq![p], y) <==> inr(p, y),
{
    assert forall|y: nat| #[trigger] covers(seq![p], y) <==> inr(p, y) by {
        if inr(p, y) {
            assert(inr(seq![p][0], y));
        }
    }
}

pub proof fn lemma_contains_cat(a: Seq<(u64, u64)>, b: Seq<(u64, u64)>)
    ensures
        forall|p: (u64, u64)| #[trigger] (a + b).contains(p) <==> a.contains(p) || b.contains(p),
{
    assert forall|p: (u64, u64)| #[trigger] (a + b).contains(p) <==> a.contains(p) || b.contains(p) by {
        if (a + b).contains(p) {
            let i = choose|i: int| 0 <= i < (a + b).len() && (a + b)[i] == p;
            if i < a.len() {
                assert(a[i] == p);
            } else {
                assert(b[i - a.len()] == p);
            }
        }
        if a.contains(p) {
            let i = choose|i: int| 0 <= i < a.len() && a[i] == p;
            assert((a + b)[i] == p);
        }
        if b.contains(p) {
            let i = choose|i: int| 0 <= i < b.len() && b[i] == p;
            assert((a + b)[i + a.len()] == p);
        }
    }
}

/// The parts of a merged (disjoint) sequence are merged (disjoint), the first's ranges ending before (at or before)
/// the second's begin; and capped stays.
proof fn lemma_parts(a: Seq<(u64, u64)>, b: Seq<(u64, u64)>)
    ensures
        disjoint(a + b) ==> disjoint(a) && disjoint(b) && forall|i: int, j: int|
            0 <= i < a.len() && 0 <= j < b.len() ==> #[trigger] a[i].1 <= #[trigger] b[j].0,
        merged(a + b) ==> merged(a) && merged(b) && forall|i: int, j: int|
            0 <= i < a.len() && 0 <= j < b.len() ==> #[trigger] a[i].1 < #[trigger] b[j].0,
        capped(a + b) ==> capped(a) && capped(b),
{
    let c = a + b;
    if disjoint(c) {
        assert forall|i: int, j: int| 0 <= i < j < a.len() implies #[trigger] a[i].1 <= #[trigger] a[j].0 by {
            assert(c[i] == a[i] && c[j] == a[j]);
        }
        assert forall|i: int| 0 <= i < a.len() implies #[trigger] a[i].0 < a[i].1 by {
            assert(c[i] == a[i]);
        }
        assert forall|i: int, j: int| 0 <= i < j < b.len() implies #[trigger] b[i].1 <= #[trigger] b[j].0 by {
            assert(c[i + a.len()] == b[i] && c[j + a.len()] == b[j]);
        }
        assert forall|i: int| 0 <= i < b.len() implies #[trigger] b[i].0 < b[i].1 by {
            assert(c[i + a.len()] == b[i]);
        }
        assert forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() implies #[trigger] a[i].1
            <= #[trigger] b[j].0 by {
            assert(c[i] == a[i] && c[j + a.len()] == b[j]);
        }
    }
    if merged(c) {
        assert forall|i: int, j: int| 0 <= i < j < a.len() implies #[trigger] a[i].1 < #[trigger] a[j].0 by {
            assert(c[i] == a[i] && c[j] == a[j]);
        }
        assert forall|i: int| 0 <= i < a.len() implies #[trigger] a[i].0 < a[i].1 by {
            assert(c[i] == a[i]);
        }
        assert forall|i: int, j: int| 0 <= i < j < b.len() implies #[trigger] b[i].1 < #[trigger] b[j].0 by {
            assert(c[i + a.len()] == b[i] && c[j + a.len()] == b[j]);
        }
        assert forall|i: int| 0 <= i < b.len() implies #[trigger] b[i].0 < b[i].1 by {
            assert(c[i + a.len()] == b[i]);
        }
        assert forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() implies #[trigger] a[i].1
            < #[trigger] b[j].0 by {
            assert(c[i] == a[i] && c[j + a.len()] == b[j]);
        }
    }
    if capped(c) {
        assert forall|i: int| 0 <= i < a.len() implies #[trigger] a[i].1 <= VARINT_MAX by {
            assert(c[i] == a[i]);
        }
        assert forall|i: int| 0 <= i < b.len() implies #[trigger] b[i].1 <= VARINT_MAX by {
            assert(c[i + a.len()] == b[i]);
        }
    }
}

/// `a`, then `p`, then `b` is merged (disjoint) when each part is and `p` sits strictly (weakly) between.
proof fn lemma_join3(a: Seq<(u64, u64)>, p: (u64, u64), b: Seq<(u64, u64)>, strict: bool)
    requires
        p.0 < p.1,
        strict ==> merged(a) && merged(b),
        !strict ==> disjoint(a) && disjoint(b),
        forall|i: int| 0 <= i < a.len() ==> if strict { #[trigger] a[i].1 < p.0 } else { a[i].1 <= p.0 },
        forall|j: int| 0 <= j < b.len() ==> if strict { p.1 < #[trigger] b[j].0 } else { p.1 <= b[j].0 },
        capped(a),
        capped(b),
        p.1 <= VARINT_MAX,
    ensures
        strict ==> merged(a + seq![p] + b),
        !strict ==> disjoint(a + seq![p] + b),
        capped(a + seq![p] + b),
{
    let c = a + seq![p] + b;
    let n = a.len();
    assert forall|i: int| 0 <= i < c.len() implies #[trigger] c[i].0 < c[i].1 && c[i].1 <= VARINT_MAX by {
        if i < n {
            assert(c[i] == a[i]);
        } else if i > n {
            assert(c[i] == b[i - n - 1]);
        }
    }
    assert forall|i: int, j: int| 0 <= i < j < c.len() implies if strict { #[trigger] c[i].1 < #[trigger] c[j].0 } else {
        c[i].1 <= c[j].0
    } by {
        if i < n {
            assert(c[i] == a[i]);
        } else if i > n {
            assert(c[i] == b[i - n - 1]);
        }
        if j < n {
            assert(c[j] == a[j]);
        } else if j > n {
            assert(c[j] == b[j - n - 1]);
        }
    }
}

/// The entry of a sorted-key sequence with key `k`, at index `i`, is the only one with that key.
proof fn lemma_key_unique(v: Seq<(u64, u64)>, i: int, p: (u64, u64))
    requires
        disjoint(v),
        0 <= i < v.len(),
        v[i].0 == p.0,
        v.contains(p),
    ensures
        v[i] == p,
        v.index_of(p) == i,
{
    let j = choose|j: int| 0 <= j < v.len() && v[j] == p;
    if j < i {
        assert(v[j].1 <= v[i].0);
    } else if j > i {
        assert(v[i].1 <= v[j].0);
    }
    assert(v[i] == p);
    let k = v.index_of(p);
    if k < i {
        assert(v[k].1 <= v[i].0);
    } else if k > i {
        assert(v[i].1 <= v[k].0);
    }
}

/// Splitting a set at `s` around a gap `[s, e)` it does not meet: the left part ends at or below `s`, the right part
/// starts at or past `e`.
proof fn lemma_gap(t: Seq<(u64, u64)>, l: Seq<(u64, u64)>, r: Seq<(u64, u64)>, s: u64, e: u64)
    requires
        t == l + r,
        disjoint(t),
        forall|i: int| 0 <= i < l.len() ==> #[trigger] l[i].0 < s,
        forall|i: int| 0 <= i < r.len() ==> #[trigger] r[i].0 >= s,
        forall|x: nat| s <= x < e ==> !covers(t, x),
        s < e,
    ensures
        forall|i: int| 0 <= i < l.len() ==> #[trigger] l[i].1 <= s,
        forall|i: int| 0 <= i < r.len() ==> #[trigger] r[i].0 >= e,
{
    assert forall|i: int| 0 <= i < l.len() implies #[trigger] l[i].1 <= s by {
        assert(t[i] == l[i]);
        if l[i].1 > s {
            assert(l[i].0 < s);
            assert(inr(t[i], s as nat));
            assert(covers(t, s as nat));
        }
    }
    assert forall|i: int| 0 <= i < r.len() implies #[trigger] r[i].0 >= e by {
        assert(t[i + l.len()] == r[i]);
        if r[i].0 < e {
            assert(r[i].0 >= s);
            assert(t[i + l.len()].0 < t[i + l.len()].1);
            assert(inr(t[i + l.len()], r[i].0 as nat));
            assert(covers(t, r[i].0 as nat));
        }
    }
}

/// `RangeSet::add`'s view: the old sequence is `sl`, the merged neighbours, `sr`; the new one `sl`, the merged range,
/// `sr`.
proof fn lemma_add_view(
    t0: Seq<(u64, u64)>,
    l: Seq<(u64, u64)>,
    r: Seq<(u64, u64)>,
    sl: Seq<(u64, u64)>,
    sr: Seq<(u64, u64)>,
    f: Seq<(u64, u64)>,
    s: u64,
    e: u64,
    ns: u64,
    ne: u64,
)
    requires
        t0 == l + r,
        s < e,
        ns <= s,
        e <= ne,
        ns == s ==> l == sl,
        ns < s ==> l == sl + seq![(ns, s)],
        ne == e ==> r == sr,
        ne > e ==> r == seq![(e, ne)] + sr,
        f == sl + seq![(ns, ne)] + sr,
    ensures
        forall|x: nat| #[trigger] covers(f, x) <==> covers(t0, x) || (s <= x && x < e),
        f.contains((ns, ne)),
        ns == s || t0.contains((ns, s)),
        ne == e || t0.contains((e, ne)),
        forall|p: (u64, u64)| #[trigger] f.contains(p) && p != (ns, ne) ==> t0.contains(p),
        f.len() + (if ns < s { 1int } else { 0 }) + (if ne > e { 1int } else { 0 }) == t0.len() + 1,
{
    let ml: Seq<(u64, u64)> = if ns < s { seq![(ns, s)] } else { Seq::empty() };
    let mr: Seq<(u64, u64)> = if ne > e { seq![(e, ne)] } else { Seq::empty() };
    assert(l =~= sl + ml);
    assert(r =~= mr + sr);
    assert(t0 =~= sl + (ml + mr) + sr);
    lemma_covers_cat(sl + seq![(ns, ne)], sr);
    lemma_covers_cat(sl, seq![(ns, ne)]);
    lemma_covers_cat(sl + (ml + mr), sr);
    lemma_covers_cat(sl, ml + mr);
    lemma_covers_cat(ml, mr);
    lemma_covers_one((ns, ne));
    lemma_covers_one((ns, s));
    lemma_covers_one((e, ne));
    assert forall|x: nat| #[trigger] covers(f, x) <==> covers(t0, x) || (s <= x && x < e) by {
        if ns >= s {
            assert(!covers(ml, x));
        }
        if ne <= e {
            assert(!covers(mr, x));
        }
    }
    assert(f[sl.len() as int] == (ns, ne));
    lemma_contains_cat(sl + seq![(ns, ne)], sr);
    lemma_contains_cat(sl, seq![(ns, ne)]);
    lemma_contains_cat(sl + (ml + mr), sr);
    lemma_contains_cat(sl, ml + mr);
    lemma_contains_cat(ml, mr);
    assert forall|p: (u64, u64)| #[trigger] f.contains(p) && p != (ns, ne) implies t0.contains(p) by {
        if seq![(ns, ne)].contains(p) {
            assert(seq![(ns, ne)][0] == p);
        }
    }
    if ns < s {
        assert(ml[0] == (ns, s));
        assert(ml.contains((ns, s)));
    }
    if ne > e {
        assert(mr[0] == (e, ne));
        assert(mr.contains((e, ne)));
    }
}

// ---- The sets.

/// Merged ranges: sorted, disjoint, non-adjacent; key the start, value the end.
pub struct RangeSet {
    t: Tree<u64>,
    n: u64,
}

/// Disjoint pieces, never merged; key the start, value the end.
pub struct PieceSet {
    t: Tree<u64>,
    n: u64,
}

impl View for RangeSet {
    type V = Seq<(u64, u64)>;

    closed spec fn view(&self) -> Seq<(u64, u64)> {
        seq(self.t)
    }
}

impl View for PieceSet {
    type V = Seq<(u64, u64)>;

    closed spec fn view(&self) -> Seq<(u64, u64)> {
        seq(self.t)
    }
}

/// `split`'s keys facts, as index facts on the parts' sequences.
proof fn lemma_split_keys(l: Tree<u64>, r: Tree<u64>, s: u64)
    requires
        keys_lt(l, s),
        keys_ge(r, s),
    ensures
        forall|i: int| 0 <= i < seq(l).len() ==> #[trigger] seq(l)[i].0 < s,
        forall|i: int| 0 <= i < seq(r).len() ==> #[trigger] seq(r)[i].0 >= s,
{
}

/// `remove_range`'s and `take`'s found path: `t`'s entries are `l`'s, `(s, e)`, `r2`'s; the result `l` then `r2`.
fn cut_out(l: Tree<u64>, r2: Tree<u64>, Ghost(t): Ghost<Seq<(u64, u64)>>, Ghost(s): Ghost<u64>, Ghost(e): Ghost<u64>) -> (res: (
    Tree<u64>,
    Ghost<nat>,
))
    requires
        wf(l),
        wf(r2),
        t == seq(l) + seq![(s, e)] + seq(r2),
        disjoint(t),
        capped(t),
        keys_lt(l, s),
        keys_gt(r2, s),
    ensures
        wf(res.0),
        seq(res.0) == t.remove(t.index_of((s, e))),
        seq(res.0) == seq(l) + seq(r2),
        ht(res.0) <= vstd::math::max(ht(l) as int, ht(r2) as int) + 1,
        res.1@ <= c_join2() * (vstd::math::max(ht(l) as int, ht(r2) as int) + 1),
{
    let ghost mut work: nat = 0;
    proof {
        lemma_small(t);
        lemma_join2_order(l, r2, s);
        assert forall|i: int, j: int| 0 <= i < seq(l).len() && 0 <= j < seq(r2).len() implies #[trigger] seq(l)[i].0
            < #[trigger] seq(r2)[j].0 by {
            assert(seq(r2)[j].0 > s);
        }
        let n = seq(l).len() as int;
        assert(t[n] == (s, e));
        assert(t.contains((s, e)));
        lemma_key_unique(t, n, (s, e));
        assert(t.remove(n) =~= seq(l) + seq(r2));
    }
    let (j, Ghost(c)) = join2(l, r2);
    proof {
        work = work + c;
    }
    (j, Ghost(work))
}

impl RangeSet {
    pub closed spec fn wf(&self) -> bool {
        &&& wf(self.t)
        &&& merged(seq(self.t))
        &&& capped(seq(self.t))
        &&& self.n == seq(self.t).len()
    }

    pub closed spec fn ht(&self) -> nat {
        ht(self.t)
    }

    pub proof fn lemma_wf(&self)
        requires
            self.wf(),
        ensures
            merged(self@),
            disjoint(self@),
            capped(self@),
            self@.len() <= VARINT_MAX,
            self.ht() <= 126,
    {
        lemma_count(self@);
        if let Some(b) = self.t {
            assert(b.h <= 126);
        }
    }

    pub fn new() -> (r: RangeSet)
        ensures
            r.wf(),
            r@.len() == 0,
            r.ht() == 0,
    {
        RangeSet { t: None, n: 0 }
    }

    pub fn len(&self) -> (r: u64)
        requires
            self.wf(),
        ensures
            r == self@.len(),
    {
        self.n
    }

    pub fn clear(&mut self) -> (r: Ghost<nat>)
        ensures
            final(self).wf(),
            final(self)@.len() == 0,
            final(self).ht() == 0,
            r@ <= c_free() * (2 * old(self)@.len() + 1),
    {
        let ghost mut work: nat = 0;
        let t = self.t.take();
        let Ghost(c) = free(t);
        self.n = 0;
        proof {
            work = work + c;
        }
        Ghost(work)
    }

    /// Frees the first ranges within `budget` (`avl::pop_some`): at least one while any remain; the rest stay.
    pub fn reap_some(&mut self, budget: u64) -> (r: Ghost<nat>)
        requires
            old(self).wf(),
            c_pop() * 127 + 2 <= budget,
        ensures
            final(self).wf(),
            final(self)@.len() <= old(self)@.len(),
            old(self)@.len() > 0 ==> final(self)@.len() < old(self)@.len(),
            r@ <= budget,
    {
        let ghost s0 = self@;
        let (k, Ghost(c)) = pop_some(&mut self.t, budget);
        self.n = self.n - k;
        proof {
            let s1 = seq(self.t);
            assert(s1 == s0.skip(k as int));
            assert forall|i: int| 0 <= i < s1.len() implies #[trigger] s1[i] == s0[i + k] by {}
            assert(merged(s1)) by {
                assert forall|i: int, j: int| 0 <= i < j < s1.len() implies #[trigger] s1[i].1 < #[trigger] s1[j].0 by {
                    assert(s1[i] == s0[i + k] && s1[j] == s0[j + k]);
                }
                assert forall|i: int| 0 <= i < s1.len() implies #[trigger] s1[i].0 < s1[i].1 by {
                    assert(s1[i] == s0[i + k]);
                }
            }
            assert(capped(s1)) by {
                assert forall|i: int| 0 <= i < s1.len() implies #[trigger] s1[i].1 <= VARINT_MAX by {
                    assert(s1[i] == s0[i + k]);
                }
            }
        }
        Ghost(c)
    }

    pub fn first(&self) -> (r: (Option<(u64, u64)>, Ghost<nat>))
        requires
            self.wf(),
        ensures
            r.0 == (if self@.len() > 0 { Some(self@[0]) } else { None::<(u64, u64)> }),
            r.1@ <= c_rs() * (self.ht() + 1),
    {
        let ghost mut work: nat = 0;
        let (p, Ghost(c)) = first(&self.t);
        proof {
            work = work + c;
        }
        match p {
            Some((k, v)) => (Some((k, *v)), Ghost(work)),
            None => (None, Ghost(work)),
        }
    }

    /// The left neighbour of `[s, e)` in `l` (every range of which ends at or below `s`): the one ending at `s`, if
    /// any, detached; `ns` its start, else `s`.
    fn take_left(l: Tree<u64>, s: u64) -> (res: (Tree<u64>, u64, Ghost<nat>))
        requires
            wf(l),
            merged(seq(l)),
            capped(seq(l)),
            forall|i: int| 0 <= i < seq(l).len() ==> #[trigger] seq(l)[i].1 <= s,
        ensures
            wf(res.0),
            ht(res.0) <= ht(l),
            merged(seq(res.0)),
            capped(seq(res.0)),
            res.1 <= s,
            res.1 == s ==> seq(l) == seq(res.0),
            res.1 < s ==> seq(l) == seq(res.0) + seq![(res.1, s)],
            forall|i: int| 0 <= i < seq(res.0).len() ==> #[trigger] seq(res.0)[i].1 < res.1,
            keys_lt(res.0, res.1),
            res.2@ <= 44 * (ht(l) + 1) + 1,
    {
        let ghost l0 = seq(l);
        let ghost mut work: nat = 0;
        proof {
            assert(c_get() == 1 && c_split6() == 37 && c_pop() == 6 && c_free() == 1);
        }
        let (last, Ghost(c1)) = get_le(&l, u64::MAX);
        let lk: Option<(u64, u64)> = match last {
            Some((k, v)) => Some((k, *v)),
            None => None,
        };
        proof {
            work = work + c1;
        }
        match lk {
            Some((k0, v0)) => {
                proof {
                    let i = choose|i: int| #[trigger] last_le(l0, u64::MAX, i, k0, v0);
                    if i < l0.len() - 1 {
                        assert(l0[l0.len() - 1].0 > u64::MAX);
                    }
                    assert(i == l0.len() - 1);
                }
                if v0 == s {
                    proof {
                        lemma_small(l0);
                    }
                    let (l1, l2, Ghost(c2)) = split(l, k0);
                    proof {
                        lemma_split_cost(l, l1, l2, c2);
                        work = work + c2;
                        let n = l0.len() - 1;
                        assert(l0[n] == (k0, s));
                        // Only the last entry has a key at or past k0.
                        assert forall|i: int| 0 <= i < seq(l1).len() implies #[trigger] seq(l1)[i] == l0[i] by {}
                        assert(seq(l1).len() == n) by {
                            if seq(l1).len() > n {
                                assert(seq(l1)[n] == l0[n]);
                                assert(seq(l1)[n].0 < k0);
                            }
                            if seq(l1).len() < n {
                                let m = seq(l1).len() as int;
                                assert(l0[m] == seq(l2)[0]);
                                assert(seq(l2)[0].0 >= k0);
                                assert(l0[m].0 < l0[m].1);
                                assert(l0[m].1 < l0[n].0);
                            }
                        }
                        assert(seq(l2).len() > 0);
                    }
                    let (l3, _k, _v, Ghost(c3)) = pop_min(l2);
                    let Ghost(c4) = free(l3);
                    proof {
                        work = work + c3 + c4;
                        assert(seq(l3).len() == 0);
                        assert(seq(l1) + seq![(k0, s)] =~= l0) by {
                            assert(seq(l2) =~= seq![(k0, s)]);
                        }
                        lemma_parts(seq(l1), seq![(k0, s)]);
                        assert forall|i: int| 0 <= i < seq(l1).len() implies #[trigger] seq(l1)[i].1 < k0 by {
                            assert(seq(l1)[i] == l0[i]);
                            assert(l0[i].1 < l0[l0.len() - 1].0);
                        }
                    }
                    (l1, k0, Ghost(work))
                } else {
                    proof {
                        assert forall|i: int| 0 <= i < l0.len() implies #[trigger] l0[i].1 < s by {
                            if i < l0.len() - 1 {
                                assert(l0[i].1 < l0[l0.len() - 1].0);
                            }
                        }
                        assert forall|i: int| 0 <= i < l0.len() implies #[trigger] l0[i].0 < s by {
                            assert(l0[i].0 < l0[i].1);
                        }
                    }
                    (l, s, Ghost(work))
                }
            },
            None => {
                proof {
                    assert(l0.len() == 0) by {
                        if l0.len() > 0 {
                            assert(l0[0].0 > u64::MAX);
                        }
                    }
                }
                (l, s, Ghost(work))
            },
        }
    }

    /// The right neighbour of `[s, e)` in `r` (every range of which starts at or past `e`): the one starting at `e`,
    /// if any, detached; `ne` its end, else `e`.
    fn take_right(r: Tree<u64>, e: u64) -> (res: (Tree<u64>, u64, Ghost<nat>))
        requires
            wf(r),
            merged(seq(r)),
            capped(seq(r)),
            forall|i: int| 0 <= i < seq(r).len() ==> #[trigger] seq(r)[i].0 >= e,
        ensures
            wf(res.0),
            ht(res.0) <= ht(r),
            merged(seq(res.0)),
            capped(seq(res.0)),
            res.1 >= e,
            res.1 == e ==> seq(r) == seq(res.0),
            res.1 > e ==> seq(r) == seq![(e, res.1)] + seq(res.0),
            forall|i: int| 0 <= i < seq(res.0).len() ==> res.1 < #[trigger] seq(res.0)[i].0,
            keys_gt(res.0, res.1),
            res.1 <= VARINT_MAX || res.1 == e,
            res.2@ <= 7 * (ht(r) + 1),
    {
        let ghost r0 = seq(r);
        let ghost mut work: nat = 0;
        proof {
            assert(c_first() == 1 && c_pop() == 6);
        }
        let (fst, Ghost(c1)) = first(&r);
        let fk: Option<(u64, u64)> = match fst {
            Some((k, v)) => Some((k, *v)),
            None => None,
        };
        proof {
            work = work + c1;
        }
        match fk {
            Some((k1, v1)) => {
                if k1 == e {
                    let (r2, _k, _v, Ghost(c2)) = pop_min(r);
                    proof {
                        work = work + c2;
                        assert(seq![(e, v1)] + seq(r2) =~= r0);
                        lemma_parts(seq![(e, v1)], seq(r2));
                        assert(r0[0] == (e, v1));
                        assert forall|i: int| 0 <= i < seq(r2).len() implies v1 < #[trigger] seq(r2)[i].0 by {
                            assert(r0[i + 1] == seq(r2)[i]);
                        }
                    }
                    (r2, v1, Ghost(work))
                } else {
                    proof {
                        assert forall|i: int| 0 <= i < r0.len() implies e < #[trigger] r0[i].0 by {
                            if i > 0 {
                                assert(r0[0].1 < r0[i].0);
                            }
                        }
                    }
                    (r, e, Ghost(work))
                }
            },
            None => (r, e, Ghost(work)),
        }
    }

    /// Adds `[s, e)`, which no range meets, merging it with the range ending at `s` and the one starting at `e`; `r.0`
    /// is the merged range.
    pub fn add(&mut self, s: u64, e: u64) -> (r: ((u64, u64), Ghost<nat>))
        requires
            old(self).wf(),
            s < e <= VARINT_MAX,
            forall|x: nat| s <= x < e ==> !covers(old(self)@, x),
        ensures
            final(self).wf(),
            forall|x: nat| #[trigger] covers(final(self)@, x) <==> covers(old(self)@, x) || (s <= x && x < e),
            final(self)@.contains(r.0),
            r.0.0 <= s,
            e <= r.0.1,
            r.0.0 == s || old(self)@.contains((r.0.0, s)),
            r.0.1 == e || old(self)@.contains((e, r.0.1)),
            forall|p: (u64, u64)| #[trigger] final(self)@.contains(p) && p != r.0 ==> old(self)@.contains(p),
            old(self)@.len() <= final(self)@.len() + 2,
            final(self)@.len() <= old(self)@.len() + 1,
            final(self).ht() <= old(self).ht() + 1,
            r.1@ <= c_rs() * (old(self).ht() + 1) + c_free() * 3,
    {
        let ghost t0 = seq(self.t);
        let ghost h = ht(self.t);
        let ghost mut work: nat = 0;
        proof {
            assert(t0 == old(self)@);
            lemma_small(t0);
            assert(c_split6() == 37 && c_join() == 6);
        }
        let t = self.t.take();
        let (l, r, Ghost(c1)) = split(t, s);
        proof {
            lemma_split_cost(t, l, r, c1);
            work = work + c1;
            lemma_split_keys(l, r, s);
            lemma_gap(t0, seq(l), seq(r), s, e);
            lemma_parts(seq(l), seq(r));
        }
        let (left, ns, Ghost(c2)) = RangeSet::take_left(l, s);
        let (right, ne, Ghost(c3)) = RangeSet::take_right(r, e);
        let ghost (sl, sr) = (seq(left), seq(right));
        proof {
            work = work + c2 + c3;
            lemma_join3(sl, (ns, ne), sr, true);
            assert(sl.len() <= seq(l).len() && sr.len() <= seq(r).len());
        }
        let (j, Ghost(c4)) = join(left, ns, ne, right);
        proof {
            work = work + c4;
            assert(c4 <= c_join() * (h + 1)) by {
                assert(vstd::math::abs(ht(left) - ht(right)) <= h);
            }
            assert(ht(j) <= h + 1);
            lemma_add_view(t0, seq(l), seq(r), sl, sr, seq(j), s, e, ns, ne);
        }
        let k = (if ns < s { 1u64 } else { 0 }) + (if ne > e { 1u64 } else { 0 });
        self.t = j;
        self.n = self.n + 1 - k;
        ((ns, ne), Ghost(work))
    }

    /// Removes the range `(s, e)`.
    // `e` names the range for the spec only.
    #[allow(unused_variables)]
    pub fn remove_range(&mut self, s: u64, e: u64) -> (r: Ghost<nat>)
        requires
            old(self).wf(),
            old(self)@.contains((s, e)),
        ensures
            final(self).wf(),
            final(self)@ == old(self)@.remove(old(self)@.index_of((s, e))),
            forall|x: nat| #[trigger] covers(final(self)@, x) <==> covers(old(self)@, x) && !(s <= x && x < e),
            forall|p: (u64, u64)| #[trigger] final(self)@.contains(p) <==> old(self)@.contains(p) && p != (s, e),
            final(self).ht() <= old(self).ht() + 1,
            r@ <= c_rs() * (old(self).ht() + 1),
    {
        let ghost t0 = seq(self.t);
        let ghost mut work: nat = 0;
        proof {
            assert(t0 == old(self)@);
            lemma_small(t0);
            assert(c_split6() == 37 && c_join2() == 13 && c_pop() == 6 && c_rs() == 100);
            assert(c_split6() == 37 && c_join2() == 13 && c_pop() == 6 && c_first() == 1);
        }
        let t = self.t.take();
        let (l, r, Ghost(c1)) = split(t, s);
        proof {
            lemma_split_cost(t, l, r, c1);
            work = work + c1;
            lemma_split_keys(l, r, s);
            let i = choose|i: int| 0 <= i < t0.len() && t0[i] == (s, e);
            let n = seq(l).len() as int;
            assert(i >= n) by {
                if i < n {
                    assert(seq(l)[i] == t0[i]);
                    assert(seq(l)[i].0 < s);
                }
            }
            assert(t0[n] == seq(r)[0]);
            assert(seq(r)[0].0 >= s);
            assert(t0[n].0 < t0[n].1);
            if i > n {
                assert(t0[n].1 < t0[i].0);
            }
            assert(t0[n] == (s, e));
        }
        let (r2, _k, _v, Ghost(c2)) = pop_min(r);
        proof {
            work = work + c2;
            assert((seq![(_k, _v)] + seq(r2))[0] == (_k, _v));
            assert(t0 =~= seq(l) + seq![(s, e)] + seq(r2));
        }
        let (j, Ghost(c3)) = cut_out(l, r2, Ghost(t0), Ghost(s), Ghost(e));
        proof {
            work = work + c3;
            let n = seq(l).len() as int;
            assert(t0[n] == (s, e));
            lemma_key_unique(t0, n, (s, e));
            lemma_covers_remove(t0, n);
            lemma_contains_remove(t0, n);
            lemma_drop_mid(seq(l), (s, e), seq(r2));
        }
        self.t = j;
        self.n = self.n - 1;
        Ghost(work)
    }

    /// Takes `[s, s + k)` off the first range `[s, e)`, `k` at most its length.
    pub fn take_first(&mut self, k: u64) -> (r: Ghost<nat>)
        requires
            old(self).wf(),
            old(self)@.len() > 0,
            0 < k <= old(self)@[0].1 - old(self)@[0].0,
        ensures
            final(self).wf(),
            forall|x: nat| #[trigger] covers(final(self)@, x) <==> covers(old(self)@, x) && !(old(self)@[0].0 <= x
                && x < old(self)@[0].0 + k),
            final(self)@ == (if k == old(self)@[0].1 - old(self)@[0].0 {
                old(self)@.skip(1)
            } else {
                old(self)@.update(0, ((old(self)@[0].0 + k) as u64, old(self)@[0].1))
            }),
            final(self).ht() <= old(self).ht() + 1,
            r@ <= c_rs() * (old(self).ht() + 1),
    {
        let ghost t0 = seq(self.t);
        let ghost mut work: nat = 0;
        proof {
            lemma_small(t0);
        }
        let t = self.t.take();
        let (rest, s, e, Ghost(c1)) = pop_min(t);
        proof {
            work = work + c1;
            assert(t0[0] == (s, e));
            assert(seq(rest) =~= t0.skip(1));
            lemma_parts(seq![(s, e)], seq(rest));
            lemma_covers_cat(seq![(s, e)], seq(rest));
            lemma_covers_one((s, e));
            assert forall|x: nat| #[trigger] covers(seq(rest), x) implies x >= e by {
                let i = choose|i: int| 0 <= i < seq(rest).len() && #[trigger] inr(seq(rest)[i], x);
                assert(t0[i + 1] == seq(rest)[i]);
                assert(t0[0].1 < t0[i + 1].0);
            }
        }
        if k == e - s {
            self.t = rest;
            self.n = self.n - 1;
            Ghost(work)
        } else {
            proof {
                assert forall|i: int| 0 <= i < seq(rest).len() implies (s + k) < #[trigger] seq(rest)[i].0 by {}
                assert(keys_gt(rest, (s + k) as u64));
            }
            let (j, Ghost(c2)) = join(None, s + k, e, rest);
            proof {
                work = work + c2;
                let p = ((s + k) as u64, e);
                lemma_join3(Seq::empty(), p, seq(rest), true);
                assert(seq(j) =~= Seq::<(u64, u64)>::empty() + seq![p] + seq(rest));
                assert(seq(j) =~= t0.update(0, p));
                lemma_covers_cat(seq![p], seq(rest));
                lemma_covers_one(p);
                assert(seq(j) =~= seq![p] + seq(rest));
            }
            self.t = j;
            Ghost(work)
        }
    }
}

/// Removing range `i` of a disjoint sequence removes exactly its bytes.
pub proof fn lemma_covers_remove(v: Seq<(u64, u64)>, i: int)
    requires
        disjoint(v),
        0 <= i < v.len(),
    ensures
        forall|x: nat| #[trigger] covers(v.remove(i), x) <==> covers(v, x) && !inr(v[i], x),
{
    let w = v.remove(i);
    assert forall|x: nat| #[trigger] covers(w, x) <==> covers(v, x) && !inr(v[i], x) by {
        if covers(w, x) {
            let j = choose|j: int| 0 <= j < w.len() && #[trigger] inr(w[j], x);
            let jj = if j < i { j } else { j + 1 };
            assert(w[j] == v[jj]);
            assert(inr(v[jj], x));
            if inr(v[i], x) {
                if jj < i {
                    assert(v[jj].1 <= v[i].0);
                } else {
                    assert(v[i].1 <= v[jj].0);
                }
            }
        }
        if covers(v, x) && !inr(v[i], x) {
            let j = choose|j: int| 0 <= j < v.len() && #[trigger] inr(v[j], x);
            if j < i {
                assert(w[j] == v[j]);
                assert(inr(w[j], x));
            } else {
                assert(j != i);
                assert(w[j - 1] == v[j]);
                assert(inr(w[j - 1], x));
            }
        }
    }
}

/// What a removal leaves is in the sequence; and only `v[i]` goes, when `v`'s entries are distinct.
pub proof fn lemma_contains_remove(v: Seq<(u64, u64)>, i: int)
    requires
        disjoint(v),
        0 <= i < v.len(),
    ensures
        forall|p: (u64, u64)| #[trigger] v.remove(i).contains(p) <==> v.contains(p) && p != v[i],
{
    let w = v.remove(i);
    assert forall|p: (u64, u64)| #[trigger] w.contains(p) <==> v.contains(p) && p != v[i] by {
        if w.contains(p) {
            let j = choose|j: int| 0 <= j < w.len() && w[j] == p;
            let jj = if j < i { j } else { j + 1 };
            assert(w[j] == v[jj]);
            if jj < i {
                assert(v[jj].1 <= v[i].0);
            } else {
                assert(v[i].1 <= v[jj].0);
            }
        }
        if v.contains(p) && p != v[i] {
            let j = choose|j: int| 0 <= j < v.len() && v[j] == p;
            if j < i {
                assert(w[j] == v[j]);
            } else {
                assert(w[j - 1] == v[j]);
            }
        }
    }
}

/// Dropping the middle entry of a merged (disjoint, capped) sequence leaves one.
proof fn lemma_drop_mid(a: Seq<(u64, u64)>, p: (u64, u64), b: Seq<(u64, u64)>)
    ensures
        merged(a + seq![p] + b) ==> merged(a + b),
        disjoint(a + seq![p] + b) ==> disjoint(a + b),
        capped(a + seq![p] + b) ==> capped(a + b),
{
    let c = a + seq![p] + b;
    let d = a + b;
    let n = a.len();
    assert forall|i: int| 0 <= i < d.len() implies #[trigger] d[i] == c[if i < n { i } else { i + 1 }] by {}
    if merged(c) {
        assert forall|i: int, j: int| 0 <= i < j < d.len() implies #[trigger] d[i].1 < #[trigger] d[j].0 by {
            assert(d[i] == c[if i < n { i } else { i + 1 }]);
            assert(d[j] == c[if j < n { j } else { j + 1 }]);
        }
        assert forall|i: int| 0 <= i < d.len() implies #[trigger] d[i].0 < d[i].1 by {
            assert(d[i] == c[if i < n { i } else { i + 1 }]);
        }
    }
    if disjoint(c) {
        assert forall|i: int, j: int| 0 <= i < j < d.len() implies #[trigger] d[i].1 <= #[trigger] d[j].0 by {
            assert(d[i] == c[if i < n { i } else { i + 1 }]);
            assert(d[j] == c[if j < n { j } else { j + 1 }]);
        }
        assert forall|i: int| 0 <= i < d.len() implies #[trigger] d[i].0 < d[i].1 by {
            assert(d[i] == c[if i < n { i } else { i + 1 }]);
        }
    }
    if capped(c) {
        assert forall|i: int| 0 <= i < d.len() implies #[trigger] d[i].1 <= VARINT_MAX by {
            assert(d[i] == c[if i < n { i } else { i + 1 }]);
        }
    }
}

impl PieceSet {
    pub closed spec fn wf(&self) -> bool {
        &&& wf(self.t)
        &&& disjoint(seq(self.t))
        &&& capped(seq(self.t))
        &&& self.n == seq(self.t).len()
    }

    pub closed spec fn ht(&self) -> nat {
        ht(self.t)
    }

    pub proof fn lemma_wf(&self)
        requires
            self.wf(),
        ensures
            disjoint(self@),
            capped(self@),
            self@.len() <= VARINT_MAX,
            self.ht() <= 126,
    {
        lemma_count(self@);
        if let Some(b) = self.t {
            assert(b.h <= 126);
        }
    }

    pub fn new() -> (r: PieceSet)
        ensures
            r.wf(),
            r@.len() == 0,
            r.ht() == 0,
    {
        PieceSet { t: None, n: 0 }
    }

    pub fn len(&self) -> (r: u64)
        requires
            self.wf(),
        ensures
            r == self@.len(),
    {
        self.n
    }

    pub fn clear(&mut self) -> (r: Ghost<nat>)
        ensures
            final(self).wf(),
            final(self)@.len() == 0,
            final(self).ht() == 0,
            r@ <= c_free() * (2 * old(self)@.len() + 1),
    {
        let ghost mut work: nat = 0;
        let t = self.t.take();
        let Ghost(c) = free(t);
        self.n = 0;
        proof {
            work = work + c;
        }
        Ghost(work)
    }

    /// Frees the first ranges within `budget` (`avl::pop_some`): at least one while any remain; the rest stay.
    pub fn reap_some(&mut self, budget: u64) -> (r: Ghost<nat>)
        requires
            old(self).wf(),
            c_pop() * 127 + 2 <= budget,
        ensures
            final(self).wf(),
            final(self)@.len() <= old(self)@.len(),
            old(self)@.len() > 0 ==> final(self)@.len() < old(self)@.len(),
            r@ <= budget,
    {
        let ghost s0 = self@;
        let (k, Ghost(c)) = pop_some(&mut self.t, budget);
        self.n = self.n - k;
        proof {
            let s1 = seq(self.t);
            assert(s1 == s0.skip(k as int));
            assert forall|i: int| 0 <= i < s1.len() implies #[trigger] s1[i] == s0[i + k] by {}
            assert(disjoint(s1)) by {
                assert forall|i: int, j: int| 0 <= i < j < s1.len() implies #[trigger] s1[i].1 <= #[trigger] s1[j].0 by {
                    assert(s1[i] == s0[i + k] && s1[j] == s0[j + k]);
                }
                assert forall|i: int| 0 <= i < s1.len() implies #[trigger] s1[i].0 < s1[i].1 by {
                    assert(s1[i] == s0[i + k]);
                }
            }
            assert(capped(s1)) by {
                assert forall|i: int| 0 <= i < s1.len() implies #[trigger] s1[i].1 <= VARINT_MAX by {
                    assert(s1[i] == s0[i + k]);
                }
            }
        }
        Ghost(c)
    }

    /// Adds the piece `[s, e)`, which no piece meets.
    pub fn insert_piece(&mut self, s: u64, e: u64) -> (r: Ghost<nat>)
        requires
            old(self).wf(),
            s < e <= VARINT_MAX,
            forall|x: nat| s <= x < e ==> !covers(old(self)@, x),
        ensures
            final(self).wf(),
            forall|x: nat| #[trigger] covers(final(self)@, x) <==> covers(old(self)@, x) || (s <= x && x < e),
            forall|p: (u64, u64)| #[trigger] final(self)@.contains(p) <==> old(self)@.contains(p) || p == (s, e),
            final(self)@.len() == old(self)@.len() + 1,
            final(self).ht() <= old(self).ht() + 1,
            r@ <= c_rs() * (old(self).ht() + 1),
    {
        let ghost t0 = seq(self.t);
        let ghost h = ht(self.t);
        let ghost mut work: nat = 0;
        proof {
            assert(t0 == old(self)@);
            lemma_small(t0);
            assert(c_split6() == 37 && c_join() == 6);
        }
        let t = self.t.take();
        let (l, r, Ghost(c1)) = split(t, s);
        proof {
            lemma_split_cost(t, l, r, c1);
            work = work + c1;
            lemma_split_keys(l, r, s);
            lemma_gap(t0, seq(l), seq(r), s, e);
            lemma_parts(seq(l), seq(r));
            lemma_join3(seq(l), (s, e), seq(r), false);
            assert(keys_gt(r, s)) by {
                assert forall|i: int| 0 <= i < seq(r).len() implies #[trigger] seq(r)[i].0 > s by {}
            }
        }
        let (j, Ghost(c2)) = join(l, s, e, r);
        proof {
            work = work + c2;
            assert(vstd::math::abs(ht(l) - ht(r)) <= h);
            let f = seq(j);
            lemma_covers_cat(seq(l) + seq![(s, e)], seq(r));
            lemma_covers_cat(seq(l), seq![(s, e)]);
            lemma_covers_cat(seq(l), seq(r));
            lemma_covers_one((s, e));
            lemma_contains_cat(seq(l) + seq![(s, e)], seq(r));
            lemma_contains_cat(seq(l), seq![(s, e)]);
            lemma_contains_cat(seq(l), seq(r));
            assert forall|p: (u64, u64)| #[trigger] seq![(s, e)].contains(p) <==> p == (s, e) by {
                if p == (s, e) {
                    assert(seq![(s, e)][0] == p);
                }
            }
        }
        self.t = j;
        self.n = self.n + 1;
        Ghost(work)
    }

    /// Removes exactly the piece `[s, e)`, if it is one.
    pub fn take_piece(&mut self, s: u64, e: u64) -> (r: (bool, Ghost<nat>))
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            r.0 == old(self)@.contains((s, e)),
            r.0 ==> final(self)@ == old(self)@.remove(old(self)@.index_of((s, e))),
            r.0 ==> forall|x: nat| #[trigger] covers(final(self)@, x) <==> covers(old(self)@, x) && !(s <= x && x < e),
            r.0 ==> forall|p: (u64, u64)| #[trigger] final(self)@.contains(p) <==> old(self)@.contains(p) && p != (s, e),
            !r.0 ==> final(self)@ == old(self)@,
            final(self).ht() <= old(self).ht() + 1,
            r.1@ <= c_rs() * (old(self).ht() + 1) + c_free(),
    {
        let ghost t0 = seq(self.t);
        let ghost mut work: nat = 0;
        proof {
            assert(t0 == old(self)@);
            lemma_small(t0);
            assert(c_split6() == 37 && c_join2() == 13 && c_pop() == 6 && c_first() == 1);
        }
        let t = self.t.take();
        let (l, r, Ghost(c1)) = split(t, s);
        proof {
            lemma_split_cost(t, l, r, c1);
            work = work + c1;
            lemma_split_keys(l, r, s);
        }
        let (fst, Ghost(c2)) = first(&r);
        let hit = match fst {
            Some((k, v)) => k == s && *v == e,
            None => false,
        };
        proof {
            work = work + c2;
            let n = seq(l).len() as int;
            // `(s, e)`, if present, is the right part's first entry.
            if t0.contains((s, e)) {
                let i = choose|i: int| 0 <= i < t0.len() && t0[i] == (s, e);
                assert(i >= n) by {
                    if i < n {
                        assert(seq(l)[i] == t0[i]);
                        assert(seq(l)[i].0 < s);
                    }
                }
                assert(t0[n] == seq(r)[0]);
                assert(seq(r)[0].0 >= s);
                if i > n {
                    assert(t0[n].1 <= t0[i].0);
                    assert(t0[n].0 < t0[n].1);
                }
            }
        }
        if hit {
            let (r2, _k, _v, Ghost(c3)) = pop_min(r);
            proof {
                work = work + c3;
                assert((seq![(_k, _v)] + seq(r2))[0] == (_k, _v));
                assert(t0 =~= seq(l) + seq![(s, e)] + seq(r2));
                assert(t0[seq(l).len() as int] == (s, e));
            }
            let (j, Ghost(c4)) = cut_out(l, r2, Ghost(t0), Ghost(s), Ghost(e));
            proof {
                work = work + c4;
                assert(t0.contains((s, e)));
                lemma_key_unique(t0, seq(l).len() as int, (s, e));
                lemma_covers_remove(t0, seq(l).len() as int);
                lemma_contains_remove(t0, seq(l).len() as int);
                lemma_drop_mid(seq(l), (s, e), seq(r2));
            }
            self.t = j;
            self.n = self.n - 1;
            (true, Ghost(work))
        } else {
            proof {
                lemma_join2_order(l, r, s);
            }
            let (j, Ghost(c3)) = join2(l, r);
            proof {
                work = work + c3;
            }
            self.t = j;
            (false, Ghost(work))
        }
    }
}

} // verus!

/// Test support: the ranges in order.
fn walk(t: &crate::avl::Tree<u64>, out: &mut Vec<(u64, u64)>) {
    if let Some(b) = t {
        walk(&b.left, out);
        out.push((b.key, b.val));
        walk(&b.right, out);
    }
}

impl RangeSet {
    /// Test support: the ranges in order.
    #[doc(hidden)]
    pub fn to_vec(&self) -> Vec<(u64, u64)> {
        let mut v = Vec::new();
        walk(&self.t, &mut v);
        v
    }
}

impl PieceSet {
    /// Test support: the pieces in order.
    #[doc(hidden)]
    pub fn to_vec(&self) -> Vec<(u64, u64)> {
        let mut v = Vec::new();
        walk(&self.t, &mut v);
        v
    }
}
