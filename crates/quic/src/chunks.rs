//! The chunk store that replaces `Frags`'s sorted `Vec` (Phase 9b1; Task 7 moves it into frags.rs): chunks of at
//! most `CAP` bytes in a verified AVL keyed by start, sorted and disjoint but possibly adjacent. A chunk starting
//! where the previous one ends (a follower) holds at least `K` bytes, so `K · (chunks − runs) <= held`.
use crate::avl::*;
use vstd::prelude::*;
// Used only in ghost code, which a plain `cargo build` erases.
#[allow(unused_imports)]
use crate::frags::*;
#[allow(unused_imports)]
use wire::varint::*;

verus! {

broadcast use vstd::set_lib::range_set_properties;

/// The least length of a follower.
pub const K: u64 = 128;

/// The most bytes a chunk holds.
pub const CAP: u64 = 256;

/// The cost constant of `after_insert_w`.
spec fn c_walk() -> nat {
    2
}

/// A chunk's end.
spec fn end(c: (nat, Seq<u8>)) -> nat {
    c.0 + c.1.len()
}

/// Chunk `i` of `f` starts where chunk `i - 1` ends.
spec fn fol(f: Seq<(nat, Seq<u8>)>, i: int) -> bool {
    0 < i < f.len() && end(f[i - 1]) == f[i].0
}

/// Non-empty chunks of at most `CAP` bytes ending by `VARINT_MAX`, in order and disjoint (adjacent allowed); a
/// follower holds at least `K` bytes.
spec fn ok(f: Seq<(nat, Seq<u8>)>) -> bool {
    &&& forall|i: int| #![trigger f[i]] 0 <= i < f.len() ==> 0 < f[i].1.len() <= CAP && end(f[i]) <= VARINT_MAX
    &&& forall|i: int, j: int| #![trigger f[i], f[j]] 0 <= i < j < f.len() ==> end(f[i]) <= f[j].0
    &&& forall|i: int| #[trigger] fol(f, i) ==> f[i].1.len() >= K
}

/// The tree's entries as chunks.
spec fn mp(s: Seq<(u64, Vec<u8>)>) -> Seq<(nat, Seq<u8>)> {
    Seq::new(s.len(), |i: int| (s[i].0 as nat, s[i].1@))
}

/// The end of the last chunk, 0 with none.
spec fn hi_of(f: Seq<(nat, Seq<u8>)>) -> nat {
    if f.len() == 0 {
        0
    } else {
        end(f.last())
    }
}

// ---- The walk's sums over the chunks starting in `[s, e]` (`M`), in order.

spec fn inr(c: (nat, Seq<u8>), s: nat, e: nat) -> bool {
    s <= c.0 <= e
}

/// The bytes of chunk `c` (starting at most `e`) below `e`.
spec fn cut(c: (nat, Seq<u8>), e: nat) -> nat {
    ((if end(c) < e {
        end(c)
    } else {
        e
    }) - c.0) as nat
}

/// `|M|`.
spec fn nm(f: Seq<(nat, Seq<u8>)>, s: nat, e: nat) -> nat
    decreases f.len(),
{
    if f.len() == 0 {
        0
    } else {
        nm(f.drop_last(), s, e) + if inr(f.last(), s, e) {
            1nat
        } else {
            0
        }
    }
}

/// The bytes of `[s, e)` that `M` holds.
spec fn cvf(f: Seq<(nat, Seq<u8>)>, s: nat, e: nat) -> nat
    decreases f.len(),
{
    if f.len() == 0 {
        0
    } else {
        cvf(f.drop_last(), s, e) + if inr(f.last(), s, e) {
            cut(f.last(), e)
        } else {
            0
        }
    }
}

/// The end of the last chunk of `M`, `pe` with none.
spec fn lp(f: Seq<(nat, Seq<u8>)>, s: nat, e: nat, pe: int) -> int
    decreases f.len(),
{
    if f.len() == 0 {
        pe
    } else if inr(f.last(), s, e) {
        end(f.last()) as int
    } else {
        lp(f.drop_last(), s, e, pe)
    }
}

/// The chunks of `M` not starting where the one before them ends (the first one's predecessor ends at `pe`).
spec fn hds(f: Seq<(nat, Seq<u8>)>, s: nat, e: nat, pe: int) -> nat
    decreases f.len(),
{
    if f.len() == 0 {
        0
    } else {
        hds(f.drop_last(), s, e, pe) + if inr(f.last(), s, e) && lp(f.drop_last(), s, e, pe) != f.last().0 {
            1nat
        } else {
            0
        }
    }
}

/// The end of the last chunk starting below `s`, -1 with none.
spec fn pre(f: Seq<(nat, Seq<u8>)>, s: nat) -> int
    decreases f.len(),
{
    if f.len() == 0 {
        -1
    } else if f.last().0 < s {
        end(f.last()) as int
    } else {
        pre(f.drop_last(), s)
    }
}

/// The bytes of `[s, e)` that a chunk ending at `p` (and starting below `s`) holds.
spec fn clip(p: int, s: nat, e: nat) -> nat {
    if p > s {
        ((if p < e {
            p
        } else {
            e as int
        }) - s) as nat
    } else {
        0
    }
}

/// The positions of `st` in `[s, e]`.
spec fn ss(st: Set<nat>, s: nat, e: nat) -> Set<nat> {
    st.filter(|x: nat| s <= x <= e)
}

/// The positions of `st` outside `[s, e]`.
spec fn so(st: Set<nat>, s: nat, e: nat) -> Set<nat> {
    st.filter(|x: nat| !(s <= x <= e))
}

/// `{s}` if adding `[s, e)` to `p` starts a run at `s`.
spec fn xs(p: Set<nat>, s: nat) -> Set<nat> {
    if s == 0 || !p.contains((s - 1) as nat) {
        Set::empty().insert(s)
    } else {
        Set::empty()
    }
}

// ---- Sequence lemmas.

proof fn lemma_ok_drop(f: Seq<(nat, Seq<u8>)>)
    requires
        ok(f),
        f.len() > 0,
    ensures
        ok(f.drop_last()),
{
    let g = f.drop_last();
    assert forall|i: int| #![trigger g[i]] 0 <= i < g.len() implies 0 < g[i].1.len() <= CAP && end(g[i])
        <= VARINT_MAX by {
        assert(g[i] == f[i]);
    }
    assert forall|i: int, j: int| #![trigger g[i], g[j]] 0 <= i < j < g.len() implies end(g[i]) <= g[j].0 by {
        assert(g[i] == f[i] && g[j] == f[j]);
    }
    assert forall|i: int| #[trigger] fol(g, i) implies g[i].1.len() >= K by {
        assert(g[i] == f[i] && g[i - 1] == f[i - 1]);
        assert(fol(f, i));
    }
}

/// The last chunk adds its range to the others' positions, all below its start.
proof fn lemma_pos_last(f: Seq<(nat, Seq<u8>)>)
    requires
        ok(f),
        f.len() > 0,
    ensures
        ok(f.drop_last()),
        pos(f) =~= pos(f.drop_last()) + Set::range(f.last().0, end(f.last())),
        forall|k: nat| #[trigger] pos(f.drop_last()).contains(k) ==> k < f.last().0,
        forall|k: nat| #[trigger] pos(f).contains(k) ==> k < end(f.last()),
        pos(f).contains((end(f.last()) - 1) as nat),
{
    let n = f.len() - 1;
    let g = f.drop_last();
    lemma_ok_drop(f);
    assert forall|k: nat| #[trigger] pos(g).contains(k) implies k < f.last().0 by {
        let i = choose|i: int| inf(g, i, k);
        assert(g[i] == f[i]);
        assert(end(f[i]) <= f[n].0);
    }
    assert forall|k: nat| pos(f).contains(k) <==> #[trigger] (pos(g) + Set::range(f.last().0, end(f.last()))).contains(k) by {
        if pos(f).contains(k) {
            let i = choose|i: int| inf(f, i, k);
            if i < n {
                assert(g[i] == f[i]);
                assert(inf(g, i, k));
            }
        }
        if pos(g).contains(k) {
            let i = choose|i: int| inf(g, i, k);
            assert(g[i] == f[i]);
            assert(inf(f, i, k));
        }
        if f.last().0 <= k < end(f.last()) {
            assert(inf(f, n, k));
        }
    }
    assert(inf(f, n, (end(f.last()) - 1) as nat));
}

proof fn lemma_pos_empty(f: Seq<(nat, Seq<u8>)>)
    requires
        f.len() == 0,
    ensures
        pos(f) =~= Set::<nat>::empty(),
        starts(pos(f)) =~= Set::<nat>::empty(),
{
}

/// The last chunk's start is a run start exactly when it is not a follower.
proof fn lemma_starts_last(f: Seq<(nat, Seq<u8>)>)
    requires
        ok(f),
        f.len() > 0,
    ensures
        !starts(pos(f.drop_last())).contains(f.last().0),
        fol(f, f.len() - 1) ==> starts(pos(f)) =~= starts(pos(f.drop_last())),
        !fol(f, f.len() - 1) ==> starts(pos(f)) =~= starts(pos(f.drop_last())).insert(f.last().0),
{
    let n = f.len() - 1;
    let g = f.drop_last();
    let a = f.last().0;
    lemma_pos_last(f);
    if n > 0 {
        lemma_pos_last(g);
        assert(g.last() == f[n - 1]);
        assert(end(f[n - 1]) <= a);
    } else {
        lemma_pos_empty(g);
    }
    let x = if fol(f, n) {
        starts(pos(g))
    } else {
        starts(pos(g)).insert(a)
    };
    assert forall|p: nat| #[trigger] starts(pos(f)).contains(p) <==> x.contains(p) by {
        if pos(g).contains(p) && p > 0 {
            assert(pos(f).contains((p - 1) as nat) <==> pos(g).contains((p - 1) as nat));
        }
        if a < p < end(f.last()) {
            assert(pos(f).contains((p - 1) as nat));
        }
        if p == a && a > 0 {
            assert(pos(f).contains((a - 1) as nat) <==> pos(g).contains((a - 1) as nat));
        }
    }
}

/// `K · (n − runs) <= held`: every chunk but a run's first is a follower of at least `K` bytes.
proof fn lemma_k(f: Seq<(nat, Seq<u8>)>)
    requires
        ok(f),
    ensures
        K * (f.len() - runs(pos(f))) <= sum_len(f),
    decreases f.len(),
{
    if f.len() == 0 {
        lemma_pos_empty(f);
    } else {
        let g = f.drop_last();
        lemma_ok_drop(f);
        lemma_k(g);
        lemma_starts_last(f);
        if fol(f, f.len() - 1) {
            assert(f[f.len() - 1].1.len() >= K);
        }
    }
}

/// The sums over a concatenation.
proof fn lemma_cat(a: Seq<(nat, Seq<u8>)>, b: Seq<(nat, Seq<u8>)>, s: nat, e: nat, pe: int)
    ensures
        nm(a + b, s, e) == nm(a, s, e) + nm(b, s, e),
        cvf(a + b, s, e) == cvf(a, s, e) + cvf(b, s, e),
        lp(a + b, s, e, pe) == lp(b, s, e, lp(a, s, e, pe)),
        hds(a + b, s, e, pe) == hds(a, s, e, pe) + hds(b, s, e, lp(a, s, e, pe)),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
    } else {
        lemma_cat(a, b.drop_last(), s, e, pe);
        assert((a + b).drop_last() =~= a + b.drop_last());
        assert((a + b).last() == b.last());
    }
}

/// The sums over chunks none of which starts in `[s, e]`.
proof fn lemma_out(f: Seq<(nat, Seq<u8>)>, s: nat, e: nat, pe: int)
    requires
        forall|i: int| #![trigger f[i]] 0 <= i < f.len() ==> !inr(f[i], s, e),
    ensures
        nm(f, s, e) == 0,
        cvf(f, s, e) == 0,
        hds(f, s, e, pe) == 0,
        lp(f, s, e, pe) == pe,
    decreases f.len(),
{
    if f.len() > 0 {
        let g = f.drop_last();
        assert forall|i: int| #![trigger g[i]] 0 <= i < g.len() implies !inr(g[i], s, e) by {
            assert(g[i] == f[i]);
        }
        lemma_out(g, s, e, pe);
        assert(!inr(f[f.len() - 1], s, e));
    }
}

/// With no chunk starting below `s`, `pre` is -1.
proof fn lemma_pre_none(f: Seq<(nat, Seq<u8>)>, s: nat)
    requires
        forall|i: int| 0 <= i < f.len() ==> #[trigger] f[i].0 >= s,
    ensures
        pre(f, s) == -1,
    decreases f.len(),
{
    if f.len() > 0 {
        let g = f.drop_last();
        assert forall|i: int| 0 <= i < g.len() implies #[trigger] g[i].0 >= s by {
            assert(g[i] == f[i]);
        }
        lemma_pre_none(g, s);
        assert(f[f.len() - 1].0 >= s);
    }
}

/// `pre` is the end of chunk `i` when it is the last one starting below `s`.
proof fn lemma_pre_at(f: Seq<(nat, Seq<u8>)>, s: nat, i: int)
    requires
        0 <= i < f.len(),
        f[i].0 < s,
        forall|j: int| i < j < f.len() ==> #[trigger] f[j].0 >= s,
    ensures
        pre(f, s) == end(f[i]),
    decreases f.len(),
{
    let n = f.len() - 1;
    if i < n {
        let g = f.drop_last();
        assert(f[n].0 >= s);
        assert forall|j: int| i < j < g.len() implies #[trigger] g[j].0 >= s by {
            assert(g[j] == f[j]);
        }
        assert(g[i] == f[i]);
        lemma_pre_at(g, s, i);
    }
}

/// Chunks before the last one start below it.
proof fn lemma_below_last(f: Seq<(nat, Seq<u8>)>)
    requires
        ok(f),
        f.len() > 0,
    ensures
        forall|i: int| 0 <= i < f.drop_last().len() ==> #[trigger] f.drop_last()[i].0 < f.last().0,
{
    let g = f.drop_last();
    let n = f.len() - 1;
    assert forall|i: int| 0 <= i < g.len() implies #[trigger] g[i].0 < f.last().0 by {
        assert(g[i] == f[i]);
        assert(end(f[i]) <= f[n].0);
    }
}

/// A bound on `|M|` from the last start `l`: `min(l, e) - s + 1`, or 0 when that is below `s`.
spec fn bnd(f: Seq<(nat, Seq<u8>)>, s: nat, e: nat) -> nat {
    if f.len() == 0 {
        0
    } else {
        let m = if f.last().0 < e {
            f.last().0
        } else {
            e
        };
        if m >= s {
            (m - s + 1) as nat
        } else {
            0
        }
    }
}

/// `|M| <= e - s + 1`: starts strictly increase.
proof fn lemma_nm_le(f: Seq<(nat, Seq<u8>)>, s: nat, e: nat)
    requires
        ok(f),
    ensures
        nm(f, s, e) <= bnd(f, s, e),
    decreases f.len(),
{
    if f.len() > 0 {
        let g = f.drop_last();
        lemma_ok_drop(f);
        lemma_below_last(f);
        lemma_nm_le(g, s, e);
        if f.last().0 < s {
            assert forall|i: int| #![trigger g[i]] 0 <= i < g.len() implies !inr(g[i], s, e) by {}
            lemma_out(g, s, e, 0);
        }
        if g.len() > 0 {
            assert(g.last() == g[g.len() - 1]);
        }
    }
}

/// The chunk before the last (when the last is in `M`) ends where `lp` says.
proof fn lemma_lp_pre(f: Seq<(nat, Seq<u8>)>, s: nat, e: nat)
    requires
        ok(f),
        f.len() >= 2,
        s <= f.last().0 <= e,
    ensures
        lp(f.drop_last(), s, e, pre(f.drop_last(), s)) == end(f[f.len() - 2]),
{
    let g = f.drop_last();
    lemma_below_last(f);
    assert(g.last() == f[f.len() - 2]);
    assert(g.last().0 < f.last().0);
    if g.last().0 < s {
        lemma_ok_drop(f);
        lemma_below_last(g);
        let h = g.drop_last();
        assert forall|i: int| #![trigger h[i]] 0 <= i < h.len() implies !inr(h[i], s, e) by {}
        lemma_out(h, s, e, pre(g, s));
    }
}

// ---- Set lemmas: the counts after adding `[s, e)`.

/// `|pos(f) ∩ [s, e)|`: the chunk before `M`'s share and `M`'s.
proof fn lemma_meet(f: Seq<(nat, Seq<u8>)>, s: nat, e: nat)
    requires
        ok(f),
        s < e,
    ensures
        pos(f).intersect(Set::range(s, e)).len() == clip(pre(f, s), s, e) + cvf(f, s, e),
    decreases f.len(),
{
    let r = Set::range(s, e);
    if f.len() == 0 {
        lemma_pos_empty(f);
        assert(pos(f).intersect(r) =~= Set::<nat>::empty());
    } else {
        let g = f.drop_last();
        let c = f.last();
        lemma_pos_last(f);
        let lo2 = if c.0 < s {
            s
        } else {
            c.0
        };
        let hi2 = if end(c) < e {
            end(c)
        } else {
            e
        };
        let hi3 = if hi2 < lo2 {
            lo2
        } else {
            hi2
        };
        assert(Set::range(c.0, end(c)).intersect(r) =~= Set::range(lo2, hi3));
        assert(pos(f).intersect(r) =~= pos(g).intersect(r) + Set::range(lo2, hi3));
        assert(pos(g).intersect(r).disjoint(Set::range(lo2, hi3)));
        vstd::set_lib::lemma_set_disjoint_lens(pos(g).intersect(r), Set::range(lo2, hi3));
        if c.0 < s {
            lemma_below_last(f);
            assert forall|i: int| #![trigger g[i]] 0 <= i < g.len() implies !inr(g[i], s, e) by {}
            lemma_out(g, s, e, 0);
            assert(pos(g).intersect(r) =~= Set::<nat>::empty());
        } else {
            lemma_meet(g, s, e);
        }
    }
}

/// `s - 1` is held exactly when the chunk before `M` reaches `s`.
proof fn lemma_prev(f: Seq<(nat, Seq<u8>)>, s: nat)
    requires
        ok(f),
        s > 0,
    ensures
        pos(f).contains((s - 1) as nat) <==> pre(f, s) >= s,
    decreases f.len(),
{
    if f.len() == 0 {
        lemma_pos_empty(f);
    } else {
        lemma_pos_last(f);
        if f.last().0 >= s {
            lemma_prev(f.drop_last(), s);
        }
    }
}

/// The run starts in `[s, e]` are `M`'s heads.
proof fn lemma_ss(f: Seq<(nat, Seq<u8>)>, s: nat, e: nat)
    requires
        ok(f),
    ensures
        ss(starts(pos(f)), s, e).len() == hds(f, s, e, pre(f, s)),
    decreases f.len(),
{
    if f.len() == 0 {
        lemma_pos_empty(f);
        assert(ss(starts(pos(f)), s, e) =~= Set::<nat>::empty());
    } else {
        let n = f.len() - 1;
        let g = f.drop_last();
        let c = f.last();
        lemma_ok_drop(f);
        lemma_starts_last(f);
        lemma_ss(g, s, e);
        let a = ss(starts(pos(g)), s, e);
        if c.0 < s {
            lemma_below_last(f);
            assert forall|i: int| #![trigger f[i]] 0 <= i < f.len() implies !inr(f[i], s, e) by {
                if i < n {
                    assert(g[i] == f[i]);
                }
            }
            lemma_out(f, s, e, pre(f, s));
            assert forall|i: int| #![trigger g[i]] 0 <= i < g.len() implies !inr(g[i], s, e) by {}
            lemma_out(g, s, e, pre(g, s));
            assert(ss(starts(pos(f)), s, e) =~= a);
        } else {
            if inr(c, s, e) && n > 0 {
                lemma_lp_pre(f, s, e);
            }
            if inr(c, s, e) && !fol(f, n) {
                assert(ss(starts(pos(f)), s, e) =~= a.insert(c.0));
            } else {
                assert(ss(starts(pos(f)), s, e) =~= a);
            }
        }
    }
}

/// Adding `[s, e)` to `p`: run starts in `[s, e]` go, and `s` starts a run unless `s - 1` is held.
proof fn lemma_starts_q(p: Set<nat>, s: nat, e: nat)
    requires
        s < e,
    ensures
        starts(p + Set::range(s, e)) =~= so(starts(p), s, e) + xs(p, s),
{
    let q = p + Set::range(s, e);
    assert forall|x: nat| #[trigger] starts(q).contains(x) <==> (so(starts(p), s, e) + xs(p, s)).contains(x) by {
        if x > 0 && (x < s || x > e) {
            assert(q.contains((x - 1) as nat) <==> p.contains((x - 1) as nat));
        }
        if s < x <= e {
            assert(q.contains((x - 1) as nat));
        }
        if x == s && s > 0 {
            assert(q.contains((s - 1) as nat) <==> p.contains((s - 1) as nat));
        }
    }
}

/// Runs after adding `[s, e)` to `p`.
proof fn lemma_runs_q(p: Set<nat>, s: nat, e: nat)
    requires
        s < e,
    ensures
        runs(p + Set::range(s, e)) + ss(starts(p), s, e).len() == runs(p) + xs(p, s).len(),
        ss(starts(p), s, e).len() <= runs(p),
{
    lemma_starts_q(p, s, e);
    let a = ss(starts(p), s, e);
    let b = so(starts(p), s, e);
    assert(starts(p) =~= a + b);
    assert(a.disjoint(b));
    vstd::set_lib::lemma_set_disjoint_lens(a, b);
    assert(b.disjoint(xs(p, s)));
    vstd::set_lib::lemma_set_disjoint_lens(b, xs(p, s));
}

/// `after_insert`'s counts from the walk's: held and runs after adding `[s, e)`.
proof fn lemma_after(f: Seq<(nat, Seq<u8>)>, s: nat, e: nat)
    requires
        ok(f),
        s < e,
    ensures
        clip(pre(f, s), s, e) + cvf(f, s, e) <= e - s,
        (pos(f) + Set::range(s, e)).len() + clip(pre(f, s), s, e) + cvf(f, s, e) == pos(f).len() + (e - s),
        hds(f, s, e, pre(f, s)) <= runs(pos(f)),
        runs(pos(f) + Set::range(s, e)) + hds(f, s, e, pre(f, s)) == runs(pos(f)) + if pre(f, s) >= s {
            0nat
        } else {
            1nat
        },
{
    let p = pos(f);
    let r = Set::range(s, e);
    lemma_meet(f, s, e);
    vstd::set_lib::lemma_len_subset(p.intersect(r), r);
    vstd::set_lib::lemma_set_intersect_union_lens(p, r);
    lemma_ss(f, s, e);
    lemma_runs_q(p, s, e);
    if s == 0 {
        lemma_pre_none(f, s);
    } else {
        lemma_prev(f, s);
    }
}

// ---- The walk over the tree.

/// `M`'s count in the tree.
spec fn nmt(t: Tree<Vec<u8>>, s: u64, e: u64) -> nat {
    nm(mp(seq(t)), s as nat, e as nat)
}

/// Every key of `t` is at most `e`.
spec fn all_le(t: Tree<Vec<u8>>, e: u64) -> bool {
    forall|i: int| 0 <= i < seq(t).len() ==> #[trigger] seq(t)[i].0 <= e
}

/// Every key of `t` is at least `s`.
spec fn all_ge(t: Tree<Vec<u8>>, s: u64) -> bool {
    forall|i: int| 0 <= i < seq(t).len() ==> #[trigger] seq(t)[i].0 >= s
}

/// Every chunk ends by `VARINT_MAX`.
spec fn eok(f: Seq<(nat, Seq<u8>)>) -> bool {
    forall|i: int| 0 <= i < f.len() ==> #[trigger] end(f[i]) <= VARINT_MAX
}

/// `-1` for no chunk, else its end.
spec fn pi(pe: Option<u64>) -> int {
    match pe {
        Some(x) => x as int,
        None => -1,
    }
}

/// The calls `walk` makes on `t`: one per node it visits and one per empty child it reaches.
spec fn vis(t: Tree<Vec<u8>>, s: u64, e: u64) -> nat
    decreases t,
{
    match t {
        None => 1,
        Some(b) => if b.key < s {
            1 + vis(b.right, s, e)
        } else if b.key > e {
            1 + vis(b.left, s, e)
        } else {
            1 + vis(b.left, s, e) + vis(b.right, s, e)
        },
    }
}

/// A node's chunks: its left subtree's, its own, its right subtree's.
proof fn lemma_mp_node(t: Tree<Vec<u8>>)
    requires
        t is Some,
    ensures
        mp(seq(t)) == mp(seq(t->0.left)) + seq![(t->0.key as nat, t->0.val@)] + mp(seq(t->0.right)),
{
    let b = t->0;
    let (l, r) = (mp(seq(b.left)), mp(seq(b.right)));
    let x = (b.key as nat, b.val@);
    lemma_seq_node(t);
    let n = l.len() as int;
    assert forall|i: int| 0 <= i < mp(seq(t)).len() implies #[trigger] mp(seq(t))[i] == (l + seq![x] + r)[i] by {
        if i < n {
            assert(seq(t)[i] == seq(b.left)[i]);
        } else if i > n {
            assert(seq(t)[i] == seq(b.right)[i - n - 1]);
        }
    }
    assert(mp(seq(t)) =~= l + seq![x] + r);
}

/// The walk's sums at a node.
proof fn lemma_walk_node(t: Tree<Vec<u8>>, s: nat, e: nat, pe: int)
    requires
        t is Some,
    ensures
        ({
            let b = t->0;
            let (l, r) = (mp(seq(b.left)), mp(seq(b.right)));
            let x = (b.key as nat, b.val@);
            let m = if inr(x, s, e) {
                end(x) as int
            } else {
                lp(l, s, e, pe)
            };
            &&& nm(mp(seq(t)), s, e) == nm(l, s, e) + (if inr(x, s, e) {
                1nat
            } else {
                0
            }) + nm(r, s, e)
            &&& cvf(mp(seq(t)), s, e) == cvf(l, s, e) + (if inr(x, s, e) {
                cut(x, e)
            } else {
                0
            }) + cvf(r, s, e)
            &&& hds(mp(seq(t)), s, e, pe) == hds(l, s, e, pe) + (if inr(x, s, e) && lp(l, s, e, pe) != x.0 {
                1nat
            } else {
                0
            }) + hds(r, s, e, m)
            &&& lp(mp(seq(t)), s, e, pe) == lp(r, s, e, m)
            &&& (eok(mp(seq(t))) ==> eok(l) && eok(r) && end(x) <= VARINT_MAX)
        }),
{
    let b = t->0;
    let (l, r) = (mp(seq(b.left)), mp(seq(b.right)));
    let x = (b.key as nat, b.val@);
    let lx = l + seq![x];
    lemma_mp_node(t);
    lemma_cat(lx, r, s, e, pe);
    lemma_cat(l, seq![x], s, e, pe);
    let q = lp(l, s, e, pe);
    let o = seq![x].drop_last();
    assert(o =~= Seq::<(nat, Seq<u8>)>::empty());
    assert(seq![x].last() == x);
    assert(lp(o, s, e, q) == q && hds(o, s, e, q) == 0 && nm(o, s, e) == 0 && cvf(o, s, e) == 0);
    let f = mp(seq(t));
    if eok(f) {
        let n = l.len() as int;
        assert(f[n] == x);
        assert forall|i: int| 0 <= i < l.len() implies #[trigger] end(l[i]) <= VARINT_MAX by {
            assert(f[i] == l[i]);
        }
        assert forall|i: int| 0 <= i < r.len() implies #[trigger] end(r[i]) <= VARINT_MAX by {
            assert(f[n + 1 + i] == r[i]);
        }
    }
}

/// A subtree with no key in `[s, e]` adds nothing to the walk's sums.
proof fn lemma_walk_skip(t: Tree<Vec<u8>>, s: u64, e: u64, pe: int, pr: int)
    requires
        crate::avl::wf(t),
        t is Some,
    ensures
        t->0.key < s ==> nm(mp(seq(t->0.left)), s as nat, e as nat) == 0 && cvf(mp(seq(t->0.left)), s as nat, e as nat)
            == 0 && hds(mp(seq(t->0.left)), s as nat, e as nat, pe) == 0 && lp(mp(seq(t->0.left)), s as nat, e as nat, pe)
            == pe,
        t->0.key > e ==> nm(mp(seq(t->0.right)), s as nat, e as nat) == 0 && cvf(mp(seq(t->0.right)), s as nat, e as nat)
            == 0 && hds(mp(seq(t->0.right)), s as nat, e as nat, pr) == 0 && lp(mp(seq(t->0.right)), s as nat, e as nat, pr)
            == pr,
{
    let b = t->0;
    let (l, r) = (mp(seq(b.left)), mp(seq(b.right)));
    assert(keys_lt(b.left, b.key) && keys_gt(b.right, b.key));
    if b.key < s {
        assert forall|i: int| #![trigger l[i]] 0 <= i < l.len() implies !inr(l[i], s as nat, e as nat) by {
            assert(l[i].0 == seq(b.left)[i].0);
        }
        lemma_out(l, s as nat, e as nat, pe);
    }
    if b.key > e {
        assert forall|i: int| #![trigger r[i]] 0 <= i < r.len() implies !inr(r[i], s as nat, e as nat) by {
            assert(r[i].0 == seq(b.right)[i].0);
        }
        lemma_out(r, s as nat, e as nat, pr);
    }
}

/// Range and height facts passed from a node to its subtrees.
proof fn lemma_sub(t: Tree<Vec<u8>>, s: u64, e: u64)
    requires
        crate::avl::wf(t),
        t is Some,
    ensures
        ({
            let b = t->0;
            &&& crate::avl::wf(b.left) && crate::avl::wf(b.right)
            &&& ht(b.left) + 1 <= ht(t) && ht(b.right) + 1 <= ht(t)
            &&& all_le(t, e) ==> all_le(b.left, e) && all_le(b.right, e) && b.key <= e
            &&& all_ge(t, s) ==> all_ge(b.left, s) && all_ge(b.right, s) && b.key >= s
            &&& b.key <= e ==> all_le(b.left, e)
            &&& b.key >= s ==> all_ge(b.right, s)
            &&& nmt(t, s, e) == nmt(b.left, s, e) + (if s <= b.key <= e {
                1nat
            } else {
                0
            }) + nmt(b.right, s, e)
        }),
{
    let b = t->0;
    let (l, r) = (seq(b.left), seq(b.right));
    let n = l.len() as int;
    assert(crate::avl::wf(b.left) && crate::avl::wf(b.right));
    assert(keys_lt(b.left, b.key) && keys_gt(b.right, b.key));
    lemma_seq_node(t);
    lemma_walk_node(t, s as nat, e as nat, 0);
    assert(seq(t)[n] == (b.key, b.val));
    if all_le(t, e) {
        assert(seq(t)[n].0 <= e);
        assert forall|i: int| 0 <= i < l.len() implies #[trigger] l[i].0 <= e by {
            assert(seq(t)[i] == l[i]);
        }
        assert forall|i: int| 0 <= i < r.len() implies #[trigger] r[i].0 <= e by {
            assert(seq(t)[n + 1 + i] == r[i]);
        }
    }
    if all_ge(t, s) {
        assert(seq(t)[n].0 >= s);
        assert forall|i: int| 0 <= i < l.len() implies #[trigger] l[i].0 >= s by {
            assert(seq(t)[i] == l[i]);
        }
        assert forall|i: int| 0 <= i < r.len() implies #[trigger] r[i].0 >= s by {
            assert(seq(t)[n + 1 + i] == r[i]);
        }
    }
}

/// A walk over keys all in `[s, e]` reaches every node and empty child.
proof fn lemma_vis_full(t: Tree<Vec<u8>>, s: u64, e: u64)
    requires
        crate::avl::wf(t),
        all_ge(t, s),
        all_le(t, e),
    ensures
        vis(t, s, e) <= 2 * nmt(t, s, e) + 1,
    decreases t,
{
    if let Some(b) = t {
        lemma_sub(t, s, e);
        lemma_vis_full(b.left, s, e);
        lemma_vis_full(b.right, s, e);
    }
}

/// A walk bounded only below (keys all at most `e`): `M`'s nodes, their children, and one path.
proof fn lemma_vis_lo(t: Tree<Vec<u8>>, s: u64, e: u64)
    requires
        crate::avl::wf(t),
        all_le(t, e),
    ensures
        vis(t, s, e) <= 2 * nmt(t, s, e) + ht(t) + 1,
    decreases t,
{
    if let Some(b) = t {
        lemma_sub(t, s, e);
        if b.key < s {
            lemma_vis_lo(b.right, s, e);
        } else {
            lemma_vis_lo(b.left, s, e);
            lemma_vis_full(b.right, s, e);
        }
    }
}

/// A walk bounded only above (keys all at least `s`).
proof fn lemma_vis_hi(t: Tree<Vec<u8>>, s: u64, e: u64)
    requires
        crate::avl::wf(t),
        all_ge(t, s),
    ensures
        vis(t, s, e) <= 2 * nmt(t, s, e) + ht(t) + 1,
    decreases t,
{
    if let Some(b) = t {
        lemma_sub(t, s, e);
        if b.key > e {
            lemma_vis_hi(b.left, s, e);
        } else {
            lemma_vis_full(b.left, s, e);
            lemma_vis_hi(b.right, s, e);
        }
    }
}

/// The walk's visit bound: one path down to the first key in `[s, e]`, then two one-sided walks.
proof fn lemma_vis(t: Tree<Vec<u8>>, s: u64, e: u64)
    requires
        crate::avl::wf(t),
    ensures
        vis(t, s, e) <= 2 * nmt(t, s, e) + 2 * ht(t) + 2,
    decreases t,
{
    if let Some(b) = t {
        lemma_sub(t, s, e);
        if b.key < s {
            lemma_vis(b.right, s, e);
        } else if b.key > e {
            lemma_vis(b.left, s, e);
        } else {
            lemma_vis_lo(b.left, s, e);
            lemma_vis_hi(b.right, s, e);
        }
    }
}

/// The in-order walk over the chunks starting in `[s, e]`, entering a subtree only if it can hold one: their
/// clipped bytes below `e`, their heads (`pe` ends the chunk before the first), and the last one's end.
fn walk(t: &Tree<Vec<u8>>, s: u64, e: u64, pe: Option<u64>) -> (r: (u64, usize, Option<u64>, Ghost<nat>))
    requires
        crate::avl::wf(*t),
        eok(mp(seq(*t))),
        cvf(mp(seq(*t)), s as nat, e as nat) <= u64::MAX,
        hds(mp(seq(*t)), s as nat, e as nat, pi(pe)) <= usize::MAX,
    ensures
        r.0 == cvf(mp(seq(*t)), s as nat, e as nat),
        r.1 == hds(mp(seq(*t)), s as nat, e as nat, pi(pe)),
        pi(r.2) == lp(mp(seq(*t)), s as nat, e as nat, pi(pe)),
        r.3@ == vis(*t, s, e),
        r.3@ <= 2 * nmt(*t, s, e) + 2 * ht(*t) + 2,
    decreases *t,
{
    proof {
        lemma_vis(*t, s, e);
    }
    let ghost mut work: nat = 1;
    match t {
        None => (0, 0, pe, Ghost(work)),
        Some(b) => {
            proof {
                assert(crate::avl::wf(b.left) && crate::avl::wf(b.right));
                lemma_walk_node(*t, s as nat, e as nat, pi(pe));
                lemma_walk_skip(*t, s, e, pi(pe), lp(mp(seq(b.left)), s as nat, e as nat, pi(pe)));
            }
            if b.key < s {
                let (c, h, p, Ghost(w)) = walk(&b.right, s, e, pe);
                proof {
                    work = work + w;
                }
                (c, h, p, Ghost(work))
            } else if b.key > e {
                let (c, h, p, Ghost(w)) = walk(&b.left, s, e, pe);
                proof {
                    work = work + w;
                }
                (c, h, p, Ghost(work))
            } else {
                let (c1, h1, p1, Ghost(w1)) = walk(&b.left, s, e, pe);
                let len = b.val.len() as u64;
                let en = b.key + len;
                let c2 = if en < e {
                    len
                } else {
                    e - b.key
                };
                let h2: usize = match p1 {
                    Some(x) => if x == b.key {
                        0
                    } else {
                        1
                    },
                    None => 1,
                };
                let (c3, h3, p3, Ghost(w3)) = walk(&b.right, s, e, Some(en));
                proof {
                    work = work + w1 + w3;
                }
                (c1 + c2 + c3, h1 + h2 + h3, p3, Ghost(work))
            }
        },
    }
}

/// The sparse store, as chunks.
pub struct Chunks {
    t: Tree<Vec<u8>>,
    held: u64,
    count: usize,
    hi: u64,
}

impl Chunks {
    spec fn fs(&self) -> Seq<(nat, Seq<u8>)> {
        mp(seq(self.t))
    }

    /// The bytes held, by position.
    pub closed spec fn view(&self) -> Map<nat, u8> {
        vw(self.fs())
    }

    pub closed spec fn held_spec(&self) -> u64 {
        self.held
    }

    pub closed spec fn count_spec(&self) -> usize {
        self.count
    }

    /// The end of the last chunk, 0 with none.
    pub closed spec fn hi_spec(&self) -> nat {
        hi_of(self.fs())
    }

    /// A wf AVL of chunks (`ok`); `held` is the number of bytes they hold, which is their total length; `count`
    /// is the number of maximal runs of positions held; `hi` is the end of the last chunk.
    pub closed spec fn wf(&self) -> bool {
        &&& crate::avl::wf(self.t)
        &&& ok(self.fs())
        &&& self.held == sum_len(self.fs())
        &&& self.held == self.view().dom().len()
        &&& self.count == runs(self.view().dom())
        &&& self.hi == hi_of(self.fs())
    }

    /// `|M|` for a frame: the chunks starting in `[max(lo, off), off + d.len()]`.
    spec fn m_len(&self, lo: u64, off: u64, d: Seq<u8>) -> nat {
        nm(self.fs(), if lo >= off { lo as nat } else { off as nat }, (off + d.len()) as nat)
    }

    /// Every chunk but a run's first is a follower of at least `K` bytes.
    proof fn lemma_followers(&self)
        requires
            self.wf(),
        ensures
            K * (self.fs().len() - self.count) <= self.held,
    {
        lemma_k(self.fs());
    }

    /// `|M| <= d + 1`: the chunks of `M` start at distinct positions of `[s, e]`.
    proof fn lemma_m_le(&self, lo: u64, off: u64, d: Seq<u8>)
        requires
            self.wf(),
        ensures
            self.m_len(lo, off, d) <= d.len() + 1,
    {
        let s: nat = if lo >= off { lo as nat } else { off as nat };
        lemma_nm_le(self.fs(), s, (off + d.len()) as nat);
    }

    pub fn new() -> (r: Chunks)
        ensures
            r.wf(),
            r.view() == Map::<nat, u8>::empty(),
            r.held() == 0,
            r.count() == 0,
    {
        let r = Chunks { t: None, held: 0, count: 0, hi: 0 };
        proof {
            assert(r.fs() =~= Seq::<(nat, Seq<u8>)>::empty());
            lemma_pos_empty(r.fs());
            assert(r.view() =~= Map::<nat, u8>::empty());
        }
        r
    }

    #[verifier::when_used_as_spec(held_spec)]
    pub fn held(&self) -> (r: u64)
        ensures
            r == self.held_spec(),
    {
        self.held
    }

    #[verifier::when_used_as_spec(count_spec)]
    pub fn count(&self) -> (r: usize)
        ensures
            r == self.count_spec(),
    {
        self.count
    }

    /// The end of the last chunk, 0 with none.
    pub fn hi(&self) -> (r: u64)
        requires
            self.wf(),
        ensures
            r == self.hi_spec(),
    {
        self.hi
    }

    /// The end of the last chunk starting below `s` (`pre`), and `get_le`'s cost.
    fn pred(&self, s: u64) -> (r: (Option<u64>, Ghost<nat>))
        requires
            self.wf(),
        ensures
            pi(r.0) == pre(self.fs(), s as nat),
            r.1@ <= ht(self.t) + 1,
    {
        let ghost f = self.fs();
        if s == 0 {
            proof {
                lemma_pre_none(f, 0);
            }
            return (None, Ghost(0));
        }
        let (g, Ghost(c)) = get_le(&self.t, s - 1);
        match g {
            Some((k, v)) => {
                proof {
                    let i = choose|i: int| #[trigger] last_le(seq(self.t), (s - 1) as u64, i, k, *v);
                    assert(f[i] == (k as nat, v@));
                    assert forall|j: int| i < j < f.len() implies #[trigger] f[j].0 >= s by {
                        assert(f[j].0 == seq(self.t)[j].0);
                    }
                    lemma_pre_at(f, s as nat, i);
                }
                (Some(k + v.len() as u64), Ghost(c))
            },
            None => {
                proof {
                    assert forall|j: int| 0 <= j < f.len() implies #[trigger] f[j].0 >= s by {
                        assert(f[j].0 == seq(self.t)[j].0);
                    }
                    lemma_pre_none(f, s as nat);
                }
                (None, Ghost(c))
            },
        }
    }

    /// The `(held, count)` that `insert(lo, off, data)` would give, `self` unchanged, and the walk's cost.
    fn after_insert_w(&self, lo: u64, off: u64, data: &[u8]) -> (r: ((u64, usize), Ghost<nat>))
        requires
            self.wf(),
            off + data@.len() <= VARINT_MAX,
        ensures
            r.0.0 == put(self.view(), lo as nat, off as nat, data@).dom().len(),
            r.0.1 == runs(put(self.view(), lo as nat, off as nat, data@).dom()),
            r.1@ <= c_walk() * (2 * (ht(self.t) + 1) + self.m_len(lo, off, data@) + 2),
    {
        let ghost mut work: nat = 1;
        let ghost f = self.fs();
        let s = if lo >= off { lo } else { off };
        let e = off + data.len() as u64;
        if s >= e {
            proof {
                assert(put(self.view(), lo as nat, off as nat, data@).dom() =~= self.view().dom());
            }
            return ((self.held, self.count), Ghost(work));
        }
        let (pe, Ghost(c0)) = self.pred(s);
        proof {
            work = work + c0;
            self.lemma_counts(s as nat, e as nat);
        }
        let (cov, hd, _p, Ghost(c1)) = walk(&self.t, s, e, pe);
        let ov: u64 = match pe {
            Some(x) => if x > s {
                (if x < e {
                    x
                } else {
                    e
                }) - s
            } else {
                0
            },
            None => 0,
        };
        let nx: usize = match pe {
            Some(x) => if x >= s {
                0
            } else {
                1
            },
            None => 1,
        };
        proof {
            work = work + c1;
            assert(put(self.view(), lo as nat, off as nat, data@).dom() =~= pos(f) + Set::range(s as nat, e as nat));
        }
        ((self.held + ((e - s) - ov - cov), self.count - hd + nx), Ghost(work))
    }

    /// `lemma_after` on the store, with the walk's preconditions.
    proof fn lemma_counts(&self, s: nat, e: nat)
        requires
            self.wf(),
            s < e <= VARINT_MAX,
        ensures
            ({
                let f = self.fs();
                let p = pre(f, s);
                &&& clip(p, s, e) + cvf(f, s, e) <= e - s
                &&& (pos(f) + Set::range(s, e)).len() + clip(p, s, e) + cvf(f, s, e) == self.held + (e - s)
                &&& hds(f, s, e, p) <= self.count
                &&& runs(pos(f) + Set::range(s, e)) + hds(f, s, e, p) == self.count + if p >= s {
                    0nat
                } else {
                    1nat
                }
                &&& self.held <= VARINT_MAX
                &&& self.count <= VARINT_MAX
                &&& eok(f)
            }),
    {
        let f = self.fs();
        lemma_after(f, s, e);
        vstd::set_lib::lemma_len_subset(pos(f), Set::range(0, VARINT_MAX as nat));
        lemma_runs_le_len(pos(f));
        assert(self.view().dom() =~= pos(f));
        assert forall|i: int| 0 <= i < f.len() implies #[trigger] end(f[i]) <= VARINT_MAX by {}
    }

    /// The `(held, count)` that `insert(lo, off, data)` would give, `self` unchanged.
    pub fn after_insert(&self, lo: u64, off: u64, data: &[u8]) -> (r: (u64, usize))
        requires
            self.wf(),
            off + data@.len() <= VARINT_MAX,
        ensures
            r.0 == put(self.view(), lo as nat, off as nat, data@).dom().len(),
            r.1 == runs(put(self.view(), lo as nat, off as nat, data@).dom()),
    {
        let (r, Ghost(c)) = self.after_insert_w(lo, off, data);
        proof {
            self.lemma_m_le(lo, off, data@);
            assert(c <= c_walk() * (2 * (ht(self.t) + 1) + data@.len() + 3));
        }
        r
    }
}

} // verus!
