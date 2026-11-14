//! A sparse byte store: chunks of at most `CAP` bytes in a verified AVL keyed by start, sorted and disjoint but
//! possibly adjacent, so its memory follows the bytes held, not the span of offsets they cover. A chunk starting where
//! the previous one ends (a follower) holds at least `K` bytes, so `K · (chunks − runs) <= held`. CRYPTO's
//! out-of-order data (RFC 9000 §7.5) lives here.
use crate::avl::*;
use byteq::capvec::CapVec;
use vstd::prelude::*;
// Used only in ghost code, which a plain `cargo build` erases.
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;
// Used only in ghost code, which a plain `cargo build` erases.
#[allow(unused_imports)]
use wire::varint::*;

verus! {

broadcast use vstd::set_lib::range_set_properties;

/// Position `p` starts a run of `s`: it is in `s` and its predecessor is not.
pub open spec fn run_start(s: Set<nat>, p: nat) -> bool {
    p == 0 || !s.contains((p - 1) as nat)
}

/// The first position of each maximal run of consecutive positions in `s`.
pub open spec fn starts(s: Set<nat>) -> Set<nat> {
    s.filter(|p: nat| run_start(s, p))
}

/// The number of maximal runs of consecutive positions in `s`.
pub open spec fn runs(s: Set<nat>) -> nat {
    starts(s).len()
}

/// `m` with the bytes of `d` at `off` added at each position at or past `lo` that `m` does not
/// hold: the first writer wins.
pub open spec fn put(m: Map<nat, u8>, lo: nat, off: nat, d: Seq<u8>) -> Map<nat, u8> {
    Map::new(
        m.dom() + Set::range(if lo >= off { lo } else { off }, off + d.len()),
        |k: nat|
            if m.contains_key(k) {
                m[k]
            } else {
                d[k - off]
            },
    )
}

/// A run never holds less than one position.
pub proof fn lemma_runs_le_len(s: Set<nat>)
    ensures
        runs(s) <= s.len(),
{
    assert(starts(s).subset_of(s));
    vstd::set_lib::lemma_len_subset(starts(s), s);
}

/// Cutting `s` below a position it does not hold creates no run.
pub proof fn lemma_runs_cut(s: Set<nat>, t: Set<nat>, r: nat)
    requires
        !s.contains(r),
        forall|k: nat| #[trigger] t.contains(k) <==> s.contains(k) && k > r,
    ensures
        runs(t) <= runs(s),
{
    assert forall|p: nat| #[trigger] starts(t).contains(p) implies starts(s).contains(p) by {
        if p > 0 && s.contains((p - 1) as nat) {
            assert(p - 1 == r || t.contains((p - 1) as nat));
        }
    }
    assert(starts(t).subset_of(starts(s)));
    vstd::set_lib::lemma_len_subset(starts(t), starts(s));
}

/// Chunk `i` of `f` holds position `k`.
pub(crate) open spec fn inf(f: Seq<(nat, Seq<u8>)>, i: int, k: nat) -> bool {
    0 <= i < f.len() && f[i].0 <= k < f[i].0 + f[i].1.len()
}

/// The positions the chunks hold.
pub(crate) open spec fn pos(f: Seq<(nat, Seq<u8>)>) -> Set<nat> {
    Set::range(0, VARINT_MAX as nat).filter(|k: nat| exists|i: int| inf(f, i, k))
}

/// The byte at `k`: that of the chunk holding it (the only one, under `ok`).
pub(crate) open spec fn at(f: Seq<(nat, Seq<u8>)>, k: nat) -> u8 {
    let i = choose|i: int| inf(f, i, k);
    f[i].1[k - f[i].0]
}

/// The bytes the chunks hold, by position.
pub(crate) open spec fn vw(f: Seq<(nat, Seq<u8>)>) -> Map<nat, u8> {
    Map::new(pos(f), |k: nat| at(f, k))
}

pub(crate) open spec fn sum_len(f: Seq<(nat, Seq<u8>)>) -> nat
    decreases f.len(),
{
    if f.len() == 0 {
        0
    } else {
        sum_len(f.drop_last()) + f.last().1.len()
    }
}

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
spec fn mp(s: Seq<(u64, CapVec<u8>)>) -> Seq<(nat, Seq<u8>)> {
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

/// The positions held number the chunks' total length.
proof fn lemma_len(f: Seq<(nat, Seq<u8>)>)
    requires
        ok(f),
    ensures
        pos(f).len() == sum_len(f),
    decreases f.len(),
{
    if f.len() == 0 {
        lemma_pos_empty(f);
    } else {
        let g = f.drop_last();
        let r = Set::range(f.last().0, end(f.last()));
        lemma_pos_last(f);
        lemma_len(g);
        assert(pos(g).disjoint(r));
        vstd::set_lib::lemma_set_disjoint_lens(pos(g), r);
    }
}

/// Every chunk holds a byte, and the first starts a run.
proof fn lemma_some(f: Seq<(nat, Seq<u8>)>)
    requires
        ok(f),
    ensures
        f.len() <= sum_len(f),
        f.len() > 0 ==> runs(pos(f)) > 0,
    decreases f.len(),
{
    if f.len() > 0 {
        let g = f.drop_last();
        lemma_ok_drop(f);
        lemma_some(g);
        lemma_starts_last(f);
        assert(f[f.len() - 1].1.len() > 0);
        if g.len() == 0 {
            lemma_pos_empty(g);
            assert(!fol(f, 0));
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
spec fn nmt(t: Tree<CapVec<u8>>, s: u64, e: u64) -> nat {
    nm(mp(seq(t)), s as nat, e as nat)
}

/// Every key of `t` is at most `e`.
spec fn all_le(t: Tree<CapVec<u8>>, e: u64) -> bool {
    forall|i: int| 0 <= i < seq(t).len() ==> #[trigger] seq(t)[i].0 <= e
}

/// Every key of `t` is at least `s`.
spec fn all_ge(t: Tree<CapVec<u8>>, s: u64) -> bool {
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

/// The calls `walk` makes on `t`: one per node it visits and one per empty child it reaches. It enters a subtree
/// only if it can hold a key in `[s, e]`.
spec fn vis(t: Tree<CapVec<u8>>, s: u64, e: u64) -> nat
    decreases t,
{
    match t {
        None => 1,
        Some(b) => if b.key < s {
            1 + vis(b.right, s, e)
        } else if b.key > e {
            1 + vis(b.left, s, e)
        } else {
            1 + (if b.key > s {
                vis(b.left, s, e)
            } else {
                0
            }) + (if b.key < e {
                vis(b.right, s, e)
            } else {
                0
            })
        },
    }
}

/// A node's chunks: its left subtree's, its own, its right subtree's.
proof fn lemma_mp_node(t: Tree<CapVec<u8>>)
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
proof fn lemma_walk_node(t: Tree<CapVec<u8>>, s: nat, e: nat, pe: int)
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
proof fn lemma_walk_skip(t: Tree<CapVec<u8>>, s: u64, e: u64, pe: int, pr: int)
    requires
        crate::avl::wf(t),
        t is Some,
    ensures
        t->0.key <= s ==> nm(mp(seq(t->0.left)), s as nat, e as nat) == 0 && cvf(mp(seq(t->0.left)), s as nat, e as nat)
            == 0 && hds(mp(seq(t->0.left)), s as nat, e as nat, pe) == 0 && lp(mp(seq(t->0.left)), s as nat, e as nat, pe)
            == pe,
        t->0.key >= e ==> nm(mp(seq(t->0.right)), s as nat, e as nat) == 0 && cvf(mp(seq(t->0.right)), s as nat, e as nat)
            == 0 && hds(mp(seq(t->0.right)), s as nat, e as nat, pr) == 0 && lp(mp(seq(t->0.right)), s as nat, e as nat, pr)
            == pr,
{
    let b = t->0;
    let (l, r) = (mp(seq(b.left)), mp(seq(b.right)));
    assert(keys_lt(b.left, b.key) && keys_gt(b.right, b.key));
    if b.key <= s {
        assert forall|i: int| #![trigger l[i]] 0 <= i < l.len() implies !inr(l[i], s as nat, e as nat) by {
            assert(l[i].0 == seq(b.left)[i].0);
        }
        lemma_out(l, s as nat, e as nat, pe);
    }
    if b.key >= e {
        assert forall|i: int| #![trigger r[i]] 0 <= i < r.len() implies !inr(r[i], s as nat, e as nat) by {
            assert(r[i].0 == seq(b.right)[i].0);
        }
        lemma_out(r, s as nat, e as nat, pr);
    }
}

/// Range and height facts passed from a node to its subtrees.
proof fn lemma_sub(t: Tree<CapVec<u8>>, s: u64, e: u64)
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
proof fn lemma_vis_full(t: Tree<CapVec<u8>>, s: u64, e: u64)
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
proof fn lemma_vis_lo(t: Tree<CapVec<u8>>, s: u64, e: u64)
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
proof fn lemma_vis_hi(t: Tree<CapVec<u8>>, s: u64, e: u64)
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
proof fn lemma_vis(t: Tree<CapVec<u8>>, s: u64, e: u64)
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
fn walk(t: &Tree<CapVec<u8>>, s: u64, e: u64, pe: Option<u64>) -> (r: (u64, usize, Option<u64>, Ghost<nat>))
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
                let (c1, h1, p1, Ghost(w1)) = if b.key > s {
                    walk(&b.left, s, e, pe)
                } else {
                    (0, 0, pe, Ghost(0))
                };
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
                proof {
                    lemma_walk_skip(*t, s, e, pi(pe), en as int);
                }
                let (c3, h3, p3, Ghost(w3)) = if b.key < e {
                    walk(&b.right, s, e, Some(en))
                } else {
                    (0, 0, Some(en), Ghost(0))
                };
                proof {
                    work = work + w1 + w3;
                }
                (c1 + c2 + c3, h1 + h2 + h3, p3, Ghost(work))
            }
        },
    }
}

/// The sparse store, as chunks.
pub struct Frags {
    t: Tree<CapVec<u8>>,
    held: u64,
    count: usize,
    hi: u64,
}

impl Frags {
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

    /// Spec "The bound": at most 16384 bytes held in at most 4096 runs (CryptoStream's caps) give at most
    /// `4096 + 128` chunks and height at most 25.
    proof fn lemma_caps_height(&self)
        requires
            self.wf(),
            self.held <= 16384,
            self.count <= 4096,
        ensures
            seq(self.t).len() <= 4096 + 128,
            ht(self.t) <= 25,
    {
        self.lemma_followers();
        self.lemma_size();
        lemma_height(self.t);
        lemma2_to64();
        let e = ht(self.t) / 2;
        if e > 13 {
            lemma_pow2_strictly_increases(13, e);
        }
    }

    /// The invariant, in terms of the accessors.
    pub proof fn lemma_wf(&self)
        requires
            self.wf(),
        ensures
            self.held() <= VARINT_MAX,
            self.hi_spec() <= VARINT_MAX,
            forall|k: nat| #[trigger] self.view().contains_key(k) ==> k < self.hi_spec(),
            self.count() > 0 ==> self.hi_spec() > 0 && self.view().contains_key(
                (self.hi_spec() - 1) as nat,
            ),
            self.count() == 0 ==> self.view().dom() =~= Set::<nat>::empty(),
            self.count() <= VARINT_MAX,
            self.held() == self.view().dom().len(),
            self.count() == runs(self.view().dom()),
    {
        let f = self.fs();
        assert(self.view().dom() =~= pos(f));
        lemma_runs_le_len(pos(f));
        vstd::set_lib::lemma_len_subset(pos(f), Set::range(0, VARINT_MAX as nat));
        lemma_some(f);
        if f.len() > 0 {
            lemma_pos_last(f);
            assert(f.last() == f[f.len() - 1]);
        } else {
            lemma_pos_empty(f);
        }
    }

    /// The chunk count is at most `held`, so it fits the AVL's `seq(t).len() < 2^63`.
    proof fn lemma_size(&self)
        requires
            self.wf(),
        ensures
            seq(self.t).len() == self.fs().len(),
            self.fs().len() <= self.held <= VARINT_MAX,
            self.fs().len() < pow2(63),
    {
        let f = self.fs();
        lemma_some(f);
        self.lemma_wf();
        vstd::arithmetic::power2::lemma2_to64_rest();
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

    pub fn new() -> (r: Frags)
        ensures
            r.wf(),
            r.view() == Map::<nat, u8>::empty(),
            r.held() == 0,
            r.count() == 0,
    {
        let r = Frags { t: None, held: 0, count: 0, hi: 0 };
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
            assert(c1 <= 2 * self.m_len(lo, off, data@) + 2 * ht(self.t) + 2);
            assert(work <= 2 * (2 * (ht(self.t) + 1) + self.m_len(lo, off, data@) + 2));
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

// ---- `insert` and `take_front`.

/// `insert`'s cost constants: at most `c_ins1() · (h + 1) · (d / K + 4) + c_ins2() · (d + 4K)`.
spec fn c_ins1() -> nat {
    28
}

spec fn c_ins2() -> nat {
    8
}

/// `take_front`'s: at most `c_tf1() · (h + 1) · (max / K + 3) + c_tf2() · (max + CAP)`.
spec fn c_tf1() -> nat {
    8
}

spec fn c_tf2() -> nat {
    10
}

/// A stored height is at most 126.
proof fn lemma_ht_le<V>(t: Tree<V>)
    requires
        crate::avl::wf(t),
    ensures
        ht(t) <= 126,
{
    if let Some(b) = t {
        assert(b.h <= 126);
    }
}

/// Under `ok` a position is in at most one chunk, whose byte `at` gives.
proof fn lemma_at_ok(f: Seq<(nat, Seq<u8>)>)
    requires
        ok(f),
    ensures
        forall|i: int, k: nat| #[trigger] inf(f, i, k) ==> pos(f).contains(k) && at(f, k) == f[i].1[k - f[i].0],
{
    assert forall|i: int, k: nat| #[trigger] inf(f, i, k) implies pos(f).contains(k) && at(f, k) == f[i].1[k
        - f[i].0] by {
        let t = choose|t: int| inf(f, t, k);
        if t < i {
            assert(end(f[t]) <= f[i].0);
        } else if t > i {
            assert(end(f[i]) <= f[t].0);
        }
        assert(end(f[i]) <= VARINT_MAX);
    }
}

/// A slice of chunks in order is in order.
proof fn lemma_ok_sub(f: Seq<(nat, Seq<u8>)>, a: int, b: int)
    requires
        ok(f),
        0 <= a <= b <= f.len(),
    ensures
        ok(f.subrange(a, b)),
{
    let g = f.subrange(a, b);
    assert forall|i: int| #![trigger g[i]] 0 <= i < g.len() implies 0 < g[i].1.len() <= CAP && end(g[i])
        <= VARINT_MAX by {
        assert(g[i] == f[a + i]);
    }
    assert forall|i: int, j: int| #![trigger g[i], g[j]] 0 <= i < j < g.len() implies end(g[i]) <= g[j].0 by {
        assert(g[i] == f[a + i] && g[j] == f[a + j]);
    }
    assert forall|i: int| #[trigger] fol(g, i) implies g[i].1.len() >= K by {
        assert(g[i] == f[a + i] && g[i - 1] == f[a + i - 1]);
        assert(fol(f, a + i));
    }
}

/// Both halves of chunks in order are in order.
proof fn lemma_ok_split(x: Seq<(nat, Seq<u8>)>, y: Seq<(nat, Seq<u8>)>)
    requires
        ok(x + y),
    ensures
        ok(x),
        ok(y),
{
    lemma_ok_sub(x + y, 0, x.len() as int);
    lemma_ok_sub(x + y, x.len() as int, (x + y).len() as int);
    assert((x + y).subrange(0, x.len() as int) =~= x);
    assert((x + y).subrange(x.len() as int, (x + y).len() as int) =~= y);
}

/// `lemma_ok_cat`'s first conjunct: every chunk of `a + b` is a non-empty chunk of at most `CAP` ending by
/// `VARINT_MAX`.
proof fn lemma_ok_cat_bounds(a: Seq<(nat, Seq<u8>)>, b: Seq<(nat, Seq<u8>)>)
    requires
        ok(a),
        ok(b),
    ensures
        forall|i: int| #![trigger (a + b)[i]] 0 <= i < (a + b).len() ==> 0 < (a + b)[i].1.len() <= CAP && end(
            (a + b)[i],
        ) <= VARINT_MAX,
{
    let g = a + b;
    let n = a.len() as int;
    assert forall|i: int| #![trigger g[i]] 0 <= i < g.len() implies 0 < g[i].1.len() <= CAP && end(g[i])
        <= VARINT_MAX by {
        if i < n {
            assert(g[i] == a[i]);
        } else {
            assert(g[i] == b[i - n]);
        }
    }
}

/// `lemma_ok_cat`'s second conjunct: the chunks of `a + b` are in order and disjoint.
proof fn lemma_ok_cat_order(a: Seq<(nat, Seq<u8>)>, b: Seq<(nat, Seq<u8>)>)
    requires
        ok(a),
        ok(b),
        a.len() > 0 && b.len() > 0 ==> end(a.last()) <= b[0].0,
    ensures
        forall|i: int, j: int| #![trigger (a + b)[i], (a + b)[j]] 0 <= i < j < (a + b).len() ==> end((a + b)[i]) <= (a
            + b)[j].0,
{
    let g = a + b;
    let n = a.len() as int;
    assert forall|i: int, j: int| #![trigger g[i], g[j]] 0 <= i < j < g.len() implies end(g[i]) <= g[j].0 by {
        if j < n {
            assert(g[i] == a[i] && g[j] == a[j]);
        } else if i >= n {
            assert(g[i] == b[i - n] && g[j] == b[j - n]);
        } else {
            assert(g[i] == a[i] && g[j] == b[j - n]);
            assert(a.last() == a[n - 1]);
            if i < n - 1 {
                assert(end(a[i]) <= a[n - 1].0);
            }
            if j > n {
                assert(end(b[0]) <= b[j - n].0);
            }
        }
    }
}

/// `lemma_ok_cat`'s third conjunct: every follower of `a + b` holds at least `K` bytes.
proof fn lemma_ok_cat_fol(a: Seq<(nat, Seq<u8>)>, b: Seq<(nat, Seq<u8>)>)
    requires
        ok(a),
        ok(b),
        a.len() > 0 && b.len() > 0 && end(a.last()) == b[0].0 ==> b[0].1.len() >= K,
    ensures
        forall|i: int| #[trigger] fol(a + b, i) ==> (a + b)[i].1.len() >= K,
{
    let g = a + b;
    let n = a.len() as int;
    assert forall|i: int| #[trigger] fol(g, i) implies g[i].1.len() >= K by {
        if i < n {
            assert(g[i] == a[i] && g[i - 1] == a[i - 1]);
            assert(fol(a, i));
        } else if i == n {
            assert(g[i] == b[0] && g[i - 1] == a[n - 1]);
            assert(a.last() == a[n - 1]);
        } else {
            assert(g[i] == b[i - n] && g[i - 1] == b[i - n - 1]);
            assert(fol(b, i - n));
        }
    }
}

/// Two runs of chunks in order, the second starting at or after the first's end (as a follower if there).
proof fn lemma_ok_cat(a: Seq<(nat, Seq<u8>)>, b: Seq<(nat, Seq<u8>)>)
    requires
        ok(a),
        ok(b),
        a.len() > 0 && b.len() > 0 ==> end(a.last()) <= b[0].0,
        a.len() > 0 && b.len() > 0 && end(a.last()) == b[0].0 ==> b[0].1.len() >= K,
    ensures
        ok(a + b),
{
    lemma_ok_cat_bounds(a, b);
    lemma_ok_cat_order(a, b);
    lemma_ok_cat_fol(a, b);
}

/// The positions of a concatenation.
proof fn lemma_pos_cat(a: Seq<(nat, Seq<u8>)>, b: Seq<(nat, Seq<u8>)>)
    ensures
        pos(a + b) == pos(a) + pos(b),
{
    let g = a + b;
    let n = a.len() as int;
    assert forall|k: nat| #[trigger] pos(g).contains(k) <==> (pos(a) + pos(b)).contains(k) by {
        if pos(g).contains(k) {
            let i = choose|i: int| inf(g, i, k);
            if i < n {
                assert(g[i] == a[i]);
                assert(inf(a, i, k));
            } else {
                assert(g[i] == b[i - n]);
                assert(inf(b, i - n, k));
            }
        }
        if pos(a).contains(k) {
            let i = choose|i: int| inf(a, i, k);
            assert(g[i] == a[i]);
            assert(inf(g, i, k));
        }
        if pos(b).contains(k) {
            let i = choose|i: int| inf(b, i, k);
            assert(g[n + i] == b[i]);
            assert(inf(g, n + i, k));
        }
    }
    assert(pos(g) =~= pos(a) + pos(b));
}

/// `mp` over a concatenation.
proof fn lemma_mp_cat(a: Seq<(u64, CapVec<u8>)>, b: Seq<(u64, CapVec<u8>)>)
    ensures
        mp(a + b) == mp(a) + mp(b),
{
    assert(mp(a + b) =~= mp(a) + mp(b));
}

/// The length of `t`'s first chunk if it starts at `r`, every key being at least `r`.
fn front_at(t: &Tree<CapVec<u8>>, r: u64) -> (res: (Option<usize>, Ghost<nat>))
    requires
        crate::avl::wf(*t),
        keys_ge(*t, r),
    ensures
        res.0 is Some <==> seq(*t).len() > 0 && seq(*t)[0].0 == r,
        res.0 is Some ==> res.0->0 == seq(*t)[0].1@.len(),
        res.0 is None ==> keys_gt(*t, r),
        res.1@ <= ht(*t) + 1,
{
    let (g, Ghost(c)) = get_le(t, r);
    match g {
        Some((_k, v)) => {
            proof {
                let i = choose|i: int| #[trigger] last_le(seq(*t), r, i, _k, *v);
                lemma_wf_sorted(*t);
                assert(seq(*t)[0].0 >= r);
                if i > 0 {
                    assert(seq(*t)[0].0 < seq(*t)[i].0);
                }
            }
            (Some(v.len()), Ghost(c))
        },
        None => {
            proof {
                if seq(*t).len() > 0 {
                    assert(seq(*t)[0].0 > r);
                }
            }
            (None, Ghost(c))
        },
    }
}

/// Removing a run `[end, r)` that starts `p` removes one run and `r - end` positions.
proof fn lemma_runs_front(p: Set<nat>, q: Set<nat>, st: nat, r: nat)
    requires
        st < r,
        forall|k: nat| #[trigger] p.contains(k) ==> k >= st,
        forall|k: nat| st <= k < r ==> #[trigger] p.contains(k),
        !p.contains(r),
        forall|k: nat| #[trigger] q.contains(k) <==> p.contains(k) && k > r,
    ensures
        runs(q) + 1 == runs(p),
        q.len() + (r - st) == p.len(),
{
    assert(q =~= p.filter(|k: nat| k > r));
    assert forall|x: nat| #[trigger] starts(p).contains(x) <==> starts(q).insert(st).contains(x) by {
        if x > 0 {
            if x > r {
                assert(p.contains((x - 1) as nat) <==> q.contains((x - 1) as nat));
            }
            if st < x < r {
                assert(p.contains((x - 1) as nat));
            }
        }
    }
    assert(starts(p) =~= starts(q).insert(st));
    assert(!starts(q).contains(st));
    assert(p =~= q + Set::range(st, r));
    assert(q.disjoint(Set::range(st, r)));
    vstd::set_lib::lemma_set_disjoint_lens(q, Set::range(st, r));
}

/// Removing `[st, r)` from the front of a run that goes on at `r` keeps the runs and removes `r - st` positions.
proof fn lemma_runs_mid(p: Set<nat>, q: Set<nat>, st: nat, r: nat)
    requires
        st < r,
        forall|k: nat| #[trigger] p.contains(k) ==> k >= st,
        forall|k: nat| st <= k < r ==> #[trigger] p.contains(k),
        p.contains(r),
        forall|k: nat| #[trigger] q.contains(k) <==> p.contains(k) && k >= r,
    ensures
        runs(q) == runs(p),
        q.len() + (r - st) == p.len(),
{
    assert(q =~= p.filter(|k: nat| k >= r));
    assert(starts(q).contains(r));
    assert(st > 0 ==> !p.contains((st - 1) as nat));
    assert(starts(p).contains(st));
    assert forall|x: nat| #[trigger] starts(p).contains(x) <==> starts(q).remove(r).insert(st).contains(x) by {
        if x > 0 {
            if x > r {
                assert(p.contains((x - 1) as nat) <==> q.contains((x - 1) as nat));
            }
            if st < x <= r {
                assert(p.contains((x - 1) as nat));
            }
        }
    }
    assert(starts(p) =~= starts(q).remove(r).insert(st));
    assert(!starts(q).remove(r).contains(st));
    assert(p =~= q + Set::range(st, r));
    assert(q.disjoint(Set::range(st, r)));
    vstd::set_lib::lemma_set_disjoint_lens(q, Set::range(st, r));
}

/// The positions and runs left after taking `[st, r)` from the front of `p` (`q`, the positions at or past `r`).
proof fn lemma_tf_post(p: Set<nat>, q: Set<nat>, st: nat, r: nat)
    requires
        st <= r,
        forall|k: nat| #[trigger] p.contains(k) ==> k >= st,
        forall|k: nat| st <= k < r ==> #[trigger] p.contains(k),
        forall|k: nat| #[trigger] q.contains(k) <==> p.contains(k) && k >= r,
    ensures
        q.len() + (r - st) == p.len(),
        runs(q) + (if st < r && !p.contains(r) {
            1nat
        } else {
            0
        }) == runs(p),
{
    if st == r {
        assert(q =~= p);
    } else if p.contains(r) {
        lemma_runs_mid(p, q, st, r);
    } else {
        lemma_runs_front(p, q, st, r);
    }
}

/// Taking chunks `[0, i)`, all ending by `r`, the rest starting at or past `r`: the rest hold the positions at or past
/// `r`, with their bytes.
proof fn lemma_take_rest(f: Seq<(nat, Seq<u8>)>, i: int, r: nat)
    requires
        ok(f),
        0 <= i <= f.len(),
        forall|j: int| 0 <= j < i ==> end(#[trigger] f[j]) <= r,
        forall|j: int| i <= j < f.len() ==> #[trigger] f[j].0 >= r,
    ensures
        ok(f.skip(i)),
        forall|k: nat| #[trigger] pos(f.skip(i)).contains(k) <==> pos(f).contains(k) && k >= r,
        forall|k: nat| #[trigger] pos(f.skip(i)).contains(k) ==> vw(f.skip(i))[k] == vw(f)[k],
{
    let g = f.skip(i);
    lemma_ok_sub(f, i, f.len() as int);
    assert(g =~= f.subrange(i, f.len() as int));
    lemma_at_ok(f);
    lemma_at_ok(g);
    assert forall|k: nat| #[trigger] pos(g).contains(k) <==> pos(f).contains(k) && k >= r by {
        if pos(g).contains(k) {
            let j = choose|j: int| inf(g, j, k);
            assert(g[j] == f[i + j]);
            assert(inf(f, i + j, k));
        }
        if pos(f).contains(k) && k >= r {
            let j = choose|j: int| inf(f, j, k);
            assert(j < i ==> end(f[j]) <= r);
            assert(g[j - i] == f[j]);
            assert(inf(g, j - i, k));
        }
    }
    assert forall|k: nat| #[trigger] pos(g).contains(k) implies vw(g)[k] == vw(f)[k] by {
        let j = choose|j: int| inf(g, j, k);
        assert(g[j] == f[i + j]);
        assert(inf(f, i + j, k));
    }
}

/// One step of `take_front_w`: the chunk popped at `r` is `f[i]`, which holds the view's bytes there; the rest
/// start at or past its end.
proof fn lemma_take_step(f: Seq<(nat, Seq<u8>)>, i: int, t: Tree<CapVec<u8>>, t2: Tree<CapVec<u8>>, k: u64, v: CapVec<u8>)
    requires
        ok(f),
        0 <= i < f.len(),
        mp(seq(t)) == f.skip(i),
        seq![(k, v)] + seq(t2) == seq(t),
    ensures
        f[i] == (k as nat, v@),
        end(f[i]) <= VARINT_MAX,
        i > 0 && end(f[i - 1]) == k ==> v@.len() >= K,
        mp(seq(t2)) == f.skip(i + 1),
        forall|j: int| 0 <= j < seq(t2).len() ==> #[trigger] seq(t2)[j].0 >= end(f[i]),
        forall|j: int| 0 <= j < v@.len() ==> #[trigger] v@[j] == vw(f)[(k + j) as nat],
        forall|j: int| 0 <= j < v@.len() ==> #[trigger] pos(f).contains((k + j) as nat),
{
    let a = mp(seq![(k, v)]);
    lemma_mp_cat(seq![(k, v)], seq(t2));
    assert(a =~= seq![(k as nat, v@)]);
    assert(mp(seq(t)) == a + mp(seq(t2)));
    assert(a.len() == 1);
    assert(f.skip(i).len() == 1 + mp(seq(t2)).len());
    assert(f.skip(i)[0] == f[i]);
    assert forall|j: int| 0 <= j < mp(seq(t2)).len() implies #[trigger] mp(seq(t2))[j] == f.skip(i + 1)[j] by {
        assert(mp(seq(t2))[j] == (a + mp(seq(t2)))[j + 1]);
        assert(f.skip(i)[j + 1] == f[i + 1 + j]);
    }
    assert(mp(seq(t2)) =~= f.skip(i + 1));
    assert forall|j: int| 0 <= j < seq(t2).len() implies #[trigger] seq(t2)[j].0 >= end(f[i]) by {
        assert(mp(seq(t2))[j] == f[i + 1 + j]);
    }
    if i > 0 {
        if end(f[i - 1]) == k {
            assert(fol(f, i));
        }
    }
    lemma_at_ok(f);
    assert forall|j: int| 0 <= j < v@.len() implies #[trigger] v@[j] == vw(f)[(k + j) as nat] by {
        assert(inf(f, i, (k + j) as nat));
    }
    assert forall|j: int| 0 <= j < v@.len() implies #[trigger] pos(f).contains((k + j) as nat) by {
        assert(inf(f, i, (k + j) as nat));
    }
}

/// The bytes `take_front_w` appends: `vv` continues `o1` with the view's bytes from `r0`.
proof fn lemma_take_out(o: Seq<u8>, o1: Seq<u8>, vv: Seq<u8>, f: Seq<(nat, Seq<u8>)>, st: nat, r0: nat)
    requires
        st <= r0,
        o1 == o + Seq::new((r0 - st) as nat, |j: int| vw(f)[(st + j) as nat]),
        forall|j: int| 0 <= j < vv.len() ==> #[trigger] vv[j] == vw(f)[(r0 + j) as nat],
    ensures
        o1 + vv == o + Seq::new((r0 + vv.len() - st) as nat, |j: int| vw(f)[(st + j) as nat]),
{
    let n = (r0 - st) as int;
    assert forall|j: int| 0 <= j < (o1 + vv).len() implies #[trigger] (o1 + vv)[j] == (o + Seq::new(
        (r0 + vv.len() - st) as nat,
        |j: int| vw(f)[(st + j) as nat],
    ))[j] by {
        if j >= o.len() + n {
            assert((o1 + vv)[j] == vv[j - o.len() - n]);
        }
    }
    assert(o1 + vv =~= o + Seq::new((r0 + vv.len() - st) as nat, |j: int| vw(f)[(st + j) as nat]));
}

/// After `take_run`: the store is `f.skip(i)`, the bytes `[st, r)` gone, every key left at or past `r`.
proof fn lemma_take_end(f: Seq<(nat, Seq<u8>)>, i: int, st: nat, r: u64, t: Tree<CapVec<u8>>)
    requires
        ok(f),
        0 <= i <= f.len(),
        mp(seq(t)) == f.skip(i),
        keys_ge(t, r),
        i == 0 ==> r == st,
        i > 0 ==> r == end(f[i - 1]),
        forall|k: nat| #[trigger] pos(f).contains(k) ==> k >= st,
    ensures
        ok(f.skip(i)),
        forall|k: nat| #[trigger] pos(f.skip(i)).contains(k) <==> pos(f).contains(k) && k >= r,
        forall|k: nat| #[trigger] pos(f.skip(i)).contains(k) ==> vw(f.skip(i))[k] == vw(f)[k],
        pos(f.skip(i)).len() == sum_len(f.skip(i)),
        f.skip(i).len() > 0 ==> f.skip(i).last() == f.last(),
        keys_gt(t, r) ==> !pos(f).contains(r as nat),
        seq(t).len() > 0 && seq(t)[0].0 == r ==> pos(f).contains(r as nat),
{
    assert forall|j: int| 0 <= j < i implies end(#[trigger] f[j]) <= r by {
        if j < i - 1 {
            assert(end(f[j]) <= f[i - 1].0);
        }
    }
    assert(mp(seq(t)).len() == seq(t).len());
    assert(f.skip(i).len() == f.len() - i);
    assert forall|j: int| i <= j < f.len() implies #[trigger] f[j].0 >= r by {
        assert(f.skip(i)[j - i] == f[j]);
        assert(mp(seq(t))[j - i] == f[j]);
        assert(seq(t)[j - i].0 >= r);
    }
    lemma_take_rest(f, i, r as nat);
    lemma_len(f.skip(i));
    if keys_gt(t, r) && pos(f).contains(r as nat) {
        assert(pos(f.skip(i)).contains(r as nat));
        let j = choose|j: int| inf(f.skip(i), j, r as nat);
        assert(f.skip(i)[j] == mp(seq(t))[j]);
        assert(seq(t)[j].0 > r);
    }
    if seq(t).len() > 0 && seq(t)[0].0 == r {
        assert(f.skip(i)[0] == f[i]);
        assert(mp(seq(t))[0] == f[i]);
        assert(inf(f, i, r as nat));
    }
}

// ---- The merged bytes (D3 steps 3-5).

/// The byte at `k` of the merged bytes: that of the chunk of `c` holding `k`, else the frame's.
spec fn src(c: Seq<(nat, Seq<u8>)>, d: Seq<u8>, off: nat, k: nat) -> u8 {
    if pos(c).contains(k) {
        at(c, k)
    } else {
        d[k - off]
    }
}

/// The cursor `ci` at position `q`: every chunk before it ends by `q`, and it does not.
spec fn cur(c: Seq<(nat, Seq<u8>)>, ci: int, q: nat) -> bool {
    &&& 0 <= ci <= c.len()
    &&& forall|j: int| 0 <= j < ci ==> end(#[trigger] c[j]) <= q
    &&& ci < c.len() ==> q < end(c[ci])
}

/// Every chunk of `f` starts at or after `a` and ends by `b`.
spec fn within(f: Seq<(nat, Seq<u8>)>, a: nat, b: nat) -> bool {
    forall|j: int| 0 <= j < f.len() ==> a <= #[trigger] f[j].0 && end(f[j]) <= b
}

/// Every chunk of `f` ends by `a`.
spec fn ends_le(f: Seq<(nat, Seq<u8>)>, a: nat) -> bool {
    forall|j: int| 0 <= j < f.len() ==> end(#[trigger] f[j]) <= a
}

/// Every chunk of `f` starts at or after `a`.
spec fn starts_ge(f: Seq<(nat, Seq<u8>)>, a: nat) -> bool {
    forall|j: int| 0 <= j < f.len() ==> #[trigger] f[j].0 >= a
}

/// Every position of `[a, b)` that `c` does not hold is in the frame's `[s, e)`.
spec fn cov(c: Seq<(nat, Seq<u8>)>, a: nat, b: nat, s: nat, e: nat) -> bool {
    forall|k: nat| a <= k < b && !#[trigger] pos(c).contains(k) ==> s <= k < e
}

/// Every position of `[s, e)` at or past `b` is held by `rest`.
spec fn cov2(rest: Seq<(nat, Seq<u8>)>, b: nat, s: nat, e: nat) -> bool {
    forall|k: nat| s <= k < e && k >= b ==> #[trigger] pos(rest).contains(k)
}

/// The first chunk of `rest`, if it starts at `b`, holds at least `K` bytes.
spec fn front_ok(rest: Seq<(nat, Seq<u8>)>, b: nat) -> bool {
    rest.len() > 0 && rest[0].0 == b ==> rest[0].1.len() >= K
}

/// A kept `Rc` as chunks.
spec fn zs(z: Option<(u64, CapVec<u8>)>) -> Seq<(nat, Seq<u8>)> {
    match z {
        Some(x) => seq![(x.0 as nat, x.1@)],
        None => Seq::empty(),
    }
}

/// The length of the next piece with `rem` merged bytes left: `CAP`, but the last two split evenly if the last would
/// hold fewer than `K`.
spec fn plen(rem: nat) -> nat {
    if rem <= CAP {
        rem
    } else if rem < CAP + K {
        rem / 2
    } else {
        CAP as nat
    }
}

/// The number of pieces of `x` bytes: `ceil(x / CAP)`.
spec fn npc(x: int) -> int {
    (x + CAP - 1) / (CAP as int)
}

/// `n` bytes from position `q` into a fresh `CapVec` of capacity `n`, by exactly `n` pushes: those of the chunk of `cl`
/// holding the position (`ci` the cursor), else `data`'s at `q - off`.
fn fill(cl: &Vec<(u64, CapVec<u8>)>, data: &[u8], off: u64, q: u64, n: u64, ci: usize) -> (r: (
    CapVec<u8>,
    usize,
    Ghost<nat>,
))
    requires
        ok(mp(cl@)),
        cur(mp(cl@), ci as int, q as nat),
        q + n <= VARINT_MAX,
        n <= CAP,
        forall|k: nat| q <= k < q + n && !#[trigger] pos(mp(cl@)).contains(k) ==> off <= k < off + data@.len(),
    ensures
        r.0@ == Seq::new(n as nat, |j: int| src(mp(cl@), data@, off as nat, (q + j) as nat)),
        cur(mp(cl@), r.1 as int, (q + n) as nat),
        r.2@ <= n + 1,
{
    let ghost c = mp(cl@);
    let ghost mut work: nat = 1;
    let mut v: CapVec<u8> = CapVec::new(n as usize);
    let mut j: u64 = 0;
    let mut ci = ci;
    proof {
        lemma_at_ok(c);
        assert(v@ =~= Seq::new(0, |i: int| src(c, data@, off as nat, (q + i) as nat)));
    }
    while j < n
        invariant
            ok(c),
            c == mp(cl@),
            j <= n,
            q + n <= VARINT_MAX,
            v.wf(),
            v.cap() == n,
            cur(c, ci as int, (q + j) as nat),
            v@ == Seq::new(j as nat, |i: int| src(c, data@, off as nat, (q + i) as nat)),
            forall|k: nat| q <= k < q + n && !#[trigger] pos(c).contains(k) ==> off <= k < off + data@.len(),
            forall|i: int, k: nat| #[trigger] inf(c, i, k) ==> pos(c).contains(k) && at(c, k) == c[i].1[k - c[i].0],
            work <= 1 + j,
        decreases n - j,
    {
        let p = q + j;
        let ghost v0 = v@;
        if ci < cl.len() && cl[ci].0 <= p {
            proof {
                assert(c[ci as int] == (cl@[ci as int].0 as nat, cl@[ci as int].1@));
                assert(inf(c, ci as int, p as nat));
                assert(end(c[ci as int]) <= VARINT_MAX);
            }
            let b = *cl[ci].1.index((p - cl[ci].0) as usize);
            v.push(b);
            if p + 1 == cl[ci].0 + cl[ci].1.len() as u64 {
                proof {
                    if ci + 1 < c.len() {
                        assert(end(c[ci as int]) <= c[ci + 1].0);
                    }
                }
                ci = ci + 1;
            }
        } else {
            proof {
                if pos(c).contains(p as nat) {
                    let i = choose|i: int| inf(c, i, p as nat);
                    if i > ci {
                        assert(end(c[ci as int]) <= c[i].0);
                    }
                    assert(false);
                }
            }
            v.push(data[(p - off) as usize]);
        }
        j = j + 1;
        proof {
            work = work + 1;
            assert(v@ =~= Seq::new(j as nat, |i: int| src(c, data@, off as nat, (q + i) as nat)));
        }
    }
    (v, ci, Ghost(work))
}

/// One piece: `ps` extended by the chunk `(q, v)` stays in order and covers `[s0, q + n)`.
proof fn lemma_piece(ps: Seq<(u64, CapVec<u8>)>, q: u64, v: CapVec<u8>, s0: nat)
    requires
        ok(mp(ps)),
        s0 <= q,
        pos(mp(ps)) == Set::range(s0, q as nat),
        ps.len() > 0 ==> end(mp(ps).last()) == q,
        ps.len() == 0 ==> q == s0,
        0 < v@.len() <= CAP,
        q + v@.len() <= VARINT_MAX,
        ps.len() > 0 ==> v@.len() >= K,
    ensures
        ok(mp(ps.push((q, v)))),
        pos(mp(ps.push((q, v)))) == Set::range(s0, (q + v@.len()) as nat),
        end(mp(ps.push((q, v))).last()) == q + v@.len(),
        mp(ps.push((q, v))) == mp(ps).push((q as nat, v@)),
{
    let a = mp(ps);
    let g = mp(ps.push((q, v)));
    assert(g =~= a.push((q as nat, v@)));
    assert(a.push((q as nat, v@)) == a + seq![(q as nat, v@)]);
    if a.len() > 0 {
        assert(a.last() == a[a.len() - 1]);
    }
    lemma_ok_cat(a, seq![(q as nat, v@)]);
    assert(g.drop_last() =~= a);
    assert(g.last() == (q as nat, v@));
    lemma_pos_last(g);
    assert(pos(g.drop_last()) == pos(a));
    assert(Set::range(s0, q as nat) + Set::range(q as nat, (q + v@.len()) as nat) =~= Set::range(
        s0,
        (q + v@.len()) as nat,
    ));
}

/// The pieces' lengths: each in `1..=CAP`, at least `K` when `rem >= K`, leaving 0 or at least `K`, and the count
/// left, `ceil(rem / CAP)`, drops by one.
proof fn lemma_plen(rem: nat)
    requires
        rem > 0,
    ensures
        0 < plen(rem) <= CAP,
        plen(rem) <= rem,
        rem >= K ==> plen(rem) >= K,
        rem - plen(rem) == 0 || rem - plen(rem) >= K,
        npc(rem - plen(rem)) + 1 == npc(rem as int),
{
}

/// The pieces `p` cut so far, up to `q`, of the merged bytes of `[s0, me2)`.
#[verifier::opaque]
spec fn pcs(p: Seq<(nat, Seq<u8>)>, s0: nat, q: nat, me2: nat, c: Seq<(nat, Seq<u8>)>, d: Seq<u8>, off: nat) -> bool {
    &&& ok(p)
    &&& pos(p) == Set::range(s0, q)
    &&& p.len() > 0 ==> p[0].0 == s0 && end(p.last()) == q
    &&& p.len() == 0 <==> q == s0
    &&& p.len() > 0 && q < me2 ==> me2 - q >= K
    &&& p.len() > 0 && me2 - s0 >= K ==> p[0].1.len() >= K
    &&& forall|i: int, k: nat| #[trigger] inf(p, i, k) ==> p[i].1[k - p[i].0] == src(c, d, off, k)
    &&& p.len() * K <= (q - s0) + K
    &&& p.len() + npc(me2 - q) == npc(me2 - s0)
}

/// No piece yet.
proof fn lemma_pcs_empty(s0: nat, me2: nat, c: Seq<(nat, Seq<u8>)>, d: Seq<u8>, off: nat)
    requires
        s0 < me2,
    ensures
        pcs(Seq::empty(), s0, s0, me2, c, d, off),
{
    reveal(pcs);
    lemma_pos_empty(Seq::<(nat, Seq<u8>)>::empty());
    assert(Set::range(s0, s0) =~= Set::<nat>::empty());
}

/// One more piece `(q, v)` of `plen(me2 - q)` merged bytes.
proof fn lemma_pcs_step(
    ps: Seq<(u64, CapVec<u8>)>,
    q: u64,
    v: CapVec<u8>,
    s0: nat,
    me2: nat,
    c: Seq<(nat, Seq<u8>)>,
    d: Seq<u8>,
    off: nat,
)
    requires
        pcs(mp(ps), s0, q as nat, me2, c, d, off),
        s0 <= q < me2 <= VARINT_MAX,
        v@.len() == plen((me2 - q) as nat),
        v@ == Seq::new(v@.len(), |j: int| src(c, d, off, (q + j) as nat)),
    ensures
        pcs(mp(ps.push((q, v))), s0, (q + v@.len()) as nat, me2, c, d, off),
{
    reveal(pcs);
    let p = mp(ps);
    let g = mp(ps.push((q, v)));
    lemma_plen((me2 - q) as nat);
    lemma_piece(ps, q, v, s0);
    assert forall|i: int, k: nat| #[trigger] inf(g, i, k) implies g[i].1[k - g[i].0] == src(c, d, off, k) by {
        if i < p.len() {
            assert(g[i] == p[i]);
            assert(inf(p, i, k));
        } else {
            assert(g[i] == (q as nat, v@));
            assert(v@[k - q] == src(c, d, off, (q + (k - q)) as nat));
        }
    }
    if p.len() > 0 {
        assert(g[0] == p[0]);
    }
}

/// All pieces cut: what `close_up` needs of them.
proof fn lemma_pcs_done(p: Seq<(nat, Seq<u8>)>, s0: nat, me2: nat, c: Seq<(nat, Seq<u8>)>, d: Seq<u8>, off: nat)
    requires
        pcs(p, s0, me2, me2, c, d, off),
        s0 < me2,
    ensures
        ok(p),
        p.len() > 0,
        p[0].0 == s0,
        end(p.last()) == me2,
        p.len() * K <= (me2 - s0) + K,
{
    reveal(pcs);
}

/// D3 step 5: the merged bytes of `[s0, me2)` (`cl`'s where a chunk of it holds them, else the frame's) cut into fresh
/// pieces of `plen` bytes, each a `CapVec` of exactly its capacity.
fn fill_all(cl: &Vec<(u64, CapVec<u8>)>, data: &[u8], off: u64, s0: u64, me2: u64, _s: u64, _e: u64) -> (r: (
    Vec<(u64, CapVec<u8>)>,
    Ghost<nat>,
))
    requires
        ok(mp(cl@)),
        within(mp(cl@), s0 as nat, me2 as nat),
        cov(mp(cl@), s0 as nat, me2 as nat, _s as nat, _e as nat),
        off <= _s,
        _e == off + data@.len(),
        s0 < me2 <= VARINT_MAX,
    ensures
        pcs(mp(r.0@), s0 as nat, me2 as nat, me2 as nat, mp(cl@), data@, off as nat),
        r.1@ <= (me2 - s0) + 2 * r.0@.len() + 1,
{
    let ghost c = mp(cl@);
    let ghost mut work: nat = 1;
    let mut ps: Vec<(u64, CapVec<u8>)> = Vec::with_capacity(((me2 - s0 + (CAP - 1)) / CAP) as usize);
    let mut q = s0;
    let mut ci: usize = 0;
    proof {
        assert(mp(ps@) =~= Seq::<(nat, Seq<u8>)>::empty());
        lemma_pcs_empty(s0 as nat, me2 as nat, c, data@, off as nat);
        if c.len() > 0 {
            assert(s0 <= c[0].0);
        }
    }
    while q < me2
        invariant
            ok(c),
            c == mp(cl@),
            within(c, s0 as nat, me2 as nat),
            cov(c, s0 as nat, me2 as nat, _s as nat, _e as nat),
            off <= _s,
            _e == off + data@.len(),
            s0 <= q <= me2 <= VARINT_MAX,
            pcs(mp(ps@), s0 as nat, q as nat, me2 as nat, c, data@, off as nat),
            cur(c, ci as int, q as nat),
            work <= 1 + (q - s0) + 2 * ps@.len(),
        decreases me2 - q,
    {
        let rem = me2 - q;
        let n = if rem <= CAP {
            rem
        } else if rem < CAP + K {
            rem / 2
        } else {
            CAP
        };
        proof {
            lemma_plen(rem as nat);
            assert(n == plen(rem as nat));
        }
        let (v, ci2, Ghost(cf)) = fill(cl, data, off, q, n, ci);
        proof {
            lemma_pcs_step(ps@, q, v, s0 as nat, me2 as nat, c, data@, off as nat);
        }
        ps.push((q, v));
        q = q + n;
        ci = ci2;
        proof {
            work = work + cf + 1;
        }
    }
    (ps, Ghost(work))
}

/// The number of entries of `t`, counted by a walk over every node.
fn size<V>(t: &Tree<V>) -> (r: (usize, Ghost<nat>))
    requires
        seq(*t).len() <= usize::MAX,
    ensures
        r.0 == seq(*t).len(),
        r.1@ <= 2 * seq(*t).len() + 1,
    decreases *t,
{
    let ghost mut work: nat = 1;
    match t {
        None => (0, Ghost(work)),
        Some(b) => {
            proof {
                lemma_seq_node(*t);
            }
            let (a, Ghost(ca)) = size(&b.left);
            let (c, Ghost(cc)) = size(&b.right);
            proof {
                work = work + ca + cc;
            }
            (a + 1 + c, Ghost(work))
        },
    }
}

/// The height of the balanced tree `build` makes of `n` entries.
spec fn hb(n: nat) -> nat
    decreases n,
{
    if n == 0 {
        0
    } else {
        1 + hb(n / 2)
    }
}

proof fn lemma_hb_mono(a: nat, b: nat)
    requires
        a <= b,
    ensures
        hb(a) <= hb(b),
    decreases a,
{
    if a > 0 {
        lemma_hb_mono(a / 2, b / 2);
    }
}

proof fn lemma_hb_succ(m: nat)
    ensures
        hb(m + 1) <= hb(m) + 1,
    decreases m,
{
    if m > 0 && (m + 1) / 2 != m / 2 {
        lemma_hb_succ(m / 2);
        assert((m + 1) / 2 == m / 2 + 1);
    }
}

proof fn lemma_hb_le(n: nat)
    ensures
        hb(n) <= n,
    decreases n,
{
    if n > 0 {
        lemma_hb_le(n / 2);
    }
}

proof fn lemma_hb_pow(n: nat, k: nat)
    requires
        n < pow2(k),
    ensures
        hb(n) <= k,
    decreases k,
{
    if n > 0 {
        if k == 0 {
            lemma2_to64();
        } else {
            lemma_pow2_unfold(k);
            lemma_hb_pow(n / 2, (k - 1) as nat);
        }
    }
}

/// `sorted` holds for a prefix.
proof fn lemma_sorted_take<V>(s: Seq<(u64, V)>, n: int)
    requires
        sorted(s),
        0 <= n <= s.len(),
    ensures
        sorted(s.take(n)),
{
    let t = s.take(n);
    assert forall|i: int, j: int| #![trigger t[i], t[j]] 0 <= i < j < t.len() implies t[i].0 < t[j].0 by {
        assert(t[i] == s[i] && t[j] == s[j]);
    }
}

/// The node `build` makes: its parts, ordered and balanced, form a wf tree of height `hb(n)`.
proof fn lemma_build_node(o: Seq<(u64, CapVec<u8>)>, n: nat, l: Tree<CapVec<u8>>, k: u64, x: CapVec<u8>, r: Tree<CapVec<u8>>)
    requires
        sorted(o),
        0 < n <= o.len(),
        crate::avl::wf(l),
        crate::avl::wf(r),
        seq(r) == o.skip(o.len() - n / 2),
        o[o.len() - n / 2 - 1] == (k, x),
        seq(l) == o.subrange(o.len() - n, o.len() - n / 2 - 1),
        ht(l) == hb((n - 1 - n / 2) as nat),
        ht(r) == hb(n / 2),
        n <= usize::MAX,
    ensures
        keys_lt(l, k),
        keys_gt(r, k),
        ht(l) <= ht(r) <= ht(l) + 1,
        ht(r) + 1 == hb(n),
        hb(n) <= 65,
        seq(l) + seq![(k, x)] + seq(r) == o.skip(o.len() - n),
{
    let m = o.len() as int;
    let nr = n / 2;
    let nl = (n - 1 - nr) as nat;
    lemma_hb_mono(nl, nr);
    lemma_hb_succ(nl);
    lemma_hb_mono(nr, nl + 1);
    lemma2_to64();
    lemma_hb_pow(n, 64);
    assert forall|i: int| 0 <= i < seq(l).len() implies #[trigger] seq(l)[i].0 < k by {
        assert(seq(l)[i] == o[m - n + i]);
    }
    assert forall|i: int| 0 <= i < seq(r).len() implies #[trigger] seq(r)[i].0 > k by {
        assert(seq(r)[i] == o[m - nr + i]);
    }
    assert(seq(l) + seq![(k, x)] + seq(r) =~= o.skip(m - n));
}

/// The last `n` entries of `v`, in order, as a perfectly balanced tree (height `hb(n)`), built node by node.
fn build(v: &mut Vec<(u64, CapVec<u8>)>, n: usize) -> (r: (Tree<CapVec<u8>>, Ghost<nat>))
    requires
        n <= old(v)@.len(),
        sorted(old(v)@),
    ensures
        final(v)@ == old(v)@.take(old(v)@.len() - n),
        seq(r.0) == old(v)@.skip(old(v)@.len() - n),
        crate::avl::wf(r.0),
        ht(r.0) == hb(n as nat),
        r.1@ <= 2 * n + 1,
    decreases n,
{
    let ghost o = v@;
    let ghost m = o.len() as int;
    let ghost mut work: nat = 1;
    if n == 0 {
        proof {
            assert(o.take(m) =~= o);
            assert(o.skip(m) =~= Seq::<(u64, CapVec<u8>)>::empty());
        }
        return (None, Ghost(work));
    }
    let nr = n / 2;
    let nl = n - 1 - nr;
    let (r, Ghost(cr)) = build(v, nr);
    proof {
        lemma_sorted_take(o, m - nr);
        assert(v@.len() == m - nr);
    }
    let (k, x) = v.pop().unwrap();
    proof {
        assert((k, x) == o[m - nr - 1]);
        assert(v@ =~= o.take(m - nr - 1));
        lemma_sorted_take(o, m - nr - 1);
    }
    let (l, Ghost(cl)) = build(v, nl);
    proof {
        assert(v@ =~= o.take(m - n));
        assert(o.take(m - nr - 1).skip(m - nr - 1 - nl) =~= o.subrange(m - n, m - nr - 1));
        lemma_build_node(o, n as nat, l, k, x, r);
    }
    let h = height(&r) + 1;
    let t = Some(Box::new(Node { key: k, val: x, h, left: l, right: r }));
    proof {
        assert(seq(t) == seq(l) + seq![(k, x)] + seq(r));
        work = work + cr + cl;
    }
    (t, Ghost(work))
}

/// D3 step 1 over the chunks `f` of `t`: `Lc`, the chunk holding or ending at `s`, if any. Returns whether it exists and
/// `s0`, its start (else `s`).
fn find_lc(t: &Tree<CapVec<u8>>, s: u64, _f: Ghost<Seq<(nat, Seq<u8>)>>) -> (r: (bool, u64, Ghost<nat>))
    requires
        crate::avl::wf(*t),
        ok(_f@),
        _f@ == mp(seq(*t)),
    ensures
        r.1 <= s,
        !r.0 ==> r.1 == s,
        r.0 ==> exists|j: int| 0 <= j < _f@.len() && #[trigger] _f@[j].0 == r.1 && end(_f@[j]) >= s,
        forall|j: int|
            0 <= j < _f@.len() && #[trigger] _f@[j].0 < r.1 ==> end(_f@[j]) <= r.1 && (end(_f@[j]) == r.1 ==> r.0),
        forall|j: int| 0 <= j < _f@.len() && #[trigger] _f@[j].0 >= r.1 ==> (r.0 && _f@[j].0 == r.1) || _f@[j].0 > s,
        r.2@ <= ht(*t) + 1,
{
    let ghost _f = _f@;
    let (g, Ghost(c)) = get_le(t, s);
    match g {
        Some((k, v)) => {
            let ghost i = choose|i: int| #[trigger] last_le(seq(*t), s, i, k, *v);
            proof {
                assert(_f[i] == (k as nat, v@));
                assert(end(_f[i]) <= VARINT_MAX);
                assert forall|j: int| 0 <= j < _f.len() implies (j < i ==> end(#[trigger] _f[j]) <= _f[i].0) && (j > i
                    ==> _f[j].0 > s) by {
                    if j > i {
                        assert(_f[j].0 == seq(*t)[j].0);
                    }
                }
            }
            if k + v.len() as u64 >= s {
                (true, k, Ghost(c))
            } else {
                (false, s, Ghost(c))
            }
        },
        None => {
            proof {
                assert forall|j: int| 0 <= j < _f.len() implies #[trigger] _f[j].0 > s by {
                    assert(_f[j].0 == seq(*t)[j].0);
                }
            }
            (false, s, Ghost(c))
        },
    }
}

/// `gather`'s result over the chunks: `cl` (merged) then `rest` are `M`'s then `B`'s; `cl` and the frame cover
/// `[s0, me2)`, `rest` the frame's bytes past `me2`, and `rest`'s first chunk may follow the merged bytes.
#[verifier::opaque]
spec fn gat(
    cl: Seq<(nat, Seq<u8>)>,
    rest: Seq<(nat, Seq<u8>)>,
    fm: Seq<(nat, Seq<u8>)>,
    fb: Seq<(nat, Seq<u8>)>,
    s0: nat,
    me2: nat,
    s: nat,
    e: nat,
    lc: bool,
) -> bool {
    &&& cl + rest == fm + fb
    &&& within(cl, s0, me2)
    &&& starts_ge(rest, me2)
    &&& cov(cl, s0, me2, s, e)
    &&& cov2(rest, me2, s, e)
    &&& front_ok(rest, me2)
    &&& s < me2 <= VARINT_MAX
    &&& s0 + CAP >= s ==> me2 - s0 <= (e - s) + 4 * K
    &&& lc ==> cl.len() > 0 && cl[0] == fm[0]
}

/// What `gather` needs of `M` (`fm`) and `B` (`fb`).
#[verifier::opaque]
spec fn mfacts(
    fm: Seq<(nat, Seq<u8>)>,
    fb: Seq<(nat, Seq<u8>)>,
    s0: nat,
    s: nat,
    e: nat,
    lc: bool,
) -> bool {
    &&& ok(fm + fb)
    &&& s0 <= s < e <= VARINT_MAX
    &&& forall|j: int| 0 <= j < fm.len() ==> #[trigger] fm[j].0 < e
    &&& starts_ge(fb, e)
    &&& lc ==> fm.len() > 0 && fm[0].0 == s0 && end(fm[0]) >= s
    &&& !lc ==> s0 == s
    &&& forall|j: int| 0 <= j < fm.len() ==> (lc && j == 0) || #[trigger] fm[j].0 > s
}

/// What `gather` itself uses of `mfacts`.
proof fn lemma_gather_ok(fm: Seq<(nat, Seq<u8>)>, fb: Seq<(nat, Seq<u8>)>, s0: nat, s: nat, e: nat, lc: bool)
    requires
        mfacts(fm, fb, s0, s, e, lc),
    ensures
        ok(fm),
        ok(fb),
{
    reveal(mfacts);
    lemma_ok_split(fm, fb);
}

/// `Rc` kept as a follower: the merged bytes end at its start.
proof fn lemma_gather_kept(
    fm: Seq<(nat, Seq<u8>)>,
    fb: Seq<(nat, Seq<u8>)>,
    s0: nat,
    s: nat,
    e: nat,
    lc: bool,
)
    requires
        mfacts(fm, fb, s0, s, e, lc),
        fm.len() > 0,
        end(fm.last()) > e,
        fm.last().1.len() >= K,
        !(lc && fm.len() == 1),
    ensures
        gat(fm.drop_last(), seq![fm.last()] + fb, fm, fb, s0, fm.last().0, s, e, lc),
        starts_ge(fb, e),
        fm.last().0 < e,
{
    reveal(mfacts);
    reveal(gat);
    let n = fm.len() as int;
    let f = fm + fb;
    let cl = fm.drop_last();
    let z = fm.last();
    let rest = seq![z] + fb;
    lemma_ok_split(fm, fb);
    assert(z == fm[n - 1]);
    assert(cl + rest =~= fm + fb);
    assert(z.0 > s);
    assert(end(fm[n - 1]) <= VARINT_MAX);
    assert forall|j: int| 0 <= j < cl.len() implies s0 <= #[trigger] cl[j].0 && end(cl[j]) <= z.0 by {
        assert(cl[j] == fm[j]);
        assert(end(fm[j]) <= fm[n - 1].0);
    }
    assert forall|j: int| 0 <= j < rest.len() implies #[trigger] rest[j].0 >= z.0 by {
        if j > 0 {
            assert(rest[j] == fb[j - 1]);
            assert(f[n - 1] == z && f[n + j - 1] == fb[j - 1]);
            assert(end(f[n - 1]) <= f[n + j - 1].0);
        }
    }
    assert forall|k: nat| s0 <= k < z.0 && !#[trigger] pos(cl).contains(k) implies s <= k < e by {
        if k < s {
            assert(cl[0] == fm[0]);
            assert(inf(cl, 0, k));
        }
    }
    assert forall|k: nat| s <= k < e && k >= z.0 implies #[trigger] pos(rest).contains(k) by {
        assert(inf(rest, 0, k));
    }
    if lc {
        assert(cl[0] == fm[0]);
    }
}

/// `Rc` merged (or none): the merged bytes of `M` end at `me`, the larger of `e` and `M`'s last end.
proof fn lemma_gather_m(fm: Seq<(nat, Seq<u8>)>, fb: Seq<(nat, Seq<u8>)>, s0: nat, s: nat, e: nat, lc: bool, me: nat)
    requires
        mfacts(fm, fb, s0, s, e, lc),
        me == (if fm.len() > 0 && end(fm.last()) > e { end(fm.last()) } else { e }),
        fm.len() > 0 && end(fm.last()) > e ==> fm.last().1.len() < K || (lc && fm.len() == 1),
    ensures
        within(fm, s0, me),
        cov(fm, s0, me, s, e),
        e <= me <= VARINT_MAX,
        starts_ge(fb, me),
        s0 + CAP >= s ==> me - s0 <= (e - s) + 3 * K,
{
    reveal(mfacts);
    let n = fm.len() as int;
    let f = fm + fb;
    lemma_ok_split(fm, fb);
    if n > 0 {
        assert(fm.last() == fm[n - 1]);
        assert(end(fm[n - 1]) <= VARINT_MAX);
        assert(fm[n - 1].1.len() <= CAP);
    }
    assert forall|j: int| 0 <= j < fm.len() implies s0 <= #[trigger] fm[j].0 && end(fm[j]) <= me by {
        if j < n - 1 {
            assert(end(fm[j]) <= fm[n - 1].0);
        }
    }
    assert forall|k: nat| s0 <= k < me && !#[trigger] pos(fm).contains(k) implies s <= k < e by {
        if k < s {
            assert(inf(fm, 0, k));
        }
        if k >= e {
            assert(inf(fm, n - 1, k));
        }
    }
    assert forall|j: int| 0 <= j < fb.len() implies #[trigger] fb[j].0 >= me by {
        if n > 0 {
            assert(f[n - 1] == fm[n - 1] && f[n + j] == fb[j]);
            assert(end(f[n - 1]) <= f[n + j].0);
        }
    }
}

/// `Rc` merged, `B`'s first chunk not: `rest` is `B`.
proof fn lemma_gather_nopop(
    fm: Seq<(nat, Seq<u8>)>,
    fb: Seq<(nat, Seq<u8>)>,
    s0: nat,
    s: nat,
    e: nat,
    lc: bool,
    me: nat,
)
    requires
        mfacts(fm, fb, s0, s, e, lc),
        within(fm, s0, me),
        cov(fm, s0, me, s, e),
        e <= me <= VARINT_MAX,
        starts_ge(fb, me),
        s0 + CAP >= s ==> me - s0 <= (e - s) + 3 * K,
        front_ok(fb, me),
    ensures
        gat(fm, fb, fm, fb, s0, me, s, e, lc),
{
    reveal(mfacts);
    reveal(gat);
}

/// `B`'s first chunk `w` merged: it starts at `me` and holds fewer than `K` bytes.
proof fn lemma_gather_pop(
    fm: Seq<(nat, Seq<u8>)>,
    fb: Seq<(nat, Seq<u8>)>,
    fb2: Seq<(nat, Seq<u8>)>,
    w: (nat, Seq<u8>),
    s0: nat,
    s: nat,
    e: nat,
    lc: bool,
    me: nat,
)
    requires
        mfacts(fm, fb, s0, s, e, lc),
        within(fm, s0, me),
        cov(fm, s0, me, s, e),
        e <= me <= VARINT_MAX,
        starts_ge(fb, me),
        s0 + CAP >= s ==> me - s0 <= (e - s) + 3 * K,
        fb == seq![w] + fb2,
        w.0 == me,
        w.1.len() < K,
    ensures
        gat(fm.push(w), fb2, fm, fb, s0, me + w.1.len(), s, e, lc),
        starts_ge(fb2, me + w.1.len()),
{
    reveal(mfacts);
    reveal(gat);
    let n = fm.len() as int;
    let f = fm + fb;
    let cl = fm.push(w);
    let me2 = me + w.1.len();
    lemma_ok_split(fm, fb);
    assert(fb[0] == w);
    assert(f[n] == w);
    assert(end(f[n]) <= VARINT_MAX);
    assert(cl + fb2 =~= fm + fb);
    assert forall|j: int| 0 <= j < cl.len() implies s0 <= #[trigger] cl[j].0 && end(cl[j]) <= me2 by {
        if j < n {
            assert(cl[j] == fm[j]);
        }
    }
    assert forall|j: int| 0 <= j < fb2.len() implies #[trigger] fb2[j].0 >= me2 by {
        assert(f[n + 1 + j] == fb2[j]);
        assert(end(f[n]) <= f[n + 1 + j].0);
    }
    assert forall|k: nat| s0 <= k < me2 && !#[trigger] pos(cl).contains(k) implies s <= k < e by {
        if k < me {
            if pos(fm).contains(k) {
                let i = choose|i: int| inf(fm, i, k);
                assert(cl[i] == fm[i]);
                assert(inf(cl, i, k));
            }
        } else {
            assert(inf(cl, n, k));
        }
    }
    if fb2.len() > 0 && fb2[0].0 == me2 {
        assert(f[n + 1] == fb2[0]);
        assert(fol(f, n + 1));
    }
    if lc {
        assert(cl[0] == fm[0]);
    }
}

/// D3 steps 3-4: `M`'s chunks into `mv` (its last, `Rc`, kept out as `z` if it runs past `e` with at least `K` bytes
/// and is not `Lc`), then `B`'s first chunk into `mv` if it starts where the merged bytes end and holds fewer than
/// `K`. `me2` ends the merged bytes; `rest` is `z` then what is left of `B`.
fn gather(m: Tree<CapVec<u8>>, b: Tree<CapVec<u8>>, _s: u64, e: u64, _s0: u64, lc: bool) -> (r: (
    (Vec<(u64, CapVec<u8>)>, Option<(u64, CapVec<u8>)>),
    Tree<CapVec<u8>>,
    u64,
    Ghost<nat>,
))
    requires
        crate::avl::wf(m),
        crate::avl::wf(b),
        seq(m).len() + seq(b).len() < pow2(63),
        keys_ge(b, e),
        mfacts(mp(seq(m)), mp(seq(b)), _s0 as nat, _s as nat, e as nat, lc),
    ensures
        gat(mp(r.0.0@), zs(r.0.1) + mp(seq(r.1)), mp(seq(m)), mp(seq(b)), _s0 as nat, r.2 as nat, _s as nat, e as nat, lc),
        crate::avl::wf(r.1),
        ht(r.1) <= ht(b),
        seq(r.1).len() <= seq(b).len(),
        r.0.1 is Some ==> (r.0.1->0).0 == r.2 && keys_gt(r.1, r.2),
        r.0.1 is None ==> keys_ge(r.1, r.2),
        r.3@ <= 4 * seq(m).len() + 7 * (ht(b) + 1) + 3,
{
    let ghost fm = mp(seq(m));
    let ghost fb = mp(seq(b));
    let ghost mut work: nat = 1;
    proof {
        lemma_gather_ok(fm, fb, _s0 as nat, _s as nat, e as nat, lc);
        lemma2_to64_rest();
        assert(c_drain() == 1 && c_pop() == 6);
    }
    let (n, Ghost(c1)) = size(&m);
    let mut mv: Vec<(u64, CapVec<u8>)> = Vec::with_capacity(n + 1);
    let Ghost(c2) = drain(m, &mut mv);
    proof {
        work = work + c1 + c2;
        assert(mv@ =~= seq(m));
    }
    let mut me = e;
    let mut z: Option<(u64, CapVec<u8>)> = None;
    if mv.len() > 0 {
        let zi = mv.len() - 1;
        proof {
            assert(fm[zi as int] == (mv@[zi as int].0 as nat, mv@[zi as int].1@));
            assert(fm.last() == fm[zi as int]);
            assert(end(fm[zi as int]) <= VARINT_MAX);
        }
        let zk = mv[zi].0;
        let ze = zk + mv[zi].1.len() as u64;
        if ze > e && mv[zi].1.len() as u64 >= K && !(lc && zi == 0) {
            z = mv.pop();
            me = zk;
            proof {
                lemma_gather_kept(fm, fb, _s0 as nat, _s as nat, e as nat, lc);
                assert(mp(mv@) =~= fm.drop_last());
                assert(zs(z) == seq![fm.last()]);
                assert forall|j: int| 0 <= j < seq(b).len() implies #[trigger] seq(b)[j].0 > zk by {
                    assert(fb[j].0 == seq(b)[j].0);
                }
            }
            return ((mv, z), b, me, Ghost(work));
        } else if ze > e {
            me = ze;
        }
    }
    proof {
        assert(mp(mv@) == fm);
        lemma_gather_m(fm, fb, _s0 as nat, _s as nat, e as nat, lc, me as nat);
        assert forall|j: int| 0 <= j < seq(b).len() implies #[trigger] seq(b)[j].0 >= me by {
            assert(fb[j].0 == seq(b)[j].0);
        }
    }
    let (fl, Ghost(c3)) = front_at(&b, me);
    proof {
        work = work + c3;
    }
    if let Some(wl) = fl {
        if (wl as u64) < K {
            let (b2, wk, wv, Ghost(c4)) = pop_min(b);
            let ghost w = (wk as nat, wv@);
            mv.push((wk, wv));
            proof {
                work = work + c4;
                lemma_mp_cat(seq![(wk, wv)], seq(b2));
                assert(mp(seq![(wk, wv)]) =~= seq![w]);
                lemma_gather_pop(fm, fb, mp(seq(b2)), w, _s0 as nat, _s as nat, e as nat, lc, me as nat);
                assert(mp(mv@) =~= fm.push(w));
                assert(zs(z) + mp(seq(b2)) =~= mp(seq(b2)));
                assert forall|j: int| 0 <= j < seq(b2).len() implies #[trigger] seq(b2)[j].0 >= me + wl by {
                    assert(mp(seq(b2))[j].0 == seq(b2)[j].0);
                }
            }
            return ((mv, z), b2, me + wl as u64, Ghost(work));
        }
    }
    proof {
        if fb.len() > 0 && fb[0].0 == me {
            assert(fl is Some);
        }
        lemma_gather_nopop(fm, fb, _s0 as nat, _s as nat, e as nat, lc, me as nat);
        assert(zs(z) + fb =~= fb);
    }
    ((mv, z), b, me, Ghost(work))
}

/// Chunks all starting in `[a, b]` all count in `nm`.
proof fn lemma_nm_all(g: Seq<(nat, Seq<u8>)>, a: nat, b: nat)
    requires
        forall|j: int| 0 <= j < g.len() ==> #[trigger] inr(g[j], a, b),
    ensures
        nm(g, a, b) == g.len(),
    decreases g.len(),
{
    if g.len() > 0 {
        let h = g.drop_last();
        assert forall|j: int| 0 <= j < h.len() implies #[trigger] inr(h[j], a, b) by {
            assert(h[j] == g[j]);
        }
        lemma_nm_all(h, a, b);
        assert(inr(g[g.len() - 1], a, b));
    }
}

/// `|M| <= e - s`: every chunk of `M` but `Lc` starts in `(s, e)`, and starts strictly increase.
proof fn lemma_m_count(fm: Seq<(nat, Seq<u8>)>, s: nat, e: nat, lc: bool)
    requires
        ok(fm),
        s < e,
        forall|j: int| 0 <= j < fm.len() ==> #[trigger] fm[j].0 < e,
        forall|j: int| 0 <= j < fm.len() ==> (lc && j == 0) || #[trigger] fm[j].0 > s,
    ensures
        fm.len() <= e - s,
{
    let k: int = if lc && fm.len() > 0 { 1 } else { 0 };
    let g = fm.subrange(k, fm.len() as int);
    lemma_ok_sub(fm, k, fm.len() as int);
    assert forall|j: int| 0 <= j < g.len() implies #[trigger] inr(g[j], s + 1, (e - 1) as nat) by {
        assert(g[j] == fm[k + j]);
    }
    lemma_nm_all(g, s + 1, (e - 1) as nat);
    lemma_nm_le(g, s + 1, (e - 1) as nat);
}

/// `lemma_mfacts`, `Lc`'s part: it is `M`'s first chunk.
proof fn lemma_mfacts_lc(
    f: Seq<(nat, Seq<u8>)>,
    fa: Seq<(nat, Seq<u8>)>,
    fm: Seq<(nat, Seq<u8>)>,
    fb: Seq<(nat, Seq<u8>)>,
    s0: nat,
    s: nat,
    e: nat,
    lc: bool,
)
    requires
        ok(f),
        f == fa + fm + fb,
        s0 <= s < e <= VARINT_MAX,
        !lc ==> s0 == s,
        lc ==> exists|j: int| 0 <= j < f.len() && #[trigger] f[j].0 == s0 && end(f[j]) >= s,
        forall|j: int| 0 <= j < f.len() && #[trigger] f[j].0 < s0 ==> end(f[j]) <= s0 && (end(f[j]) == s0 ==> lc),
        forall|j: int| 0 <= j < f.len() && #[trigger] f[j].0 >= s0 ==> (lc && f[j].0 == s0) || f[j].0 > s,
        forall|j: int| 0 <= j < fa.len() ==> #[trigger] fa[j].0 < s0,
        forall|j: int| 0 <= j < fm.len() ==> s0 <= #[trigger] fm[j].0 < e,
        starts_ge(fb, e),
    ensures
        lc ==> fm.len() > 0 && fm[0].0 == s0 && end(fm[0]) >= s && fm[0].1.len() <= CAP,
{
    let na = fa.len() as int;
    let nm_ = fm.len() as int;
    if lc {
        assert(f =~= fa + (fm + fb));
        lemma_ok_split(fa, fm + fb);
        lemma_ok_split(fm, fb);
        let j0 = choose|j: int| 0 <= j < f.len() && #[trigger] f[j].0 == s0 && end(f[j]) >= s;
        if j0 < na {
            assert(f[j0] == fa[j0]);
        } else if j0 >= na + nm_ {
            assert(f[j0] == fb[j0 - na - nm_]);
        } else if j0 > na {
            assert(f[na] == fm[0]);
            assert(end(f[na]) <= f[j0].0);
        }
        assert(j0 == na);
        assert(f[na] == fm[0]);
        assert(fm[0].1.len() <= CAP);
    }
}

/// `lemma_mfacts`, `A`'s part: its chunks end by `s0`, and one ending there is followed by `Lc`, of at least `K`.
proof fn lemma_mfacts_fa(
    f: Seq<(nat, Seq<u8>)>,
    fa: Seq<(nat, Seq<u8>)>,
    fm: Seq<(nat, Seq<u8>)>,
    fb: Seq<(nat, Seq<u8>)>,
    s0: nat,
    s: nat,
    e: nat,
    lc: bool,
)
    requires
        ok(f),
        f == fa + fm + fb,
        s0 <= s < e <= VARINT_MAX,
        !lc ==> s0 == s,
        lc ==> exists|j: int| 0 <= j < f.len() && #[trigger] f[j].0 == s0 && end(f[j]) >= s,
        forall|j: int| 0 <= j < f.len() && #[trigger] f[j].0 < s0 ==> end(f[j]) <= s0 && (end(f[j]) == s0 ==> lc),
        forall|j: int| 0 <= j < f.len() && #[trigger] f[j].0 >= s0 ==> (lc && f[j].0 == s0) || f[j].0 > s,
        forall|j: int| 0 <= j < fa.len() ==> #[trigger] fa[j].0 < s0,
        forall|j: int| 0 <= j < fm.len() ==> s0 <= #[trigger] fm[j].0 < e,
        starts_ge(fb, e),
        lc ==> fm.len() > 0 && fm[0].0 == s0,
    ensures
        ok(fa),
        ends_le(fa, s0),
        fa.len() > 0 && end(fa.last()) == s0 ==> lc && fm.len() > 0 && fm[0].1.len() >= K,
{
    let na = fa.len() as int;
    assert(f =~= fa + (fm + fb));
    lemma_ok_split(fa, fm + fb);
    assert forall|j: int| 0 <= j < fa.len() implies end(#[trigger] fa[j]) <= s0 by {
        assert(f[j] == fa[j]);
        assert(f[j].0 < s0);
    }
    if na > 0 && end(fa.last()) == s0 {
        assert(fa.last() == f[na - 1]);
        assert(f[na - 1].0 < s0);
        assert(f[na] == fm[0]);
        assert(fol(f, na));
    }
}

/// From `find_lc` and the two splits (`f` is `A`'s, `M`'s and `B`'s chunks): what `gather` needs, and the facts about
/// `A`'s chunks.
proof fn lemma_mfacts(
    f: Seq<(nat, Seq<u8>)>,
    fa: Seq<(nat, Seq<u8>)>,
    fm: Seq<(nat, Seq<u8>)>,
    fb: Seq<(nat, Seq<u8>)>,
    s0: nat,
    s: nat,
    e: nat,
    lc: bool,
)
    requires
        ok(f),
        f == fa + fm + fb,
        s0 <= s < e <= VARINT_MAX,
        !lc ==> s0 == s,
        lc ==> exists|j: int| 0 <= j < f.len() && #[trigger] f[j].0 == s0 && end(f[j]) >= s,
        forall|j: int| 0 <= j < f.len() && #[trigger] f[j].0 < s0 ==> end(f[j]) <= s0 && (end(f[j]) == s0 ==> lc),
        forall|j: int| 0 <= j < f.len() && #[trigger] f[j].0 >= s0 ==> (lc && f[j].0 == s0) || f[j].0 > s,
        forall|j: int| 0 <= j < fa.len() ==> #[trigger] fa[j].0 < s0,
        forall|j: int| 0 <= j < fm.len() ==> s0 <= #[trigger] fm[j].0 < e,
        starts_ge(fb, e),
    ensures
        mfacts(fm, fb, s0, s, e, lc),
        ok(fa),
        ends_le(fa, s0),
        fa.len() > 0 && end(fa.last()) == s0 ==> lc && fm.len() > 0 && fm[0].1.len() >= K,
        fm.len() <= e - s,
        s0 + CAP >= s,
        lc ==> fm.len() > 0 && fm[0].0 == s0,
{
    reveal(mfacts);
    let na = fa.len() as int;
    lemma_mfacts_lc(f, fa, fm, fb, s0, s, e, lc);
    lemma_mfacts_fa(f, fa, fm, fb, s0, s, e, lc);
    assert(f =~= fa + (fm + fb));
    lemma_ok_split(fa, fm + fb);
    lemma_ok_split(fm, fb);
    assert forall|j: int| 0 <= j < fm.len() implies (lc && j == 0) || #[trigger] fm[j].0 > s by {
        assert(f[na + j] == fm[j]);
        assert(f[na + j].0 >= s0);
        if j > 0 && lc && fm[j].0 == s0 {
            assert(end(fm[0]) <= fm[j].0);
        }
    }
    lemma_m_count(fm, s, e, lc);
}

/// The merged bytes are `put`'s: where `cl` holds a position its byte, else the frame's.
proof fn lemma_src(
    f: Seq<(nat, Seq<u8>)>,
    fa: Seq<(nat, Seq<u8>)>,
    cl: Seq<(nat, Seq<u8>)>,
    rest: Seq<(nat, Seq<u8>)>,
    s0: nat,
    me2: nat,
    lo: nat,
    off: nat,
    d: Seq<u8>,
)
    requires
        ok(f),
        f == fa + cl + rest,
        ends_le(fa, s0),
        starts_ge(rest, me2),
        cov(cl, s0, me2, (if lo >= off { lo } else { off }), off + d.len()),
    ensures
        forall|k: nat|
            s0 <= k < me2 ==> #[trigger] src(cl, d, off, k) == put(vw(f), lo, off, d)[k] && put(
                vw(f),
                lo,
                off,
                d,
            ).contains_key(k),
{
    let na = fa.len() as int;
    let nc = cl.len() as int;
    lemma_ok_split(fa + cl, rest);
    lemma_ok_split(fa, cl);
    lemma_at_ok(f);
    lemma_at_ok(cl);
    assert forall|k: nat| s0 <= k < me2 implies #[trigger] src(cl, d, off, k) == put(vw(f), lo, off, d)[k] && put(
        vw(f),
        lo,
        off,
        d,
    ).contains_key(k) by {
        if pos(cl).contains(k) {
            let j = choose|j: int| inf(cl, j, k);
            assert(f[na + j] == cl[j]);
            assert(inf(f, na + j, k));
        } else {
            if pos(f).contains(k) {
                let i = choose|i: int| inf(f, i, k);
                if i < na {
                    assert(f[i] == fa[i]);
                } else if i < na + nc {
                    assert(f[i] == cl[i - na]);
                    assert(inf(cl, i - na, k));
                } else {
                    assert(f[i] == rest[i - na - nc]);
                }
            }
        }
    }
}

/// `lemma_new_view`'s domain half.
proof fn lemma_new_dom(
    f: Seq<(nat, Seq<u8>)>,
    fa: Seq<(nat, Seq<u8>)>,
    cl: Seq<(nat, Seq<u8>)>,
    rest: Seq<(nat, Seq<u8>)>,
    p: Seq<(nat, Seq<u8>)>,
    s0: nat,
    me2: nat,
    lo: nat,
    off: nat,
    d: Seq<u8>,
)
    requires
        ok(f),
        f == fa + cl + rest,
        ends_le(fa, s0),
        within(cl, s0, me2),
        starts_ge(rest, me2),
        s0 <= (if lo >= off { lo } else { off }),
        cov(cl, s0, me2, (if lo >= off { lo } else { off }), off + d.len()),
        cov2(rest, me2, (if lo >= off { lo } else { off }), off + d.len()),
        ok(fa + p + rest),
        pos(p) == Set::range(s0, me2),
        forall|i: int, k: nat| #[trigger] inf(p, i, k) ==> p[i].1[k - p[i].0] == src(cl, d, off, k),
    ensures
        pos(fa + p + rest) == put(vw(f), lo, off, d).dom(),
{
    let g = fa + p + rest;
    let pv = put(vw(f), lo, off, d);
    let s: nat = if lo >= off { lo } else { off };
    let e = off + d.len();
    lemma_pos_cat(fa + cl, rest);
    lemma_pos_cat(fa, cl);
    lemma_pos_cat(fa + p, rest);
    lemma_pos_cat(fa, p);
    assert forall|k: nat| #[trigger] pos(g).contains(k) <==> pv.dom().contains(k) by {
        if pos(cl).contains(k) {
            let j = choose|j: int| inf(cl, j, k);
        }
        if s <= k < e && k >= me2 {
            assert(pos(rest).contains(k));
        }
        if s0 <= k < me2 && !pos(cl).contains(k) {
            assert(s <= k < e);
        }
    }
    assert(pos(g) =~= pv.dom());
}

/// `lemma_new_view`'s values half.
proof fn lemma_new_vals(
    f: Seq<(nat, Seq<u8>)>,
    fa: Seq<(nat, Seq<u8>)>,
    cl: Seq<(nat, Seq<u8>)>,
    rest: Seq<(nat, Seq<u8>)>,
    p: Seq<(nat, Seq<u8>)>,
    s0: nat,
    me2: nat,
    lo: nat,
    off: nat,
    d: Seq<u8>,
)
    requires
        ok(f),
        f == fa + cl + rest,
        ends_le(fa, s0),
        within(cl, s0, me2),
        starts_ge(rest, me2),
        s0 <= (if lo >= off { lo } else { off }),
        cov(cl, s0, me2, (if lo >= off { lo } else { off }), off + d.len()),
        cov2(rest, me2, (if lo >= off { lo } else { off }), off + d.len()),
        ok(fa + p + rest),
        pos(p) == Set::range(s0, me2),
        forall|i: int, k: nat| #[trigger] inf(p, i, k) ==> p[i].1[k - p[i].0] == src(cl, d, off, k),
    ensures
        forall|k: nat| #[trigger] pos(fa + p + rest).contains(k) ==> vw(fa + p + rest)[k] == put(vw(f), lo, off, d)[k],
{
    let g = fa + p + rest;
    let pv = put(vw(f), lo, off, d);
    let (na, np, nc) = (fa.len() as int, p.len() as int, cl.len() as int);
    lemma_at_ok(f);
    lemma_at_ok(g);
    lemma_src(f, fa, cl, rest, s0, me2, lo, off, d);
    assert forall|k: nat| #[trigger] pos(g).contains(k) implies vw(g)[k] == pv[k] by {
        let i = choose|i: int| inf(g, i, k);
        if i < na {
            assert(g[i] == fa[i] && f[i] == fa[i]);
            assert(inf(f, i, k));
        } else if i < na + np {
            assert(g[i] == p[i - na]);
            assert(inf(p, i - na, k));
            assert(end(g[i]) <= VARINT_MAX);
            assert(pos(p).contains(k));
            assert(s0 <= k < me2);
            assert(src(cl, d, off, k) == pv[k]);
        } else {
            assert(g[i] == rest[i - na - np] && f[i - np + nc] == rest[i - na - np]);
            assert(inf(f, i - np + nc, k));
        }
    }
}

/// The new chunks `fa`, `p`, `rest` hold `put`'s bytes: `fa` and `rest` keep theirs, and the pieces `p` hold the
/// merged bytes of `[s0, me2)`.
proof fn lemma_new_view(
    f: Seq<(nat, Seq<u8>)>,
    fa: Seq<(nat, Seq<u8>)>,
    cl: Seq<(nat, Seq<u8>)>,
    rest: Seq<(nat, Seq<u8>)>,
    p: Seq<(nat, Seq<u8>)>,
    s0: nat,
    me2: nat,
    lo: nat,
    off: nat,
    d: Seq<u8>,
)
    requires
        ok(f),
        f == fa + cl + rest,
        ends_le(fa, s0),
        within(cl, s0, me2),
        starts_ge(rest, me2),
        s0 <= (if lo >= off { lo } else { off }),
        cov(cl, s0, me2, (if lo >= off { lo } else { off }), off + d.len()),
        cov2(rest, me2, (if lo >= off { lo } else { off }), off + d.len()),
        ok(fa + p + rest),
        pos(p) == Set::range(s0, me2),
        forall|i: int, k: nat| #[trigger] inf(p, i, k) ==> p[i].1[k - p[i].0] == src(cl, d, off, k),
    ensures
        vw(fa + p + rest) == put(vw(f), lo, off, d),
{
    lemma_new_dom(f, fa, cl, rest, p, s0, me2, lo, off, d);
    lemma_new_vals(f, fa, cl, rest, p, s0, me2, lo, off, d);
    assert(vw(fa + p + rest) =~= put(vw(f), lo, off, d));
}

/// The new chunks are in order: `A`'s, the pieces from `s0` to `me2`, then `rest`, followers at the seams holding at
/// least `K` bytes.
proof fn lemma_new_ok(
    fa: Seq<(nat, Seq<u8>)>,
    p: Seq<(nat, Seq<u8>)>,
    rest: Seq<(nat, Seq<u8>)>,
    s0: nat,
    me2: nat,
)
    requires
        ok(fa),
        ok(p),
        ok(rest),
        ends_le(fa, s0),
        starts_ge(rest, me2),
        p.len() > 0,
        p[0].0 == s0,
        end(p.last()) == me2,
        fa.len() > 0 && end(fa.last()) == s0 ==> p[0].1.len() >= K,
        front_ok(rest, me2),
    ensures
        ok(fa + p + rest),
{
    if fa.len() > 0 {
        assert(fa.last() == fa[fa.len() - 1]);
    }
    lemma_ok_cat(fa, p);
    assert((fa + p).last() == p.last());
    lemma_ok_cat(fa + p, rest);
}

/// `ok` chunks have strictly increasing starts.
proof fn lemma_ok_sorted(v: Seq<(u64, CapVec<u8>)>)
    requires
        ok(mp(v)),
    ensures
        sorted(v),
{
    let f = mp(v);
    assert forall|i: int, j: int| #![trigger v[i], v[j]] 0 <= i < j < v.len() implies v[i].0 < v[j].0 by {
        assert(f[i].0 == v[i].0 && f[j].0 == v[j].0);
        assert(end(f[i]) <= f[j].0);
    }
}

/// `open_up`'s result over the chunks: `f` is `A`'s (`fa`), the merged chunks (`cl`), then `rest`; `cl` and the frame
/// `[s, e)` cover `[s0, me2)`, `rest` the frame's positions past `me2`, and the seams admit followers.
#[verifier::opaque]
spec fn opened(
    f: Seq<(nat, Seq<u8>)>,
    fa: Seq<(nat, Seq<u8>)>,
    cl: Seq<(nat, Seq<u8>)>,
    rest: Seq<(nat, Seq<u8>)>,
    s0: nat,
    me2: nat,
    s: nat,
    e: nat,
) -> bool {
    &&& f == fa + cl + rest
    &&& ends_le(fa, s0)
    &&& fa.len() > 0 && end(fa.last()) == s0 ==> me2 - s0 >= K
    &&& within(cl, s0, me2)
    &&& starts_ge(rest, me2)
    &&& cov(cl, s0, me2, s, e)
    &&& cov2(rest, me2, s, e)
    &&& front_ok(rest, me2)
    &&& s0 <= s < me2 <= VARINT_MAX
    &&& me2 - s0 <= (e - s) + 4 * K
}

/// What `fill_all` needs of `open_up`'s result.
proof fn lemma_opened(
    f: Seq<(nat, Seq<u8>)>,
    fa: Seq<(nat, Seq<u8>)>,
    cl: Seq<(nat, Seq<u8>)>,
    rest: Seq<(nat, Seq<u8>)>,
    s0: nat,
    me2: nat,
    s: nat,
    e: nat,
)
    requires
        ok(f),
        opened(f, fa, cl, rest, s0, me2, s, e),
    ensures
        ok(cl),
        within(cl, s0, me2),
        cov(cl, s0, me2, s, e),
        me2 - s0 <= (e - s) + 4 * K,
        fa.len() + rest.len() <= f.len(),
{
    reveal(opened);
    lemma_ok_split(fa + cl, rest);
    lemma_ok_split(fa, cl);
}

/// `open_up`'s result, from the split (`f` is `fa`, `fm`, `fb`) and `gather`'s.
proof fn lemma_open_end(
    f: Seq<(nat, Seq<u8>)>,
    fa: Seq<(nat, Seq<u8>)>,
    fm: Seq<(nat, Seq<u8>)>,
    fb: Seq<(nat, Seq<u8>)>,
    cl: Seq<(nat, Seq<u8>)>,
    rest: Seq<(nat, Seq<u8>)>,
    s0: nat,
    me2: nat,
    s: nat,
    e: nat,
    lc: bool,
)
    requires
        f == fa + fm + fb,
        ends_le(fa, s0),
        fa.len() > 0 && end(fa.last()) == s0 ==> lc && fm.len() > 0 && fm[0].1.len() >= K,
        lc ==> fm.len() > 0 && fm[0].0 == s0,
        s0 <= s,
        s0 + CAP >= s,
        gat(cl, rest, fm, fb, s0, me2, s, e, lc),
    ensures
        opened(f, fa, cl, rest, s0, me2, s, e),
        s0 <= s < me2 <= VARINT_MAX,
        me2 - s0 <= (e - s) + 4 * K,
{
    reveal(gat);
    reveal(opened);
    assert(f =~= fa + cl + rest) by {
        assert(fa + cl + rest =~= fa + (cl + rest));
        assert(f =~= fa + (fm + fb));
    }
    if fa.len() > 0 && end(fa.last()) == s0 {
        assert(cl[0] == fm[0]);
        assert(end(cl[0]) <= me2);
    }
}

/// The split trees' keys as facts about their chunks.
proof fn lemma_mp_keys(a: Tree<CapVec<u8>>, m: Tree<CapVec<u8>>, b: Tree<CapVec<u8>>, s0: u64, e: u64)
    requires
        keys_lt(a, s0),
        keys_ge(m, s0),
        keys_lt(m, e),
        keys_ge(b, e),
    ensures
        forall|j: int| 0 <= j < mp(seq(a)).len() ==> #[trigger] mp(seq(a))[j].0 < s0,
        forall|j: int| 0 <= j < mp(seq(m)).len() ==> s0 <= #[trigger] mp(seq(m))[j].0 < e,
        starts_ge(mp(seq(b)), e as nat),
{
    let (fa, fm, fb) = (mp(seq(a)), mp(seq(m)), mp(seq(b)));
    assert forall|j: int| 0 <= j < fa.len() implies #[trigger] fa[j].0 < s0 by {
        assert(fa[j].0 == seq(a)[j].0);
    }
    assert forall|j: int| 0 <= j < fm.len() implies s0 <= #[trigger] fm[j].0 < e by {
        assert(fm[j].0 == seq(m)[j].0);
    }
    assert forall|j: int| 0 <= j < fb.len() implies #[trigger] fb[j].0 >= e by {
        assert(fb[j].0 == seq(b)[j].0);
    }
}

/// `split_frame`'s result over the chunks, from `find_lc`'s and the two splits'.
proof fn lemma_split_frame(
    f: Seq<(nat, Seq<u8>)>,
    t: Tree<CapVec<u8>>,
    a: Tree<CapVec<u8>>,
    rt: Tree<CapVec<u8>>,
    m: Tree<CapVec<u8>>,
    b: Tree<CapVec<u8>>,
    s0: u64,
    s: u64,
    e: u64,
    lc: bool,
)
    requires
        ok(f),
        f == mp(seq(t)),
        s0 <= s < e <= VARINT_MAX,
        !lc ==> s0 == s,
        lc ==> exists|j: int| 0 <= j < f.len() && #[trigger] f[j].0 == s0 && end(f[j]) >= s,
        forall|j: int| 0 <= j < f.len() && #[trigger] f[j].0 < s0 ==> end(f[j]) <= s0 && (end(f[j]) == s0 ==> lc),
        forall|j: int| 0 <= j < f.len() && #[trigger] f[j].0 >= s0 ==> (lc && f[j].0 == s0) || f[j].0 > s,
        seq(a) + seq(rt) == seq(t),
        seq(m) + seq(b) == seq(rt),
        keys_lt(a, s0),
        keys_ge(rt, s0),
        keys_lt(m, e),
        keys_ge(b, e),
    ensures
        ({
            let (fa, fm, fb) = (mp(seq(a)), mp(seq(m)), mp(seq(b)));
            &&& f == fa + fm + fb
            &&& mfacts(fm, fb, s0 as nat, s as nat, e as nat, lc)
            &&& ends_le(fa, s0 as nat)
            &&& fa.len() > 0 && end(fa.last()) == s0 ==> lc && fm.len() > 0 && fm[0].1.len() >= K
            &&& lc ==> fm.len() > 0 && fm[0].0 == s0
            &&& fm.len() <= e - s
            &&& s0 + CAP >= s
        }),
{
    let (fa, fm, fb) = (mp(seq(a)), mp(seq(m)), mp(seq(b)));
    lemma_mp_cat(seq(a), seq(rt));
    lemma_mp_cat(seq(m), seq(b));
    lemma_keys_app(rt, m, b, s0);
    assert(f =~= fa + fm + fb);
    lemma_mp_keys(a, m, b, s0, e);
    lemma_mfacts(f, fa, fm, fb, s0 as nat, s as nat, e as nat, lc);
}

/// D3 steps 1-2 on the tree `t` of chunks `f`: find `Lc` (whether it exists, `s0`), then split at `s0` and at `e`
/// into `A`, `M`, `B`.
fn split_frame(t: Tree<CapVec<u8>>, s: u64, e: u64, _f: Ghost<Seq<(nat, Seq<u8>)>>) -> (r: (
    (Tree<CapVec<u8>>, Tree<CapVec<u8>>, Tree<CapVec<u8>>),
    (bool, u64),
    Ghost<nat>,
))
    requires
        crate::avl::wf(t),
        ok(_f@),
        _f@ == mp(seq(t)),
        _f@.len() <= VARINT_MAX,
        s < e <= VARINT_MAX,
    ensures
        ({
            let (a, m, b) = (r.0.0, r.0.1, r.0.2);
            let (lc, s0) = (r.1.0, r.1.1);
            let (fa, fm, fb) = (mp(seq(a)), mp(seq(m)), mp(seq(b)));
            &&& _f@ == fa + fm + fb
            &&& mfacts(fm, fb, s0 as nat, s as nat, e as nat, lc)
            &&& ends_le(fa, s0 as nat)
            &&& fa.len() > 0 && end(fa.last()) == s0 ==> lc && fm.len() > 0 && fm[0].1.len() >= K
            &&& lc ==> fm.len() > 0 && fm[0].0 == s0
            &&& fm.len() <= e - s
            &&& s0 <= s
            &&& s0 + CAP >= s
            &&& crate::avl::wf(a) && keys_lt(a, s0) && ht(a) <= ht(t)
            &&& crate::avl::wf(m)
            &&& crate::avl::wf(b) && keys_ge(b, e) && ht(b) <= ht(t)
            &&& seq(a).len() + seq(m).len() + seq(b).len() == _f@.len()
        }),
        r.2@ <= 75 * (ht(t) + 1) + 1,
{
    let ghost _f = _f@;
    let ghost mut work: nat = 1;
    proof {
        lemma2_to64_rest();
    }
    let (lc, s0, Ghost(c0)) = find_lc(&t, s, Ghost(_f));
    let (a, rt, Ghost(c1)) = split(t, s0);
    let (m, b, Ghost(c2)) = split(rt, e);
    proof {
        lemma_split_cost(t, a, rt, c1);
        lemma_split_cost(rt, m, b, c2);
        lemma_split_frame(_f, t, a, rt, m, b, s0, s, e, lc);
        assert(c_split6() == 37);
        work = work + c0 + c1 + c2;
    }
    ((a, m, b), (lc, s0), Ghost(work))
}

/// D3 steps 1-4 on the tree `t` of chunks `f`: `split_frame`, then gather `M` (and maybe `B`'s first chunk) into
/// `mv`. Returns `A`, `mv`, the kept `Rc`, what is left of `B`, `s0` and `me2`.
fn open_up(t: Tree<CapVec<u8>>, s: u64, e: u64, _f: Ghost<Seq<(nat, Seq<u8>)>>) -> (r: (
    (Tree<CapVec<u8>>, Vec<(u64, CapVec<u8>)>, Option<(u64, CapVec<u8>)>, Tree<CapVec<u8>>),
    (u64, u64),
    Ghost<nat>,
))
    requires
        crate::avl::wf(t),
        ok(_f@),
        _f@ == mp(seq(t)),
        _f@.len() <= VARINT_MAX,
        s < e <= VARINT_MAX,
    ensures
        ({
            let (a, cl, z, b2) = (r.0.0, mp(r.0.1@), r.0.2, r.0.3);
            let (s0, me2) = (r.1.0 as nat, r.1.1 as nat);
            let (fa, rest) = (mp(seq(a)), zs(z) + mp(seq(b2)));
            &&& opened(_f@, fa, cl, rest, s0, me2, s as nat, e as nat)
            &&& s0 <= s < me2 <= VARINT_MAX
            &&& me2 - s0 <= (e - s) + 4 * K
            &&& crate::avl::wf(a) && keys_lt(a, r.1.0) && ht(a) <= ht(t)
            &&& crate::avl::wf(b2) && ht(b2) <= ht(t)
            &&& z is Some ==> (z->0).0 == r.1.1 && keys_gt(b2, r.1.1)
            &&& z is None ==> keys_ge(b2, r.1.1)
            &&& seq(a).len() + seq(b2).len() <= _f@.len()
        }),
        r.2@ <= 82 * (ht(t) + 1) + 4 * (e - s) + 5,
{
    let ghost _f = _f@;
    let ghost mut work: nat = 1;
    proof {
        lemma2_to64_rest();
    }
    let ((a, m, b), (lc, s0), Ghost(c0)) = split_frame(t, s, e, Ghost(_f));
    let ghost (fa, fm, fb) = (mp(seq(a)), mp(seq(m)), mp(seq(b)));
    let ((mv, z), b2, me2, Ghost(c3)) = gather(m, b, s, e, s0, lc);
    proof {
        lemma_open_end(_f, fa, fm, fb, mp(mv@), zs(z) + mp(seq(b2)), s0 as nat, me2 as nat, s as nat, e as nat, lc);
        work = work + c0 + c3;
    }
    ((a, mv, z, b2), (s0, me2), Ghost(work))
}

/// The pieces' starts lie in `[s0, me2)`.
proof fn lemma_piece_keys(ps: Seq<(u64, CapVec<u8>)>, s0: nat, me2: nat)
    requires
        ok(mp(ps)),
        ps.len() > 0,
        mp(ps)[0].0 == s0,
        end(mp(ps).last()) == me2,
    ensures
        forall|j: int| 0 <= j < ps.len() ==> s0 <= #[trigger] ps[j].0 < me2,
        s0 < me2,
{
    let p = mp(ps);
    let n = ps.len() as int;
    assert(p.last() == p[n - 1]);
    assert forall|j: int| 0 <= j < ps.len() implies s0 <= #[trigger] ps[j].0 < me2 by {
        assert(p[j].0 == ps[j].0);
        if j > 0 {
            assert(end(p[0]) <= p[j].0);
        }
        if j < n - 1 {
            assert(end(p[j]) <= p[n - 1].0);
        }
    }
}

/// D3 step 6, first half: the pieces as a balanced tree, joined after `A`.
fn join_pieces(a: Tree<CapVec<u8>>, ps: Vec<(u64, CapVec<u8>)>, _s0: u64, _me2: u64, _hh: Ghost<nat>) -> (r: (
    Tree<CapVec<u8>>,
    Ghost<nat>,
))
    requires
        crate::avl::wf(a),
        ht(a) <= _hh@,
        keys_lt(a, _s0),
        ok(mp(ps@)),
        ps@.len() > 0,
        mp(ps@)[0].0 == _s0,
        end(mp(ps@).last()) == _me2,
        seq(a).len() + ps@.len() + 1 < pow2(63),
    ensures
        crate::avl::wf(r.0),
        mp(seq(r.0)) == mp(seq(a)) + mp(ps@),
        seq(r.0).len() == seq(a).len() + ps@.len(),
        keys_lt(r.0, _me2),
        ht(r.0) <= _hh@ + ps@.len() + 1,
        r.1@ <= 13 * (_hh@ + ps@.len() + 1) + 2 * ps@.len() + 2,
{
    let ghost ps0 = ps@;
    let ghost np = ps@.len();
    let ghost mut work: nat = 1;
    let mut ps = ps;
    proof {
        lemma_ok_sorted(ps0);
        lemma_piece_keys(ps0, _s0 as nat, _me2 as nat);
        lemma_hb_le(np);
        assert(c_join2() == 13);
    }
    let n = ps.len();
    let (pt, Ghost(c5)) = build(&mut ps, n);
    proof {
        assert(ps0.skip(0) =~= ps0);
        assert(seq(pt) == ps0);
        lemma_join2_order(a, pt, _s0);
    }
    let (ap, Ghost(c6)) = join2(a, pt);
    proof {
        work = work + c5 + c6;
        assert(keys_lt(ap, _me2)) by {
            lemma_keys_app(ap, a, pt, _me2);
            assert forall|i: int| 0 <= i < seq(a).len() implies #[trigger] seq(a)[i].0 < _me2 by {}
        }
        lemma_mp_cat(seq(a), seq(pt));
    }
    (ap, Ghost(work))
}

/// D3 step 6: `A` and the pieces (`join_pieces`), the kept `Rc`, then what is left of `B`, joined in order.
fn close_up(
    a: Tree<CapVec<u8>>,
    ps: Vec<(u64, CapVec<u8>)>,
    z: Option<(u64, CapVec<u8>)>,
    b2: Tree<CapVec<u8>>,
    _s0: u64,
    _me2: u64,
    _hh: Ghost<nat>,
) -> (r: (Tree<CapVec<u8>>, Ghost<nat>))
    requires
        crate::avl::wf(a),
        crate::avl::wf(b2),
        ht(a) <= _hh@,
        ht(b2) <= _hh@,
        keys_lt(a, _s0),
        z is Some ==> (z->0).0 == _me2 && keys_gt(b2, _me2),
        z is None ==> keys_ge(b2, _me2),
        ok(mp(ps@)),
        ps@.len() > 0,
        mp(ps@)[0].0 == _s0,
        end(mp(ps@).last()) == _me2,
        seq(a).len() + ps@.len() + 1 + seq(b2).len() < pow2(63),
    ensures
        crate::avl::wf(r.0),
        mp(seq(r.0)) == mp(seq(a)) + mp(ps@) + (zs(z) + mp(seq(b2))),
        r.1@ <= 26 * (_hh@ + 1) + 28 * ps@.len() + 16,
{
    let ghost ps0 = ps@;
    let ghost mut work: nat = 1;
    let (ap, Ghost(c6)) = join_pieces(a, ps, _s0, _me2, _hh);
    proof {
        work = work + c6;
        assert(c_join() == 6 && c_join2() == 13);
    }
    match z {
        Some((zk, zv)) => {
            let (t2, Ghost(c7)) = join(ap, zk, zv, b2);
            proof {
                work = work + c7;
                lemma_mp_cat(seq(ap) + seq![(zk, zv)], seq(b2));
                lemma_mp_cat(seq(ap), seq![(zk, zv)]);
                assert(mp(seq![(zk, zv)]) =~= zs(z));
                assert(mp(seq(t2)) =~= mp(seq(a)) + mp(ps0) + (zs(z) + mp(seq(b2))));
            }
            (t2, Ghost(work))
        },
        None => {
            proof {
                lemma_join2_order(ap, b2, _me2);
            }
            let (t2, Ghost(c7)) = join2(ap, b2);
            proof {
                work = work + c7;
                lemma_mp_cat(seq(ap), seq(b2));
                assert(zs(z) + mp(seq(b2)) =~= mp(seq(b2)));
                assert(mp(seq(t2)) =~= mp(seq(a)) + mp(ps0) + (zs(z) + mp(seq(b2))));
            }
            (t2, Ghost(work))
        },
    }
}

/// `merge_w`'s result: the chunks `fa`, `p`, `rest` are in order, hold `put`'s bytes, and end where `hi` says.
proof fn lemma_merge_end(
    f: Seq<(nat, Seq<u8>)>,
    fa: Seq<(nat, Seq<u8>)>,
    cl: Seq<(nat, Seq<u8>)>,
    rest: Seq<(nat, Seq<u8>)>,
    p: Seq<(nat, Seq<u8>)>,
    s0: nat,
    me2: nat,
    lo: nat,
    off: nat,
    d: Seq<u8>,
)
    requires
        ok(f),
        opened(f, fa, cl, rest, s0, me2, (if lo >= off { lo } else { off }), off + d.len()),
        pcs(p, s0, me2, me2, cl, d, off),
    ensures
        ok(fa + p + rest),
        vw(fa + p + rest) == put(vw(f), lo, off, d),
        pos(fa + p + rest).len() == sum_len(fa + p + rest),
        hi_of(fa + p + rest) == (if rest.len() == 0 { me2 } else { hi_of(f) }),
{
    reveal(opened);
    reveal(pcs);
    let g = fa + p + rest;
    lemma_ok_split(fa + cl, rest);
    lemma_ok_split(fa, cl);
    lemma_new_ok(fa, p, rest, s0, me2);
    lemma_new_view(f, fa, cl, rest, p, s0, me2, lo, off, d);
    lemma_len(g);
    if rest.len() > 0 {
        assert(g.last() == rest.last() && f.last() == rest.last());
    } else {
        assert(g.last() == p.last());
    }
}

/// A frame whose positions are all held changes nothing; one that leaves the count of positions held unchanged holds
/// no new position.
proof fn lemma_put_same(m: Map<nat, u8>, lo: nat, off: nat, d: Seq<u8>)
    ensures
        (forall|k: nat| (if lo >= off { lo } else { off }) <= k < off + d.len() ==> #[trigger] m.contains_key(k))
            ==> put(m, lo, off, d).dom() == m.dom(),
        put(m, lo, off, d).dom().len() == m.dom().len() ==> put(m, lo, off, d) == m,
{
    let pv = put(m, lo, off, d);
    let s: nat = if lo >= off { lo } else { off };
    if forall|k: nat| s <= k < off + d.len() ==> #[trigger] m.contains_key(k) {
        assert(pv.dom() =~= m.dom());
    }
    if pv.dom().len() == m.dom().len() {
        assert(m.dom().subset_of(pv.dom()));
        if exists|x: nat| pv.dom().contains(x) && !m.dom().contains(x) {
            let x = choose|x: nat| pv.dom().contains(x) && !m.dom().contains(x);
            assert(m.dom().subset_of(pv.dom().remove(x)));
            vstd::set_lib::lemma_len_subset(m.dom(), pv.dom().remove(x));
        }
        assert(pv.dom() =~= m.dom());
        assert(pv =~= m);
    }
}

/// `insert`'s cost from its parts: the walk and the merge.
proof fn lemma_ins_cost(h: nat, d: nat, m: nat, cw: nat, cm: nat)
    requires
        m <= d + 1,
        cw <= 2 * (2 * (h + 1) + m + 2),
        cm <= 108 * (h + 1) + 6 * d + 1200,
    ensures
        1 + cw + cm <= c_ins1() * (h + 1) * (d / (K as nat) + 4) + c_ins2() * (d + 4 * K),
        1 + cw <= c_ins1() * (h + 1) * (d / (K as nat) + 4) + c_ins2() * (d + 4 * K),
        1 <= c_ins1() * (h + 1) * (d / (K as nat) + 4) + c_ins2() * (d + 4 * K),
        1 + cw + cm <= 112 * (h + 1) + 8 * d + 1207,
{
    assert((h + 1) * (d / (K as nat) + 4) >= (h + 1) * 4) by (nonlinear_arith);
    assert(c_ins1() * (h + 1) * (d / (K as nat) + 4) == 28 * ((h + 1) * (d / (K as nat) + 4))) by (nonlinear_arith)
        requires
            c_ins1() == 28,
    ;
}

/// D3 steps 5-6 after `open_up`: cut the merged bytes into fresh pieces, then join `A`, the pieces, the kept `Rc` and
/// what is left of `B`. Returns the tree and its pieces' chunks.
fn rebuild(
    mv: &Vec<(u64, CapVec<u8>)>,
    a: Tree<CapVec<u8>>,
    z: Option<(u64, CapVec<u8>)>,
    b2: Tree<CapVec<u8>>,
    data: &[u8],
    lo: u64,
    off: u64,
    s0: u64,
    me2: u64,
    _hh: Ghost<nat>,
    _f: Ghost<Seq<(nat, Seq<u8>)>>,
) -> (r: (Tree<CapVec<u8>>, Ghost<Seq<(nat, Seq<u8>)>>, Ghost<nat>))
    requires
        ok(_f@),
        opened(
            _f@,
            mp(seq(a)),
            mp(mv@),
            zs(z) + mp(seq(b2)),
            s0 as nat,
            me2 as nat,
            (if lo >= off { lo } else { off }) as nat,
            (off + data@.len()) as nat,
        ),
        off + data@.len() <= VARINT_MAX,
        s0 <= (if lo >= off { lo } else { off }) < me2 <= VARINT_MAX,
        crate::avl::wf(a),
        keys_lt(a, s0),
        ht(a) <= _hh@,
        crate::avl::wf(b2),
        ht(b2) <= _hh@,
        z is Some ==> (z->0).0 == me2 && keys_gt(b2, me2),
        z is None ==> keys_ge(b2, me2),
        seq(a).len() + seq(b2).len() <= _f@.len() <= VARINT_MAX,
    ensures
        ({
            let (fa, p, rest) = (mp(seq(a)), r.1@, zs(z) + mp(seq(b2)));
            &&& crate::avl::wf(r.0)
            &&& mp(seq(r.0)) == fa + p + rest
            &&& ok(fa + p + rest)
            &&& vw(fa + p + rest) == put(vw(_f@), lo as nat, off as nat, data@)
            &&& pos(fa + p + rest).len() == sum_len(fa + p + rest)
            &&& hi_of(fa + p + rest) == (if rest.len() == 0 { me2 as nat } else { hi_of(_f@) })
        }),
        r.2@ <= 26 * (_hh@ + 1) + 2 * (me2 - s0) + 146,
{
    let ghost f = _f@;
    let ghost fa = mp(seq(a));
    let ghost cl = mp(mv@);
    let ghost rest = zs(z) + mp(seq(b2));
    let ghost mut work: nat = 1;
    let s = if lo >= off {
        lo
    } else {
        off
    };
    let e = off + data.len() as u64;
    proof {
        lemma2_to64_rest();
        lemma_opened(f, fa, cl, rest, s0 as nat, me2 as nat, s as nat, e as nat);
    }
    let (ps, Ghost(c2)) = fill_all(mv, data, off, s0, me2, s, e);
    let ghost p = mp(ps@);
    proof {
        lemma_pcs_done(p, s0 as nat, me2 as nat, cl, data@, off as nat);
    }
    let (t2, Ghost(c3)) = close_up(a, ps, z, b2, s0, me2, _hh);
    proof {
        lemma_merge_end(f, fa, cl, rest, p, s0 as nat, me2 as nat, lo as nat, off as nat, data@);
        work = work + c2 + c3;
    }
    (t2, Ghost(p), Ghost(work))
}

/// D3 steps 1-6 on the tree `t` of chunks `f` (ending at `hi0`) for a frame `[s, e)`: `open_up`, then `rebuild`.
/// Returns the new tree and the end of its last chunk.
fn merge(
    t: Tree<CapVec<u8>>,
    hi0: u64,
    lo: u64,
    off: u64,
    data: &[u8],
    s: u64,
    e: u64,
    _f: Ghost<Seq<(nat, Seq<u8>)>>,
) -> (r: (Tree<CapVec<u8>>, u64, Ghost<nat>))
    requires
        crate::avl::wf(t),
        ok(_f@),
        _f@ == mp(seq(t)),
        _f@.len() <= VARINT_MAX,
        hi0 == hi_of(_f@),
        s == (if lo >= off { lo } else { off }),
        e == off + data@.len(),
        s < e <= VARINT_MAX,
    ensures
        crate::avl::wf(r.0),
        ok(mp(seq(r.0))),
        vw(mp(seq(r.0))) == put(vw(_f@), lo as nat, off as nat, data@),
        pos(mp(seq(r.0))).len() == sum_len(mp(seq(r.0))),
        r.1 == hi_of(mp(seq(r.0))),
        r.2@ <= 108 * (ht(t) + 1) + 6 * data@.len() + 1199,
{
    let ghost f = _f@;
    let ghost h = ht(t);
    let ghost mut work: nat = 1;
    let ((a, mv, z, b2), (s0, me2), Ghost(c1)) = open_up(t, s, e, Ghost(f));
    let ghost rest = zs(z) + mp(seq(b2));
    let hi = if z.is_none() && b2.is_none() {
        me2
    } else {
        hi0
    };
    proof {
        assert(rest.len() == 0 <==> z.is_none() && b2.is_none()) by {
            if b2.is_some() {
                lemma_seq_node(b2);
            }
        }
    }
    let (t2, Ghost(_p), Ghost(c2)) = rebuild(&mv, a, z, b2, data, lo, off, s0, me2, Ghost(h), Ghost(f));
    // `mv` (M's drained chunks) drops at the end of this fn: an implicit O(|M|) free that the ghost cost does not count (frees are outside the cost model, TRUSTED.md's Vec row).
    proof {
        work = work + c1 + c2;
    }
    (t2, hi, Ghost(work))
}

/// `take_front_w`'s loop over the tree `t` of chunks `f`: `pop_min` while the next chunk starts where the bytes taken
/// end and fits in what is left of `max`, appending its bytes to `out`. Returns the rest, the end `r` of the bytes taken,
/// and how many chunks were.
fn take_run(t: Tree<CapVec<u8>>, st: u64, max: u64, out: &mut CapVec<u8>, _f: Ghost<Seq<(nat, Seq<u8>)>>) -> (res: (
    Tree<CapVec<u8>>,
    u64,
    Ghost<int>,
    Ghost<nat>,
))
    requires
        ok(_f@),
        _f@.len() < pow2(63),
        crate::avl::wf(t),
        mp(seq(t)) == _f@,
        st <= VARINT_MAX,
        forall|k: nat| #[trigger] pos(_f@).contains(k) ==> k >= st,
        old(out).wf(),
        old(out)@.len() + max <= old(out).cap(),
    ensures
        ({
            let (t2, r, i) = (res.0, res.1, res.2@);
            &&& 0 <= i <= _f@.len()
            &&& crate::avl::wf(t2)
            &&& ht(t2) <= ht(t)
            &&& mp(seq(t2)) == _f@.skip(i)
            &&& st <= r <= VARINT_MAX
            &&& r - st <= max
            &&& i == 0 <==> r == st
            &&& i > 0 ==> r == end(_f@[i - 1])
            &&& keys_ge(t2, r)
            &&& seq(t2).len() > 0 && seq(t2)[0].0 == r ==> seq(t2)[0].1@.len() > max - (r - st)
            &&& forall|k: nat| st <= k < r ==> #[trigger] pos(_f@).contains(k)
            &&& final(out).wf()
            &&& final(out).cap() == old(out).cap()
            &&& final(out)@ == old(out)@ + Seq::new((r - st) as nat, |j: int| vw(_f@)[(st + j) as nat])
        }),
        res.3@ <= 1 + 8 * (ht(t) + 1) + 9 * (res.1 - st),
{
    let ghost _f = _f@;
    let ghost h = ht(t);
    let ghost mut work: nat = 1;
    proof {
        lemma_ht_le(t);
        lemma_at_ok(_f);
        assert forall|j: int| 0 <= j < _f.len() implies #[trigger] _f[j].0 >= st by {
            assert(inf(_f, j, _f[j].0));
        }
        assert(_f.skip(0) =~= _f);
        assert forall|j: int| 0 <= j < seq(t).len() implies #[trigger] seq(t)[j].0 >= st by {
            assert(_f[j].0 == seq(t)[j].0);
        }
    }
    let mut t = t;
    let mut r = st;
    let ghost mut i: int = 0;
    let (fl, Ghost(c)) = front_at(&t, r);
    let mut go = match fl {
        Some(n) => n as u64 <= max,
        None => false,
    };
    proof {
        work = work + c;
        assert(out@ =~= old(out)@ + Seq::new((r - st) as nat, |j: int| vw(_f)[(st + j) as nat]));
    }
    while go
        invariant
            ok(_f),
            _f.len() < pow2(63),
            0 <= i <= _f.len(),
            crate::avl::wf(t),
            mp(seq(t)) == _f.skip(i),
            ht(t) <= h <= 126,
            st <= r <= VARINT_MAX,
            r - st <= max,
            i == 0 <==> r == st,
            i > 0 ==> r == end(_f[i - 1]),
            forall|k: nat| #[trigger] pos(_f).contains(k) ==> k >= st,
            forall|k: nat| st <= k < r ==> #[trigger] pos(_f).contains(k),
            out.wf(),
            out.cap() == old(out).cap(),
            old(out)@.len() + max <= out.cap(),
            out@ == old(out)@ + Seq::new((r - st) as nat, |j: int| vw(_f)[(st + j) as nat]),
            keys_ge(t, r),
            go ==> seq(t).len() > 0 && seq(t)[0].0 == r && seq(t)[0].1@.len() <= max - (r - st),
            !go ==> (seq(t).len() > 0 && seq(t)[0].0 == r ==> seq(t)[0].1@.len() > max - (r - st)),
            work <= 1 + (h + 1) + (if i > 0 { 7 * (h + 1) } else { 0 }) + 9 * (r - st),
        decreases seq(t).len(),
    {
        proof {
            assert(seq(t).len() == mp(seq(t)).len());
            assert(seq(t).len() == _f.len() - i);
        }
        let (t2, _k, v, Ghost(cp)) = pop_min(t);
        proof {
            lemma_take_step(_f, i, t, t2, _k, v);
            assert(seq(t)[0] == (_k, v));
        }
        let ghost o1 = out@;
        let ghost vv = v@;
        let n = v.len() as u64;
        let Ghost(cw) = out.push_slice(v.as_slice());
        let ghost r0 = r;
        r = r + n;
        proof {
            lemma_take_out(old(out)@, o1, vv, _f, st as nat, r0 as nat);
            assert forall|kk: nat| st <= kk < r implies #[trigger] pos(_f).contains(kk) by {
                if kk >= r0 {
                    assert(pos(_f).contains((_k + (kk - _k)) as nat));
                }
            }
        }
        let (fl, Ghost(c)) = front_at(&t2, r);
        proof {
            assert(c_pop() == 6);
            assert(c_pop() * (ht(t) + 1) == 6 * (ht(t) + 1));
            assert(cp <= 6 * (h + 1));
            assert(c <= h + 1);
            assert(i > 0 ==> n >= K);
            assert(cp + cw + c + 1 <= 7 * (h + 1) + 2 * n);
            assert(i > 0 ==> 7 * (h + 1) + 2 * n <= 9 * n);
        }
        t = t2;
        go = match fl {
            Some(m) => m as u64 <= max - (r - st),
            None => false,
        };
        proof {
            work = work + cp + cw + c + 1;
            i = i + 1;
        }
    }
    (t, r, Ghost(i), Ghost(work))
}

/// The piece cut from chunk `i` at `r2`, then the chunks after `i`.
spec fn cut_rest(f: Seq<(nat, Seq<u8>)>, i: int, r2: nat) -> Seq<(nat, Seq<u8>)> {
    seq![(r2, f[i].1.subrange(r2 - f[i].0, f[i].1.len() as int))] + f.skip(i + 1)
}

/// `lemma_cut`'s order facts: the cut piece and the chunks after it are in order and end where `f` does.
proof fn lemma_cut_ok(f: Seq<(nat, Seq<u8>)>, i: int, r2: nat)
    requires
        ok(f),
        0 <= i < f.len(),
        f[i].0 < r2 < end(f[i]),
    ensures
        ok(cut_rest(f, i, r2)),
        end(cut_rest(f, i, r2).last()) == end(f.last()),
{
    let x = (r2, f[i].1.subrange(r2 - f[i].0, f[i].1.len() as int));
    let a = seq![x];
    let b = f.skip(i + 1);
    let e = end(f[i]);
    assert(end(x) == e);
    assert(a[0] == x);
    assert(ok(a));
    lemma_ok_sub(f, i + 1, f.len() as int);
    assert(b =~= f.subrange(i + 1, f.len() as int));
    if b.len() > 0 {
        assert(b[0] == f[i + 1]);
        if e == b[0].0 {
            assert(fol(f, i + 1));
        }
    }
    lemma_ok_cat(a, b);
    assert(cut_rest(f, i, r2) == a + b);
    if b.len() > 0 {
        assert((a + b).last() == b.last());
        assert(b.last() == f.last());
    } else {
        assert((a + b).last() == x);
        assert(f.last() == f[i]);
    }
}

/// `lemma_cut`'s positions: those of `f` at or past `r2`.
proof fn lemma_cut_pos(f: Seq<(nat, Seq<u8>)>, i: int, r2: nat)
    requires
        ok(f),
        0 <= i < f.len(),
        f[i].0 < r2 < end(f[i]),
    ensures
        forall|k: nat| #[trigger] pos(cut_rest(f, i, r2)).contains(k) <==> pos(f).contains(k) && k >= r2,
{
    let x = (r2, f[i].1.subrange(r2 - f[i].0, f[i].1.len() as int));
    let a = seq![x];
    let b = f.skip(i + 1);
    let e = end(f[i]);
    assert forall|j: int| 0 <= j < i + 1 implies end(#[trigger] f[j]) <= e by {
        if j < i {
            assert(end(f[j]) <= f[i].0);
        }
    }
    assert forall|j: int| i + 1 <= j < f.len() implies #[trigger] f[j].0 >= e by {}
    lemma_take_rest(f, i + 1, e);
    lemma_pos_cat(a, b);
    assert(cut_rest(f, i, r2) == a + b);
    assert(a[0] == x);
    assert forall|k: nat| #[trigger] pos(a).contains(k) <==> r2 <= k < e by {
        if r2 <= k < e {
            assert(inf(a, 0, k));
        }
    }
    assert forall|k: nat| #[trigger] pos(a + b).contains(k) <==> pos(f).contains(k) && k >= r2 by {
        if r2 <= k < e {
            assert(inf(f, i, k));
        }
        if pos(f).contains(k) && k >= r2 && k < e {
            let j = choose|j: int| inf(f, j, k);
            if j < i {
                assert(end(f[j]) <= f[i].0);
            }
            if j > i {
                assert(e <= f[j].0);
            }
        }
    }
}

/// `lemma_cut`'s bytes: those of `f`.
proof fn lemma_cut_vw(f: Seq<(nat, Seq<u8>)>, i: int, r2: nat)
    requires
        ok(f),
        0 <= i < f.len(),
        f[i].0 < r2 < end(f[i]),
        ok(cut_rest(f, i, r2)),
    ensures
        forall|k: nat| #[trigger] pos(cut_rest(f, i, r2)).contains(k) ==> vw(cut_rest(f, i, r2))[k] == vw(f)[k],
{
    let x = (r2, f[i].1.subrange(r2 - f[i].0, f[i].1.len() as int));
    let b = f.skip(i + 1);
    let g = cut_rest(f, i, r2);
    let e = end(f[i]);
    assert(g[0] == x);
    lemma_at_ok(f);
    lemma_at_ok(g);
    assert forall|k: nat| #[trigger] pos(g).contains(k) implies vw(g)[k] == vw(f)[k] by {
        let j = choose|j: int| inf(g, j, k);
        if j == 0 {
            assert(inf(f, i, k));
        } else {
            assert(g[j] == b[j - 1]);
            assert(b[j - 1] == f[i + j]);
            assert(inf(f, i + j, k));
        }
    }
}

/// Cutting chunk `i` of `f` at `r2` inside it: the piece from `r2` and the chunks after `i` hold the positions of `f`
/// at or past `r2`, with their bytes, in order, and end where `f` does.
proof fn lemma_cut(f: Seq<(nat, Seq<u8>)>, i: int, r2: nat)
    requires
        ok(f),
        0 <= i < f.len(),
        f[i].0 < r2 < end(f[i]),
    ensures
        ok(cut_rest(f, i, r2)),
        forall|k: nat| #[trigger] pos(cut_rest(f, i, r2)).contains(k) <==> pos(f).contains(k) && k >= r2,
        forall|k: nat| #[trigger] pos(cut_rest(f, i, r2)).contains(k) ==> vw(cut_rest(f, i, r2))[k] == vw(f)[k],
        pos(cut_rest(f, i, r2)).len() == sum_len(cut_rest(f, i, r2)),
        end(cut_rest(f, i, r2).last()) == end(f.last()),
{
    lemma_cut_ok(f, i, r2);
    lemma_cut_pos(f, i, r2);
    lemma_cut_vw(f, i, r2);
    lemma_len(cut_rest(f, i, r2));
}

/// `take_front_w`'s cut: `out` gains the cut chunk's first `rem` bytes, which with `[st, r)` are held, and `r + rem`
/// is held too.
proof fn lemma_tf_cut(f: Seq<(nat, Seq<u8>)>, i: int, st: nat, r: nat, rem: nat, o: Seq<u8>, o1: Seq<u8>)
    requires
        ok(f),
        0 <= i < f.len(),
        f[i].0 == r,
        st <= r,
        0 < rem < f[i].1.len(),
        forall|k: nat| st <= k < r ==> #[trigger] pos(f).contains(k),
        o1 == o + Seq::new((r - st) as nat, |j: int| vw(f)[(st + j) as nat]),
    ensures
        o1 + f[i].1.subrange(0, rem as int) == o + Seq::new((r + rem - st) as nat, |j: int| vw(f)[(st + j) as nat]),
        forall|k: nat| st <= k < r + rem ==> #[trigger] pos(f).contains(k),
        pos(f).contains(r + rem),
{
    lemma_at_ok(f);
    let vv = f[i].1.subrange(0, rem as int);
    assert forall|j: int| 0 <= j < vv.len() implies #[trigger] vv[j] == vw(f)[(r + j) as nat] by {
        assert(inf(f, i, (r + j) as nat));
    }
    lemma_take_out(o, o1, vv, f, st, r);
    assert forall|k: nat| st <= k < r + rem implies #[trigger] pos(f).contains(k) by {
        if k >= r {
            assert(inf(f, i, k));
        }
    }
    assert(inf(f, i, r + rem));
}

/// Moves the first `rem` bytes of `t`'s first chunk (`f[i]`, which holds more) into `out`; the rest of it goes back
/// under its new start in a fresh piece of exactly its length, a run head.
fn cut_front(t: Tree<CapVec<u8>>, rem: u64, out: &mut CapVec<u8>, _f: Ghost<Seq<(nat, Seq<u8>)>>, _i: Ghost<int>) -> (res: (
    Tree<CapVec<u8>>,
    Ghost<nat>,
))
    requires
        ok(_f@),
        _f@.len() < pow2(63),
        0 <= _i@ < _f@.len(),
        crate::avl::wf(t),
        mp(seq(t)) == _f@.skip(_i@),
        0 < rem < _f@[_i@].1.len(),
        old(out).wf(),
        old(out)@.len() + rem <= old(out).cap(),
    ensures
        crate::avl::wf(res.0),
        mp(seq(res.0)) == cut_rest(_f@, _i@, (_f@[_i@].0 + rem) as nat),
        final(out).wf(),
        final(out).cap() == old(out).cap(),
        final(out)@ == old(out)@ + _f@[_i@].1.subrange(0, rem as int),
        res.1@ <= 12 * (ht(t) + 1) + CAP + 3,
{
    let ghost f = _f@;
    let ghost i = _i@;
    let ghost mut work: nat = 1;
    proof {
        assert(seq(t).len() == mp(seq(t)).len());
        assert(seq(t).len() == f.len() - i);
    }
    let (t3, k, v, Ghost(cp)) = pop_min(t);
    proof {
        lemma_take_step(f, i, t, t3, k, v);
        assert(c_pop() == 6);
    }
    let n = v.len();
    let ru = rem as usize;
    let Ghost(c3) = out.push_slice(vstd::slice::slice_subrange(v.as_slice(), 0, ru));
    let mut w: CapVec<u8> = CapVec::new(n - ru);
    let Ghost(c4) = w.push_slice(vstd::slice::slice_subrange(v.as_slice(), ru, n));
    let r2 = k + rem;
    proof {
        assert(w@ =~= f[i].1.subrange(rem as int, f[i].1.len() as int));
        assert forall|j: int| 0 <= j < seq(t3).len() implies #[trigger] seq(t3)[j].0 > r2 by {}
        assert(seq::<CapVec<u8>>(None).len() == 0);
    }
    let ghost wv = w@;
    let (t4, Ghost(cj)) = join(None, r2, w, t3);
    proof {
        assert(seq(t4) =~= seq![(r2, w)] + seq(t3)) by {
            assert(seq::<CapVec<u8>>(None) =~= Seq::<(u64, CapVec<u8>)>::empty());
        }
        lemma_mp_cat(seq![(r2, w)], seq(t3));
        assert(mp(seq![(r2, w)]) =~= seq![(r2 as nat, wv)]);
        assert(mp(seq(t4)) =~= cut_rest(f, i, r2 as nat));
        assert(c_join() == 6);
        assert(cj <= 6 * (ht(t3) + 1));
        work = work + cp + c3 + 1 + c4 + cj + 1;
    }
    (t4, Ghost(work))
}

/// `take_front_w`'s cost in the brief's form, from its parts: `take_run`'s, a lookup, and at most one cut.
proof fn lemma_tf_cost(h: nat, max: nat, c: nat, c2: nat, work: nat, d: nat)
    requires
        d <= max,
        c <= 1 + 8 * (h + 1) + 9 * d,
        c2 <= h + 1,
        work <= 1 + c + c2 + 12 * (h + 1) + CAP + 3,
    ensures
        work <= c_tf1() * (h + 1) * (max / (K as nat) + 3) + c_tf2() * (max + CAP),
{
    assert((h + 1) * (max / (K as nat) + 3) >= 3 * (h + 1)) by (nonlinear_arith);
    assert(8 * (h + 1) * (max / (K as nat) + 3) == 8 * ((h + 1) * (max / (K as nat) + 3))) by (nonlinear_arith);
}

/// `take_front_w` on the tree `t` of chunks `f`: the run's chunks that fit whole (`take_run`), then, if the limit falls
/// inside a chunk, its first bytes (`cut_front`). Returns the rest, the end `r` of the bytes taken, and whether `r` is
/// held.
fn take_tree(t: Tree<CapVec<u8>>, st: u64, max: u64, out: &mut CapVec<u8>, _f: Ghost<Seq<(nat, Seq<u8>)>>) -> (res: (
    Tree<CapVec<u8>>,
    u64,
    bool,
    Ghost<nat>,
))
    requires
        ok(_f@),
        _f@.len() < pow2(63),
        crate::avl::wf(t),
        mp(seq(t)) == _f@,
        st <= VARINT_MAX,
        forall|k: nat| #[trigger] pos(_f@).contains(k) ==> k >= st,
        old(out).wf(),
        old(out)@.len() + max <= old(out).cap(),
    ensures
        ({
            let (f, g, r) = (_f@, mp(seq(res.0)), res.1 as nat);
            &&& crate::avl::wf(res.0)
            &&& ok(g)
            &&& st <= r <= st + max
            &&& forall|k: nat| st <= k < r ==> #[trigger] pos(f).contains(k)
            &&& res.2 <==> pos(f).contains(r)
            &&& r < st + max ==> !res.2
            &&& forall|k: nat| #[trigger] pos(g).contains(k) <==> pos(f).contains(k) && k >= r
            &&& forall|k: nat| #[trigger] pos(g).contains(k) ==> vw(g)[k] == vw(f)[k]
            &&& pos(g).len() == sum_len(g)
            &&& g.len() > 0 ==> end(g.last()) == end(f.last())
            &&& final(out).wf()
            &&& final(out).cap() == old(out).cap()
            &&& final(out)@ == old(out)@ + Seq::new((r - st) as nat, |j: int| vw(f)[(st + j) as nat])
        }),
        res.3@ <= c_tf1() * (ht(t) + 1) * (max / K + 3) + c_tf2() * (max + CAP),
{
    let ghost f = _f@;
    let ghost h = ht(t);
    let ghost mut work: nat = 1;
    let (t2, r, Ghost(i), Ghost(c)) = take_run(t, st, max, out, Ghost(f));
    proof {
        lemma_take_end(f, i, st as nat, r, t2);
        work = work + c;
    }
    let (fl, Ghost(c2)) = front_at(&t2, r);
    proof {
        work = work + c2;
    }
    let mut t = t2;
    let mut r = r;
    let mut held_at_end = fl.is_some();
    if fl.is_some() && r - st < max {
        let ghost o1 = out@;
        let rem = max - (r - st);
        proof {
            assert(f.skip(i)[0] == f[i]);
            assert(mp(seq(t))[0] == f[i]);
        }
        let (t4, Ghost(c3)) = cut_front(t, rem, out, Ghost(f), Ghost(i));
        proof {
            work = work + c3;
            lemma_cut(f, i, (r + rem) as nat);
            lemma_tf_cut(f, i, st as nat, r as nat, rem as nat, old(out)@, o1);
        }
        t = t4;
        r = r + rem;
        held_at_end = true;
    }
    proof {
        lemma_tf_cost(h, max as nat, c, c2, work, (r - st) as nat);
    }
    (t, r, held_at_end, Ghost(work))
}

// ---- `run_end`: the end of the run holding a position.

/// The number of chunks of `f` starting in `[lo, hi)`.
spec fn nch(f: Seq<(nat, Seq<u8>)>, lo: nat, hi: nat) -> nat
    decreases f.len(),
{
    if f.len() == 0 {
        0
    } else {
        nch(f.drop_last(), lo, hi) + if lo <= f.last().0 < hi {
            1nat
        } else {
            0
        }
    }
}

/// No chunk starting in `[lo, hi)`: none counted.
proof fn lemma_nch_out(f: Seq<(nat, Seq<u8>)>, lo: nat, hi: nat)
    requires
        forall|j: int| 0 <= j < f.len() ==> !(lo <= #[trigger] f[j].0 < hi),
    ensures
        nch(f, lo, hi) == 0,
    decreases f.len(),
{
    if f.len() > 0 {
        let g = f.drop_last();
        assert forall|j: int| 0 <= j < g.len() implies !(lo <= #[trigger] g[j].0 < hi) by {
            assert(g[j] == f[j]);
        }
        lemma_nch_out(g, lo, hi);
        assert(f.last() == f[f.len() - 1]);
    }
}

/// Every chunk starting below `h1 <= h2`: the count up to `h1` is the count up to `h2`.
proof fn lemma_nch_hi(f: Seq<(nat, Seq<u8>)>, lo: nat, h1: nat, h2: nat)
    requires
        h1 <= h2,
        forall|j: int| 0 <= j < f.len() ==> #[trigger] f[j].0 < h1,
    ensures
        nch(f, lo, h1) == nch(f, lo, h2),
    decreases f.len(),
{
    if f.len() > 0 {
        let g = f.drop_last();
        assert forall|j: int| 0 <= j < g.len() implies #[trigger] g[j].0 < h1 by {
            assert(g[j] == f[j]);
        }
        lemma_nch_hi(g, lo, h1, h2);
        assert(f.last() == f[f.len() - 1]);
    }
}

/// `a / K + 1 == (a + K) / K`, and division by `K` is monotone.
proof fn lemma_div_k(a: nat, b: nat)
    requires
        a + K <= b,
    ensures
        a / (K as nat) + 1 <= b / (K as nat),
{
    vstd::arithmetic::div_mod::lemma_hoist_over_denominator(a as int, 1, K as nat);
    vstd::arithmetic::div_mod::lemma_div_is_ordered((a + K) as int, b as int, K as int);
}

/// The last chunk of `f` starts past `lo` with `[lo, its start)` held: it is a follower.
proof fn lemma_nch_fol(f: Seq<(nat, Seq<u8>)>, lo: nat)
    requires
        ok(f),
        f.len() > 0,
        lo < f.last().0,
        pos(f).contains((f.last().0 - 1) as nat),
    ensures
        f.last().1.len() >= K,
{
    let n = f.len() - 1;
    let g = f.drop_last();
    lemma_pos_last(f);
    assert(pos(g).contains((f.last().0 - 1) as nat));
    lemma_pos_last(g);
    assert(g.last() == f[n - 1]);
    assert(end(f[n - 1]) <= f[n].0);
    assert(fol(f, n));
}

/// `[lo, hi)` held, every chunk starting there ending by `hi`: at most `1 + (hi − lo)/K` such chunks (all but the
/// first are followers lying inside).
proof fn lemma_nch_tight(f: Seq<(nat, Seq<u8>)>, lo: nat, hi: nat)
    requires
        lo <= hi,
        ok(f),
        forall|k: nat| lo <= k < hi ==> #[trigger] pos(f).contains(k),
        forall|j: int| 0 <= j < f.len() && lo <= #[trigger] f[j].0 < hi ==> end(f[j]) <= hi,
    ensures
        nch(f, lo, hi) <= 1 + ((hi - lo) as nat) / (K as nat),
    decreases f.len(),
{
    if f.len() > 0 {
        let n = f.len() - 1;
        let g = f.drop_last();
        let x = f.last();
        assert(x == f[n]);
        lemma_pos_last(f);
        assert forall|j: int| 0 <= j < g.len() implies #[trigger] g[j].0 < x.0 && end(g[j]) <= x.0 by {
            assert(g[j] == f[j]);
            assert(end(f[j]) <= f[n].0);
        }
        if x.0 >= hi {
            assert forall|k: nat| lo <= k < hi implies #[trigger] pos(g).contains(k) by {
                assert(pos(f).contains(k));
            }
            assert forall|j: int| 0 <= j < g.len() && lo <= #[trigger] g[j].0 < hi implies end(g[j]) <= hi by {
                assert(g[j] == f[j]);
            }
            lemma_nch_tight(g, lo, hi);
        } else if x.0 <= lo {
            lemma_nch_out(g, lo, hi);
        } else {
            lemma_nch_fol(f, lo);
            assert forall|k: nat| lo <= k < x.0 implies #[trigger] pos(g).contains(k) by {
                assert(pos(f).contains(k));
            }
            lemma_nch_tight(g, lo, x.0);
            lemma_nch_hi(g, lo, x.0, hi);
            lemma_div_k((x.0 - lo) as nat, (hi - lo) as nat);
        }
    }
}

/// `[lo, hi)` held: at most `2 + (hi − lo)/K` chunks start there (D7(c), the follower rule).
proof fn lemma_nch_held(f: Seq<(nat, Seq<u8>)>, lo: nat, hi: nat)
    requires
        lo <= hi,
        ok(f),
        forall|k: nat| lo <= k < hi ==> #[trigger] pos(f).contains(k),
    ensures
        nch(f, lo, hi) <= 2 + ((hi - lo) as nat) / (K as nat),
    decreases f.len(),
{
    if f.len() > 0 {
        let n = f.len() - 1;
        let g = f.drop_last();
        let x = f.last();
        assert(x == f[n]);
        lemma_pos_last(f);
        assert forall|j: int| 0 <= j < g.len() implies #[trigger] g[j].0 < x.0 && end(g[j]) <= x.0 by {
            assert(g[j] == f[j]);
            assert(end(f[j]) <= f[n].0);
        }
        if x.0 >= hi {
            assert forall|k: nat| lo <= k < hi implies #[trigger] pos(g).contains(k) by {
                assert(pos(f).contains(k));
            }
            lemma_nch_held(g, lo, hi);
        } else if x.0 <= lo {
            lemma_nch_out(g, lo, hi);
        } else {
            assert forall|k: nat| lo <= k < x.0 implies #[trigger] pos(g).contains(k) by {
                assert(pos(f).contains(k));
            }
            lemma_nch_tight(g, lo, x.0);
            lemma_nch_hi(g, lo, x.0, hi);
            vstd::arithmetic::div_mod::lemma_div_is_ordered((x.0 - lo) as int, (hi - lo) as int, K as int);
        }
    }
}

/// `M` for `[e, r]` counts no more than the chunks starting in `[p, r)`, for `p <= e` and no chunk starting at `r`.
proof fn lemma_nm_nch(f: Seq<(nat, Seq<u8>)>, p: nat, e: nat, r: nat)
    requires
        p <= e,
        forall|j: int| 0 <= j < f.len() ==> #[trigger] f[j].0 != r,
    ensures
        nm(f, e, r) <= nch(f, p, r),
    decreases f.len(),
{
    if f.len() > 0 {
        let g = f.drop_last();
        assert forall|j: int| 0 <= j < g.len() implies #[trigger] g[j].0 != r by {
            assert(g[j] == f[j]);
        }
        lemma_nm_nch(g, p, e, r);
        assert(f.last() == f[f.len() - 1]);
    }
}

/// `vis` grows with `e` (from `s` up).
proof fn lemma_vis_mono(t: Tree<CapVec<u8>>, s: u64, e1: u64, e2: u64)
    requires
        s <= e1 <= e2,
    ensures
        vis(t, s, e1) <= vis(t, s, e2),
    decreases t,
{
    if let Some(b) = t {
        lemma_vis_mono(b.left, s, e1, e2);
        lemma_vis_mono(b.right, s, e1, e2);
    }
}

/// Every chunk starting at or past `s` ends by `r` or starts past it.
#[verifier::opaque]
spec fn past(f: Seq<(nat, Seq<u8>)>, s: nat, r: nat) -> bool {
    forall|j: int| 0 <= j < f.len() && #[trigger] f[j].0 >= s ==> end(f[j]) <= r || f[j].0 > r
}

/// Every chunk starting at or past `s` ends by `r`.
#[verifier::opaque]
spec fn upto(f: Seq<(nat, Seq<u8>)>, s: nat, r: nat) -> bool {
    forall|j: int| 0 <= j < f.len() && #[trigger] f[j].0 >= s ==> end(f[j]) <= r
}

/// Every chunk starting at or past `s` starts at or past `c`.
#[verifier::opaque]
spec fn fresh(f: Seq<(nat, Seq<u8>)>, s: nat, c: nat) -> bool {
    forall|j: int| 0 <= j < f.len() && #[trigger] f[j].0 >= s ==> f[j].0 >= c
}

/// `[c, r)` is held.
#[verifier::opaque]
spec fn held_in(f: Seq<(nat, Seq<u8>)>, c: nat, r: nat) -> bool {
    forall|k: nat| c <= k < r ==> #[trigger] pos(f).contains(k)
}

/// A node's chunks `l + [x] + r` and its parts.
proof fn lemma_rn_node(t: Tree<CapVec<u8>>)
    requires
        crate::avl::wf(t),
        t is Some,
        ok(mp(seq(t))),
    ensures
        ({
            let b = t->0;
            let (l, r) = (mp(seq(b.left)), mp(seq(b.right)));
            let x = (b.key as nat, b.val@);
            &&& mp(seq(t)) == l + seq![x] + r
            &&& crate::avl::wf(b.left) && crate::avl::wf(b.right)
            &&& ok(l) && ok(r)
            &&& 0 < x.1.len() && end(x) <= VARINT_MAX
        }),
{
    let b = t->0;
    let (l, r) = (mp(seq(b.left)), mp(seq(b.right)));
    let x = (b.key as nat, b.val@);
    lemma_mp_node(t);
    assert(crate::avl::wf(b.left) && crate::avl::wf(b.right));
    lemma_ok_split(l + seq![x], r);
    lemma_ok_split(l, seq![x]);
    assert(seq![x][0] == x);
}

/// The order facts of `l + [x] + r`, its positions and its last chunk.
proof fn lemma_rn_parts(l: Seq<(nat, Seq<u8>)>, x: (nat, Seq<u8>), r: Seq<(nat, Seq<u8>)>)
    requires
        ok(l + seq![x] + r),
    ensures
        0 < x.1.len(),
        forall|j: int| 0 <= j < l.len() ==> #[trigger] end(l[j]) <= x.0 && l[j].0 < x.0,
        forall|j: int| 0 <= j < r.len() ==> #[trigger] r[j].0 >= end(x),
        forall|k: nat| #[trigger] pos(l + seq![x] + r).contains(k) <==> pos(l).contains(k) || (x.0 <= k < end(x))
            || pos(r).contains(k),
        (l + seq![x] + r).last() == (if r.len() > 0 { r.last() } else { x }),
        l.len() > 0 ==> l.last() == l[l.len() - 1],
{
    let f = l + seq![x] + r;
    let n = l.len() as int;
    assert(f[n] == x);
    assert forall|j: int| 0 <= j < l.len() implies #[trigger] end(l[j]) <= x.0 && l[j].0 < x.0 by {
        assert(f[j] == l[j]);
    }
    assert forall|j: int| 0 <= j < r.len() implies #[trigger] r[j].0 >= end(x) by {
        assert(f[n + 1 + j] == r[j]);
    }
    lemma_pos_cat(l + seq![x], r);
    lemma_pos_cat(l, seq![x]);
    assert forall|k: nat| #[trigger] pos(seq![x]).contains(k) <==> x.0 <= k < end(x) by {
        if x.0 <= k < end(x) {
            assert(inf(seq![x], 0, k));
        }
    }
    if r.len() > 0 {
        assert(f.last() == r.last());
    }
}

/// `walk_run` on an empty tree.
proof fn lemma_rn_empty(f: Seq<(nat, Seq<u8>)>, s: nat, c: nat)
    requires
        f.len() == 0,
    ensures
        held_in(f, c, c),
        past(f, s, c),
        upto(f, s, c),
{
    reveal(held_in);
    reveal(past);
    reveal(upto);
}

/// What `fresh` of a node gives its parts.
proof fn lemma_rn_fresh(l: Seq<(nat, Seq<u8>)>, x: (nat, Seq<u8>), r: Seq<(nat, Seq<u8>)>, s: nat, c: nat)
    requires
        ok(l + seq![x] + r),
        fresh(l + seq![x] + r, s, c),
    ensures
        fresh(l, s, c),
        x.0 < s ==> fresh(r, s, c),
        x.0 >= s ==> x.0 >= c,
        fresh(r, s, end(x)),
        x.0 <= s ==> held_in(l, c, c) && past(l, s, c) && upto(l, s, c),
{
    reveal(fresh);
    reveal(held_in);
    reveal(past);
    reveal(upto);
    let f = l + seq![x] + r;
    let n = l.len() as int;
    lemma_rn_parts(l, x, r);
    assert(f[n] == x);
    assert forall|j: int| 0 <= j < l.len() && #[trigger] l[j].0 >= s implies l[j].0 >= c by {
        assert(f[j] == l[j]);
    }
    if x.0 < s {
        assert forall|j: int| 0 <= j < r.len() && #[trigger] r[j].0 >= s implies r[j].0 >= c by {
            assert(f[n + 1 + j] == r[j]);
        }
    }
}

/// `walk_run` past a node whose key is below `s`: the right part's result is the node's.
proof fn lemma_rn_skip(l: Seq<(nat, Seq<u8>)>, x: (nat, Seq<u8>), r: Seq<(nat, Seq<u8>)>, s: nat, c: nat, c3: nat, d3: bool)
    requires
        ok(l + seq![x] + r),
        x.0 < s,
        held_in(r, c, c3),
        past(r, s, c3),
        !d3 ==> upto(r, s, c3),
        d3 ==> r.len() > 0 && r.last().0 > c3,
    ensures
        held_in(l + seq![x] + r, c, c3),
        past(l + seq![x] + r, s, c3),
        !d3 ==> upto(l + seq![x] + r, s, c3),
        d3 ==> (l + seq![x] + r).len() > 0 && (l + seq![x] + r).last().0 > c3,
{
    reveal(held_in);
    reveal(past);
    reveal(upto);
    let f = l + seq![x] + r;
    let n = l.len() as int;
    lemma_rn_parts(l, x, r);
    assert forall|j: int| 0 <= j < f.len() && #[trigger] f[j].0 >= s implies end(f[j]) <= c3 || f[j].0 > c3 by {
        if j < n {
            assert(f[j] == l[j]);
        } else if j > n {
            assert(f[j] == r[j - n - 1]);
        }
    }
    if !d3 {
        assert forall|j: int| 0 <= j < f.len() && #[trigger] f[j].0 >= s implies end(f[j]) <= c3 by {
            if j < n {
                assert(f[j] == l[j]);
            } else if j > n {
                assert(f[j] == r[j - n - 1]);
            }
        }
    }
}

/// After the left part, the bytes reached `c1` at most the node's key.
proof fn lemma_rn_c1(l: Seq<(nat, Seq<u8>)>, x: (nat, Seq<u8>), r: Seq<(nat, Seq<u8>)>, c: nat, c1: nat)
    requires
        ok(l + seq![x] + r),
        held_in(l, c, c1),
        x.0 >= c,
    ensures
        c1 <= x.0,
{
    reveal(held_in);
    lemma_rn_parts(l, x, r);
    if c1 > x.0 {
        assert(pos(l).contains(x.0));
        let j = choose|j: int| inf(l, j, x.0);
        assert(end(l[j]) <= x.0);
    }
}

/// `walk_run` stopping at a node: the left part ended at `c1`, below the node's key.
proof fn lemma_rn_stop(l: Seq<(nat, Seq<u8>)>, x: (nat, Seq<u8>), r: Seq<(nat, Seq<u8>)>, s: nat, c: nat, c1: nat, d1: bool)
    requires
        ok(l + seq![x] + r),
        c1 <= x.0,
        d1 ==> l.len() > 0 && l.last().0 > c1,
        !d1 ==> x.0 != c1,
        held_in(l, c, c1),
        past(l, s, c1),
    ensures
        x.0 > c1,
        held_in(l + seq![x] + r, c, c1),
        past(l + seq![x] + r, s, c1),
        (l + seq![x] + r).len() > 0 && (l + seq![x] + r).last().0 > c1,
{
    reveal(held_in);
    reveal(past);
    let f = l + seq![x] + r;
    let n = l.len() as int;
    lemma_rn_parts(l, x, r);
    if d1 {
        assert(end(l[l.len() - 1]) <= x.0);
    }
    assert(x.0 > c1);
    assert forall|j: int| 0 <= j < f.len() && #[trigger] f[j].0 >= s implies end(f[j]) <= c1 || f[j].0 > c1 by {
        if j < n {
            assert(f[j] == l[j]);
        } else if j > n {
            assert(f[j] == r[j - n - 1]);
        }
    }
    if r.len() > 0 {
        assert(r.last() == r[r.len() - 1]);
    }
}

/// `walk_run` through a node starting at `c1`, the right part walked from its end to `c3`.
proof fn lemma_rn_go(
    l: Seq<(nat, Seq<u8>)>,
    x: (nat, Seq<u8>),
    r: Seq<(nat, Seq<u8>)>,
    s: nat,
    c: nat,
    c1: nat,
    c3: nat,
    d3: bool,
)
    requires
        ok(l + seq![x] + r),
        x.0 == c1,
        x.0 >= s,
        end(x) <= c3,
        held_in(l, c, c1),
        upto(l, s, c1),
        held_in(r, end(x), c3),
        past(r, s, c3),
        !d3 ==> upto(r, s, c3),
        d3 ==> r.len() > 0 && r.last().0 > c3,
    ensures
        held_in(l + seq![x] + r, c, c3),
        past(l + seq![x] + r, s, c3),
        !d3 ==> upto(l + seq![x] + r, s, c3),
        d3 ==> (l + seq![x] + r).len() > 0 && (l + seq![x] + r).last().0 > c3,
{
    reveal(held_in);
    reveal(past);
    reveal(upto);
    let f = l + seq![x] + r;
    let n = l.len() as int;
    lemma_rn_parts(l, x, r);
    assert(f[n] == x);
    assert forall|j: int| 0 <= j < f.len() && #[trigger] f[j].0 >= s implies end(f[j]) <= c3 || f[j].0 > c3 by {
        if j < n {
            assert(f[j] == l[j]);
        } else if j > n {
            assert(f[j] == r[j - n - 1]);
        }
    }
    if !d3 {
        assert forall|j: int| 0 <= j < f.len() && #[trigger] f[j].0 >= s implies end(f[j]) <= c3 by {
            if j < n {
                assert(f[j] == l[j]);
            } else if j > n {
                assert(f[j] == r[j - n - 1]);
            }
        }
    }
}

/// The in-order walk from `c` (no chunk at or past `s` starts below `c`) through the chunks starting where the bytes
/// so far end: their end `r`, and whether a chunk past `r` was met (the walk stops there). It enters a subtree only
/// if it can hold a key in `[s, r]`, so it costs at most `vis(t, s, r)`.
fn walk_run(t: &Tree<CapVec<u8>>, s: u64, c: u64) -> (r: (u64, bool, Ghost<nat>))
    requires
        crate::avl::wf(*t),
        ok(mp(seq(*t))),
        s <= c <= VARINT_MAX,
        fresh(mp(seq(*t)), s as nat, c as nat),
    ensures
        c <= r.0 <= VARINT_MAX,
        held_in(mp(seq(*t)), c as nat, r.0 as nat),
        past(mp(seq(*t)), s as nat, r.0 as nat),
        !r.1 ==> upto(mp(seq(*t)), s as nat, r.0 as nat),
        r.1 ==> mp(seq(*t)).len() > 0 && mp(seq(*t)).last().0 > r.0,
        r.2@ <= vis(*t, s, r.0),
    decreases *t,
{
    let ghost mut work: nat = 1;
    match t {
        None => {
            proof {
                lemma_rn_empty(mp(seq(*t)), s as nat, c as nat);
            }
            (c, false, Ghost(work))
        },
        Some(b) => {
            let ghost (l, rr) = (mp(seq(b.left)), mp(seq(b.right)));
            let ghost x = (b.key as nat, b.val@);
            proof {
                lemma_rn_node(*t);
                lemma_rn_fresh(l, x, rr, s as nat, c as nat);
            }
            if b.key < s {
                let (c3, d3, Ghost(w3)) = walk_run(&b.right, s, c);
                proof {
                    lemma_rn_skip(l, x, rr, s as nat, c as nat, c3 as nat, d3);
                    work = work + w3;
                }
                return (c3, d3, Ghost(work));
            }
            let (c1, d1, Ghost(w1)) = if b.key > s {
                walk_run(&b.left, s, c)
            } else {
                (c, false, Ghost(0))
            };
            proof {
                lemma_rn_c1(l, x, rr, c as nat, c1 as nat);
                work = work + w1;
            }
            if d1 || b.key != c1 {
                proof {
                    lemma_rn_stop(l, x, rr, s as nat, c as nat, c1 as nat, d1);
                }
                return (c1, true, Ghost(work));
            }
            let c2 = b.key + b.val.len() as u64;
            let (c3, d3, Ghost(w3)) = walk_run(&b.right, s, c2);
            proof {
                lemma_rn_go(l, x, rr, s as nat, c as nat, c1 as nat, c3 as nat, d3);
                if b.key > s {
                    lemma_vis_mono(b.left, s, c1, c3);
                }
                work = work + w3;
            }
            (c3, d3, Ghost(work))
        },
    }
}

/// `run_end_w`'s cost constants: at most `c_re1() · (h + 1) + c_re2() · (chunks_in(p, r) + 1)`.
pub open spec fn c_re1() -> nat {
    3
}

pub open spec fn c_re2() -> nat {
    2
}

impl Frags {
    /// The chunks whose start lies in `[lo, hi)`.
    pub closed spec fn chunks_in(&self, lo: nat, hi: nat) -> nat {
        nch(self.fs(), lo, hi)
    }

    /// The chunks of the store (its tree's nodes).
    pub closed spec fn nodes(&self) -> nat {
        seq(self.t).len()
    }

    /// The height of the store's tree.
    pub closed spec fn tree_ht(&self) -> nat {
        ht(self.t)
    }

    /// The tree's height bounds, for composing `run_end_w`'s cost: at most 126, and logarithmic in the chunks.
    pub proof fn lemma_tree_ht(&self)
        requires
            self.wf(),
        ensures
            self.tree_ht() <= 126,
            self.nodes() + 1 >= pow2(self.tree_ht() / 2),
    {
        lemma_ht_le(self.t);
        lemma_height(self.t);
    }

    /// Every chunk holds a byte: at most `held` nodes, none when nothing is held.
    pub proof fn lemma_nodes_le_held(&self)
        requires
            self.wf(),
        ensures
            self.nodes() <= self.held(),
            self.held() == 0 <==> self.nodes() == 0,
    {
        self.lemma_size();
        if self.fs().len() == 0 {
            assert(self.fs() =~= Seq::<(nat, Seq<u8>)>::empty());
        }
    }

    /// With `[lo, hi)` held, at most `2 + (hi − lo)/K` chunks start there (the follower rule).
    pub proof fn lemma_chunks_in_held(&self, lo: nat, hi: nat)
        requires
            lo <= hi,
            self.wf(),
            forall|k: nat| lo <= k < hi ==> #[trigger] self.view().contains_key(k),
        ensures
            self.chunks_in(lo, hi) <= 2 + ((hi - lo) as nat) / (K as nat),
    {
        assert(self.view().dom() =~= pos(self.fs()));
        assert forall|k: nat| lo <= k < hi implies #[trigger] pos(self.fs()).contains(k) by {
            assert(self.view().contains_key(k));
        }
        lemma_nch_held(self.fs(), lo, hi);
    }

    /// `run_end`, and its cost: a lookup for the chunk holding `p`, then the walk on from its end.
    pub fn run_end_w(&self, p: u64) -> (r: (u64, Ghost<nat>))
        requires
            self.wf(),
            p <= VARINT_MAX,
        ensures
            p <= r.0 <= VARINT_MAX,
            forall|k: nat| p <= k < r.0 ==> #[trigger] self.view().contains_key(k),
            !self.view().contains_key(r.0 as nat),
            r.1@ <= c_re1() * (self.tree_ht() + 1) + c_re2() * (self.chunks_in(p as nat, r.0 as nat) + 1),
    {
        let ghost f = self.fs();
        let ghost mut work: nat = 1;
        proof {
            assert(self.view().dom() =~= pos(f));
            lemma_at_ok(f);
        }
        let (g, Ghost(c)) = get_le(&self.t, p);
        proof {
            work = work + c;
            assert(c_get() == 1);
        }
        if let Some((k, v)) = g {
            let ghost i = choose|i: int| #[trigger] last_le(seq(self.t), p, i, k, *v);
            proof {
                assert(f[i] == (k as nat, v@));
                assert(end(f[i]) <= VARINT_MAX);
            }
            let e = k + v.len() as u64;
            if e > p {
                proof {
                    reveal(fresh);
                }
                let (r, _d, Ghost(w)) = walk_run(&self.t, e, e);
                proof {
                    work = work + w;
                    self.lemma_run_end_at(i, p as nat, e as nat, r as nat, w);
                }
                return (r, Ghost(work));
            }
            proof {
                self.lemma_run_end_none(Some(i), p as nat);
            }
            return (p, Ghost(work));
        }
        proof {
            self.lemma_run_end_none(None, p as nat);
            lemma_nch_out(f, p as nat, p as nat);
        }
        (p, Ghost(work))
    }

    /// `run_end_w` with no run at `p`: `p` is not held.
    proof fn lemma_run_end_none(&self, i: Option<int>, p: nat)
        requires
            self.wf(),
            i is None ==> keys_gt(self.t, p as u64),
            i matches Some(i) ==> 0 <= i < self.fs().len() && self.fs()[i].0 <= p && end(self.fs()[i]) <= p && (forall|j: int|
                i < j < seq(self.t).len() ==> #[trigger] seq(self.t)[j].0 > p),
        ensures
            !self.view().contains_key(p),
            self.chunks_in(p, p) == 0,
    {
        let f = self.fs();
        assert(self.view().dom() =~= pos(f));
        lemma_nch_out(f, p, p);
        if pos(f).contains(p) {
            let j = choose|j: int| inf(f, j, p);
            assert(f[j].0 == seq(self.t)[j].0);
            if let Some(i) = i {
                if j < i {
                    assert(end(f[j]) <= f[i].0);
                }
            }
        }
    }

    /// `run_end_w` after the walk from `e`, the end of chunk `i` (which holds `p`).
    proof fn lemma_run_end_at(&self, i: int, p: nat, e: nat, r: nat, w: nat)
        requires
            self.wf(),
            0 <= i < self.fs().len(),
            self.fs()[i].0 <= p < e,
            e == end(self.fs()[i]),
            e <= r <= VARINT_MAX,
            held_in(self.fs(), e, r),
            past(self.fs(), e, r),
            w <= vis(self.t, e as u64, r as u64),
        ensures
            forall|k: nat| p <= k < r ==> #[trigger] self.view().contains_key(k),
            !self.view().contains_key(r),
            w <= 2 * (self.chunks_in(p, r) + 1) + 2 * ht(self.t),
    {
        reveal(held_in);
        reveal(past);
        let f = self.fs();
        assert(self.view().dom() =~= pos(f));
        assert forall|k: nat| p <= k < r implies #[trigger] pos(f).contains(k) by {
            if k < e {
                assert(inf(f, i, k));
            }
        }
        assert forall|j: int| 0 <= j < f.len() implies #[trigger] f[j].0 != r && (end(f[j]) <= r || f[j].0 > r) by {
            if j < i {
                assert(end(f[j]) <= f[i].0);
            } else if j > i {
                assert(end(f[i]) <= f[j].0);
            }
        }
        if pos(f).contains(r) {
            let j = choose|j: int| inf(f, j, r);
            assert(end(f[j]) <= r || f[j].0 > r);
        }
        lemma_vis(self.t, e as u64, r as u64);
        lemma_nm_nch(f, p, e, r);
    }

    /// The end of the run holding or starting at `p` (`p` itself if no chunk holds it).
    pub fn run_end(&self, p: u64) -> (r: u64)
        requires
            self.wf(),
            p <= VARINT_MAX,
        ensures
            p <= r <= VARINT_MAX,
            forall|k: nat| p <= k < r ==> #[trigger] self.view().contains_key(k),
            !self.view().contains_key(r as nat),
    {
        let (r, Ghost(c)) = self.run_end_w(p);
        proof {
            assert(c <= c_re1() * (self.tree_ht() + 1) + c_re2() * (self.chunks_in(p as nat, r as nat) + 1));
        }
        r
    }

    /// The store's tree, for a teardown slot (`avl::pop_some` frees it). Each key is a chunk's start, a position held.
    pub fn into_tree(self) -> (r: Tree<CapVec<u8>>)
        requires
            self.wf(),
        ensures
            crate::avl::wf(r),
            seq(r).len() == self.nodes(),
            forall|i: int| 0 <= i < seq(r).len() ==> #[trigger] self.view().contains_key(seq(r)[i].0 as nat),
    {
        proof {
            let f = self.fs();
            assert(self.view().dom() =~= pos(f));
            assert forall|i: int| 0 <= i < seq(self.t).len() implies #[trigger] self.view().contains_key(
                seq(self.t)[i].0 as nat,
            ) by {
                assert(f[i] == (seq(self.t)[i].0 as nat, seq(self.t)[i].1@));
                assert(inf(f, i, f[i].0));
                assert(f[i].0 < VARINT_MAX);
            }
        }
        self.t
    }
}

impl Frags {
    /// `take_front_w`'s store `b` after taking `[st, r)` from `a`: its chunks `g` hold `a`'s positions at or past `r`.
    proof fn lemma_tf_frags(a: Frags, b: Frags, g: Seq<(nat, Seq<u8>)>, st: nat, r: nat)
        requires
            a.wf(),
            crate::avl::wf(b.t),
            mp(seq(b.t)) == g,
            ok(g),
            st <= r,
            forall|k: nat| #[trigger] pos(a.fs()).contains(k) ==> k >= st,
            forall|k: nat| st <= k < r ==> #[trigger] pos(a.fs()).contains(k),
            forall|k: nat| #[trigger] pos(g).contains(k) <==> pos(a.fs()).contains(k) && k >= r,
            forall|k: nat| #[trigger] pos(g).contains(k) ==> vw(g)[k] == vw(a.fs())[k],
            pos(g).len() == sum_len(g),
            g.len() > 0 ==> end(g.last()) == end(a.fs().last()),
            b.held == a.held - (r - st),
            b.count == a.count - (if st < r && !pos(a.fs()).contains(r) {
                1nat
            } else {
                0
            }),
            b.hi == (if g.len() == 0 {
                0
            } else {
                a.hi
            }),
        ensures
            b.wf(),
            forall|k: nat| #[trigger] b.view().contains_key(k) <==> a.view().contains_key(k) && k >= r,
            forall|k: nat| #[trigger] b.view().contains_key(k) ==> b.view()[k] == a.view()[k],
    {
        let f = a.fs();
        assert(a.view().dom() =~= pos(f));
        assert(b.view().dom() =~= pos(g));
        lemma_tf_post(pos(f), pos(g), st, r);
        if g.len() > 0 {
            assert(f.len() > 0) by {
                lemma_pos_last(g);
                assert(pos(f).contains((end(g.last()) - 1) as nat));
            }
        }
    }
}

impl Frags {
    /// The store after `merge_w` is wf and holds `pv`, its chunks `g` being in order and holding `pv`'s bytes.
    proof fn lemma_merged(&self, g: Seq<(nat, Seq<u8>)>, pv: Map<nat, u8>)
        requires
            crate::avl::wf(self.t),
            mp(seq(self.t)) == g,
            ok(g),
            vw(g) == pv,
            pos(g).len() == sum_len(g),
            self.held == pv.dom().len(),
            self.count == runs(pv.dom()),
            self.hi == hi_of(g),
        ensures
            self.wf(),
            self.view() == pv,
    {
    }

    /// D3 steps 1-6 for a frame `[s, e)` adding a position: split out the chunks meeting `[s0, e)`, merge them and the
    /// frame into fresh pieces, and join the pieces back. `nh` and `nc` are `after_insert`'s counts.
    fn merge_w(&mut self, _lo: u64, off: u64, data: &[u8], s: u64, e: u64, nh: u64, nc: usize) -> (r: Ghost<nat>)
        requires
            old(self).wf(),
            s == (if _lo >= off { _lo } else { off }),
            e == off + data@.len(),
            s < e <= VARINT_MAX,
            nh == put(old(self).view(), _lo as nat, off as nat, data@).dom().len(),
            nc == runs(put(old(self).view(), _lo as nat, off as nat, data@).dom()),
        ensures
            final(self).wf(),
            final(self).view() == put(old(self).view(), _lo as nat, off as nat, data@),
            final(self).held == nh,
            final(self).count == nc,
            r@ <= 108 * (ht(old(self).t) + 1) + 6 * data@.len() + 1200,
    {
        let ghost f = self.fs();
        let ghost h = ht(self.t);
        let ghost pv = put(self.view(), _lo as nat, off as nat, data@);
        let ghost mut work: nat = 1;
        proof {
            self.lemma_size();
            lemma2_to64_rest();
        }
        let t = self.t.take();
        let (t2, hi, Ghost(c1)) = merge(t, self.hi, _lo, off, data, s, e, Ghost(f));
        self.t = t2;
        self.held = nh;
        self.count = nc;
        self.hi = hi;
        proof {
            self.lemma_merged(mp(seq(t2)), pv);
            work = work + c1;
        }
        Ghost(work)
    }

    /// `insert`, and its cost (D3): the all-held check by the walk, then one split pair, the merge into fresh pieces, and
    /// the joins. The cost is bounded in the spec's form and additively, `112 (h + 1) + 8 d + 1207`.
    fn insert_w(&mut self, lo: u64, off: u64, data: &[u8]) -> (r: Ghost<nat>)
        requires
            old(self).wf(),
            off + data@.len() <= VARINT_MAX,
        ensures
            final(self).wf(),
            final(self).view() == put(old(self).view(), lo as nat, off as nat, data@),
            final(self).held() == put(old(self).view(), lo as nat, off as nat, data@).dom().len(),
            final(self).count() == runs(put(old(self).view(), lo as nat, off as nat, data@).dom()),
            (forall|k: nat| (if lo >= off { lo } else { off }) <= k < off + data@.len() ==> #[trigger]
                old(self).view().contains_key(k)) ==> *final(self) == *old(self),
            r@ <= c_ins1() * (ht(old(self).t) + 1) * (data@.len() / (K as nat) + 4) + c_ins2() * (data@.len() + 4 * K),
            r@ <= 112 * (ht(old(self).t) + 1) + 8 * data@.len() + 1207,
    {
        let ghost mut work: nat = 1;
        let ghost h = ht(self.t);
        proof {
            lemma_put_same(self.view(), lo as nat, off as nat, data@);
            lemma_ins_cost(h, data@.len(), 0, 0, 0);
        }
        let s = if lo >= off {
            lo
        } else {
            off
        };
        let e = off + data.len() as u64;
        if s >= e {
            proof {
                assert(put(self.view(), lo as nat, off as nat, data@) =~= self.view());
            }
            return Ghost(work);
        }
        let ((nh, nc), Ghost(cw)) = self.after_insert_w(lo, off, data);
        let ghost ml = self.m_len(lo, off, data@);
        proof {
            self.lemma_m_le(lo, off, data@);
            lemma_ins_cost(h, data@.len(), ml, cw, 0);
            work = work + cw;
        }
        if nh == self.held {
            return Ghost(work);
        }
        let Ghost(cm) = self.merge_w(lo, off, data, s, e, nh, nc);
        proof {
            lemma_ins_cost(h, data@.len(), ml, cw, cm);
            work = work + cm;
        }
        Ghost(work)
    }

    /// Adds each byte of `data` (at `off`) at a position at or past `lo` that is not held: the first writer wins.
    /// The chunks the frame meets are merged with it into fresh pieces of at most `CAP` bytes.
    pub fn insert(&mut self, lo: u64, off: u64, data: &[u8])
        requires
            old(self).wf(),
            off + data@.len() <= VARINT_MAX,
        ensures
            final(self).wf(),
            final(self).view() == put(old(self).view(), lo as nat, off as nat, data@),
            final(self).held() == put(old(self).view(), lo as nat, off as nat, data@).dom().len(),
            final(self).count() == runs(put(old(self).view(), lo as nat, off as nat, data@).dom()),
            // A frame holding no new position changes nothing: it returns after the walk, copying and allocating
            // nothing.
            (forall|k: nat| (if lo >= off { lo } else { off }) <= k < off + data@.len() ==> #[trigger]
                old(self).view().contains_key(k)) ==> *final(self) == *old(self),
    {
        let Ghost(c) = self.insert_w(lo, off, data);
        proof {
            assert(c <= c_ins1() * (ht(old(self).t) + 1) * (data@.len() / (K as nat) + 4) + c_ins2() * (data@.len()
                + 4 * K));
            assert(c <= 112 * (ht(old(self).t) + 1) + 8 * data@.len() + 1207);
        }
    }

    /// `take_front`, and its cost: the run's chunks that fit whole, then, if the limit falls inside a chunk, that
    /// chunk's first bytes, its rest put back as a fresh piece.
    fn take_front_w(&mut self, st: u64, max: u64, out: &mut CapVec<u8>) -> (r: (u64, Ghost<nat>))
        requires
            old(self).wf(),
            st <= VARINT_MAX,
            forall|k: nat| #[trigger] old(self).view().contains_key(k) ==> k >= st,
            old(out).wf(),
            old(out)@.len() + max <= old(out).cap(),
        ensures
            final(self).wf(),
            st <= r.0 <= st + max,
            forall|k: nat| st <= k < r.0 ==> #[trigger] old(self).view().contains_key(k),
            r.0 < st + max ==> !old(self).view().contains_key(r.0 as nat),
            final(out).wf(),
            final(out).cap() == old(out).cap(),
            final(out)@ == old(out)@ + Seq::new((r.0 - st) as nat, |i: int| old(self).view()[(st + i) as nat]),
            forall|k: nat| #[trigger]
                final(self).view().contains_key(k) <==> old(self).view().contains_key(k) && k >= r.0,
            forall|k: nat| #[trigger]
                final(self).view().contains_key(k) ==> final(self).view()[k] == old(self).view()[k],
            r.1@ <= c_tf1() * (ht(old(self).t) + 1) * (max / K + 3) + c_tf2() * (max + CAP),
    {
        let ghost f = self.fs();
        let ghost a = *self;
        proof {
            self.lemma_size();
            lemma_ht_le(self.t);
            assert(self.view().dom() =~= pos(f));
        }
        let t = self.t.take();
        let (t2, r, held_at_end, Ghost(c)) = take_tree(t, st, max, out, Ghost(f));
        proof {
            lemma_tf_post(pos(f), pos(mp(seq(t2))), st as nat, r as nat);
        }
        self.t = t2;
        self.held = self.held - (r - st);
        if r > st && !held_at_end {
            self.count = self.count - 1;
        }
        if self.t.is_none() {
            self.hi = 0;
        }
        proof {
            Frags::lemma_tf_frags(a, *self, mp(seq(t2)), st as nat, r as nat);
        }
        (r, Ghost(c))
    }

    /// Appends at most `max` bytes of the run from `st` to `out` and removes them; returns the end of the bytes taken
    /// (`st` itself if no chunk starts there). If the limit falls inside a chunk, the rest of that chunk stays, as a
    /// fresh piece under its new start.
    pub fn take_front(&mut self, st: u64, max: u64, out: &mut CapVec<u8>) -> (r: u64)
        requires
            old(self).wf(),
            st <= VARINT_MAX,
            forall|k: nat| #[trigger] old(self).view().contains_key(k) ==> k >= st,
            old(out).wf(),
            old(out)@.len() + max <= old(out).cap(),
        ensures
            final(self).wf(),
            st <= r <= st + max,
            forall|k: nat| st <= k < r ==> #[trigger] old(self).view().contains_key(k),
            r < st + max ==> !old(self).view().contains_key(r as nat),
            final(out).wf(),
            final(out).cap() == old(out).cap(),
            final(out)@ == old(out)@ + Seq::new((r - st) as nat, |i: int| old(self).view()[(st + i) as nat]),
            forall|k: nat| #[trigger]
                final(self).view().contains_key(k) <==> old(self).view().contains_key(k) && k >= r,
            forall|k: nat| #[trigger]
                final(self).view().contains_key(k) ==> final(self).view()[k] == old(self).view()[k],
    {
        let (r, Ghost(c)) = self.take_front_w(st, max, out);
        proof {
            assert(c <= c_tf1() * (ht(old(self).t) + 1) * (max / K + 3) + c_tf2() * (max + CAP));
        }
        r
    }
}

} // verus!

impl Frags {
    /// Test support: the bytes allocated for the chunks: per node, the node itself and its piece's capacity (the inner
    /// `Vec`'s). Verus models `Vec` length, not capacity (TRUSTED.md).
    #[doc(hidden)]
    pub fn capacity(&self) -> usize {
        fn go(t: &Tree<CapVec<u8>>) -> usize {
            match t {
                None => 0,
                Some(b) => std::mem::size_of::<Node<CapVec<u8>>>() + b.val.capacity() + go(&b.left) + go(&b.right),
            }
        }
        go(&self.t)
    }

    /// Test support: each chunk's start and length, in order.
    #[doc(hidden)]
    pub fn chunk_lens(&self) -> Vec<(u64, usize)> {
        fn go(t: &Tree<CapVec<u8>>, out: &mut Vec<(u64, usize)>) {
            if let Some(b) = t {
                go(&b.left, out);
                out.push((b.key, b.val.len()));
                go(&b.right, out);
            }
        }
        let mut out = Vec::new();
        go(&self.t, &mut out);
        out
    }
}
