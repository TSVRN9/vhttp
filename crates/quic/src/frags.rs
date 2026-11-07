//! A sparse byte store: sorted, pairwise disjoint and non-adjacent non-empty fragments, so its
//! memory follows the bytes held, not the span of offsets they cover. CRYPTO's out-of-order data
//! (RFC 9000 §7.5) lives here.
use vstd::prelude::*;
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

/// Fragment `i` of `f` holds position `k`.
spec fn inf(f: Seq<(nat, Seq<u8>)>, i: int, k: nat) -> bool {
    0 <= i < f.len() && f[i].0 <= k < f[i].0 + f[i].1.len()
}

/// The positions the fragments hold.
spec fn pos(f: Seq<(nat, Seq<u8>)>) -> Set<nat> {
    Set::range(0, VARINT_MAX as nat).filter(|k: nat| exists|i: int| inf(f, i, k))
}

/// The byte at `k`: that of a fragment holding it (the only one, under `sep`).
spec fn at(f: Seq<(nat, Seq<u8>)>, k: nat) -> u8 {
    let i = choose|i: int| inf(f, i, k);
    f[i].1[k - f[i].0]
}

/// The bytes the fragments hold, by position.
spec fn vw(f: Seq<(nat, Seq<u8>)>) -> Map<nat, u8> {
    Map::new(pos(f), |k: nat| at(f, k))
}

/// Non-empty fragments ending by `VARINT_MAX`, in order, with a gap of at least one position
/// between any two.
spec fn sep(f: Seq<(nat, Seq<u8>)>) -> bool {
    &&& forall|i: int|
        #![trigger f[i]]
        0 <= i < f.len() ==> 0 < f[i].1.len() && f[i].0 + f[i].1.len() <= VARINT_MAX
    &&& forall|i: int, j: int|
        #![trigger f[i], f[j]]
        0 <= i < j < f.len() ==> f[i].0 + f[i].1.len() < f[j].0
}

spec fn sum_len(f: Seq<(nat, Seq<u8>)>) -> nat
    decreases f.len(),
{
    if f.len() == 0 {
        0
    } else {
        sum_len(f.drop_last()) + f.last().1.len()
    }
}

/// The byte `insert` writes at `q`: the one held, else the new one.
spec fn nb(f: Seq<(nat, Seq<u8>)>, d: Seq<u8>, off: nat, q: nat) -> u8 {
    if pos(f).contains(q) {
        at(f, q)
    } else {
        d[q - off]
    }
}

/// The fragments `[i, j)` of `f` replaced by `m`.
spec fn splice(f: Seq<(nat, Seq<u8>)>, i: int, j: int, m: (nat, Seq<u8>)) -> Seq<(nat, Seq<u8>)> {
    f.take(i).push(m) + f.skip(j)
}

/// The start of the fragment merging `[s, e)` with fragments `[i, j)`.
spec fn mlo(f: Seq<(nat, Seq<u8>)>, i: int, j: int, s: nat) -> nat {
    if i < j && f[i].0 < s {
        f[i].0
    } else {
        s
    }
}

/// Its end.
spec fn mhi(f: Seq<(nat, Seq<u8>)>, i: int, j: int, e: nat) -> nat {
    if i < j && f[j - 1].0 + f[j - 1].1.len() > e {
        f[j - 1].0 + f[j - 1].1.len()
    } else {
        e
    }
}

/// `[i, j)` are the fragments touching `[s, e)`, adjacent ones included: those before end before
/// `s - 1`, those after start past `e`.
spec fn located(f: Seq<(nat, Seq<u8>)>, s: nat, e: nat, i: int, j: int) -> bool {
    &&& 0 <= i <= j <= f.len()
    &&& forall|t: int| #![trigger f[t]] 0 <= t < i ==> f[t].0 + f[t].1.len() < s
    &&& i < f.len() ==> f[i].0 + f[i].1.len() >= s
    &&& forall|t: int| #![trigger f[t]] i <= t < j ==> f[t].0 <= e
    &&& j < f.len() ==> f[j].0 > e
}

proof fn lemma_sep_sub(f: Seq<(nat, Seq<u8>)>, a: int, b: int)
    requires
        sep(f),
        0 <= a <= b <= f.len(),
    ensures
        sep(f.subrange(a, b)),
{
    let g = f.subrange(a, b);
    assert forall|i: int| #![trigger g[i]] 0 <= i < g.len() implies 0 < g[i].1.len() && g[i].0
        + g[i].1.len() <= VARINT_MAX by {
        assert(g[i] == f[a + i]);
    }
    assert forall|i: int, j: int| #![trigger g[i], g[j]] 0 <= i < j < g.len() implies g[i].0
        + g[i].1.len() < g[j].0 by {
        assert(g[i] == f[a + i] && g[j] == f[a + j]);
    }
}

/// Under `sep` a position is in at most one fragment, whose byte `at` gives.
proof fn lemma_at(f: Seq<(nat, Seq<u8>)>)
    requires
        sep(f),
    ensures
        forall|i: int, k: nat| #[trigger]
            inf(f, i, k) ==> pos(f).contains(k) && at(f, k) == f[i].1[k - f[i].0],
        forall|k: nat| #[trigger] pos(f).contains(k) ==> exists|i: int| inf(f, i, k),
{
    assert forall|i: int, k: nat| #[trigger] inf(f, i, k) implies pos(f).contains(k) && at(f, k)
        == f[i].1[k - f[i].0] by {
        let t = choose|t: int| inf(f, t, k);
        if t < i {
            assert(f[t].0 + f[t].1.len() < f[i].0);
        } else if t > i {
            assert(f[i].0 + f[i].1.len() < f[t].0);
        }
        assert(f[i].0 + f[i].1.len() <= VARINT_MAX);
    }
}

/// The last fragment adds its range to the others', with a gap below it.
proof fn lemma_pos_last(f: Seq<(nat, Seq<u8>)>)
    requires
        sep(f),
        f.len() > 0,
    ensures
        sep(f.drop_last()),
        pos(f) =~= pos(f.drop_last()) + Set::range(f.last().0, f.last().0 + f.last().1.len()),
        forall|k: nat| #[trigger] pos(f.drop_last()).contains(k) ==> k + 1 < f.last().0,
{
    let n = f.len() - 1;
    let p = f.drop_last();
    assert(p =~= f.subrange(0, n));
    lemma_sep_sub(f, 0, n);
    lemma_at(f);
    lemma_at(p);
    assert forall|k: nat| #[trigger] pos(p).contains(k) implies k + 1 < f.last().0 by {
        let i = choose|i: int| inf(p, i, k);
        assert(p[i] == f[i]);
        assert(f[i].0 + f[i].1.len() < f[n].0);
    }
    assert forall|k: nat| pos(f).contains(k) <==> #[trigger] (pos(p) + Set::range(
        f.last().0,
        f.last().0 + f.last().1.len(),
    )).contains(k) by {
        if pos(f).contains(k) {
            let i = choose|i: int| inf(f, i, k);
            if i < n {
                assert(p[i] == f[i]);
                assert(inf(p, i, k));
            }
        }
        if pos(p).contains(k) {
            let i = choose|i: int| inf(p, i, k);
            assert(p[i] == f[i]);
            assert(inf(f, i, k));
        }
        if f.last().0 <= k < f.last().0 + f.last().1.len() {
            assert(inf(f, n, k));
        }
    }
}

proof fn lemma_pos_empty(f: Seq<(nat, Seq<u8>)>)
    requires
        f.len() == 0,
    ensures
        pos(f) =~= Set::<nat>::empty(),
{
}

/// The positions held number the fragments' total length.
proof fn lemma_len(f: Seq<(nat, Seq<u8>)>)
    requires
        sep(f),
    ensures
        pos(f).len() == sum_len(f),
    decreases f.len(),
{
    if f.len() == 0 {
        lemma_pos_empty(f);
    } else {
        lemma_pos_last(f);
        lemma_len(f.drop_last());
        let r = Set::range(f.last().0, f.last().0 + f.last().1.len());
        assert(pos(f.drop_last()).disjoint(r));
        vstd::set_lib::lemma_set_disjoint_lens(pos(f.drop_last()), r);
    }
}

/// Each fragment is one run: non-adjacent fragments never join.
proof fn lemma_runs(f: Seq<(nat, Seq<u8>)>)
    requires
        sep(f),
    ensures
        runs(pos(f)) == f.len(),
    decreases f.len(),
{
    if f.len() == 0 {
        lemma_pos_empty(f);
        assert(starts(pos(f)) =~= Set::<nat>::empty());
    } else {
        let p = f.drop_last();
        let a = f.last().0;
        let b = a + f.last().1.len();
        lemma_pos_last(f);
        lemma_runs(p);
        let s = pos(f);
        let q = pos(p);
        assert(starts(s) =~= starts(q).insert(a)) by {
            assert forall|x: nat| #[trigger] starts(s).contains(x) <==> starts(q).insert(a).contains(x) by {
                if a <= x < b {
                    if x > a {
                        assert(s.contains((x - 1) as nat));
                    }
                    if a > 0 {
                        assert(!q.contains((a - 1) as nat));
                    }
                }
                if q.contains(x) && x > 0 {
                    assert(s.contains((x - 1) as nat) <==> q.contains((x - 1) as nat));
                }
            }
        }
        assert(!q.contains(a));
    }
}

/// `sum_len` adds over concatenation.
proof fn lemma_sum_append(a: Seq<(nat, Seq<u8>)>, b: Seq<(nat, Seq<u8>)>)
    ensures
        sum_len(a + b) == sum_len(a) + sum_len(b),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
    } else {
        lemma_sum_append(a, b.drop_last());
        assert((a + b).drop_last() =~= a + b.drop_last());
    }
}

/// `f` in three pieces.
proof fn lemma_sum_split(f: Seq<(nat, Seq<u8>)>, i: int, j: int)
    requires
        0 <= i <= j <= f.len(),
    ensures
        sum_len(f) == sum_len(f.take(i)) + sum_len(f.subrange(i, j)) + sum_len(f.skip(j)),
{
    assert(f =~= f.take(i) + f.subrange(i, j) + f.skip(j));
    lemma_sum_append(f.take(i) + f.subrange(i, j), f.skip(j));
    lemma_sum_append(f.take(i), f.subrange(i, j));
}

/// Ordering facts of `located`: fragments before `i` end below the merged start minus one,
/// fragments from `j` on start past the merged end, and those between lie inside it.
proof fn lemma_located(f: Seq<(nat, Seq<u8>)>, s: nat, e: nat, i: int, j: int)
    requires
        sep(f),
        located(f, s, e, i, j),
        s < e,
    ensures
        forall|t: int| #![trigger f[t]] 0 <= t < i ==> f[t].0 + f[t].1.len() < mlo(f, i, j, s),
        forall|t: int| #![trigger f[t]] j <= t < f.len() ==> f[t].0 > mhi(f, i, j, e),
        forall|t: int|
            #![trigger f[t]]
            i <= t < j ==> mlo(f, i, j, s) <= f[t].0 && f[t].0 + f[t].1.len() <= mhi(f, i, j, e),
        forall|k: nat|
            mlo(f, i, j, s) <= k < mhi(f, i, j, e) ==> (s <= k < e || inf(f, i, k) || inf(
                f,
                j - 1,
                k,
            )),
        mlo(f, i, j, s) <= s,
        e <= mhi(f, i, j, e),
{
    assert forall|t: int| #![trigger f[t]] 0 <= t < i implies f[t].0 + f[t].1.len() < mlo(
        f,
        i,
        j,
        s,
    ) by {
        if i < j {
            assert(f[t].0 + f[t].1.len() < f[i].0);
        }
    }
    assert forall|t: int| #![trigger f[t]] j <= t < f.len() implies f[t].0 > mhi(f, i, j, e) by {
        if t > j {
            assert(f[j].0 + f[j].1.len() < f[t].0);
        }
        if i < j {
            assert(f[j - 1].0 + f[j - 1].1.len() < f[j].0);
        }
    }
    assert forall|t: int| #![trigger f[t]] i <= t < j implies mlo(f, i, j, s) <= f[t].0 && f[t].0
        + f[t].1.len() <= mhi(f, i, j, e) by {
        if t > i {
            assert(f[i].0 + f[i].1.len() < f[t].0);
        }
        if t < j - 1 {
            assert(f[t].0 + f[t].1.len() < f[j - 1].0);
        }
    }
}

/// The fragments of `splice`, by index.
proof fn lemma_splice_index(f: Seq<(nat, Seq<u8>)>, i: int, j: int, m: (nat, Seq<u8>))
    requires
        0 <= i <= j <= f.len(),
    ensures
        splice(f, i, j, m).len() == f.len() - (j - i) + 1,
        forall|t: int|
            #![trigger splice(f, i, j, m)[t]]
            0 <= t < splice(f, i, j, m).len() ==> splice(f, i, j, m)[t] == if t < i {
                f[t]
            } else if t == i {
                m
            } else {
                f[t - i - 1 + j]
            },
{
}

/// The merged fragment keeps the fragments separated.
proof fn lemma_merge_sep(f: Seq<(nat, Seq<u8>)>, s: nat, e: nat, i: int, j: int, md: Seq<u8>)
    requires
        sep(f),
        located(f, s, e, i, j),
        s < e <= VARINT_MAX,
        md.len() == mhi(f, i, j, e) - mlo(f, i, j, s),
    ensures
        sep(splice(f, i, j, (mlo(f, i, j, s), md))),
{
    let m = (mlo(f, i, j, s), md);
    let g = splice(f, i, j, m);
    lemma_located(f, s, e, i, j);
    lemma_splice_index(f, i, j, m);
    if i < j {
        assert(f[j - 1].0 + f[j - 1].1.len() <= VARINT_MAX);
    }
    assert forall|t: int| #![trigger g[t]] 0 <= t < g.len() implies 0 < g[t].1.len() && g[t].0
        + g[t].1.len() <= VARINT_MAX by {
        if t > i {
            assert(g[t] == f[t - i - 1 + j]);
        }
    }
    assert forall|a: int, b: int| #![trigger g[a], g[b]] 0 <= a < b < g.len() implies g[a].0
        + g[a].1.len() < g[b].0 by {
        if b < i {
            assert(f[a].0 + f[a].1.len() < f[b].0);
        } else if b > i && a > i {
            assert(f[a - i - 1 + j].0 + f[a - i - 1 + j].1.len() < f[b - i - 1 + j].0);
        } else if b > i && a < i {
            assert(f[a].0 + f[a].1.len() < f[b - i - 1 + j].0);
        } else if b > i {
            assert(g[b] == f[b - i - 1 + j]);
        } else {
            assert(g[a] == f[a]);
        }
    }
}

/// The merged fragment holds nothing but what the old ones held and `[s, e)`.
proof fn lemma_merge_pos_sub(f: Seq<(nat, Seq<u8>)>, s: nat, e: nat, i: int, j: int, md: Seq<u8>)
    requires
        sep(f),
        located(f, s, e, i, j),
        s < e <= VARINT_MAX,
        md.len() == mhi(f, i, j, e) - mlo(f, i, j, s),
    ensures
        forall|k: nat| #[trigger] pos(splice(f, i, j, (mlo(f, i, j, s), md))).contains(k) ==> pos(f).contains(k)
            || s <= k < e,
{
    let m = (mlo(f, i, j, s), md);
    let g = splice(f, i, j, m);
    lemma_located(f, s, e, i, j);
    lemma_splice_index(f, i, j, m);
    lemma_at(f);
    assert forall|k: nat| #[trigger] pos(g).contains(k) implies pos(f).contains(k) || s <= k < e by {
        let t = choose|t: int| inf(g, t, k);
        if t < i {
            assert(inf(f, t, k));
        } else if t > i {
            assert(inf(f, t - i - 1 + j, k));
        } else if !(s <= k < e) {
            if inf(f, i, k) {
            } else {
                assert(inf(f, j - 1, k));
            }
        }
    }
}

/// The merged fragment holds what the old ones held and `[s, e)`.
proof fn lemma_merge_pos_sup(f: Seq<(nat, Seq<u8>)>, s: nat, e: nat, i: int, j: int, md: Seq<u8>)
    requires
        sep(f),
        sep(splice(f, i, j, (mlo(f, i, j, s), md))),
        located(f, s, e, i, j),
        s < e <= VARINT_MAX,
        md.len() == mhi(f, i, j, e) - mlo(f, i, j, s),
    ensures
        forall|k: nat| pos(f).contains(k) || s <= k < e ==> #[trigger] pos(splice(f, i, j, (mlo(f, i, j, s), md))).contains(k),
{
    let m = (mlo(f, i, j, s), md);
    let g = splice(f, i, j, m);
    lemma_located(f, s, e, i, j);
    lemma_splice_index(f, i, j, m);
    lemma_at(g);
    assert forall|k: nat| pos(f).contains(k) || s <= k < e implies #[trigger] pos(g).contains(k) by {
        if pos(f).contains(k) {
            let t = choose|t: int| inf(f, t, k);
            if t < i {
                assert(inf(g, t, k));
            } else if t >= j {
                assert(g[t - j + i + 1] == f[t]);
                assert(inf(g, t - j + i + 1, k));
            } else {
                assert(inf(g, i, k));
            }
        } else {
            assert(inf(g, i, k));
        }
    }
}

/// The merged fragment holds what the old ones held plus `[s, e)`.
proof fn lemma_merge_pos(f: Seq<(nat, Seq<u8>)>, s: nat, e: nat, i: int, j: int, md: Seq<u8>)
    requires
        sep(f),
        sep(splice(f, i, j, (mlo(f, i, j, s), md))),
        located(f, s, e, i, j),
        s < e <= VARINT_MAX,
        md.len() == mhi(f, i, j, e) - mlo(f, i, j, s),
    ensures
        pos(splice(f, i, j, (mlo(f, i, j, s), md))) =~= pos(f) + Set::range(s, e),
{
    lemma_merge_pos_sub(f, s, e, i, j, md);
    lemma_merge_pos_sup(f, s, e, i, j, md);
}

/// The merged fragment's length adds `[s, e)`'s new positions to the total.
proof fn lemma_merge_sum(f: Seq<(nat, Seq<u8>)>, i: int, j: int, m: (nat, Seq<u8>))
    requires
        0 <= i <= j <= f.len(),
    ensures
        sum_len(splice(f, i, j, m)) + sum_len(f.subrange(i, j)) == sum_len(f) + m.1.len(),
{
    lemma_sum_split(f, i, j);
    lemma_sum_append(f.take(i).push(m), f.skip(j));
    assert(f.take(i).push(m).drop_last() =~= f.take(i));
}

/// `lemma_merge_sep`, `lemma_merge_pos` and `lemma_merge_sum` together.
proof fn lemma_merge(f: Seq<(nat, Seq<u8>)>, s: nat, e: nat, i: int, j: int, md: Seq<u8>)
    requires
        sep(f),
        located(f, s, e, i, j),
        s < e <= VARINT_MAX,
        md.len() == mhi(f, i, j, e) - mlo(f, i, j, s),
    ensures
        sep(splice(f, i, j, (mlo(f, i, j, s), md))),
        pos(splice(f, i, j, (mlo(f, i, j, s), md))) =~= pos(f) + Set::range(s, e),
        splice(f, i, j, (mlo(f, i, j, s), md)).len() == f.len() - (j - i) + 1,
        sum_len(splice(f, i, j, (mlo(f, i, j, s), md))) + sum_len(f.subrange(i, j)) == sum_len(f)
            + md.len(),
{
    lemma_merge_sep(f, s, e, i, j, md);
    lemma_merge_pos(f, s, e, i, j, md);
    lemma_merge_sum(f, i, j, (mlo(f, i, j, s), md));
    lemma_splice_index(f, i, j, (mlo(f, i, j, s), md));
}

/// The bytes of the spliced fragments: the merged one's from `md`, the others' as before.
proof fn lemma_merge_view(
    f: Seq<(nat, Seq<u8>)>,
    s: nat,
    e: nat,
    i: int,
    j: int,
    md: Seq<u8>,
    d: Seq<u8>,
    off: nat,
)
    requires
        sep(f),
        sep(splice(f, i, j, (mlo(f, i, j, s), md))),
        0 <= i <= j <= f.len(),
        md.len() == mhi(f, i, j, e) - mlo(f, i, j, s),
        forall|q: nat|
            mlo(f, i, j, s) <= q < mhi(f, i, j, e) ==> #[trigger] md[q - mlo(f, i, j, s)] == nb(
                f,
                d,
                off,
                q,
            ),
    ensures
        forall|k: nat| #[trigger]
            pos(splice(f, i, j, (mlo(f, i, j, s), md))).contains(k) ==> at(
                splice(f, i, j, (mlo(f, i, j, s), md)),
                k,
            ) == nb(f, d, off, k),
{
    let ms = mlo(f, i, j, s);
    let g = splice(f, i, j, (ms, md));
    lemma_splice_index(f, i, j, (ms, md));
    lemma_at(f);
    lemma_at(g);
    assert forall|k: nat| #[trigger] pos(g).contains(k) implies at(g, k) == nb(f, d, off, k) by {
        let t = choose|t: int| inf(g, t, k);
        if t < i {
            assert(g[t] == f[t]);
            assert(inf(f, t, k));
        } else if t > i {
            assert(g[t] == f[t - i - 1 + j]);
            assert(inf(f, t - i - 1 + j, k));
        } else {
            assert(g[t] == (ms, md));
        }
    }
}

/// `insert`'s result: the splice keeps the fragments separated and holds `put`'s bytes; its
/// total length and fragment count are `put`'s positions and runs.
proof fn lemma_insert_post(
    f: Seq<(nat, Seq<u8>)>,
    lo: nat,
    off: nat,
    d: Seq<u8>,
    s: nat,
    e: nat,
    i: int,
    j: int,
    md: Seq<u8>,
)
    requires
        sep(f),
        located(f, s, e, i, j),
        s == (if lo >= off { lo } else { off }),
        e == off + d.len(),
        s < e <= VARINT_MAX,
        md.len() == mhi(f, i, j, e) - mlo(f, i, j, s),
        forall|q: nat|
            mlo(f, i, j, s) <= q < mhi(f, i, j, e) ==> #[trigger] md[q - mlo(f, i, j, s)] == nb(
                f,
                d,
                off,
                q,
            ),
    ensures
        sep(splice(f, i, j, (mlo(f, i, j, s), md))),
        vw(splice(f, i, j, (mlo(f, i, j, s), md))) == put(vw(f), lo, off, d),
        sum_len(splice(f, i, j, (mlo(f, i, j, s), md))) == put(vw(f), lo, off, d).dom().len(),
        splice(f, i, j, (mlo(f, i, j, s), md)).len() == runs(put(vw(f), lo, off, d).dom()),
{
    let g = splice(f, i, j, (mlo(f, i, j, s), md));
    lemma_merge(f, s, e, i, j, md);
    lemma_merge_view(f, s, e, i, j, md, d, off);
    lemma_runs(g);
    lemma_len(g);
    assert(vw(g) =~= put(vw(f), lo, off, d));
}

/// Removing the first fragment removes its positions, which end before the next one starts.
proof fn lemma_take_post(f: Seq<(nat, Seq<u8>)>)
    requires
        sep(f),
        f.len() > 0,
    ensures
        sep(f.skip(1)),
        sum_len(f) == sum_len(f.skip(1)) + f[0].1.len(),
        vw(f.skip(1)).dom().len() == sum_len(f.skip(1)),
        f.skip(1).len() == runs(vw(f.skip(1)).dom()),
        forall|k: nat| #[trigger]
            vw(f.skip(1)).contains_key(k) <==> vw(f).contains_key(k) && k > f[0].0 + f[0].1.len(),
        forall|k: nat| #[trigger] vw(f.skip(1)).contains_key(k) ==> vw(f.skip(1))[k] == vw(f)[k],
        forall|k: nat|
            f[0].0 <= k < f[0].0 + f[0].1.len() ==> #[trigger] vw(f).contains_key(k) && vw(f)[k]
                == f[0].1[k - f[0].0],
        !vw(f).contains_key(f[0].0 + f[0].1.len()),
        f[0].0 + f[0].1.len() <= VARINT_MAX,
{
    let g = f.skip(1);
    let r = f[0].0 + f[0].1.len();
    assert(g =~= f.subrange(1, f.len() as int));
    lemma_sep_sub(f, 1, f.len() as int);
    lemma_sum_split(f, 0, 1);
    assert(f.subrange(0, 1).drop_last() =~= Seq::<(nat, Seq<u8>)>::empty());
    assert(f.take(0) =~= Seq::<(nat, Seq<u8>)>::empty());
    lemma_len(g);
    lemma_runs(g);
    lemma_at(f);
    lemma_at(g);
    assert forall|k: nat| #[trigger] vw(g).contains_key(k) <==> vw(f).contains_key(k) && k > r by {
        if vw(g).contains_key(k) {
            let u = choose|u: int| inf(g, u, k);
            assert(g[u] == f[u + 1]);
            assert(inf(f, u + 1, k));
            assert(f[0].0 + f[0].1.len() < f[u + 1].0);
        }
        if vw(f).contains_key(k) && k > r {
            let u = choose|u: int| inf(f, u, k);
            assert(u != 0);
            assert(g[u - 1] == f[u]);
            assert(inf(g, u - 1, k));
        }
    }
    assert forall|k: nat| #[trigger] vw(g).contains_key(k) implies vw(g)[k] == vw(f)[k] by {
        let u = choose|u: int| inf(g, u, k);
        assert(g[u] == f[u + 1]);
        assert(inf(f, u + 1, k));
    }
    assert forall|k: nat| f[0].0 <= k < r implies #[trigger] vw(f).contains_key(k) && vw(f)[k] == f[0].1[k - f[0].0] by {
        assert(inf(f, 0, k));
    }
    if vw(f).contains_key(r) {
        let u = choose|u: int| inf(f, u, r);
        if u > 0 {
            assert(f[0].0 + f[0].1.len() < f[u].0);
        }
    }
}

/// With every position at or past `end` and no fragment starting at `end`, `end` is not held.
proof fn lemma_take_none(f: Seq<(nat, Seq<u8>)>, end: nat)
    requires
        sep(f),
        forall|k: nat| #[trigger] vw(f).contains_key(k) ==> k >= end,
        f.len() == 0 || f[0].0 != end,
    ensures
        !vw(f).contains_key(end),
{
    lemma_at(f);
    if f.len() > 0 {
        assert(inf(f, 0, f[0].0));
        if vw(f).contains_key(end) {
            let u = choose|u: int| inf(f, u, end);
            if u > 0 {
                assert(f[0].0 + f[0].1.len() < f[u].0);
            }
        }
    }
}

/// The positions from `p` (where `merged`'s fill is at fragment `t`) to the next fragment, or to
/// `e` after the last, are held by no fragment: their bytes come from `d`.
proof fn lemma_gap(
    f: Seq<(nat, Seq<u8>)>,
    s: nat,
    e: nat,
    i: int,
    j: int,
    t: int,
    p: nat,
    d: Seq<u8>,
    off: nat,
)
    requires
        sep(f),
        located(f, s, e, i, j),
        off <= s < e,
        e == off + d.len(),
        i <= t <= j,
        t == i ==> p == mlo(f, i, j, s),
        t > i ==> p == f[t - 1].0 + f[t - 1].1.len(),
    ensures
        ({
            let b = if t < j {
                f[t].0
            } else {
                e
            };
            &&& t < j ==> p <= b <= e
            &&& p < b ==> s <= p
            &&& forall|q: nat|
                p <= q < b ==> #[trigger] d.subrange(p - off, b - off)[q - p] == nb(f, d, off, q)
        }),
{
    let b = if t < j {
        f[t].0
    } else {
        e
    };
    lemma_at(f);
    if t > i {
        if t - 1 > i {
            assert(f[i].0 + f[i].1.len() < f[t - 1].0);
        }
        if t < j {
            assert(f[t - 1].0 + f[t - 1].1.len() < f[t].0);
        }
    }
    if p < b {
        assert forall|q: nat| p <= q < b implies !pos(f).contains(q) by {
            if pos(f).contains(q) {
                let u = choose|u: int| inf(f, u, q);
                if u < t - 1 && u >= i {
                    assert(f[u].0 + f[u].1.len() < f[t - 1].0);
                } else if u > t && t < j {
                    assert(f[t].0 + f[t].1.len() < f[u].0);
                } else if u > j && t == j {
                    assert(f[j].0 + f[j].1.len() < f[u].0);
                }
            }
        }
    }
}

/// Fragment `t`'s bytes are `nb`'s at its positions.
proof fn lemma_frag(f: Seq<(nat, Seq<u8>)>, t: int, d: Seq<u8>, off: nat)
    requires
        sep(f),
        0 <= t < f.len(),
    ensures
        forall|q: nat|
            f[t].0 <= q < f[t].0 + f[t].1.len() ==> #[trigger] f[t].1[q - f[t].0] == nb(f, d, off, q),
{
    lemma_at(f);
    assert forall|q: nat| f[t].0 <= q < f[t].0 + f[t].1.len() implies #[trigger] f[t].1[q - f[t].0]
        == nb(f, d, off, q) by {
        assert(inf(f, t, q));
    }
}

/// `m0` holds `fv` over `[ms, p0)` and `a` over `[p0, p0 + a.len())`: `m0 + a` over both.
proof fn lemma_extend(m0: Seq<u8>, a: Seq<u8>, ms: nat, p0: nat, fv: spec_fn(nat) -> u8)
    requires
        ms <= p0,
        m0.len() == p0 - ms,
        forall|q: nat| ms <= q < p0 ==> #[trigger] m0[q - ms] == fv(q),
        forall|q: nat| p0 <= q < p0 + a.len() ==> #[trigger] a[q - p0] == fv(q),
    ensures
        forall|q: nat| ms <= q < p0 + a.len() ==> #[trigger] (m0 + a)[q - ms] == fv(q),
{
    assert forall|q: nat| ms <= q < p0 + a.len() implies #[trigger] (m0 + a)[q - ms] == fv(q) by {
        if q < p0 {
            assert((m0 + a)[q - ms] == m0[q - ms]);
        } else {
            assert((m0 + a)[q - ms] == a[q - p0]);
        }
    }
}

/// If every position of `[s, e)` is held, fragment `i` holds them all.
proof fn lemma_all_held(f: Seq<(nat, Seq<u8>)>, s: nat, e: nat, i: int, j: int)
    requires
        sep(f),
        located(f, s, e, i, j),
        s < e,
    ensures
        (forall|k: nat| s <= k < e ==> #[trigger] pos(f).contains(k)) ==> i < j && f[i].0 <= s && e
            <= f[i].0 + f[i].1.len(),
{
    lemma_at(f);
    if forall|k: nat| s <= k < e ==> #[trigger] pos(f).contains(k) {
        assert(pos(f).contains(s));
        let t = choose|t: int| inf(f, t, s);
        if t > i {
            assert(f[i].0 + f[i].1.len() < f[t].0);
        }
        if t >= j && j < f.len() && t > j {
            assert(f[j].0 + f[j].1.len() < f[t].0);
        }
        assert(t == i);
        let r = f[i].0 + f[i].1.len();
        if e > r {
            assert(pos(f).contains(r));
            let u = choose|u: int| inf(f, u, r);
            if u > i {
                assert(f[i].0 + f[i].1.len() < f[u].0);
            } else if u < i {
                assert(f[u].0 + f[u].1.len() < f[i].0);
            }
        }
    }
}

/// The sparse store.
pub struct Frags {
    v: Vec<(u64, Vec<u8>)>,
    held: u64,
}

impl Frags {
    spec fn fs(&self) -> Seq<(nat, Seq<u8>)> {
        Seq::new(self.v@.len(), |i: int| (self.v@[i].0 as nat, self.v@[i].1@))
    }

    /// The bytes held, by position.
    pub closed spec fn view(&self) -> Map<nat, u8> {
        vw(self.fs())
    }

    pub closed spec fn held_spec(&self) -> u64 {
        self.held
    }

    pub closed spec fn count_spec(&self) -> usize {
        self.v.len()
    }

    /// The end of the last fragment, 0 with none.
    pub closed spec fn hi_spec(&self) -> nat {
        if self.v@.len() == 0 {
            0
        } else {
            self.fs().last().0 + self.fs().last().1.len()
        }
    }

    /// `held` is the number of bytes the fragments hold, which is their total length (what is
    /// allocated); `count` is the number of maximal runs of positions held.
    pub closed spec fn wf(&self) -> bool {
        &&& sep(self.fs())
        &&& self.held == sum_len(self.fs())
        &&& self.held == self.view().dom().len()
        &&& self.count() == runs(self.view().dom())
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
        lemma_runs_le_len(self.view().dom());
        lemma_at(f);
        assert(pos(f).subset_of(Set::range(0, VARINT_MAX as nat)));
        vstd::set_lib::lemma_len_subset(pos(f), Set::range(0, VARINT_MAX as nat));
        if f.len() > 0 {
            let n = f.len() - 1;
            assert(f[n].0 + f[n].1.len() <= VARINT_MAX);
            assert(inf(f, n, (f[n].0 + f[n].1.len() - 1) as nat));
            assert forall|k: nat| #[trigger] self.view().contains_key(k) implies k < self.hi_spec() by {
                let i = choose|i: int| inf(f, i, k);
                if i < n {
                    assert(f[i].0 + f[i].1.len() < f[n].0);
                }
            }
        } else {
            lemma_pos_empty(f);
        }
    }

    pub fn new() -> (r: Frags)
        ensures
            r.wf(),
            r.view() == Map::<nat, u8>::empty(),
            r.held() == 0,
            r.count() == 0,
    {
        let r = Frags { v: Vec::new(), held: 0 };
        proof {
            lemma_pos_empty(r.fs());
            assert(starts(r.view().dom()) =~= Set::<nat>::empty());
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
        self.v.len()
    }

    /// The end of the last fragment, 0 with none.
    pub fn hi(&self) -> (r: u64)
        requires
            self.wf(),
        ensures
            r == self.hi_spec(),
    {
        if self.v.len() == 0 {
            0
        } else {
            let n = self.v.len() - 1;
            proof {
                assert(self.fs()[n as int] == (self.v@[n as int].0 as nat, self.v@[n as int].1@));
            }
            self.v[n].0 + self.v[n].1.len() as u64
        }
    }

    /// The fragments touching `[s, e)`.
    fn locate(&self, s: u64, e: u64) -> (r: (usize, usize))
        requires
            self.wf(),
            s < e,
        ensures
            located(self.fs(), s as nat, e as nat, r.0 as int, r.1 as int),
    {
        let ghost f = self.fs();
        let n = self.v.len();
        proof {
            assert forall|t: int| #![trigger self.v@[t]] 0 <= t < n implies self.v@[t].0
                + self.v@[t].1@.len() <= VARINT_MAX by {
                assert(f[t] == (self.v@[t].0 as nat, self.v@[t].1@));
            }
        }
        // Binary search for the first fragment ending at or past `s`: fragments are sorted, so
        // their ends are too.
        let mut i: usize = 0;
        let mut hi: usize = n;
        while i < hi
            invariant
                forall|t: int| #![trigger self.v@[t]] 0 <= t < n ==> self.v@[t].0
                    + self.v@[t].1@.len() <= VARINT_MAX,
                f == self.fs(),
                sep(f),
                n == f.len(),
                i <= hi <= n,
                forall|t: int| #![trigger f[t]] 0 <= t < i ==> f[t].0 + f[t].1.len() < s,
                forall|t: int| #![trigger f[t]] hi <= t < n ==> f[t].0 + f[t].1.len() >= s,
            decreases hi - i,
        {
            let mid = i + (hi - i) / 2;
            assert(f[mid as int] == (self.v@[mid as int].0 as nat, self.v@[mid as int].1@));
            if self.v[mid].0 + (self.v[mid].1.len() as u64) < s {
                assert forall|t: int| #![trigger f[t]] 0 <= t <= mid implies f[t].0 + f[t].1.len() < s by {
                    if t < mid {
                        assert(f[t].0 + f[t].1.len() < f[mid as int].0);
                    }
                }
                i = mid + 1;
            } else {
                assert forall|t: int| #![trigger f[t]] mid <= t < n implies f[t].0 + f[t].1.len() >= s by {
                    if t > mid {
                        assert(f[mid as int].0 + f[mid as int].1.len() < f[t].0);
                    }
                }
                hi = mid;
            }
        }
        proof {
            if i < n {
                assert(f[i as int] == (self.v@[i as int].0 as nat, self.v@[i as int].1@));
            }
        }
        let mut j: usize = i;
        while j < n && self.v[j].0 <= e
            invariant
                f == self.fs(),
                sep(f),
                n == f.len(),
                i <= j <= n,
                forall|t: int| #![trigger f[t]] 0 <= t < i ==> f[t].0 + f[t].1.len() < s,
                i < n ==> f[i as int].0 + f[i as int].1.len() >= s,
                forall|t: int| #![trigger f[t]] i <= t < j ==> f[t].0 <= e,
            decreases n - j,
        {
            assert(f[j as int] == (self.v@[j as int].0 as nat, self.v@[j as int].1@));
            j = j + 1;
        }
        proof {
            if j < n {
                assert(f[j as int] == (self.v@[j as int].0 as nat, self.v@[j as int].1@));
            }
        }
        (i, j)
    }

    /// The total length of fragments `[i, j)`.
    fn sum_range(&self, i: usize, j: usize) -> (r: u64)
        requires
            self.wf(),
            i <= j <= self.v@.len(),
        ensures
            r == sum_len(self.fs().subrange(i as int, j as int)),
    {
        let ghost f = self.fs();
        proof {
            lemma_len(f);
            assert(pos(f).subset_of(Set::range(0, VARINT_MAX as nat)));
            vstd::set_lib::lemma_len_subset(pos(f), Set::range(0, VARINT_MAX as nat));
        }
        let mut k = i;
        let mut sum: u64 = 0;
        while k < j
            invariant
                f == self.fs(),
                i <= k <= j <= f.len(),
                sum_len(f) <= VARINT_MAX,
                sum == sum_len(f.subrange(i as int, k as int)),
            decreases j - k,
        {
            proof {
                lemma_sum_split(f, i as int, k as int + 1);
                assert(f.subrange(i as int, k + 1).drop_last() =~= f.subrange(i as int, k as int));
                assert(f[k as int] == (self.v@[k as int].0 as nat, self.v@[k as int].1@));
            }
            sum = sum + self.v[k].1.len() as u64;
            k = k + 1;
        }
        sum
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
        let ghost f = self.fs();
        let s = if lo >= off { lo } else { off };
        let e = off + data.len() as u64;
        if s >= e {
            proof {
                assert(put(self.view(), lo as nat, off as nat, data@).dom() =~= self.view().dom());
            }
            return (self.held, self.v.len());
        }
        let (i, j) = self.locate(s, e);
        self.counts(lo, off, data, s, e, i, j)
    }

    /// `after_insert` past `locate`.
    fn counts(&self, _lo: u64, _off: u64, _data: &[u8], s: u64, e: u64, i: usize, j: usize) -> (r: (u64, usize))
        requires
            self.wf(),
            _off + _data@.len() <= VARINT_MAX,
            s == (if _lo >= _off { _lo } else { _off }),
            e == _off + _data@.len(),
            s < e,
            located(self.fs(), s as nat, e as nat, i as int, j as int),
        ensures
            r.0 == put(self.view(), _lo as nat, _off as nat, _data@).dom().len(),
            r.1 == runs(put(self.view(), _lo as nat, _off as nat, _data@).dom()),
    {
        let ghost f = self.fs();
        let cov = self.sum_range(i, j);
        let (ms, me) = self.bounds(s, e, i, j);
        let ghost md = Seq::new((me - ms) as nat, |_k: int| 0u8);
        let ghost g = splice(f, i as int, j as int, (ms as nat, md));
        proof {
            assert(ms == mlo(f, i as int, j as int, s as nat));
            assert(me == mhi(f, i as int, j as int, e as nat));
            lemma_merge(f, s as nat, e as nat, i as int, j as int, md);
            lemma_len(g);
            lemma_len(f);
            lemma_runs(g);
            lemma_located(f, s as nat, e as nat, i as int, j as int);
            assert(pos(f).subset_of(Set::range(0, VARINT_MAX as nat)));
            vstd::set_lib::lemma_len_subset(pos(f), Set::range(0, VARINT_MAX as nat));
            assert(put(self.view(), _lo as nat, _off as nat, _data@).dom() =~= pos(g));
            self.lemma_wf();
        }
        (self.held + (me - ms) - cov, self.v.len() - (j - i) + 1)
    }

    /// Adds each byte of `data` (at `off`) at a position at or past `lo` that is not held: the
    /// first writer wins. Runs that become adjacent are merged into one fragment.
    // shortcut: a frame adding new positions copies the fragments it touches into the merged one and shifts the list, O(held + count) per frame (CRYPTO: at most 16384 + 4096); such frames are bounded per level by its new positions (1-RTT at most 16385; Initial and Handshake the bytes TLS accepts plus 16384). Upgrade: VecDeque fragments merged small-to-large plus an index (tracked C15).
    pub fn insert(&mut self, lo: u64, off: u64, data: &[u8])
        requires
            old(self).wf(),
            off + data@.len() <= VARINT_MAX,
        ensures
            final(self).wf(),
            final(self).view() == put(old(self).view(), lo as nat, off as nat, data@),
            final(self).held() == put(old(self).view(), lo as nat, off as nat, data@).dom().len(),
            final(self).count() == runs(put(old(self).view(), lo as nat, off as nat, data@).dom()),
            // A frame holding no new position changes nothing: it returns after `locate`'s
            // binary search and one comparison, copying and allocating nothing.
            (forall|k: nat| (if lo >= off { lo } else { off }) <= k < off + data@.len() ==> #[trigger]
                old(self).view().contains_key(k)) ==> *final(self) == *old(self),
    {
        let ghost f = self.fs();
        let s = if lo >= off { lo } else { off };
        let e = off + data.len() as u64;
        if s >= e {
            proof {
                assert(put(self.view(), lo as nat, off as nat, data@) =~= self.view());
            }
            return;
        }
        let (i, j) = self.locate(s, e);
        proof {
            lemma_all_held(f, s as nat, e as nat, i as int, j as int);
            if i < j {
                assert(f[i as int] == (self.v@[i as int].0 as nat, self.v@[i as int].1@));
            }
        }
        if i < j && self.v[i].0 <= s && e <= self.v[i].0 + self.v[i].1.len() as u64 {
            proof {
                lemma_at(f);
                assert forall|k: nat| s <= k < e implies #[trigger] self.view().contains_key(k) by {
                    assert(inf(f, i as int, k));
                }
                assert(put(self.view(), lo as nat, off as nat, data@) =~= self.view());
            }
            return;
        }
        let (h, _c) = self.counts(lo, off, data, s, e, i, j);
        let (ms, me) = self.bounds(s, e, i, j);
        let md = self.merged(off, data, s, e, i, j, ms, me);
        let ghost mdv = md@;
        self.splice_in(i, j, ms, md);
        self.held = h;
        proof {
            lemma_insert_post(f, lo as nat, off as nat, data@, s as nat, e as nat, i as int, j as int, mdv);
        }
    }

    /// The merged fragment's start and end (`mlo`, `mhi`).
    fn bounds(&self, s: u64, e: u64, i: usize, j: usize) -> (r: (u64, u64))
        requires
            self.wf(),
            s < e <= VARINT_MAX,
            located(self.fs(), s as nat, e as nat, i as int, j as int),
        ensures
            r.0 == mlo(self.fs(), i as int, j as int, s as nat),
            r.1 == mhi(self.fs(), i as int, j as int, e as nat),
    {
        let ghost f = self.fs();
        proof {
            if i < j {
                assert(f[i as int] == (self.v@[i as int].0 as nat, self.v@[i as int].1@));
                assert(f[j - 1] == (self.v@[j - 1].0 as nat, self.v@[j - 1].1@));
                assert(f[j - 1].0 + f[j - 1].1.len() <= VARINT_MAX);
            }
        }
        let ms = if i < j && self.v[i].0 < s {
            self.v[i].0
        } else {
            s
        };
        let me = if i < j && self.v[j - 1].0 + self.v[j - 1].1.len() as u64 > e {
            self.v[j - 1].0 + self.v[j - 1].1.len() as u64
        } else {
            e
        };
        (ms, me)
    }

    /// Replaces fragments `[i, j)` with `(ms, md)`.
    fn splice_in(&mut self, i: usize, j: usize, ms: u64, md: Vec<u8>)
        requires
            i <= j <= old(self).v@.len(),
        ensures
            final(self).fs() == splice(old(self).fs(), i as int, j as int, (ms as nat, md@)),
            final(self).held == old(self).held,
    {
        let ghost f = self.fs();
        let ghost mdv = md@;
        if j == i {
            // A new fragment: one shift of the tail, no reallocation of it.
            self.v.insert(i, (ms, md));
        } else if j == i + 1 {
            // One fragment replaced in place.
            self.v[i] = (ms, md);
        } else {
            let mut tail = self.v.split_off(j);
            self.v.truncate(i);
            self.v.push((ms, md));
            self.v.append(&mut tail);
        }
        proof {
            let g = splice(f, i as int, j as int, (ms as nat, mdv));
            lemma_splice_index(f, i as int, j as int, (ms as nat, mdv));
            assert(self.fs() =~= g) by {
                assert forall|t: int| 0 <= t < g.len() implies #[trigger] self.fs()[t] == g[t] by {
                    if t > i {
                        assert(self.v@[t] == old(self).v@[t - i - 1 + j]);
                    } else if t < i {
                        assert(self.v@[t] == old(self).v@[t]);
                    }
                }
            }
        }
    }

    /// `insert`'s new fragment `[ms, me)`: fragments `[i, j)` with the gaps around and between
    /// them filled from `data` (split from `insert` for the rlimit).
    #[verifier::spinoff_prover]
    fn merged(&self, off: u64, data: &[u8], _s: u64, e: u64, i: usize, j: usize, ms: u64, _me: u64) -> (md: Vec<u8>)
        requires
            self.wf(),
            off <= _s < e,
            e == off + data@.len(),
            e <= VARINT_MAX,
            located(self.fs(), _s as nat, e as nat, i as int, j as int),
            ms == mlo(self.fs(), i as int, j as int, _s as nat),
            _me == mhi(self.fs(), i as int, j as int, e as nat),
        ensures
            md@.len() == _me - ms,
            forall|q: nat| ms <= q < _me ==> #[trigger] md@[q - ms] == nb(self.fs(), data@, off as nat, q),
    {
        let ghost f = self.fs();
        let ghost fv = |q: nat| nb(f, data@, off as nat, q);
        let mut md: Vec<u8> = Vec::with_capacity((_me - ms) as usize);
        let mut p: u64 = ms;
        let mut t: usize = i;
        while t < j
            invariant
                f == self.fs(),
                fv == (|q: nat| nb(f, data@, off as nat, q)),
                sep(f),
                located(f, _s as nat, e as nat, i as int, j as int),
                ms == mlo(f, i as int, j as int, _s as nat),
                _me == mhi(f, i as int, j as int, e as nat),
                off <= _s < e,
                e == off + data@.len(),
                i <= t <= j,
                ms <= p,
                md@.len() == p - ms,
                t == i ==> p == ms,
                t > i ==> p == f[t - 1].0 + f[t - 1].1.len(),
                forall|q: nat| ms <= q < p ==> #[trigger] md@[q - ms] == fv(q),
            decreases j - t,
        {
            proof {
                assert(f[t as int] == (self.v@[t as int].0 as nat, self.v@[t as int].1@));
                lemma_gap(f, _s as nat, e as nat, i as int, j as int, t as int, p as nat, data@, off as nat);
            }
            let st = self.v[t].0;
            if p < st {
                let ghost m0 = md@;
                push_slice(&mut md, data, (p - off) as usize, (st - off) as usize);
                proof {
                    lemma_extend(m0, data@.subrange(p - off, st - off), ms as nat, p as nat, fv);
                }
            }
            let ghost m1 = md@;
            push_slice(&mut md, self.v[t].1.as_slice(), 0, self.v[t].1.len());
            proof {
                assert(self.v@[t as int].1@.subrange(0, self.v@[t as int].1@.len() as int) =~= f[t as int].1);
                lemma_frag(f, t as int, data@, off as nat);
                lemma_extend(m1, f[t as int].1, ms as nat, st as nat, fv);
            }
            p = st + self.v[t].1.len() as u64;
            t = t + 1;
        }
        proof {
            lemma_gap(f, _s as nat, e as nat, i as int, j as int, t as int, p as nat, data@, off as nat);
        }
        if p < e {
            let ghost m0 = md@;
            push_slice(&mut md, data, (p - off) as usize, (e - off) as usize);
            proof {
                lemma_extend(m0, data@.subrange(p - off, e - off), ms as nat, p as nat, fv);
            }
        }
        proof {
            if j > i {
                assert(f[j - 1].0 + f[j - 1].1.len() <= VARINT_MAX);
            }
        }
        md
    }

    /// If a fragment starts at `end`, appends its bytes to `out` and removes it; returns the end
    /// of the run of positions held from `end` (`end` itself if none starts there).
    pub fn take_front(&mut self, end: u64, out: &mut Vec<u8>) -> (r: u64)
        requires
            old(self).wf(),
            end <= VARINT_MAX,
            forall|k: nat| #[trigger] old(self).view().contains_key(k) ==> k >= end,
        ensures
            final(self).wf(),
            end <= r <= VARINT_MAX,
            forall|k: nat| end <= k < r ==> #[trigger] old(self).view().contains_key(k),
            !old(self).view().contains_key(r as nat),
            final(out)@ == old(out)@ + Seq::new((r - end) as nat, |i: int| old(self).view()[(end + i) as nat]),
            forall|k: nat| #[trigger]
                final(self).view().contains_key(k) <==> old(self).view().contains_key(k) && k > r,
            forall|k: nat| #[trigger]
                final(self).view().contains_key(k) ==> final(self).view()[k] == old(self).view()[k],
    {
        let ghost f = self.fs();
        if self.v.len() == 0 || self.v[0].0 != end {
            proof {
                if f.len() > 0 {
                    assert(f[0] == (self.v@[0].0 as nat, self.v@[0].1@));
                }
                lemma_take_none(f, end as nat);
                assert(Seq::new(0, |i: int| old(self).view()[(end + i) as nat]) =~= Seq::<u8>::empty());
                assert(out@ =~= old(out)@ + Seq::<u8>::empty());
            }
            return end;
        }
        proof {
            assert(f[0] == (self.v@[0].0 as nat, self.v@[0].1@));
            lemma_take_post(f);
        }
        let (_st, mut d) = self.v.remove(0);
        let len = d.len() as u64;
        let ghost dd = d@;
        out.append(&mut d);
        self.held = self.held - len;
        let r = end + len;
        proof {
            assert(self.fs() =~= f.skip(1));
            assert(out@ =~= old(out)@ + Seq::new((r - end) as nat, |i: int| old(self).view()[(end + i) as nat])) by {
                assert forall|i: int| 0 <= i < r - end implies #[trigger] dd[i] == old(self).view()[(end + i) as nat] by {
                    assert(old(self).view().contains_key((end + i) as nat));
                }
            }
        }
        r
    }
}

/// Appends `src[a..b]` to `out`.
fn push_slice(out: &mut Vec<u8>, src: &[u8], a: usize, b: usize)
    requires
        a <= b <= src@.len(),
    ensures
        final(out)@ == old(out)@ + src@.subrange(a as int, b as int),
{
    let mut k = a;
    while k < b
        invariant
            a <= k <= b <= src@.len(),
            out@ == old(out)@ + src@.subrange(a as int, k as int),
        decreases b - k,
    {
        out.push(src[k]);
        proof {
            assert(out@ =~= old(out)@ + src@.subrange(a as int, k + 1));
        }
        k = k + 1;
    }
}

} // verus!

impl Frags {
    /// Test support: the bytes allocated for the fragments, the list's own slots included. Verus
    /// models `Vec` length, not capacity (TRUSTED.md).
    #[doc(hidden)]
    pub fn capacity(&self) -> usize {
        let slots = self.v.capacity() * std::mem::size_of::<(u64, Vec<u8>)>();
        self.v.iter().fold(slots, |a, (_, d)| a + d.capacity())
    }
}
