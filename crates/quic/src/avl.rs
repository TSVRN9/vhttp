//! A verified AVL tree keyed by `u64`, viewed as its in-order sequence of entries. Ops return a ghost
//! cost (one unit per node visited, an empty child included) bounded in their ensures.
//! `join` charges one unit per node exposed or created; its O(1) height reads and empty children per level go uncharged.
use vstd::prelude::*;
// Used only in ghost code, which a plain `cargo build` erases.
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;

verus! {

pub struct Node<V> {
    pub key: u64,
    pub val: V,
    pub h: u8,
    pub left: Tree<V>,
    pub right: Tree<V>,
}

pub type Tree<V> = Option<Box<Node<V>>>;

/// The height: 0 for an empty tree, else the root's stored height.
pub open spec fn ht<V>(t: Tree<V>) -> nat {
    match t {
        None => 0,
        Some(b) => b.h as nat,
    }
}

/// The entries in order.
pub open spec fn seq<V>(t: Tree<V>) -> Seq<(u64, V)>
    decreases t,
{
    match t {
        None => Seq::empty(),
        Some(b) => seq(b.left) + seq![(b.key, b.val)] + seq(b.right),
    }
}

/// Every key of `t` is below `k`.
pub open spec fn keys_lt<V>(t: Tree<V>, k: u64) -> bool {
    forall|i: int| 0 <= i < seq(t).len() ==> #[trigger] seq(t)[i].0 < k
}

/// Every key of `t` is above `k`.
pub open spec fn keys_gt<V>(t: Tree<V>, k: u64) -> bool {
    forall|i: int| 0 <= i < seq(t).len() ==> #[trigger] seq(t)[i].0 > k
}

/// Keys strictly increase.
pub open spec fn sorted<V>(s: Seq<(u64, V)>) -> bool {
    forall|i: int, j: int| #![trigger s[i], s[j]] 0 <= i < j < s.len() ==> s[i].0 < s[j].0
}

/// A search tree, AVL-balanced, with correct stored heights of at most 126.
pub open spec fn wf<V>(t: Tree<V>) -> bool
    decreases t,
{
    match t {
        None => true,
        Some(b) => {
            &&& wf(b.left)
            &&& wf(b.right)
            &&& keys_lt(b.left, b.key)
            &&& keys_gt(b.right, b.key)
            &&& b.h as nat == 1 + if ht(b.left) >= ht(b.right) { ht(b.left) } else { ht(b.right) }
            &&& ht(b.left) <= ht(b.right) + 1
            &&& ht(b.right) <= ht(b.left) + 1
            &&& b.h <= 126
        },
    }
}

/// The cost constant of `get_le`.
pub open spec fn c_get() -> nat {
    1
}

/// Where a node's own entry and its subtrees' entries sit in its sequence.
pub proof fn lemma_seq_node<V>(t: Tree<V>)
    requires
        t is Some,
    ensures
        ({
            let b = t->0;
            let (l, r) = (seq(b.left), seq(b.right));
            &&& seq(t).len() == l.len() + 1 + r.len()
            &&& seq(t)[l.len() as int] == (b.key, b.val)
            &&& forall|i: int| 0 <= i < l.len() ==> #[trigger] seq(t)[i] == l[i]
            &&& forall|j: int| l.len() + 1 <= j < seq(t).len() ==> #[trigger] seq(t)[j] == r[j - l.len() - 1]
        }),
{
    let b = t->0;
    assert(seq(t) == seq(b.left) + seq![(b.key, b.val)] + seq(b.right));
}

/// `l`, then `x`, then `r` is sorted when each part is and the keys of `l` are below `x`'s and those of `r` above.
pub proof fn lemma_sorted_concat<V>(l: Seq<(u64, V)>, x: (u64, V), r: Seq<(u64, V)>)
    requires
        sorted(l),
        sorted(r),
        forall|i: int| 0 <= i < l.len() ==> #[trigger] l[i].0 < x.0,
        forall|j: int| 0 <= j < r.len() ==> #[trigger] r[j].0 > x.0,
    ensures
        sorted(l + seq![x] + r),
{
    let s = l + seq![x] + r;
    let n = l.len() as int;
    assert forall|i: int, j: int| 0 <= i < j < s.len() implies #[trigger] s[i].0 < #[trigger] s[j].0 by {
        if j < n {
            assert(s[i] == l[i] && s[j] == l[j]);
        } else if j == n {
            assert(s[i] == l[i]);
        } else if i < n {
            assert(s[i] == l[i] && s[j] == r[j - n - 1]);
        } else if i == n {
            assert(s[j] == r[j - n - 1]);
        } else {
            assert(s[i] == r[i - n - 1] && s[j] == r[j - n - 1]);
        }
    }
}

pub proof fn lemma_wf_sorted<V>(t: Tree<V>)
    requires
        wf(t),
    ensures
        sorted(seq(t)),
    decreases t,
{
    if let Some(b) = t {
        assert(wf(b.left) && wf(b.right) && keys_lt(b.left, b.key) && keys_gt(b.right, b.key));
        lemma_wf_sorted(b.left);
        lemma_wf_sorted(b.right);
        lemma_sorted_concat(seq(b.left), (b.key, b.val), seq(b.right));
        assert(seq(t) == seq(b.left) + seq![(b.key, b.val)] + seq(b.right));
    }
}

proof fn lemma_pow2_mono(a: nat, b: nat)
    requires
        a <= b,
    ensures
        pow2(a) <= pow2(b),
{
    if a < b {
        lemma_pow2_strictly_increases(a, b);
    }
}

/// An AVL tree of height `h` holds at least `2^(h/2) - 1` entries.
pub proof fn lemma_height<V>(t: Tree<V>)
    requires
        wf(t),
    ensures
        seq(t).len() + 1 >= pow2(ht(t) / 2),
    decreases t,
{
    match t {
        None => {
            lemma_pow2(0);
            vstd::arithmetic::power::lemma_pow0(2);
        },
        Some(b) => {
            let (l, r) = (b.left, b.right);
            assert(wf(l) && wf(r));
            assert(seq(t).len() == seq(l).len() + 1 + seq(r).len());
            let h = ht(t);
            lemma_height(l);
            lemma_height(r);
            if h < 2 {
                lemma_pow2(0);
                vstd::arithmetic::power::lemma_pow0(2);
                assert(h / 2 == 0);
            } else {
                let e = (h / 2 - 1) as nat;
                assert(ht(l) >= h - 2 && ht(r) >= h - 2);
                assert(ht(l) / 2 >= e && ht(r) / 2 >= e);
                lemma_pow2_mono(e, ht(l) / 2);
                lemma_pow2_mono(e, ht(r) / 2);
                lemma_pow2_unfold(h / 2);
            }
        },
    }
}

/// Two wf trees of balanced heights, with fewer than `2^63` entries in all, fit under a node of height at most 126.
pub proof fn lemma_node_cap<V>(l: Tree<V>, r: Tree<V>)
    requires
        wf(l),
        wf(r),
        ht(l) <= ht(r) + 1,
        ht(r) <= ht(l) + 1,
        seq(l).len() + seq(r).len() + 1 < pow2(63),
    ensures
        1 + (if ht(l) >= ht(r) { ht(l) } else { ht(r) }) <= 126,
{
    // A stored height is at most 126, so the bound fails only if a child has height 126, which lemma_height forbids.
    assert(ht(l) <= 126 && ht(r) <= 126) by {
        if let Some(b) = l {
            assert(b.h <= 126);
        }
        if let Some(b) = r {
            assert(b.h <= 126);
        }
    }
    lemma_height(l);
    lemma_height(r);
    if ht(l) == 126 {
        assert(ht(l) / 2 == 63);
    }
    if ht(r) == 126 {
        assert(ht(r) / 2 == 63);
    }
}

pub fn height<V>(t: &Tree<V>) -> (r: u8)
    ensures
        r == ht(*t),
{
    match t {
        None => 0,
        Some(b) => b.h,
    }
}

/// `i` is the last index of `s` whose key is at most `k`, and holds `(key, v)`.
pub open spec fn last_le<V>(s: Seq<(u64, V)>, k: u64, i: int, key: u64, v: V) -> bool {
    &&& 0 <= i < s.len()
    &&& s[i] == (key, v)
    &&& key <= k
    &&& forall|j: int| i < j < s.len() ==> #[trigger] s[j].0 > k
}

/// The node's own entry is the answer when the right subtree's keys all exceed `k`.
proof fn lemma_get_le_here<V>(t: Tree<V>, k: u64)
    requires
        wf(t),
        t is Some,
        t->0.key <= k,
        keys_gt(t->0.right, k),
    ensures
        last_le(seq(t), k, seq(t->0.left).len() as int, t->0.key, t->0.val),
{
    lemma_seq_node(t);
}

/// An answer in the left subtree is the answer, when the node's key exceeds `k`.
proof fn lemma_get_le_left<V>(t: Tree<V>, k: u64, i: int, key: u64, v: V)
    requires
        wf(t),
        t is Some,
        t->0.key > k,
        last_le(seq(t->0.left), k, i, key, v),
    ensures
        last_le(seq(t), k, i, key, v),
{
    lemma_seq_node(t);
    assert(keys_gt(t->0.right, t->0.key));
}

/// No answer in the left subtree means none in the tree, when the node's key exceeds `k`.
proof fn lemma_get_le_none<V>(t: Tree<V>, k: u64)
    requires
        wf(t),
        t is Some,
        t->0.key > k,
        keys_gt(t->0.left, k),
    ensures
        keys_gt(t, k),
{
    lemma_seq_node(t);
    assert(keys_gt(t->0.right, t->0.key));
}

/// An answer in the right subtree is the answer, shifted past the left subtree and the node.
proof fn lemma_get_le_right<V>(t: Tree<V>, k: u64, i: int, key: u64, v: V)
    requires
        t is Some,
        last_le(seq(t->0.right), k, i, key, v),
    ensures
        last_le(seq(t), k, seq(t->0.left).len() + 1 + i, key, v),
{
    lemma_seq_node(t);
}

/// The entry with the greatest key at most `k`, if any.
pub fn get_le<V>(t: &Tree<V>, k: u64) -> (r: (Option<(u64, &V)>, Ghost<nat>))
    requires
        wf(*t),
    ensures
        r.0 is Some ==> exists|i: int| #[trigger] last_le(seq(*t), k, i, (r.0->0).0, *(r.0->0).1),
        r.0 is None ==> keys_gt(*t, k),
        r.1@ <= c_get() * (ht(*t) + 1),
    decreases *t,
{
    let ghost mut work: nat = 1;
    match t {
        None => (None, Ghost(work)),
        Some(b) => {
            proof {
                assert(wf(b.left) && wf(b.right));
                assert(ht(b.left) + 1 <= ht(*t) && ht(b.right) + 1 <= ht(*t));
            }
            // Each answer's `last_le` is asserted on the returned tuple's own fields: the postcondition's trigger.
            if b.key > k {
                let (r, Ghost(c)) = get_le(&b.left, k);
                proof {
                    work = work + c;
                    match r {
                        Some((key, v)) => {
                            let i = choose|i: int| #[trigger] last_le(seq(b.left), k, i, key, *v);
                            lemma_get_le_left(*t, k, i, key, *v);
                            assert(last_le(seq(*t), k, i, (r->0).0, *(r->0).1));
                        },
                        None => lemma_get_le_none(*t, k),
                    }
                }
                (r, Ghost(work))
            } else {
                let (r, Ghost(c)) = get_le(&b.right, k);
                proof {
                    work = work + c;
                }
                match r {
                    Some((key, v)) => {
                        let res = Some((key, v));
                        proof {
                            let i = choose|i: int| #[trigger] last_le(seq(b.right), k, i, key, *v);
                            lemma_get_le_right(*t, k, i, key, *v);
                            assert(last_le(seq(*t), k, seq(b.left).len() + 1 + i, (res->0).0, *(res->0).1));
                        }
                        (res, Ghost(work))
                    },
                    None => {
                        let res = Some((b.key, &b.val));
                        proof {
                            lemma_get_le_here(*t, k);
                            assert(last_le(seq(*t), k, seq(b.left).len() as int, (res->0).0, *(res->0).1));
                        }
                        (res, Ghost(work))
                    },
                }
            }
        },
    }
}

/// The cost constant of `join`.
pub open spec fn c_join() -> nat {
    6
}

/// The keys of a tree whose entries are `seq(l)`, then `x`, then `seq(r)` are all below (above) `k` exactly when those
/// of each part are.
pub proof fn lemma_keys_cat<V>(t: Tree<V>, l: Tree<V>, x: (u64, V), r: Tree<V>, k: u64)
    requires
        seq(t) == seq(l) + seq![x] + seq(r),
    ensures
        keys_lt(t, k) <==> keys_lt(l, k) && x.0 < k && keys_lt(r, k),
        keys_gt(t, k) <==> keys_gt(l, k) && x.0 > k && keys_gt(r, k),
{
    let (s, sl, sr) = (seq(t), seq(l), seq(r));
    let n = sl.len() as int;
    assert(s.len() == n + 1 + sr.len());
    assert(s[n] == x);
    assert forall|i: int| 0 <= i < n implies #[trigger] sl[i] == s[i] by {}
    assert forall|j: int| 0 <= j < sr.len() implies #[trigger] sr[j] == s[n + 1 + j] by {}
    assert forall|i: int| 0 <= i < s.len() implies {
        ||| i < n && #[trigger] s[i] == sl[i]
        ||| i == n && s[i] == x
        ||| n < i && s[i] == sr[i - n - 1]
    } by {}
}

/// A rotation's reshaping of three parts and two entries keeps their order.
proof fn lemma_seq_rot<T>(a: Seq<T>, x: T, b: Seq<T>, y: T, c: Seq<T>)
    ensures
        (a + seq![x] + b) + seq![y] + c == a + seq![x] + (b + seq![y] + c),
{
    assert((a + seq![x] + b) + seq![y] + c =~= a + seq![x] + (b + seq![y] + c));
}

/// A double rotation's reshaping of four parts and three entries keeps their order, from either side.
proof fn lemma_seq_rot2<T>(a: Seq<T>, x: T, b: Seq<T>, y: T, c: Seq<T>, z: T, d: Seq<T>)
    ensures
        (a + seq![x] + b) + seq![y] + (c + seq![z] + d) == a + seq![x] + ((b + seq![y] + c) + seq![z] + d),
        (a + seq![x] + b) + seq![y] + (c + seq![z] + d) == (a + seq![x] + (b + seq![y] + c)) + seq![z] + d,
{
    assert((a + seq![x] + b) + seq![y] + (c + seq![z] + d) =~= a + seq![x] + ((b + seq![y] + c) + seq![z] + d));
    assert((a + seq![x] + b) + seq![y] + (c + seq![z] + d) =~= (a + seq![x] + (b + seq![y] + c)) + seq![z] + d);
}

/// A node over balanced, ordered parts: its height is one above the taller part.
fn mk<V>(l: Tree<V>, k: u64, v: V, r: Tree<V>) -> (t: Tree<V>)
    requires
        wf(l),
        wf(r),
        keys_lt(l, k),
        keys_gt(r, k),
        ht(l) <= ht(r) + 1,
        ht(r) <= ht(l) + 1,
        seq(l).len() + seq(r).len() + 1 < pow2(63),
    ensures
        wf(t),
        seq(t) == seq(l) + seq![(k, v)] + seq(r),
        ht(t) == 1 + if ht(l) >= ht(r) { ht(l) } else { ht(r) },
{
    proof {
        lemma_node_cap(l, r);
    }
    let hl = height(&l);
    let hr = height(&r);
    let h = if hl >= hr { hl + 1 } else { hr + 1 };
    Some(Box::new(Node { key: k, val: v, h, left: l, right: r }))
}

/// `Node(l, k, r)` rebalanced when `r` is two taller: a single left rotation, or a double one when `r` leans left.
fn rot_left<V>(l: Tree<V>, k: u64, v: V, r: Tree<V>) -> (res: (Tree<V>, Ghost<nat>))
    requires
        wf(l),
        wf(r),
        keys_lt(l, k),
        keys_gt(r, k),
        ht(r) == ht(l) + 2,
        seq(l).len() + seq(r).len() + 1 < pow2(63),
    ensures
        wf(res.0),
        seq(res.0) == seq(l) + seq![(k, v)] + seq(r),
        ht(r) <= ht(res.0) <= ht(r) + 1,
        res.1@ <= 5,
{
    let lean = match &r {
        Some(b) => height(&b.left) > height(&b.right),
        None => false,
    };
    if lean {
        rot_left2(l, k, v, r)
    } else {
        rot_left1(l, k, v, r)
    }
}

/// The single left rotation: `Node(Node(l, k, rl), rk, rr)`.
fn rot_left1<V>(l: Tree<V>, k: u64, v: V, r: Tree<V>) -> (res: (Tree<V>, Ghost<nat>))
    requires
        wf(l),
        wf(r),
        keys_lt(l, k),
        keys_gt(r, k),
        ht(r) == ht(l) + 2,
        seq(l).len() + seq(r).len() + 1 < pow2(63),
        r is Some ==> ht(r->0.left) <= ht(r->0.right),
    ensures
        wf(res.0),
        seq(res.0) == seq(l) + seq![(k, v)] + seq(r),
        ht(r) <= ht(res.0) <= ht(r) + 1,
        res.1@ <= 5,
{
    let ghost r0 = r;
    proof {
        lemma_rot_single(l, k, v, r0);
    }
    let rb = r.unwrap();
    let Node { key: rk, val: rv, h: _, left: rl, right: rr } = *rb;
    let x = mk(l, k, v, rl);
    proof {
        lemma_keys_cat(x, l, (k, v), rl, rk);
    }
    let t = mk(x, rk, rv, rr);
    proof {
        lemma_seq_rot(seq(l), (k, v), seq(rl), (rk, rv), seq(rr));
    }
    (t, Ghost(3))
}

/// The double left rotation: `Node(Node(l, k, rll), lk, Node(rlr, rk, rr))` for `r = Node(Node(rll, lk, rlr), rk, rr)`.
fn rot_left2<V>(l: Tree<V>, k: u64, v: V, r: Tree<V>) -> (res: (Tree<V>, Ghost<nat>))
    requires
        wf(l),
        wf(r),
        keys_lt(l, k),
        keys_gt(r, k),
        ht(r) == ht(l) + 2,
        seq(l).len() + seq(r).len() + 1 < pow2(63),
        r is Some,
        ht(r->0.right) < ht(r->0.left),
    ensures
        wf(res.0),
        seq(res.0) == seq(l) + seq![(k, v)] + seq(r),
        ht(res.0) == ht(r),
        res.1@ <= 5,
{
    let ghost r0 = r;
    proof {
        lemma_rot_double(l, k, v, r0);
    }
    let rb = r.unwrap();
    let Node { key: rk, val: rv, h: _, left: rl, right: rr } = *rb;
    let lb = rl.unwrap();
    let Node { key: lk, val: lv, h: _, left: rll, right: rlr } = *lb;
    let x = mk(l, k, v, rll);
    let y = mk(rlr, rk, rv, rr);
    proof {
        lemma_keys_cat(x, l, (k, v), rll, lk);
        lemma_keys_cat(y, rlr, (rk, rv), rr, lk);
    }
    let t = mk(x, lk, lv, y);
    proof {
        lemma_seq_rot2(seq(l), (k, v), seq(rll), (lk, lv), seq(rlr), (rk, rv), seq(rr));
    }
    (t, Ghost(5))
}

/// The facts the single left rotation needs, on `r = Node(rl, rk, rr)` not leaning left.
proof fn lemma_rot_single<V>(l: Tree<V>, k: u64, v: V, r: Tree<V>)
    requires
        wf(l),
        wf(r),
        keys_lt(l, k),
        keys_gt(r, k),
        ht(r) == ht(l) + 2,
        seq(l).len() + seq(r).len() + 1 < pow2(63),
        r is Some ==> ht(r->0.left) <= ht(r->0.right),
    ensures
        r is Some,
        ({
            let (rk, rl, rr) = (r->0.key, r->0.left, r->0.right);
            &&& wf(rl) && wf(rr)
            &&& keys_gt(rl, k) && keys_lt(rl, rk) && keys_gt(rr, rk) && keys_lt(l, rk)
            &&& k < rk
            &&& ht(rl) <= ht(rr) && ht(rr) <= ht(rl) + 1 && ht(rr) == ht(l) + 1
            &&& seq(l).len() + seq(rl).len() + 1 < pow2(63)
            &&& seq(l).len() + seq(rl).len() + seq(rr).len() + 2 < pow2(63)
            &&& seq(r) == seq(rl) + seq![(rk, r->0.val)] + seq(rr)
        }),
{
    let (rk, rl, rr) = (r->0.key, r->0.left, r->0.right);
    assert(wf(rl) && wf(rr) && keys_lt(rl, rk) && keys_gt(rr, rk));
    lemma_seq_node(r);
    lemma_keys_cat(r, rl, (rk, r->0.val), rr, k);
}

/// The facts the double left rotation needs, on `r = Node(Node(rll, lk, rlr), rk, rr)` leaning left.
proof fn lemma_rot_double<V>(l: Tree<V>, k: u64, v: V, r: Tree<V>)
    requires
        wf(l),
        wf(r),
        keys_lt(l, k),
        keys_gt(r, k),
        ht(r) == ht(l) + 2,
        seq(l).len() + seq(r).len() + 1 < pow2(63),
        r is Some,
        ht(r->0.right) < ht(r->0.left),
    ensures
        ({
            let (rk, rl, rr) = (r->0.key, r->0.left, r->0.right);
            let (lk, rll, rlr) = (rl->0.key, rl->0.left, rl->0.right);
            &&& rl is Some
            &&& wf(rll) && wf(rlr) && wf(rr)
            &&& keys_gt(rll, k) && keys_lt(rll, lk) && keys_gt(rlr, lk) && keys_lt(rlr, rk) && keys_gt(rr, rk)
            &&& k < lk < rk
            &&& ht(l) <= ht(rll) + 1 && ht(rll) <= ht(l) && ht(rlr) <= ht(rr) && ht(rr) <= ht(rlr) + 1
            &&& ht(rr) == ht(l)
            &&& seq(l).len() + seq(rll).len() + 1 < pow2(63)
            &&& seq(rlr).len() + seq(rr).len() + 1 < pow2(63)
            &&& seq(l).len() + seq(rll).len() + seq(rlr).len() + seq(rr).len() + 3 < pow2(63)
            &&& seq(r) == (seq(rll) + seq![(lk, rl->0.val)] + seq(rlr)) + seq![(rk, r->0.val)] + seq(rr)
        }),
{
    let (rk, rl, rr) = (r->0.key, r->0.left, r->0.right);
    assert(wf(rl) && wf(rr) && keys_lt(rl, rk) && keys_gt(rr, rk));
    let (lk, rll, rlr) = (rl->0.key, rl->0.left, rl->0.right);
    assert(wf(rll) && wf(rlr) && keys_lt(rll, lk) && keys_gt(rlr, lk));
    lemma_seq_node(r);
    lemma_seq_node(rl);
    lemma_keys_cat(r, rl, (rk, r->0.val), rr, k);
    lemma_keys_cat(rl, rll, (lk, rl->0.val), rlr, k);
    lemma_keys_cat(rl, rll, (lk, rl->0.val), rlr, rk);
}

/// The mirror of `rot_left`: `Node(l, k, r)` rebalanced when `l` is two taller.
fn rot_right<V>(l: Tree<V>, k: u64, v: V, r: Tree<V>) -> (res: (Tree<V>, Ghost<nat>))
    requires
        wf(l),
        wf(r),
        keys_lt(l, k),
        keys_gt(r, k),
        ht(l) == ht(r) + 2,
        seq(l).len() + seq(r).len() + 1 < pow2(63),
    ensures
        wf(res.0),
        seq(res.0) == seq(l) + seq![(k, v)] + seq(r),
        ht(l) <= ht(res.0) <= ht(l) + 1,
        res.1@ <= 5,
{
    let lean = match &l {
        Some(b) => height(&b.right) > height(&b.left),
        None => false,
    };
    if lean {
        rot_right2(l, k, v, r)
    } else {
        rot_right1(l, k, v, r)
    }
}

/// The single right rotation: `Node(ll, lk, Node(lr, k, r))`.
fn rot_right1<V>(l: Tree<V>, k: u64, v: V, r: Tree<V>) -> (res: (Tree<V>, Ghost<nat>))
    requires
        wf(l),
        wf(r),
        keys_lt(l, k),
        keys_gt(r, k),
        ht(l) == ht(r) + 2,
        seq(l).len() + seq(r).len() + 1 < pow2(63),
        l is Some ==> ht(l->0.right) <= ht(l->0.left),
    ensures
        wf(res.0),
        seq(res.0) == seq(l) + seq![(k, v)] + seq(r),
        ht(l) <= ht(res.0) <= ht(l) + 1,
        res.1@ <= 5,
{
    let ghost l0 = l;
    proof {
        lemma_rot_single_mirror(l0, k, v, r);
    }
    let lb = l.unwrap();
    let Node { key: lk, val: lv, h: _, left: ll, right: lr } = *lb;
    let x = mk(lr, k, v, r);
    proof {
        lemma_keys_cat(x, lr, (k, v), r, lk);
    }
    let t = mk(ll, lk, lv, x);
    proof {
        lemma_seq_rot(seq(ll), (lk, lv), seq(lr), (k, v), seq(r));
    }
    (t, Ghost(3))
}

/// The double right rotation: `Node(Node(ll, lk, lrl), rk, Node(lrr, k, r))` for `l = Node(ll, lk, Node(lrl, rk, lrr))`.
fn rot_right2<V>(l: Tree<V>, k: u64, v: V, r: Tree<V>) -> (res: (Tree<V>, Ghost<nat>))
    requires
        wf(l),
        wf(r),
        keys_lt(l, k),
        keys_gt(r, k),
        ht(l) == ht(r) + 2,
        seq(l).len() + seq(r).len() + 1 < pow2(63),
        l is Some,
        ht(l->0.left) < ht(l->0.right),
    ensures
        wf(res.0),
        seq(res.0) == seq(l) + seq![(k, v)] + seq(r),
        ht(res.0) == ht(l),
        res.1@ <= 5,
{
    let ghost l0 = l;
    proof {
        lemma_rot_double_mirror(l0, k, v, r);
    }
    let lb = l.unwrap();
    let Node { key: lk, val: lv, h: _, left: ll, right: lr } = *lb;
    let rb = lr.unwrap();
    let Node { key: rk, val: rv, h: _, left: lrl, right: lrr } = *rb;
    let x = mk(ll, lk, lv, lrl);
    let y = mk(lrr, k, v, r);
    proof {
        lemma_keys_cat(x, ll, (lk, lv), lrl, rk);
        lemma_keys_cat(y, lrr, (k, v), r, rk);
    }
    let t = mk(x, rk, rv, y);
    proof {
        lemma_seq_rot2(seq(ll), (lk, lv), seq(lrl), (rk, rv), seq(lrr), (k, v), seq(r));
    }
    (t, Ghost(5))
}

/// The facts the single right rotation needs, on `l = Node(ll, lk, lr)` not leaning right.
proof fn lemma_rot_single_mirror<V>(l: Tree<V>, k: u64, v: V, r: Tree<V>)
    requires
        wf(l),
        wf(r),
        keys_lt(l, k),
        keys_gt(r, k),
        ht(l) == ht(r) + 2,
        seq(l).len() + seq(r).len() + 1 < pow2(63),
        l is Some ==> ht(l->0.right) <= ht(l->0.left),
    ensures
        l is Some,
        ({
            let (lk, ll, lr) = (l->0.key, l->0.left, l->0.right);
            &&& wf(ll) && wf(lr)
            &&& keys_lt(ll, lk) && keys_gt(lr, lk) && keys_lt(lr, k) && keys_gt(r, lk)
            &&& lk < k
            &&& ht(lr) <= ht(ll) && ht(ll) <= ht(lr) + 1 && ht(ll) == ht(r) + 1
            &&& seq(lr).len() + seq(r).len() + 1 < pow2(63)
            &&& seq(ll).len() + seq(lr).len() + seq(r).len() + 2 < pow2(63)
            &&& seq(l) == seq(ll) + seq![(lk, l->0.val)] + seq(lr)
        }),
{
    let (lk, ll, lr) = (l->0.key, l->0.left, l->0.right);
    assert(wf(ll) && wf(lr) && keys_lt(ll, lk) && keys_gt(lr, lk));
    lemma_seq_node(l);
    lemma_keys_cat(l, ll, (lk, l->0.val), lr, k);
}

/// The facts the double right rotation needs, on `l = Node(ll, lk, Node(lrl, rk, lrr))` leaning right.
proof fn lemma_rot_double_mirror<V>(l: Tree<V>, k: u64, v: V, r: Tree<V>)
    requires
        wf(l),
        wf(r),
        keys_lt(l, k),
        keys_gt(r, k),
        ht(l) == ht(r) + 2,
        seq(l).len() + seq(r).len() + 1 < pow2(63),
        l is Some,
        ht(l->0.left) < ht(l->0.right),
    ensures
        ({
            let (lk, ll, lr) = (l->0.key, l->0.left, l->0.right);
            let (rk, lrl, lrr) = (lr->0.key, lr->0.left, lr->0.right);
            &&& lr is Some
            &&& wf(ll) && wf(lrl) && wf(lrr)
            &&& keys_lt(ll, lk) && keys_gt(lrl, lk) && keys_lt(lrl, rk) && keys_gt(lrr, rk) && keys_lt(lrr, k)
            &&& lk < rk < k
            &&& ht(ll) <= ht(lrl) + 1 && ht(lrl) <= ht(ll) && ht(r) <= ht(lrr) + 1 && ht(lrr) <= ht(r)
            &&& ht(ll) == ht(r)
            &&& seq(ll).len() + seq(lrl).len() + 1 < pow2(63)
            &&& seq(lrr).len() + seq(r).len() + 1 < pow2(63)
            &&& seq(ll).len() + seq(lrl).len() + seq(lrr).len() + seq(r).len() + 3 < pow2(63)
            &&& seq(l) == seq(ll) + seq![(lk, l->0.val)] + (seq(lrl) + seq![(rk, lr->0.val)] + seq(lrr))
        }),
{
    let (lk, ll, lr) = (l->0.key, l->0.left, l->0.right);
    assert(wf(ll) && wf(lr) && keys_lt(ll, lk) && keys_gt(lr, lk));
    let (rk, lrl, lrr) = (lr->0.key, lr->0.left, lr->0.right);
    assert(wf(lrl) && wf(lrr) && keys_lt(lrl, rk) && keys_gt(lrr, rk));
    lemma_seq_node(l);
    lemma_seq_node(lr);
    lemma_keys_cat(l, ll, (lk, l->0.val), lr, k);
    lemma_keys_cat(lr, lrl, (rk, lr->0.val), lrr, k);
    lemma_keys_cat(lr, lrl, (rk, lr->0.val), lrr, lk);
}

/// `Node(l, k, r)` for parts at most two apart in height, rebalanced: no taller than the taller part plus one, no
/// shorter than it, and exactly one above it when the parts were balanced.
fn bal<V>(l: Tree<V>, k: u64, v: V, r: Tree<V>) -> (res: (Tree<V>, Ghost<nat>))
    requires
        wf(l),
        wf(r),
        keys_lt(l, k),
        keys_gt(r, k),
        ht(l) <= ht(r) + 2,
        ht(r) <= ht(l) + 2,
        seq(l).len() + seq(r).len() + 1 < pow2(63),
    ensures
        wf(res.0),
        seq(res.0) == seq(l) + seq![(k, v)] + seq(r),
        vstd::math::max(ht(l) as int, ht(r) as int) <= ht(res.0) <= vstd::math::max(ht(l) as int, ht(r) as int) + 1,
        ht(l) <= ht(r) + 1 && ht(r) <= ht(l) + 1 ==> ht(res.0) == vstd::math::max(ht(l) as int, ht(r) as int) + 1,
        res.1@ <= 5,
{
    let hl = height(&l);
    let hr = height(&r);
    if hr > hl && hr - hl > 1 {
        rot_left(l, k, v, r)
    } else if hl > hr && hl - hr > 1 {
        rot_right(l, k, v, r)
    } else {
        (mk(l, k, v, r), Ghost(1))
    }
}

/// What `join` needs of `a`'s parts when it descends `a`'s right spine.
proof fn lemma_join_right<V>(a: Tree<V>, k: u64, v: V, b: Tree<V>, c: Tree<V>)
    requires
        wf(a),
        wf(b),
        keys_lt(a, k),
        keys_gt(b, k),
        seq(a).len() + seq(b).len() + 1 < pow2(63),
        ht(a) > ht(b) + 1,
        a is Some,
    ensures
        ({
            let (al, ak, av, ar) = (a->0.left, a->0.key, a->0.val, a->0.right);
            &&& wf(al) && wf(ar)
            &&& keys_lt(ar, k) && keys_lt(al, ak)
            &&& seq(ar).len() + seq(b).len() + 1 < pow2(63)
            &&& ht(b) <= ht(ar) < ht(a)
            &&& ht(a) == 1 + vstd::math::max(ht(al) as int, ht(ar) as int)
            &&& ht(al) <= ht(ar) + 1 && ht(ar) <= ht(al) + 1
            &&& seq(c) == seq(ar) + seq![(k, v)] + seq(b) ==> {
                &&& keys_gt(c, ak)
                &&& seq(al).len() + seq(c).len() + 1 < pow2(63)
                &&& seq(al) + seq![(ak, av)] + seq(c) =~= seq(a) + seq![(k, v)] + seq(b)
            }
        }),
{
    let (al, ak, av, ar) = (a->0.left, a->0.key, a->0.val, a->0.right);
    assert(wf(al) && wf(ar) && keys_lt(al, ak) && keys_gt(ar, ak));
    lemma_seq_node(a);
    lemma_keys_cat(a, al, (ak, av), ar, k);
    if seq(c) == seq(ar) + seq![(k, v)] + seq(b) {
        lemma_keys_cat(c, ar, (k, v), b, ak);
    }
}

/// The mirror of `lemma_join_right`, for descending `b`'s left spine.
proof fn lemma_join_left<V>(a: Tree<V>, k: u64, v: V, b: Tree<V>, c: Tree<V>)
    requires
        wf(a),
        wf(b),
        keys_lt(a, k),
        keys_gt(b, k),
        seq(a).len() + seq(b).len() + 1 < pow2(63),
        ht(b) > ht(a) + 1,
        b is Some,
    ensures
        ({
            let (bl, bk, bv, br) = (b->0.left, b->0.key, b->0.val, b->0.right);
            &&& wf(bl) && wf(br)
            &&& keys_gt(bl, k) && keys_gt(br, bk)
            &&& seq(a).len() + seq(bl).len() + 1 < pow2(63)
            &&& ht(a) <= ht(bl) < ht(b)
            &&& ht(b) == 1 + vstd::math::max(ht(bl) as int, ht(br) as int)
            &&& ht(bl) <= ht(br) + 1 && ht(br) <= ht(bl) + 1
            &&& seq(c) == seq(a) + seq![(k, v)] + seq(bl) ==> {
                &&& keys_lt(c, bk)
                &&& seq(c).len() + seq(br).len() + 1 < pow2(63)
                &&& seq(c) + seq![(bk, bv)] + seq(br) =~= seq(a) + seq![(k, v)] + seq(b)
            }
        }),
{
    let (bl, bk, bv, br) = (b->0.left, b->0.key, b->0.val, b->0.right);
    assert(wf(bl) && wf(br) && keys_lt(bl, bk) && keys_gt(br, bk));
    lemma_seq_node(b);
    lemma_keys_cat(b, bl, (bk, bv), br, k);
    if seq(c) == seq(a) + seq![(k, v)] + seq(bl) {
        lemma_keys_cat(c, a, (k, v), bl, bk);
    }
}

/// The tree of `a`'s entries, then `(k, v)`, then `b`'s. It descends the taller tree's inner spine to where the heights
/// meet, so its cost grows with the height difference, and its height is the taller one's or one more.
pub fn join<V>(a: Tree<V>, k: u64, v: V, b: Tree<V>) -> (r: (Tree<V>, Ghost<nat>))
    requires
        wf(a),
        wf(b),
        keys_lt(a, k),
        keys_gt(b, k),
        seq(a).len() + seq(b).len() + 1 < pow2(63),
    ensures
        wf(r.0),
        seq(r.0) == seq(a) + seq![(k, v)] + seq(b),
        vstd::math::max(ht(a) as int, ht(b) as int) <= ht(r.0) <= vstd::math::max(ht(a) as int, ht(b) as int) + 1,
        ht(a) <= ht(b) + 1 && ht(b) <= ht(a) + 1 ==> ht(r.0) == vstd::math::max(ht(a) as int, ht(b) as int) + 1,
        r.1@ <= c_join() * (vstd::math::abs(ht(a) - ht(b)) + 1),
    decreases ht(a) + ht(b),
{
    let ghost (a0, b0) = (a, b);
    let ghost mut work: nat = 1;
    let ha = height(&a);
    let hb = height(&b);
    if ha > hb && ha - hb > 1 {
        let n = a.unwrap();
        let Node { key: ak, val: av, h: _, left: al, right: ar } = *n;
        proof {
            lemma_join_right(a0, k, v, b0, ar);
        }
        let (c, Ghost(cc)) = join(ar, k, v, b);
        proof {
            lemma_join_right(a0, k, v, b0, c);
        }
        let (t, Ghost(bc)) = bal(al, ak, av, c);
        proof {
            work = work + cc + bc;
        }
        (t, Ghost(work))
    } else if hb > ha && hb - ha > 1 {
        let n = b.unwrap();
        let Node { key: bk, val: bv, h: _, left: bl, right: br } = *n;
        proof {
            lemma_join_left(a0, k, v, b0, bl);
        }
        let (c, Ghost(cc)) = join(a, k, v, bl);
        proof {
            lemma_join_left(a0, k, v, b0, c);
        }
        let (t, Ghost(bc)) = bal(c, bk, bv, br);
        proof {
            work = work + cc + bc;
        }
        (t, Ghost(work))
    } else {
        (mk(a, k, v, b), Ghost(work))
    }
}

/// Every key of `t` is at least `k`.
pub open spec fn keys_ge<V>(t: Tree<V>, k: u64) -> bool {
    forall|i: int| 0 <= i < seq(t).len() ==> #[trigger] seq(t)[i].0 >= k
}

/// The cost constant of `split`'s own visits (its joins are charged at `c_join()`).
pub open spec fn c_split() -> nat {
    1
}

/// The constant of `split`'s corollary bound: `6 * c_join() + c_split()`.
pub open spec fn c_split6() -> nat {
    37
}

/// The cost constant of `pop_min`.
pub open spec fn c_pop() -> nat {
    6
}

/// The cost constant of `join2`.
pub open spec fn c_join2() -> nat {
    13
}

/// The cost constant of `drain`.
pub open spec fn c_drain() -> nat {
    1
}

/// The keys of a tree whose entries are `seq(a)` then `seq(b)` are all below (above, at least) `k` exactly when those of
/// each part are.
pub proof fn lemma_keys_app<V>(t: Tree<V>, a: Tree<V>, b: Tree<V>, k: u64)
    requires
        seq(t) == seq(a) + seq(b),
    ensures
        keys_lt(t, k) <==> keys_lt(a, k) && keys_lt(b, k),
        keys_gt(t, k) <==> keys_gt(a, k) && keys_gt(b, k),
        keys_ge(t, k) <==> keys_ge(a, k) && keys_ge(b, k),
{
    let (s, sa, sb) = (seq(t), seq(a), seq(b));
    let n = sa.len() as int;
    assert forall|i: int| 0 <= i < n implies #[trigger] sa[i] == s[i] by {}
    assert forall|j: int| 0 <= j < sb.len() implies #[trigger] sb[j] == s[n + j] by {}
    assert forall|i: int| 0 <= i < s.len() implies {
        ||| i < n && #[trigger] s[i] == sa[i]
        ||| n <= i && s[i] == sb[i - n]
    } by {}
}

/// `lemma_keys_cat` for `keys_ge`.
pub proof fn lemma_keys_ge_cat<V>(t: Tree<V>, l: Tree<V>, x: (u64, V), r: Tree<V>, k: u64)
    requires
        seq(t) == seq(l) + seq![x] + seq(r),
    ensures
        keys_ge(t, k) <==> keys_ge(l, k) && x.0 >= k && keys_ge(r, k),
{
    let (s, sl, sr) = (seq(t), seq(l), seq(r));
    let n = sl.len() as int;
    assert(s.len() == n + 1 + sr.len());
    assert(s[n] == x);
    assert forall|i: int| 0 <= i < n implies #[trigger] sl[i] == s[i] by {}
    assert forall|j: int| 0 <= j < sr.len() implies #[trigger] sr[j] == s[n + 1 + j] by {}
    assert forall|i: int| 0 <= i < s.len() implies {
        ||| i < n && #[trigger] s[i] == sl[i]
        ||| i == n && s[i] == x
        ||| n < i && s[i] == sr[i - n - 1]
    } by {}
}

/// A wf node's parts: both subtrees wf and ordered about the key, its entries, its height and balance.
proof fn lemma_node<V>(t: Tree<V>)
    requires
        wf(t),
        t is Some,
    ensures
        ({
            let (l, x, v, r) = (t->0.left, t->0.key, t->0.val, t->0.right);
            &&& wf(l) && wf(r)
            &&& keys_lt(l, x) && keys_gt(r, x)
            &&& seq(t) == seq(l) + seq![(x, v)] + seq(r)
            &&& seq(t).len() == seq(l).len() + 1 + seq(r).len()
            &&& ht(t) == 1 + vstd::math::max(ht(l) as int, ht(r) as int)
            &&& ht(l) <= ht(r) + 1 && ht(r) <= ht(l) + 1
        }),
{
    let b = t->0;
    assert(wf(b.left) && wf(b.right) && keys_lt(b.left, b.key) && keys_gt(b.right, b.key));
    assert(seq(t) == seq(b.left) + seq![(b.key, b.val)] + seq(b.right));
}

/// The reassociations `split`, `pop_min`, `join2` and `drain` need.
proof fn lemma_seq_assoc<T>(a: Seq<T>, b: Seq<T>, x: T, c: Seq<T>)
    ensures
        a + (b + seq![x] + c) == (a + b) + seq![x] + c,
        (a + seq![x] + b) + c == a + seq![x] + (b + c),
        a.push(x) + b == a + seq![x] + b,
        a + (seq![x] + b) == a + seq![x] + b,
{
    assert(a + (b + seq![x] + c) =~= (a + b) + seq![x] + c);
    assert((a + seq![x] + b) + c =~= a + seq![x] + (b + c));
    assert(a.push(x) + b =~= a + seq![x] + b);
    assert(a + (seq![x] + b) =~= a + seq![x] + b);
}

/// Split's cost in case `k < x` (and its mirror): the subtree `s` split into `kept` and `joined`, `joined` rejoined with
/// the other subtree `o` into `c`. Join's lower bound telescopes: `cj <= C·(hc − hj + 2)`.
proof fn lemma_split_cost_side(hs: nat, ho: nat, h: nat, hk: nat, hj: nat, hc: nat, cs: nat, cj: nat)
    requires
        h == 1 + vstd::math::max(hs as int, ho as int),
        hs <= ho + 1,
        hk <= hs,
        hj <= hs,
        vstd::math::max(hj as int, ho as int) <= hc <= vstd::math::max(hj as int, ho as int) + 1,
        cs <= c_join() * (hk + hj + 4 * (hs + 1)) + c_split() * (hs + 1),
        cj <= c_join() * (vstd::math::abs(hj - ho) + 1),
    ensures
        hk <= h,
        hc <= h,
        1 + cs + cj <= c_join() * (hk + hc + 4 * (h + 1)) + c_split() * (h + 1),
{
    assert(cj <= c_join() * (hc - hj + 2));
}

/// Split's cost in case `k == x`: `l` kept whole, `c = join(None, x, r)`.
proof fn lemma_split_cost_eq(hl: nat, hr: nat, h: nat, hc: nat, cj: nat)
    requires
        h == 1 + vstd::math::max(hl as int, hr as int),
        hr <= hc <= hr + 1,
        cj <= c_join() * (vstd::math::abs(0 - hr) + 1),
    ensures
        hl <= h,
        hc <= h,
        1 + cj <= c_join() * (hl + hc + 4 * (h + 1)) + c_split() * (h + 1),
{
}

/// Split's case `k < x`: `(a, b)` split from `l`, `c = join(b, x, r)`.
proof fn lemma_split_lt<V>(l: Tree<V>, x: u64, v: V, r: Tree<V>, a: Tree<V>, b: Tree<V>, c: Tree<V>, k: u64)
    requires
        seq(a) + seq(b) == seq(l),
        keys_lt(l, x),
        keys_ge(b, k),
        k < x,
        keys_gt(r, x),
    ensures
        keys_lt(b, x),
        seq(b).len() <= seq(l).len(),
        seq(c) == seq(b) + seq![(x, v)] + seq(r) ==> {
            &&& seq(a) + seq(c) == seq(l) + seq![(x, v)] + seq(r)
            &&& keys_ge(c, k)
        },
{
    lemma_keys_app(l, a, b, x);
    if seq(c) == seq(b) + seq![(x, v)] + seq(r) {
        lemma_keys_ge_cat(c, b, (x, v), r, k);
        lemma_seq_assoc(seq(a), seq(b), (x, v), seq(r));
    }
}

/// Split's case `k > x`: `(a, b)` split from `r`, `c = join(l, x, a)`.
proof fn lemma_split_gt<V>(l: Tree<V>, x: u64, v: V, r: Tree<V>, a: Tree<V>, b: Tree<V>, c: Tree<V>, k: u64)
    requires
        seq(a) + seq(b) == seq(r),
        keys_gt(r, x),
        keys_lt(a, k),
        x < k,
        keys_lt(l, x),
    ensures
        keys_gt(a, x),
        seq(a).len() <= seq(r).len(),
        seq(c) == seq(l) + seq![(x, v)] + seq(a) ==> {
            &&& seq(c) + seq(b) == seq(l) + seq![(x, v)] + seq(r)
            &&& keys_lt(c, k)
        },
{
    lemma_keys_app(r, a, b, x);
    if seq(c) == seq(l) + seq![(x, v)] + seq(a) {
        lemma_keys_cat(c, l, (x, v), a, k);
        lemma_seq_assoc(seq(l), seq(a), (x, v), seq(b));
    }
}

/// Split's case `k == x`: `l` kept, `c = join(None, x, r)`.
proof fn lemma_split_eq<V>(l: Tree<V>, x: u64, v: V, r: Tree<V>, c: Tree<V>, k: u64)
    requires
        seq(c) == seq::<V>(None) + seq![(x, v)] + seq(r),
        keys_gt(r, x),
        k == x,
    ensures
        seq(l) + seq(c) == seq(l) + seq![(x, v)] + seq(r),
        keys_ge(c, k),
{
    lemma_keys_ge_cat(c, None, (x, v), r, k);
    assert(seq(c) =~= seq![(x, v)] + seq(r));
    lemma_seq_assoc(seq(l), seq(r), (x, v), seq(r));
}

/// The entries of `t` below `k`, and the rest. Its cost telescopes: each level's join is paid for by the growth of the
/// piece it builds, so the total is a constant times the input and output heights.
pub fn split<V>(t: Tree<V>, k: u64) -> (r: (Tree<V>, Tree<V>, Ghost<nat>))
    requires
        wf(t),
        seq(t).len() < pow2(63),
    ensures
        wf(r.0),
        wf(r.1),
        seq(r.0) + seq(r.1) == seq(t),
        keys_lt(r.0, k),
        keys_ge(r.1, k),
        ht(r.0) <= ht(t),
        ht(r.1) <= ht(t),
        r.2@ <= c_join() * (ht(r.0) + ht(r.1) + 4 * (ht(t) + 1)) + c_split() * (ht(t) + 1),
    decreases ht(t),
{
    let ghost t0 = t;
    let ghost mut work: nat = 1;
    match t {
        None => {
            proof {
                assert(seq(t0) + seq(t0) =~= seq(t0));
            }
            (None, None, Ghost(work))
        },
        Some(n) => {
            proof {
                lemma_node(t0);
            }
            let Node { key: x, val: v, h: _, left: l, right: r } = *n;
            if k < x {
                let (a, b, Ghost(cs)) = split(l, k);
                proof {
                    lemma_split_lt(l, x, v, r, a, b, b, k);
                }
                let (c, Ghost(cj)) = join(b, x, v, r);
                proof {
                    lemma_split_lt(l, x, v, r, a, b, c, k);
                    lemma_split_cost_side(ht(l), ht(r), ht(t0), ht(a), ht(b), ht(c), cs, cj);
                    work = work + cs + cj;
                }
                (a, c, Ghost(work))
            } else if k == x {
                let (c, Ghost(cj)) = join(None, x, v, r);
                proof {
                    lemma_split_eq(l, x, v, r, c, k);
                    lemma_split_cost_eq(ht(l), ht(r), ht(t0), ht(c), cj);
                    work = work + cj;
                }
                (l, c, Ghost(work))
            } else {
                let (a, b, Ghost(cs)) = split(r, k);
                proof {
                    lemma_split_gt(l, x, v, r, a, b, a, k);
                }
                let (c, Ghost(cj)) = join(l, x, v, a);
                proof {
                    lemma_split_gt(l, x, v, r, a, b, c, k);
                    assert(vstd::math::abs(ht(l) - ht(a)) == vstd::math::abs(ht(a) - ht(l)));
                    lemma_split_cost_side(ht(r), ht(l), ht(t0), ht(b), ht(a), ht(c), cs, cj);
                    work = work + cs + cj;
                }
                (c, b, Ghost(work))
            }
        },
    }
}

/// The corollary: split's cost is at most `c_split6() · (ht(t) + 1)`, its pieces being no taller than `t`.
pub proof fn lemma_split_cost<V>(t: Tree<V>, a: Tree<V>, b: Tree<V>, cost: nat)
    requires
        ht(a) <= ht(t),
        ht(b) <= ht(t),
        cost <= c_join() * (ht(a) + ht(b) + 4 * (ht(t) + 1)) + c_split() * (ht(t) + 1),
    ensures
        cost <= c_split6() * (ht(t) + 1),
{
}

/// The height of `bal(l2, x, r)`, `l2` being `l` less its first entry: at most one below `t`'s, and no taller.
proof fn lemma_pop_ht(hl: nat, hr: nat, h: nat, hl2: nat, hc: nat)
    requires
        h == 1 + vstd::math::max(hl as int, hr as int),
        hl <= hr + 1,
        hr <= hl + 1,
        hl - 1 <= hl2 <= hl,
        vstd::math::max(hl2 as int, hr as int) <= hc <= vstd::math::max(hl2 as int, hr as int) + 1,
        hl2 <= hr + 1 && hr <= hl2 + 1 ==> hc == vstd::math::max(hl2 as int, hr as int) + 1,
    ensures
        h - 1 <= hc <= h,
{
}

/// The keys left in `l2` after its first entry `(m, mv)` popped from `l` are those of `l`.
proof fn lemma_pop_keys<V>(l: Tree<V>, m: u64, mv: V, l2: Tree<V>, x: u64)
    requires
        seq![(m, mv)] + seq(l2) == seq(l),
        keys_lt(l, x),
    ensures
        keys_lt(l2, x),
{
    assert forall|i: int| 0 <= i < seq(l2).len() implies #[trigger] seq(l2)[i].0 < x by {
        assert(seq(l)[i + 1] == seq(l2)[i]);
    }
}

/// The first entry of `t`, and the rest; the height drops by at most one.
pub fn pop_min<V>(t: Tree<V>) -> (r: (Tree<V>, u64, V, Ghost<nat>))
    requires
        wf(t),
        t is Some,
        seq(t).len() < pow2(63),
    ensures
        wf(r.0),
        seq![(r.1, r.2)] + seq(r.0) == seq(t),
        ht(t) - 1 <= ht(r.0) <= ht(t),
        r.3@ <= c_pop() * (ht(t) + 1),
    decreases ht(t),
{
    let ghost t0 = t;
    let ghost mut work: nat = 1;
    proof {
        lemma_node(t0);
    }
    let n = t.unwrap();
    let Node { key: x, val: v, h: _, left: l, right: r } = *n;
    if l.is_none() {
        proof {
            assert(seq(t0) =~= seq![(x, v)] + seq(r));
        }
        (r, x, v, Ghost(work))
    } else {
        let (l2, m, mv, Ghost(cp)) = pop_min(l);
        proof {
            lemma_pop_keys(l, m, mv, l2, x);
        }
        let (c, Ghost(bc)) = bal(l2, x, v, r);
        proof {
            lemma_seq_assoc(seq![(m, mv)], seq(l2), (x, v), seq(r));
            lemma_pop_ht(ht(l), ht(r), ht(t0), ht(l2), ht(c));
            work = work + cp + bc;
        }
        (c, m, mv, Ghost(work))
    }
}

/// `b`'s first entry `(m, mv)` sits between `a`'s keys and the rest of `b`'s.
proof fn lemma_join2_keys<V>(a: Tree<V>, b: Tree<V>, m: u64, mv: V, b2: Tree<V>)
    requires
        wf(b),
        forall|i: int, j: int|
            0 <= i < seq(a).len() && 0 <= j < seq(b).len() ==> #[trigger] seq(a)[i].0 < #[trigger] seq(b)[j].0,
        seq![(m, mv)] + seq(b2) == seq(b),
    ensures
        keys_lt(a, m),
        keys_gt(b2, m),
{
    lemma_wf_sorted(b);
    assert(seq(b)[0] == (m, mv));
    assert forall|i: int| 0 <= i < seq(a).len() implies #[trigger] seq(a)[i].0 < m by {
        assert(seq(a)[i].0 < seq(b)[0].0);
    }
    assert forall|j: int| 0 <= j < seq(b2).len() implies #[trigger] seq(b2)[j].0 > m by {
        assert(seq(b)[j + 1] == seq(b2)[j]);
    }
}

/// `a`'s entries then `b`'s, every key of `a` being below every key of `b`.
pub fn join2<V>(a: Tree<V>, b: Tree<V>) -> (r: (Tree<V>, Ghost<nat>))
    requires
        wf(a),
        wf(b),
        forall|i: int, j: int|
            0 <= i < seq(a).len() && 0 <= j < seq(b).len() ==> #[trigger] seq(a)[i].0 < #[trigger] seq(b)[j].0,
        seq(a).len() + seq(b).len() < pow2(63),
    ensures
        wf(r.0),
        seq(r.0) == seq(a) + seq(b),
        ht(r.0) <= vstd::math::max(ht(a) as int, ht(b) as int) + 1,
        r.1@ <= c_join2() * (vstd::math::max(ht(a) as int, ht(b) as int) + 1),
{
    let ghost (a0, b0) = (a, b);
    let ghost mut work: nat = 1;
    if b.is_none() {
        proof {
            assert(seq(a0) + seq(b0) =~= seq(a0));
        }
        return (a, Ghost(work));
    }
    let (b2, m, mv, Ghost(cp)) = pop_min(b);
    proof {
        lemma_join2_keys(a0, b0, m, mv, b2);
    }
    let (c, Ghost(cj)) = join(a, m, mv, b2);
    proof {
        lemma_seq_assoc(seq(a0), seq(b2), (m, mv), seq(b0));
        work = work + cp + cj;
    }
    (c, Ghost(work))
}

/// Appends `t`'s entries, in order, to `out`, consuming `t`.
pub fn drain<V>(t: Tree<V>, out: &mut Vec<(u64, V)>) -> (r: Ghost<nat>)
    ensures
        final(out)@ == old(out)@ + seq(t),
        r@ <= c_drain() * (2 * seq(t).len() + 1),
    decreases t,
{
    let ghost t0 = t;
    let ghost mut work: nat = 1;
    match t {
        None => {
            proof {
                assert(out@ + seq(t0) =~= out@);
            }
            Ghost(work)
        },
        Some(n) => {
            let Node { key: x, val: v, h: _, left: l, right: r } = *n;
            let ghost o0 = out@;
            let Ghost(cl) = drain(l, out);
            let ghost o1 = out@;
            out.push((x, v));
            proof {
                lemma_seq_assoc(o1, seq(r), (x, v), seq(r));
            }
            let Ghost(cr) = drain(r, out);
            proof {
                lemma_seq_assoc(o0, seq(l), (x, v), seq(r));
                assert(seq(t0) == seq(l) + seq![(x, v)] + seq(r));
                work = work + cl + cr;
            }
            Ghost(work)
        },
    }
}

} // verus!
