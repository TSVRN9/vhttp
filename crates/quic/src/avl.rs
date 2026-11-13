//! A verified AVL tree keyed by `u64`, viewed as its in-order sequence of entries. Ops return a ghost
//! cost (one unit per node visited, an empty child included) bounded in their ensures.
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
    let rb = r.unwrap();
    let Node { key: rk, val: rv, h: _, left: rl, right: rr } = *rb;
    proof {
        assert(wf(rl) && wf(rr) && keys_lt(rl, rk) && keys_gt(rr, rk));
        lemma_seq_node(r0);
        lemma_keys_cat(r0, rl, (rk, rv), rr, k);
    }
    let x = mk(l, k, v, rl);
    proof {
        assert(keys_lt(l, rk));
        lemma_keys_cat(x, l, (k, v), rl, rk);
    }
    let t = mk(x, rk, rv, rr);
    proof {
        assert(seq(t) =~= seq(l) + seq![(k, v)] + seq(r0));
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
    let ghost rl0 = rl;
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
        assert(seq(r0) == seq(rl0) + seq![(rk, rv)] + seq(rr));
        assert(seq(rl0) == seq(rll) + seq![(lk, lv)] + seq(rlr));
        assert(seq(t) =~= seq(l) + seq![(k, v)] + seq(r0));
    }
    (t, Ghost(5))
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
    let lb = l.unwrap();
    let Node { key: lk, val: lv, h: _, left: ll, right: lr } = *lb;
    proof {
        assert(wf(ll) && wf(lr) && keys_lt(ll, lk) && keys_gt(lr, lk));
        lemma_seq_node(l0);
        lemma_keys_cat(l0, ll, (lk, lv), lr, k);
    }
    let x = mk(lr, k, v, r);
    proof {
        lemma_keys_cat(x, lr, (k, v), r, lk);
    }
    let t = mk(ll, lk, lv, x);
    proof {
        assert(seq(t) =~= seq(l0) + seq![(k, v)] + seq(r));
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
    let ghost lr0 = lr;
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
        assert(seq(l0) == seq(ll) + seq![(lk, lv)] + seq(lr0));
        assert(seq(lr0) == seq(lrl) + seq![(rk, rv)] + seq(lrr));
        assert(seq(t) =~= seq(l0) + seq![(k, v)] + seq(r));
    }
    (t, Ghost(5))
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
        r.1@ <= c_join() * (vstd::math::abs(ht(a) - ht(b)) + 1),
    decreases ht(a) + ht(b),
{
    let ghost (a0, b0) = (a, b);
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
        (t, Ghost(1 + cc + bc))
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
        (t, Ghost(1 + cc + bc))
    } else {
        (mk(a, k, v, b), Ghost(1))
    }
}

} // verus!
