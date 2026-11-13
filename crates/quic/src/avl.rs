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

} // verus!
