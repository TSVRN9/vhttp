//! `ByteQueue` (9b2 D4, D5): a byte queue whose readers always see one contiguous region, with a proved worst-case
//! cost per call. Bytes live in an active `CapVec` `a` from `head` on; a migration copies them, a few per push, into a
//! larger `b` (D4's copy rate 3), so no call copies the whole queue. `push_slice` (at most `7d + 4`) is the one writer;
//! the read side (D5) is `len`, `peek`, `as_slice` (free), `drop_front` (at most 2) and `take_front` (at most `n + 3`).
//! `caps` and `newest`, outside `verus!`, are unverified test-only accessors (TRUSTED.md lists them).
//!
//! D5 fixes the shape 9b5's incremental parsers take over a queue they own:
//! `step(&mut self, src: &mut ByteQueue, budget: usize) -> (Progress, Ghost<nat>)`, ensuring
//! `final(src)@ == old(src)@.skip(k)` for the `k <= budget` bytes consumed, cost at most `c · (budget + 1)`, and the
//! parser state equal to the spec's fold over the consumed prefix.
use crate::capvec::CapVec;
use vstd::prelude::*;

verus! {

/// The longest queue (D1): every capacity, `3·S + MIN_CAP` < 2^30, fits a 32-bit `usize`.
pub const MAX_QUEUE: usize = 0x1000_0000;

/// The smallest buffer a push allocates (D4).
pub const MIN_CAP: usize = 64;

/// A migration in progress: `b` (capacity `cb`) holds a copy of `a[bs..c)`.
struct Mig {
    b: CapVec<u8>,
    cb: usize,
    bs: usize,
    c: usize,
}

pub struct ByteQueue {
    a: CapVec<u8>,
    ca: usize,
    head: usize,
    mig: Option<Mig>,
    /// Only spec fns read it, which a plain `cargo build` erases.
    #[allow(dead_code)]
    pk: Ghost<nat>,
}

impl View for ByteQueue {
    type V = Seq<u8>;

    closed spec fn view(&self) -> Seq<u8> {
        self.a@.subrange(self.head as int, self.a@.len() as int)
    }
}

impl ByteQueue {
    /// D4's migrating clauses, with `C = ca`, `L_a = a.len`, `R = L_a − c`, `room = C − L_a`.
    closed spec fn mig_wf(&self, m: Mig) -> bool {
        let la = self.a@.len() as int;
        let r = la - m.c;
        let room = self.ca - la;
        &&& m.b.wf()
        &&& m.cb == m.b.cap()
        &&& m.bs <= self.head <= la
        &&& m.bs <= m.c <= la
        &&& m.b@ == self.a@.subrange(m.bs as int, m.c as int)
        &&& r <= 2 * room
        &&& 2 * (la - m.bs) + r <= m.cb
        &&& m.cb <= vstd::math::max(MIN_CAP as int, (3 * self.pk@) as int)
    }

    pub closed spec fn wf(&self) -> bool {
        &&& self.a.wf()
        &&& self.ca == self.a.cap()
        &&& self.head <= self.a@.len()
        &&& self.a@.len() <= self.ca
        &&& self@.len() <= self.pk@ <= MAX_QUEUE
        &&& self.ca <= vstd::math::max(MIN_CAP as int, (3 * self.pk@) as int)
        &&& self@.len() == 0 ==> self.ca == 0 && self.mig is None && self.pk@ == 0
        &&& match self.mig {
            None => 2 * self.a@.len() <= self.ca,
            Some(m) => self.mig_wf(m),
        }
    }

    /// The largest length plus push since the queue was last empty.
    pub closed spec fn peak(&self) -> nat {
        self.pk@
    }

    /// The bytes both buffers asked the allocator for.
    pub closed spec fn requested(&self) -> nat {
        match self.mig {
            None => self.ca as nat,
            Some(m) => (self.ca + m.cb) as nat,
        }
    }

    pub proof fn lemma_wf(&self)
        requires
            self.wf(),
        ensures
            self@.len() <= MAX_QUEUE,
            self.requested() <= 2 * vstd::math::max(MIN_CAP as int, (3 * self.peak()) as int),
            !self.migrating() ==> self.requested() <= vstd::math::max(MIN_CAP as int, (3 * self.peak()) as int),
            self@.len() == 0 ==> self.peak() == 0 && self.requested() == 0,
    {
    }

    /// A migration is in progress: two buffers.
    pub closed spec fn migrating(&self) -> bool {
        self.mig is Some
    }

    /// D4 cases 2, 3 and 4 exactly, for `L_a = la`, length `len`, `C = ca`: 2 = `d`; 3 = `d + 1 + min(S, 3d)`, plus 1
    /// for the swap when `S = len + d <= 3d`; 4 = `len + d + 2`.
    closed spec fn idle_cost(la: nat, len: nat, ca: nat, d: nat) -> nat {
        if la + d <= ca / 2 {
            d
        } else if d <= ca / 2 {
            if len + d <= 3 * d {
                len + 2 * d + 2
            } else {
                4 * d + 1
            }
        } else {
            len + d + 2
        }
    }

    /// `push_slice`'s exact cost, the sum of its workers' costs on D4's path: `R + 1` for a step-1 copy that ends in a
    /// swap, then cases 2-4 with `L_a := L_a − bs`, `C := cb`; `3d + d` for one that does not.
    pub closed spec fn push_cost(&self, d: nat) -> nat {
        let la = self.a@.len();
        let m = self.mig->0;
        if d == 0 {
            0
        } else if self.mig is None {
            Self::idle_cost(la, self@.len(), self.ca as nat, d)
        } else if la - m.c <= 3 * d {
            (la - m.c) as nat + 1 + Self::idle_cost((la - m.bs) as nat, self@.len(), m.cb as nat, d)
        } else {
            4 * d
        }
    }

    /// No allocation: `CapVec::new(0)`.
    pub fn new() -> (r: ByteQueue)
        ensures
            r.wf(),
            r@ == Seq::<u8>::empty(),
            r.peak() == 0,
    {
        let r = ByteQueue { a: CapVec::new(0), ca: 0, head: 0, mig: None, pk: Ghost(0) };
        assert(r@ =~= Seq::<u8>::empty());
        r
    }

    pub fn len(&self) -> (r: usize)
        requires
            self.wf(),
        ensures
            r == self@.len(),
    {
        self.a.len() - self.head
    }

    pub fn peek(&self, i: usize) -> (r: u8)
        requires
            self.wf(),
            i < self@.len(),
        ensures
            r == self@[i as int],
    {
        *self.a.index(self.head + i)
    }

    pub fn as_slice(&self) -> (r: &[u8])
        requires
            self.wf(),
        ensures
            r@ == self@,
    {
        vstd::slice::slice_subrange(self.a.as_slice(), self.head, self.a.len())
    }

    /// Advances `head` by `n` (`n > 0`); a queue left empty drops both buffers (two frees, cost 2).
    fn q_advance(&mut self, n: usize) -> (r: Ghost<nat>)
        requires
            old(self).wf(),
            0 < n <= old(self)@.len(),
        ensures
            final(self).wf(),
            final(self)@ == old(self)@.skip(n as int),
            final(self)@.len() > 0 ==> final(self).peak() == old(self).peak(),
            r@ <= 2,
    {
        let ghost v0 = self@;
        self.head = self.head + n;
        if self.head == self.a.len() {
            self.a = CapVec::new(0);
            self.ca = 0;
            self.head = 0;
            self.mig = None;
            self.pk = Ghost(0);
            assert(self@ =~= v0.skip(n as int));
            Ghost(2)
        } else {
            assert(self@ =~= v0.skip(n as int));
            Ghost(0)
        }
    }

    /// Copies the first `n` bytes into an exact `CapVec` (one allocation, `n` pushes) and consumes them.
    pub fn take_front(&mut self, n: usize) -> (r: (CapVec<u8>, Ghost<nat>))
        requires
            old(self).wf(),
            n <= old(self)@.len(),
        ensures
            final(self).wf(),
            final(self)@ == old(self)@.skip(n as int),
            r.0.wf(),
            r.0@ == old(self)@.take(n as int),
            r.0.cap() == n,
            r.1@ <= n + 3,
            final(self)@.len() > 0 ==> final(self).peak() == old(self).peak(),
            n == 0 ==> *final(self) == *old(self),
    {
        let ghost mut work: nat = 1;
        let mut out = CapVec::new(n);
        if n == 0 {
            assert(out@ =~= self@.take(0));
            assert(self@ =~= self@.skip(0));
            return (out, Ghost(work));
        }
        let s = vstd::slice::slice_subrange(self.a.as_slice(), self.head, self.head + n);
        let Ghost(c1) = out.push_slice(s);
        proof {
            work = work + c1;
        }
        assert(out@ =~= self@.take(n as int));
        let Ghost(c2) = self.q_advance(n);
        proof {
            work = work + c2;
        }
        (out, Ghost(work))
    }

    /// The structure `mig_step` copies under: `b == a[bs..c)` and room in `b` for the rest of `a`.
    closed spec fn copy_ok(&self) -> bool {
        let m = self.mig->0;
        &&& self.mig is Some
        &&& m.b.wf()
        &&& m.cb == m.b.cap()
        &&& m.bs <= m.c <= self.a@.len()
        &&& m.b@ == self.a@.subrange(m.bs as int, m.c as int)
        &&& self.a@.len() - m.bs <= m.cb
    }

    /// Appends `s` to `a` below `ca` and raises the peak to the new length (cost `d`).
    fn q_append(&mut self, s: &[u8]) -> (r: Ghost<nat>)
        requires
            old(self).a.wf(),
            old(self).ca == old(self).a.cap(),
            old(self).head <= old(self).a@.len(),
            old(self).a@.len() + s@.len() <= old(self).ca,
        ensures
            final(self).a.wf(),
            final(self).a.cap() == old(self).a.cap(),
            final(self).a@ == old(self).a@ + s@,
            final(self)@ == old(self)@ + s@,
            final(self).ca == old(self).ca,
            final(self).head == old(self).head,
            final(self).mig == old(self).mig,
            final(self).pk@ == vstd::math::max(old(self).pk@ as int, (old(self)@.len() + s@.len()) as int),
            r@ == s@.len(),
    {
        let ghost p = vstd::math::max(self.pk@ as int, (self@.len() + s@.len()) as int) as nat;
        self.pk = Ghost(p);
        let Ghost(w) = self.a.push_slice(s);
        assert(self@ =~= old(self)@ + s@);
        Ghost(w)
    }

    /// Starts a migration from `head` into `CapVec::new(max(MIN_CAP, 3·sz))` (cost 1: the allocation).
    fn mig_start(&mut self, sz: usize) -> (r: Ghost<nat>)
        requires
            old(self).mig is None,
            sz <= MAX_QUEUE,
        ensures
            final(self).a == old(self).a,
            final(self).ca == old(self).ca,
            final(self).head == old(self).head,
            final(self).pk == old(self).pk,
            final(self).mig is Some,
            final(self).mig->0.b.wf(),
            final(self).mig->0.b@ == Seq::<u8>::empty(),
            final(self).mig->0.cb == final(self).mig->0.b.cap(),
            final(self).mig->0.cb == vstd::math::max(MIN_CAP as int, 3 * sz),
            final(self).mig->0.bs == old(self).head,
            final(self).mig->0.c == old(self).head,
            r@ == 1,
    {
        let cb = if 3 * sz < MIN_CAP {
            MIN_CAP
        } else {
            3 * sz
        };
        self.mig = Some(Mig { b: CapVec::new(cb), cb, bs: self.head, c: self.head });
        Ghost(1)
    }

    /// Copies `min(R, k)` bytes of `a[c..]` into `b` (cost: that many).
    fn mig_step(&mut self, k: usize) -> (r: Ghost<nat>)
        requires
            old(self).copy_ok(),
        ensures
            final(self).copy_ok(),
            final(self).a == old(self).a,
            final(self).ca == old(self).ca,
            final(self).head == old(self).head,
            final(self).pk == old(self).pk,
            final(self).mig->0.cb == old(self).mig->0.cb,
            final(self).mig->0.bs == old(self).mig->0.bs,
            final(self).mig->0.c == old(self).mig->0.c + r@,
            r@ == vstd::math::min(old(self).a@.len() - old(self).mig->0.c, k as int),
    {
        let mut m = match self.mig.take() {
            Some(m) => m,
            None => return Ghost(0),
        };
        let rest = self.a.len() - m.c;
        let j = if rest < k {
            rest
        } else {
            k
        };
        let Ghost(w) = m.b.push_slice(vstd::slice::slice_subrange(self.a.as_slice(), m.c, m.c + j));
        m.c = m.c + j;
        assert(m.b@ =~= self.a@.subrange(m.bs as int, m.c as int));
        self.mig = Some(m);
        Ghost(w)
    }

    /// Whether the migration has copied all of `a`.
    fn copied(&self) -> (r: bool)
        ensures
            r == (self.mig is Some && self.mig->0.c == self.a@.len()),
    {
        match &self.mig {
            Some(m) => m.c == self.a.len(),
            None => false,
        }
    }

    /// `a := b` (the old `a` freed), `ca := cb`, `head −= bs`: `b` holds `a[bs..L_a)` (cost 1: the free).
    fn mig_swap(&mut self) -> (r: Ghost<nat>)
        requires
            old(self).wf(),
            old(self).mig is Some,
            old(self).mig->0.c == old(self).a@.len(),
        ensures
            final(self).wf(),
            final(self).mig is None,
            final(self)@ == old(self)@,
            final(self).ca == old(self).mig->0.cb,
            final(self).a@.len() == old(self).a@.len() - old(self).mig->0.bs,
            final(self).pk == old(self).pk,
            r@ == 1,
    {
        let ghost v0 = self@;
        let m = match self.mig.take() {
            Some(m) => m,
            None => return Ghost(0),
        };
        self.a = m.b;
        self.ca = m.cb;
        self.head = self.head - m.bs;
        assert(self@ =~= v0);
        Ghost(1)
    }

    /// D4 case 4: a fresh `CapVec` of `max(MIN_CAP, 3·S)` gets the live bytes, then `s`; the old `a` is freed (cost:
    /// the bytes copied, the allocation and the free).
    fn q_rebuild(&mut self, s: &[u8]) -> (r: Ghost<nat>)
        requires
            old(self).wf(),
            old(self).mig is None,
            0 < s@.len(),
            old(self)@.len() + s@.len() <= MAX_QUEUE,
        ensures
            final(self).wf(),
            final(self).mig is None,
            final(self)@ == old(self)@ + s@,
            final(self).pk@ == vstd::math::max(old(self).pk@ as int, (old(self)@.len() + s@.len()) as int),
            r@ == old(self)@.len() + s@.len() + 2,
    {
        let ghost mut work: nat = 2;
        let sz = self.a.len() - self.head + s.len();
        let c = if 3 * sz < MIN_CAP {
            MIN_CAP
        } else {
            3 * sz
        };
        let mut b = CapVec::new(c);
        let Ghost(w1) = b.push_slice(vstd::slice::slice_subrange(self.a.as_slice(), self.head, self.a.len()));
        proof {
            work = work + w1;
        }
        let Ghost(w2) = b.push_slice(s);
        proof {
            work = work + w2;
        }
        let ghost p = vstd::math::max(self.pk@ as int, sz as int) as nat;
        self.a = b;
        self.ca = c;
        self.head = 0;
        self.pk = Ghost(p);
        assert(self@ =~= old(self)@ + s@);
        Ghost(work)
    }

    /// D4 case 3 (`d <= C/2 < L_a + d`): append, start a migration of the `S` live bytes, copy `3d` of them; swap if
    /// that copied them all (cost at most `4d + 2`).
    fn push_c3(&mut self, s: &[u8]) -> (r: Ghost<nat>)
        requires
            old(self).wf(),
            old(self).mig is None,
            0 < s@.len() <= old(self).ca / 2 < old(self).a@.len() + s@.len(),
            old(self)@.len() + s@.len() <= MAX_QUEUE,
        ensures
            final(self).wf(),
            final(self)@ == old(self)@ + s@,
            final(self).pk@ == vstd::math::max(old(self).pk@ as int, (old(self)@.len() + s@.len()) as int),
            r@ == Self::idle_cost(old(self).a@.len(), old(self)@.len(), old(self).ca as nat, s@.len()),
            r@ <= 4 * s@.len() + 2,
    {
        let d = s.len();
        let Ghost(w1) = self.q_append(s);
        let sz = self.a.len() - self.head;
        let Ghost(w2) = self.mig_start(sz);
        assert(self.mig->0.b@ =~= self.a@.subrange(self.head as int, self.head as int));
        let Ghost(w3) = self.mig_step(3 * d);
        if self.copied() {
            let Ghost(w4) = self.mig_swap();
            return Ghost(w1 + w2 + w3 + w4);
        }
        Ghost(w1 + w2 + w3)
    }

    /// D4 cases 2, 3 and 4 (not migrating; cost at most `4d + 2`).
    fn push_idle(&mut self, s: &[u8]) -> (r: Ghost<nat>)
        requires
            old(self).wf(),
            old(self).mig is None,
            0 < s@.len(),
            old(self)@.len() + s@.len() <= MAX_QUEUE,
        ensures
            final(self).wf(),
            final(self)@ == old(self)@ + s@,
            final(self).pk@ == vstd::math::max(old(self).pk@ as int, (old(self)@.len() + s@.len()) as int),
            r@ == Self::idle_cost(old(self).a@.len(), old(self)@.len(), old(self).ca as nat, s@.len()),
            r@ <= 4 * s@.len() + 2,
    {
        if self.a.len() + s.len() <= self.ca / 2 {
            self.q_append(s)
        } else if s.len() <= self.ca / 2 {
            self.push_c3(s)
        } else {
            self.q_rebuild(s)
        }
    }

    /// D4 case 1 (migrating): copy `3d` more; if that finishes the copy, swap and leave `s` to the caller (cost at
    /// most `3d + 1`), else append `s` to `a` (cost at most `4d`).
    fn push_mig(&mut self, s: &[u8]) -> (r: Ghost<nat>)
        requires
            old(self).wf(),
            old(self).mig is Some,
            0 < s@.len(),
            old(self)@.len() + s@.len() <= MAX_QUEUE,
        ensures
            final(self).wf(),
            final(self).mig is None ==> final(self)@ == old(self)@ && final(self).pk == old(self).pk && r@ <= 3
                * s@.len() + 1,
            final(self).mig is Some ==> final(self)@ == old(self)@ + s@ && final(self).pk@ == vstd::math::max(
                old(self).pk@ as int,
                (old(self)@.len() + s@.len()) as int,
            ) && r@ == 4 * s@.len(),
            final(self).mig is None <==> old(self).a@.len() - old(self).mig->0.c <= 3 * s@.len(),
            final(self).mig is None ==> r@ == old(self).a@.len() - old(self).mig->0.c + 1,
            final(self).mig is None ==> final(self).a@.len() == old(self).a@.len() - old(self).mig->0.bs
                && final(self).ca == old(self).mig->0.cb,
    {
        let Ghost(w1) = self.mig_step(3 * s.len());
        if self.copied() {
            let Ghost(w2) = self.mig_swap();
            return Ghost(w1 + w2);
        }
        let ghost a1 = self.a@;
        let Ghost(w2) = self.q_append(s);
        assert(self.a@.subrange(self.mig->0.bs as int, self.mig->0.c as int) =~= a1.subrange(
            self.mig->0.bs as int,
            self.mig->0.c as int,
        ));
        Ghost(w1 + w2)
    }

    /// Appends `s` (D4): a no-op for empty `s`; else case 1 while migrating, then, if it swapped, cases 2-4 with
    /// `C := cb`. At most `7d + 4` (case 1 then 3); at most two buffers of `max(MIN_CAP, 3·S)` each.
    pub fn push_slice(&mut self, s: &[u8]) -> (r: Ghost<nat>)
        requires
            old(self).wf(),
            old(self)@.len() + s@.len() <= MAX_QUEUE,
        ensures
            final(self).wf(),
            final(self)@ == old(self)@ + s@,
            r@ == old(self).push_cost(s@.len()),
            r@ <= 7 * s@.len() + 4,
            final(self).peak() == vstd::math::max(old(self).peak() as int, (old(self)@.len() + s@.len()) as int),
            final(self).requested() <= 2 * vstd::math::max(MIN_CAP as int, (3 * final(self).peak()) as int),
            s@.len() == 0 ==> *final(self) == *old(self) && r@ == 0,
    {
        if s.len() == 0 {
            assert(self@ + s@ =~= self@);
            return Ghost(0);
        }
        if self.mig.is_some() {
            let Ghost(w1) = self.push_mig(s);
            if self.mig.is_some() {
                proof {
                    self.lemma_wf();
                }
                return Ghost(w1);
            }
            let Ghost(w2) = self.push_idle(s);
            proof {
                self.lemma_wf();
            }
            return Ghost(w1 + w2);
        }
        let Ghost(w) = self.push_idle(s);
        proof {
            self.lemma_wf();
        }
        Ghost(w)
    }

    /// Consumes the first `n` bytes; copies nothing.
    pub fn drop_front(&mut self, n: usize) -> (r: Ghost<nat>)
        requires
            old(self).wf(),
            n <= old(self)@.len(),
        ensures
            final(self).wf(),
            final(self)@ == old(self)@.skip(n as int),
            r@ <= 2,
            final(self)@.len() > 0 ==> final(self).peak() == old(self).peak(),
            n == 0 ==> *final(self) == *old(self),
    {
        if n == 0 {
            assert(self@ =~= self@.skip(0));
            return Ghost(0);
        }
        self.q_advance(n)
    }
}

} // verus!

impl ByteQueue {
    /// Test support: `(ca, cb)`, `cb` 0 when not migrating.
    #[doc(hidden)]
    pub fn caps(&self) -> (usize, usize) {
        (self.ca, self.mig.as_ref().map_or(0, |m| m.cb))
    }

    /// Test support: the address of the newest buffer (`b` while migrating, else `a`), which changes exactly when a
    /// push allocates a buffer (a swap moves `b`, still the newest, into `a`).
    #[doc(hidden)]
    pub fn newest(&self) -> *const u8 {
        self.mig.as_ref().map_or(self.a.as_slice(), |m| m.b.as_slice()).as_ptr()
    }
}
