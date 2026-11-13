//! `ByteQueue` (9b2 D4, D5): a byte queue whose readers always see one contiguous region, with a proved worst-case
//! cost per call. Bytes live in an active `CapVec` `a` from `head` on; a migration copies them, a few per push, into a
//! larger `b` (D4's copy rate 3), so no call copies the whole queue. This file is the read side (D5): `len`, `peek`,
//! `as_slice` (free), `drop_front` (at most 2) and `take_front` (at most `n + 3`); `push_slice` (Task 4) is the one
//! writer.
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
        &&& self@.len() == 0 ==> self.ca == 0 && self.mig is None
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
    {
    }

    /// No allocation: `CapVec::new(0)`.
    pub fn new() -> (r: ByteQueue)
        ensures
            r.wf(),
            r@ == Seq::<u8>::empty(),
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

    /// Consumes the first `n` bytes; copies nothing.
    pub fn drop_front(&mut self, n: usize) -> (r: Ghost<nat>)
        requires
            old(self).wf(),
            n <= old(self)@.len(),
        ensures
            final(self).wf(),
            final(self)@ == old(self)@.skip(n as int),
            r@ <= 2,
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
}
