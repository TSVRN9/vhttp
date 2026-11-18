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

/// `room_spec` of an empty queue: one buffer of `max(MIN_CAP, 3d)` (D4 case 4) fits `b` up to `d = b/3`.
pub open spec fn empty_room(b: nat) -> nat {
    if b >= MIN_CAP {
        b / 3
    } else {
        0
    }
}

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

    /// `max(MIN_CAP, 3·s)`: the capacity D4 allocates for `s` live bytes.
    closed spec fn new_cap(s: nat) -> nat {
        if 3 * s < MIN_CAP {
            MIN_CAP as nat
        } else {
            3 * s
        }
    }

    /// `requested()` after D4 cases 2, 3 and 4 for `d > 0` (`L_a = la`, length `len`, `C = ca`): 2 keeps `ca`; 3 adds
    /// `b` of `new_cap(len + d)` and keeps `a` unless its `3d` copy swaps (`len + d <= 3d`); 4 rebuilds into one.
    closed spec fn idle_req(la: nat, len: nat, ca: nat, d: nat) -> nat {
        if la + d <= ca / 2 {
            ca
        } else if d <= ca / 2 && len + d > 3 * d {
            ca + Self::new_cap(len + d)
        } else {
            Self::new_cap(len + d)
        }
    }

    /// `requested()` after `push_slice` of `d` bytes, exactly (D4's path, as `push_cost`): unchanged for `d == 0` or a
    /// migration step that does not finish the copy; else, after any swap, `idle_req` on the state it leaves.
    pub closed spec fn req_after(&self, d: nat) -> nat {
        let la = self.a@.len();
        let m = self.mig->0;
        if d == 0 {
            self.requested()
        } else if self.mig is None {
            Self::idle_req(la, self@.len(), self.ca as nat, d)
        } else if la - m.c <= 3 * d {
            Self::idle_req((la - m.bs) as nat, self@.len(), m.cb as nat, d)
        } else {
            self.requested()
        }
    }

    /// `idle_req`'s room: the largest `D >= d0 - 1` with `idle_req(la, len, ca, d) <= b` for every `d0 <= d <= D`.
    /// Its pieces, in `d` order, each non-decreasing: `d <= e1` keeps `ca`; `e1 < d <= e2` adds `b` beside `a`
    /// (`ca + new_cap(len + d)`, fits up to `t2`); past `e2` one buffer (`new_cap(len + d)`, fits up to `t3`).
    #[verifier::opaque]
    closed spec fn idle_room(la: int, len: int, ca: int, b: int, d0: int) -> int {
        let e1 = ca / 2 - la;
        let u2 = if len >= 1 {
            if ca / 2 < (len - 1) / 2 {
                ca / 2
            } else {
                (len - 1) / 2
            }
        } else {
            e1
        };
        let e2 = if u2 > e1 {
            u2
        } else {
            e1
        };
        let t2 = if ca + MIN_CAP <= b {
            (b - ca) / 3 - len
        } else {
            -1
        };
        let t3 = if MIN_CAP <= b {
            b / 3 - len
        } else {
            -1
        };
        let s2 = if e1 + 1 > d0 {
            e1 + 1
        } else {
            d0
        };
        let s3 = if e2 + 1 > d0 {
            e2 + 1
        } else {
            d0
        };
        if s2 <= e2 && t2 < e2 {
            if t2 > s2 - 1 {
                t2
            } else {
                s2 - 1
            }
        } else if t3 > s3 - 1 {
            t3
        } else {
            s3 - 1
        }
    }

    /// The first `d` a migration step finishes the copy at (`R = L_a − c <= 3d`), at least 1.
    closed spec fn mig_d0(r: int) -> int {
        if r == 0 {
            1
        } else {
            (r + 2) / 3
        }
    }

    /// The most bytes a push may take with `req_after` at most `b` for it and every shorter push (the pieces of
    /// `req_after` are not monotone together: a step-3 push that swaps can request less than a shorter one that
    /// does not, so the room is the largest prefix of `d`s that fit, never a `d` past one that does not).
    pub closed spec fn room_spec(&self, b: nat) -> nat {
        let la = self.a@.len() as int;
        let m = self.mig->0;
        if self.mig is None {
            Self::idle_room(la, self@.len() as int, self.ca as int, b as int, 1) as nat
        } else {
            Self::idle_room(la - m.bs, self@.len() as int, m.cb as int, b as int, Self::mig_d0(la - m.c)) as nat
        }
    }

    proof fn lemma_idle_room(la: int, len: int, ca: int, b: int, d0: int, d: int)
        requires
            0 <= len <= la,
            0 <= ca <= b,
            1 <= d0,
            d0 <= d,
        ensures
            d <= Self::idle_room(la, len, ca, b, d0) ==> len + d <= Self::idle_req(la as nat, len as nat, ca as nat, d as nat) <= b,
            d == Self::idle_room(la, len, ca, b, d0) + 1 ==> Self::idle_req(la as nat, len as nat, ca as nat, d as nat) > b,
            d0 - 1 <= Self::idle_room(la, len, ca, b, d0) <= b + d0,
            la == 0 && ca == 0 && d0 == 1 ==> Self::idle_room(la, len, ca, b, d0) == empty_room(b as nat),
    {
        reveal(ByteQueue::idle_room);
    }

    /// `req_after` within `b` for every `d` up to `room_spec(b)`, never past it at `room_spec(b) + 1`; the length plus
    /// `d` never exceeds what is requested after the push.
    pub proof fn lemma_room(&self, b: nat, d: nat)
        requires
            self.wf(),
            self.requested() <= b,
        ensures
            d <= self.room_spec(b) ==> self@.len() + d <= self.req_after(d) <= b,
            d == self.room_spec(b) + 1 ==> self.req_after(d) > b,
            self.room_spec(b) <= 2 * b + 1,
            self@.len() == 0 ==> self.room_spec(b) == empty_room(b),
    {
        if self.mig is None {
            self.lemma_room_idle(b, d);
        } else {
            self.lemma_room_mig(b, d);
        }
    }

    proof fn lemma_room_idle(&self, b: nat, d: nat)
        requires
            self.wf(),
            self.mig is None,
            self.requested() <= b,
        ensures
            d <= self.room_spec(b) ==> self@.len() + d <= self.req_after(d) <= b,
            d == self.room_spec(b) + 1 ==> self.req_after(d) > b,
            self.room_spec(b) <= 2 * b + 1,
            self@.len() == 0 ==> self.room_spec(b) == empty_room(b),
    {
        let la = self.a@.len() as int;
        let len = self@.len() as int;
        if d > 0 {
            Self::lemma_idle_room(la, len, self.ca as int, b as int, 1, d as int);
        }
        Self::lemma_idle_room(la, len, self.ca as int, b as int, 1, 1);
    }

    proof fn lemma_room_mig(&self, b: nat, d: nat)
        requires
            self.wf(),
            self.mig is Some,
            self.requested() <= b,
        ensures
            d <= self.room_spec(b) ==> self@.len() + d <= self.req_after(d) <= b,
            d == self.room_spec(b) + 1 ==> self.req_after(d) > b,
            self.room_spec(b) <= 2 * b + 1,
            self@.len() > 0,
    {
        let la = self.a@.len() as int;
        let len = self@.len() as int;
        let m = self.mig->0;
        let r = la - m.c;
        let d0 = Self::mig_d0(r);
        assert(1 <= d0 <= r + 1);
        assert(d >= 1 ==> (d < d0 <==> r > 3 * d));
        assert(r <= 3 * d0);
        if d >= d0 {
            Self::lemma_idle_room(la - m.bs, len, m.cb as int, b as int, d0, d as int);
        }
        Self::lemma_idle_room(la - m.bs, len, m.cb as int, b as int, d0, d0);
    }

    /// The bytes both buffers asked the allocator for (`requested`).
    pub fn held(&self) -> (r: usize)
        requires
            self.wf(),
        ensures
            r == self.requested(),
    {
        proof {
            self.lemma_wf();
        }
        match &self.mig {
            None => self.ca,
            Some(m) => self.ca + m.cb,
        }
    }

    /// `idle_room`, in `i64` (every input at most `2^30`).
    fn idle_room_exec(la: u64, len: u64, ca: u64, b: u64, d0: u64) -> (r: i64)
        requires
            len <= la <= 0x4000_0000,
            ca <= b <= 0x4000_0000,
            1 <= d0 <= 0x4000_0000,
        ensures
            r == Self::idle_room(la as int, len as int, ca as int, b as int, d0 as int),
    {
        proof {
            reveal(ByteQueue::idle_room);
        }
        let ca2 = (ca / 2) as i64;
        let e1 = ca2 - la as i64;
        let u2 = if len >= 1 {
            let l2 = ((len - 1) / 2) as i64;
            if ca2 < l2 {
                ca2
            } else {
                l2
            }
        } else {
            e1
        };
        let e2 = if u2 > e1 {
            u2
        } else {
            e1
        };
        let t2: i64 = if ca + MIN_CAP as u64 <= b {
            ((b - ca) / 3) as i64 - len as i64
        } else {
            -1
        };
        let t3: i64 = if MIN_CAP as u64 <= b {
            (b / 3) as i64 - len as i64
        } else {
            -1
        };
        let s2 = if e1 + 1 > d0 as i64 {
            e1 + 1
        } else {
            d0 as i64
        };
        let s3 = if e2 + 1 > d0 as i64 {
            e2 + 1
        } else {
            d0 as i64
        };
        if s2 <= e2 && t2 < e2 {
            if t2 > s2 - 1 {
                t2
            } else {
                s2 - 1
            }
        } else if t3 > s3 - 1 {
            t3
        } else {
            s3 - 1
        }
    }

    /// `room_spec(b)`: the most bytes a push may take with `requested()` within `b` after it and after every shorter one.
    pub fn room(&self, b: usize) -> (r: usize)
        requires
            self.wf(),
            self.requested() <= b <= MAX_QUEUE,
        ensures
            r == self.room_spec(b as nat),
    {
        proof {
            self.lemma_wf();
        }
        let la = self.a.len();
        let len = la - self.head;
        let r = match &self.mig {
            None => {
                proof {
                    Self::lemma_idle_room(la as int, len as int, self.ca as int, b as int, 1, 1);
                }
                Self::idle_room_exec(la as u64, len as u64, self.ca as u64, b as u64, 1)
            },
            Some(m) => {
                let rr = la - m.c;
                let d0: u64 = if rr == 0 {
                    1
                } else {
                    ((rr + 2) / 3) as u64
                };
                proof {
                    Self::lemma_idle_room((la - m.bs) as int, len as int, m.cb as int, b as int, d0 as int, d0 as int);
                }
                Self::idle_room_exec((la - m.bs) as u64, len as u64, m.cb as u64, b as u64, d0)
            },
        };
        r as usize
    }

    /// No allocation: `CapVec::new(0)`.
    pub fn new() -> (r: ByteQueue)
        ensures
            r.wf(),
            r@ == Seq::<u8>::empty(),
            r.peak() == 0,
            r.requested() == 0,
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
            final(self).requested() <= old(self).requested(),
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
            final(self).requested() <= old(self).requested(),
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
            final(self).requested() == Self::new_cap(old(self)@.len() + s@.len()),
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
            final(self).requested() == Self::idle_req(old(self).a@.len(), old(self)@.len(), old(self).ca as nat, s@.len()),
    {
        let d = s.len();
        let ghost ca0 = self.ca as nat;
        let Ghost(w1) = self.q_append(s);
        let sz = self.a.len() - self.head;
        let Ghost(w2) = self.mig_start(sz);
        let ghost cb = Self::new_cap(sz as nat);
        assert(self.mig->0.cb == cb);
        assert(self.mig->0.b@ =~= self.a@.subrange(self.head as int, self.head as int));
        let Ghost(w3) = self.mig_step(3 * d);
        if self.copied() {
            let Ghost(w4) = self.mig_swap();
            assert(self.requested() == cb);
            return Ghost(w1 + w2 + w3 + w4);
        }
        assert(self.requested() == ca0 + cb);
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
            final(self).requested() == Self::idle_req(old(self).a@.len(), old(self)@.len(), old(self).ca as nat, s@.len()),
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
            final(self).mig is Some ==> final(self).requested() == old(self).requested(),
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
            final(self).requested() == old(self).req_after(s@.len()),
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
            final(self).requested() <= old(self).requested(),
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
