//! A stream's receive buffer (9b2 D11): pages of `PAGE` positions in a ring of `ceil(W/PAGE) + 1` slots under the
//! stream's window `W`. The slot vector is allocated on the stream's first byte, a page on the first byte landing in it,
//! and a page is freed once it holds no byte at or past `base` (the next offset to deliver), so memory follows the bytes
//! held. The first writer of a position wins; delivery hands over the run from `base` in one exact `CapVec`. Every op
//! returns its cost (9b1 D1's ghost convention): `insert` O(d + PAGE), plus the slot vector once; `deliver(max)`
//! O(max + max/PAGE).
use byteq::capvec::CapVec;
use vstd::prelude::*;
// Used only in ghost code, which a plain `cargo build` erases.
#[allow(unused_imports)]
use crate::frags::*;
// Used only in ghost code, which a plain `cargo build` erases.
#[allow(unused_imports)]
use wire::varint::VARINT_MAX;

verus! {

broadcast use vstd::set_lib::range_set_properties;

/// The largest stream receive window our transport parameters may give (D11): `local_tp_ok` bounds
/// `initial_max_stream_data_*` by it, so a ring has at most `NP_MAX` slots.
pub const MAX_RECV_WINDOW: u64 = 0x1_0000;

/// Positions per page.
pub const PAGE: u64 = 256;

/// The most slots a ring holds: `MAX_RECV_WINDOW / PAGE + 2` (`ceil(W/PAGE) + 1` is at most one less).
pub const NP_MAX: usize = 258;

/// A stream receive window a ring holds. Closed, so `Streams::wf` carries it as one opaque fact per window
/// (`lemma_window_ok` opens it where a `RecvStream` is made).
pub closed spec fn window_ok(w: u64) -> bool {
    w <= MAX_RECV_WINDOW
}

pub proof fn lemma_window_ok(w: u64)
    ensures
        window_ok(w) == (w <= MAX_RECV_WINDOW),
{
}

/// `insert_bytes`'s cost constant.
pub open spec fn c_ri() -> nat {
    8
}

/// `deliver`'s cost constant.
pub open spec fn c_rd() -> nat {
    16
}

/// Slots for window `w`: every page a position of `[base, base + w)` can lie in, for any `base`.
pub open spec fn np_of(w: nat) -> nat {
    (w + 255) / 256 + 1
}

/// The slot of relative page `j` (pages past the base page) when the base page sits at slot `first`: one compare and
/// one subtraction, no general modulo.
pub open spec fn sidx(first: nat, np: nat, j: nat) -> nat {
    if first + j >= np {
        (first + j - np) as nat
    } else {
        first + j
    }
}

/// The flags of `s` that are set.
pub open spec fn count(s: Seq<bool>) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        count(s.drop_last()) + if s.last() {
            1nat
        } else {
            0nat
        }
    }
}

/// The `k` bytes of `m` from `b` on.
pub open spec fn run(m: Map<nat, u8>, b: nat, k: nat) -> Seq<u8> {
    Seq::new(k, |i: int| m[(b + i) as nat])
}

/// `m`'s entries at or past `b`.
pub open spec fn from(m: Map<nat, u8>, b: nat) -> Map<nat, u8> {
    m.restrict(m.dom().filter(|p: nat| p >= b))
}

proof fn lemma_dm(p: nat)
    ensures
        p == 256 * (p / 256) + p % 256,
        p % 256 < 256,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(p as int, 256);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(p as int, 256);
}

/// Position `i` of page `q`.
proof fn lemma_page_of(q: nat, i: nat)
    requires
        i < 256,
    ensures
        (256 * q + i) / 256 == q,
        (256 * q + i) % 256 == i,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse((256 * q + i) as int, 256, q as int, i as int);
}

/// The page of every offset in the window is fewer than `np_of(w)` pages past the base page, and so is the page of
/// the window's end.
proof fn lemma_page_span(base: nat, w: nat, off: nat)
    requires
        base <= off <= base + w,
    ensures
        base / 256 <= off / 256,
        off / 256 - base / 256 < np_of(w),
{
    vstd::arithmetic::div_mod::lemma_div_is_ordered(base as int, off as int, 256);
    lemma_dm(base);
    lemma_dm(off);
    lemma_dm(w + 255);
}

proof fn lemma_count_le(s: Seq<bool>)
    ensures
        count(s) <= s.len(),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_count_le(s.drop_last());
    }
}

proof fn lemma_count_false(n: nat)
    ensures
        count(Seq::new(n, |_i: int| false)) == 0,
    decreases n,
{
    if n > 0 {
        assert(Seq::new(n, |_i: int| false).drop_last() =~= Seq::new((n - 1) as nat, |_i: int| false));
        lemma_count_false((n - 1) as nat);
    }
}

/// Setting flag `i` to `v` changes the count by the difference.
proof fn lemma_count_set(s: Seq<bool>, i: int, v: bool)
    requires
        0 <= i < s.len(),
    ensures
        count(s.update(i, v)) + (if s[i] {
            1nat
        } else {
            0nat
        }) == count(s) + (if v {
            1nat
        } else {
            0nat
        }),
    decreases s.len(),
{
    if i == s.len() - 1 {
        assert(s.update(i, v).drop_last() =~= s.drop_last());
    } else {
        assert(s.update(i, v).drop_last() =~= s.drop_last().update(i, v));
        lemma_count_set(s.drop_last(), i, v);
    }
}

/// A set flag counts.
proof fn lemma_count_one(s: Seq<bool>, i: int)
    requires
        0 <= i < s.len(),
        s[i],
    ensures
        count(s) > 0,
{
    lemma_count_set(s, i, false);
}

/// A positive count has a set flag.
proof fn lemma_count_pos(s: Seq<bool>)
    requires
        count(s) > 0,
    ensures
        exists|i: int| 0 <= i < s.len() && s[i],
    decreases s.len(),
{
    if !s.last() {
        lemma_count_pos(s.drop_last());
        let i = choose|i: int| 0 <= i < s.drop_last().len() && s.drop_last()[i];
        assert(s[i]);
    } else {
        assert(s[s.len() - 1]);
    }
}

/// Moving the base page `dl` pages on moves `first` by `dl` slots: relative page `j` of the moved ring is relative
/// page `dl + j` of the old one, wrapped.
proof fn lemma_sidx_shift(f0: nat, np: nat, dl: nat, j: nat)
    requires
        f0 < np,
        dl < np,
        j < np,
    ensures
        sidx(f0, np, dl) < np,
        sidx(sidx(f0, np, dl), np, j) == sidx(
            f0,
            np,
            if dl + j < np {
                dl + j
            } else {
                (dl + j - np) as nat
            },
        ),
{
}

/// The pages `[lo, pos)` meets.
pub open spec fn met(lo: nat, pos: nat) -> nat {
    if pos <= lo {
        0
    } else {
        ((pos - 1) as nat / 256 - lo / 256 + 1) as nat
    }
}

/// One step of a walk over `[lo, end)` page by page: `[pos, nxt)` is the rest of `pos`'s page, cut at `end`. Every step
/// but the first starts on a page boundary, so the walk meets one more page per step, at most `(pos - lo)/PAGE + 2`.
proof fn lemma_walk(lo: nat, pos: nat, end: nat, q: nat, nxt: nat)
    requires
        lo <= pos < end,
        pos > lo ==> pos % 256 == 0,
        q == pos / 256,
        nxt == if 256 * (q + 1) < end {
            256 * (q + 1)
        } else {
            end
        },
    ensures
        pos < nxt <= end,
        pos / 256 == (nxt - 1) as nat / 256,
        nxt < end ==> nxt % 256 == 0,
        met(lo, nxt) == met(lo, pos) + 1,
        met(lo, nxt) * 256 <= nxt - lo + 510,
{
    lemma_dm(pos);
    lemma_dm(lo);
    lemma_page_of(q + 1, 0);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
        (nxt - 1) as int,
        256,
        q as int,
        (nxt - 1 - 256 * q) as int,
    );
    if pos > lo {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
            (pos - 1) as int,
            256,
            (q - 1) as int,
            255,
        );
    }
}

/// `insert_bytes`'s total: the slot vector, then at most `3·d + 521` per page met.
proof fn lemma_insert_cost(work: nat, w0: nat, d: nat, n: nat, m: nat)
    requires
        n <= d,
        m * 256 <= n + 510,
        work <= w0 + 3 * n + 521 * m,
    ensures
        work <= w0 + c_ri() * (d + 2 * (PAGE as nat)),
{
}

/// `deliver`'s total: the scan, the buffer, then at most `3·k + 9` per page met.
proof fn lemma_deliver_cost(work: nat, max: nat, k: nat, c0: nat, m: nat)
    requires
        k <= max,
        c0 <= max + 1,
        m * 256 <= k + 510,
        work <= c0 + 1 + 3 * k + 9 * m,
    ensures
        work <= c_rd() * (max + max / (PAGE as nat) + 2),
{
    lemma_dm(max);
}

/// Writing `d` up to `pos`, then from `pos` up to `nxt`, is writing it up to `nxt`.
proof fn lemma_put_step(m: Map<nat, u8>, base: nat, off: nat, d: Seq<u8>, pos: nat, nxt: nat)
    requires
        off <= pos,
        base <= pos,
        pos <= nxt <= off + d.len(),
    ensures
        put(put(m, base, off, d.subrange(0, pos - off)), pos, off, d.subrange(0, nxt - off)) == put(
            m,
            base,
            off,
            d.subrange(0, nxt - off),
        ),
{
    assert(put(put(m, base, off, d.subrange(0, pos - off)), pos, off, d.subrange(0, nxt - off)) =~= put(
        m,
        base,
        off,
        d.subrange(0, nxt - off),
    ));
}

/// Writing nothing at or past `base` changes nothing.
proof fn lemma_put_none(m: Map<nat, u8>, base: nat, off: nat, d: Seq<u8>)
    requires
        off + d.len() <= base || d.len() == 0,
    ensures
        put(m, base, off, d) == m,
{
    assert(put(m, base, off, d) =~= m);
}

/// After taking up to `pos` of a run held up to `end`: the rest of the run is still held, nothing below `pos` is.
proof fn lemma_from_run(m: Map<nat, u8>, base: nat, pos: nat, end: nat)
    requires
        base <= pos <= end,
        forall|p: nat| base <= p < end ==> m.contains_key(p),
    ensures
        forall|p: nat| pos <= p < end ==> #[trigger] from(m, pos).contains_key(p),
        forall|p: nat| #[trigger] from(m, pos).contains_key(p) ==> p >= pos,
{
}

/// Nothing taken yet.
proof fn lemma_run_empty(m: Map<nat, u8>, b: nat)
    ensures
        run(m, b, 0) == Seq::<u8>::empty(),
{
    assert(run(m, b, 0) =~= Seq::<u8>::empty());
}

/// Taking `[pos, nxt)` after `[base, pos)`, all held, is taking `[base, nxt)`.
proof fn lemma_take_step(m: Map<nat, u8>, base: nat, pos: nat, nxt: nat, o: Seq<u8>)
    requires
        base <= pos <= nxt,
        forall|p: nat| pos <= p < nxt ==> m.contains_key(p),
        o == run(m, base, (pos - base) as nat),
    ensures
        from(from(m, pos), nxt) == from(m, nxt),
        run(from(m, pos), pos, (nxt - pos) as nat).len() == nxt - pos,
        o + run(from(m, pos), pos, (nxt - pos) as nat) == run(m, base, (nxt - base) as nat),
{
    assert(from(from(m, pos), nxt) =~= from(m, nxt));
    assert(o + run(from(m, pos), pos, (nxt - pos) as nat) =~= run(m, base, (nxt - base) as nat));
}

/// `PAGE` positions: `bytes` and their `have` flags; `held` counts the flags set.
pub struct Page {
    bytes: CapVec<u8>,
    have: CapVec<bool>,
    held: u16,
}

impl Page {
    spec fn ok(&self) -> bool {
        &&& self.bytes.wf()
        &&& self.have.wf()
        &&& self.bytes@.len() == 256
        &&& self.have@.len() == 256
        &&& self.bytes.cap() == 256
        &&& self.have.cap() == 256
        &&& self.held as nat == count(self.have@)
    }

    /// Writes `src[j + (i - lo)]` at each `i` of `[lo, hi)` whose flag is clear, and sets the flags.
    fn write_new(&mut self, lo: usize, hi: usize, src: &[u8], j: usize) -> (r: Ghost<nat>)
        requires
            old(self).ok(),
            lo <= hi <= 256,
            j + (hi - lo) <= src.len(),
        ensures
            final(self).ok(),
            final(self).have@ == Seq::new(256, |x: int| old(self).have@[x] || (lo <= x < hi)),
            final(self).bytes@ == Seq::new(
                256,
                |x: int|
                    if old(self).have@[x] || !(lo <= x < hi) {
                        old(self).bytes@[x]
                    } else {
                        src@[j + x - lo]
                    },
            ),
            r@ <= 3 * (hi - lo),
    {
        let ghost mut work: nat = 0;
        let mut i = lo;
        while i < hi
            invariant
                self.ok(),
                lo <= i <= hi <= 256,
                j + (hi - lo) <= src.len(),
                old(self).have@.len() == 256,
                self.have@ == Seq::new(256, |x: int| old(self).have@[x] || (lo <= x < i)),
                self.bytes@ == Seq::new(
                    256,
                    |x: int|
                        if old(self).have@[x] || !(lo <= x < i) {
                            old(self).bytes@[x]
                        } else {
                            src@[j + x - lo]
                        },
                ),
                work <= 3 * (i - lo),
            decreases hi - i,
        {
            if !*self.have.index(i) {
                self.bytes.set(i, src[j + (i - lo)]);
                proof {
                    lemma_count_set(self.have@, i as int, true);
                    lemma_count_le(self.have@.update(i as int, true));
                }
                self.have.set(i, true);
                self.held = self.held + 1;
            }
            proof {
                assert(self.have@ =~= Seq::new(256, |x: int| old(self).have@[x] || (lo <= x < i + 1)));
                assert(self.bytes@ =~= Seq::new(
                    256,
                    |x: int|
                        if old(self).have@[x] || !(lo <= x < i + 1) {
                            old(self).bytes@[x]
                        } else {
                            src@[j + x - lo]
                        },
                ));
            }
            i = i + 1;
            proof {
                work = work + 3;
            }
        }
        Ghost(work)
    }

    /// Appends the bytes of `[lo, hi)`, all held, to `out` and clears their flags.
    fn take_held(&mut self, lo: usize, hi: usize, out: &mut CapVec<u8>) -> (r: Ghost<nat>)
        requires
            old(self).ok(),
            lo <= hi <= 256,
            forall|x: int| lo <= x < hi ==> old(self).have@[x],
            old(out).wf(),
            old(out)@.len() + (hi - lo) <= old(out).cap(),
        ensures
            final(self).ok(),
            final(self).bytes@ == old(self).bytes@,
            final(self).have@ == Seq::new(256, |x: int| old(self).have@[x] && !(lo <= x < hi)),
            final(out).wf(),
            final(out).cap() == old(out).cap(),
            final(out)@ == old(out)@ + old(self).bytes@.subrange(lo as int, hi as int),
            r@ <= 3 * (hi - lo),
    {
        let ghost mut work: nat = 0;
        let mut i = lo;
        while i < hi
            invariant
                self.ok(),
                lo <= i <= hi <= 256,
                forall|x: int| lo <= x < hi ==> old(self).have@[x],
                old(self).have@.len() == 256,
                self.bytes@ == old(self).bytes@,
                self.have@ == Seq::new(256, |x: int| old(self).have@[x] && !(lo <= x < i)),
                out.wf(),
                out.cap() == old(out).cap(),
                old(out)@.len() + (hi - lo) <= old(out).cap(),
                out@ == old(out)@ + old(self).bytes@.subrange(lo as int, i as int),
                work <= 3 * (i - lo),
            decreases hi - i,
        {
            out.push(*self.bytes.index(i));
            proof {
                assert(old(self).bytes@.subrange(lo as int, i + 1) == old(self).bytes@.subrange(
                    lo as int,
                    i as int,
                ).push(old(self).bytes@[i as int]));
                lemma_count_set(self.have@, i as int, false);
            }
            self.have.set(i, false);
            self.held = self.held - 1;
            proof {
                assert(self.have@ =~= Seq::new(256, |x: int| old(self).have@[x] && !(lo <= x < i + 1)));
            }
            i = i + 1;
            proof {
                work = work + 3;
            }
        }
        Ghost(work)
    }
}

/// A page of zeros with no flag set.
fn new_page() -> (r: (Box<Page>, Ghost<nat>))
    ensures
        r.0.ok(),
        r.0.have@ == Seq::new(256, |_x: int| false),
        r.1@ <= 515,
{
    let ghost mut work: nat = 2;
    let mut bytes: CapVec<u8> = CapVec::new(256);
    let mut have: CapVec<bool> = CapVec::new(256);
    let mut i: usize = 0;
    while i < 256
        invariant
            bytes.wf(),
            have.wf(),
            bytes.cap() == 256,
            have.cap() == 256,
            i <= 256,
            bytes@.len() == i,
            have@ == Seq::new(i as nat, |_x: int| false),
            work == 2 + 2 * i,
        decreases 256 - i,
    {
        bytes.push(0);
        have.push(false);
        proof {
            assert(have@ =~= Seq::new((i + 1) as nat, |_x: int| false));
        }
        i = i + 1;
        proof {
            work = work + 2;
        }
    }
    proof {
        lemma_count_false(256);
        work = work + 1;
    }
    (Box::new(Page { bytes, have, held: 0 }), Ghost(work))
}

/// The receive buffer of one stream: positions `[base, base + w)`, page `k` of them in slot `sidx(first, np, k − base
/// page)`.
pub struct Ring {
    base: u64,
    first: usize,
    np: usize,
    w: u64,
    slots: Option<CapVec<Option<Box<Page>>>>,
}

impl Ring {
    /// The next offset to deliver.
    pub closed spec fn base_spec(&self) -> nat {
        self.base as nat
    }

    /// The window: positions `[base, base + window)` may be held.
    pub closed spec fn window(&self) -> nat {
        self.w as nat
    }

    /// No slot vector yet: no byte has landed.
    pub closed spec fn slots_none(&self) -> bool {
        self.slots is None
    }

    spec fn bp(&self) -> nat {
        self.base as nat / 256
    }

    /// Position `p`'s page, relative to the base page.
    spec fn rel(&self, p: nat) -> nat {
        (p / 256 - self.bp()) as nat
    }

    spec fn sl(&self, j: nat) -> nat {
        sidx(self.first as nat, self.np as nat, j)
    }

    /// Relative page `j`, if allocated.
    spec fn pg(&self, j: nat) -> Option<Page> {
        match self.slots {
            Some(v) => if j < self.np && self.sl(j) < v@.len() {
                match v@[self.sl(j) as int] {
                    Some(b) => Some(*b),
                    None => None,
                }
            } else {
                None
            },
            None => None,
        }
    }

    /// Position `i` of relative page `j` is flagged.
    spec fn hj(&self, j: nat, i: nat) -> bool {
        self.pg(j) is Some && self.pg(j).unwrap().have@[i as int]
    }

    /// Position `i` of relative page `j`.
    spec fn pos(&self, j: nat, i: nat) -> nat {
        256 * (self.bp() + j) + i
    }

    spec fn held_at(&self, p: nat) -> bool {
        self.base <= p < self.base + self.w && self.hj(self.rel(p), p % 256)
    }

    /// The held positions at or past `base`, to their bytes.
    pub closed spec fn view(&self) -> Map<nat, u8> {
        Map::new(
            Set::range(self.base as nat, (self.base + self.w) as nat).filter(|p: nat| self.held_at(p)),
            |p: nat| self.pg(self.rel(p)).unwrap().bytes@[(p % 256) as int],
        )
    }

    spec fn inv(&self) -> bool {
        &&& self.w <= MAX_RECV_WINDOW
        &&& self.base <= VARINT_MAX
        &&& self.np as nat == np_of(self.w as nat)
        &&& self.first < self.np
        &&& match self.slots {
            Some(v) => v.wf() && v@.len() == self.np && v.cap() == self.np,
            None => true,
        }
        // A page is allocated only while it holds a flagged position...
        &&& forall|j: nat| #[trigger]
            self.pg(j) is Some ==> self.pg(j).unwrap().ok() && self.pg(j).unwrap().held > 0
        // ...and every flagged position is in the window, so it is held.
        &&& forall|j: nat, i: nat|
            #![trigger self.hj(j, i)]
            self.hj(j, i) && i < 256 ==> self.base <= self.pos(j, i) < self.base + self.w && self.pos(j, i)
                < VARINT_MAX
    }

    spec fn npages(&self, n: nat) -> nat
        decreases n,
    {
        if n == 0 {
            0
        } else {
            self.npages((n - 1) as nat) + if self.pg((n - 1) as nat) is Some {
                1nat
            } else {
                0nat
            }
        }
    }

    /// One more than the last allocated relative page below `n`, or 0.
    spec fn top(&self, n: nat) -> nat
        decreases n,
    {
        if n == 0 {
            0
        } else if self.pg((n - 1) as nat) is Some {
            n
        } else {
            self.top((n - 1) as nat)
        }
    }

    /// Allocated pages.
    pub closed spec fn pages(&self) -> nat {
        self.npages(self.np as nat)
    }

    /// Memory follows the bytes held: `pages() * PAGE <= span + 2 * PAGE`, `span` the end of the held positions less
    /// `base` (some held position reaches that far).
    spec fn mem_ok(&self) -> bool {
        self.pages() == 0 || exists|p: nat|
            self.view().contains_key(p) && self.pages() * 256 <= p + 1 - self.base + 2 * 256
    }

    /// `np == ceil(w/PAGE) + 1 <= NP_MAX`; relative page `j` in slot `sidx(first, np, j)`; a page is allocated iff it
    /// holds a position at or past `base`; `pages() * PAGE <= span + 2 * PAGE`.
    pub closed spec fn wf(&self) -> bool {
        self.inv() && self.mem_ok()
    }

    proof fn lemma_top(&self, n: nat)
        ensures
            self.npages(n) <= self.top(n),
            self.top(n) <= n,
            self.top(n) > 0 ==> self.pg((self.top(n) - 1) as nat) is Some,
        decreases n,
    {
        if n > 0 {
            self.lemma_top((n - 1) as nat);
        }
    }

    /// A flagged position is held.
    proof fn lemma_in_view(&self, j: nat, i: nat)
        requires
            self.inv(),
            self.hj(j, i),
            i < 256,
        ensures
            self.view().contains_key(self.pos(j, i)),
            self.rel(self.pos(j, i)) == j,
            self.pos(j, i) % 256 == i,
            self.view()[self.pos(j, i)] == self.pg(j).unwrap().bytes@[i as int],
    {
        lemma_page_of(self.bp() + j, i);
    }

    /// Position `p` of relative page `j`: held iff in the window and flagged, with its page's byte.
    proof fn lemma_at(&self, p: nat, j: nat)
        requires
            p / 256 == self.bp() + j,
        ensures
            self.view().contains_key(p) == (self.base <= p < self.base + self.w && self.hj(j, p % 256)),
            self.view().contains_key(p) ==> self.view()[p] == self.pg(j).unwrap().bytes@[(p % 256) as int],
    {
    }

    proof fn lemma_inv_facts(&self)
        requires
            self.inv(),
        ensures
            self.base <= VARINT_MAX,
            self.w <= MAX_RECV_WINDOW,
    {
    }

    /// The page `take_page` takes `[a, b)` from: allocated, those positions flagged, their bytes the run's.
    proof fn lemma_take_src(&self, a: nat, b: nat)
        requires
            self.inv(),
            self.base <= a < b <= self.base + self.w,
            a / 256 == (b - 1) as nat / 256,
            forall|p: nat| a <= p < b ==> self.view().contains_key(p),
        ensures
            self.rel(a) < self.np,
            self.bp() + self.rel(a) == a / 256,
            self.pg(self.rel(a)) is Some,
            a % 256 < b - 256 * (a / 256) <= 256,
            forall|x: int|
                a % 256 <= x < b - 256 * (a / 256) ==> #[trigger] self.pg(self.rel(a)).unwrap().have@[x],
            run(self.view(), a, (b - a) as nat) == self.pg(self.rel(a)).unwrap().bytes@.subrange(
                (a % 256) as int,
                b - 256 * (a / 256),
            ),
    {
        let q = a / 256;
        let lo = a % 256;
        let g0 = self.pg(self.rel(a)).unwrap();
        assert(self.view().contains_key(a));
        self.lemma_of_view(a);
        lemma_dm(a);
        lemma_dm((b - 1) as nat);
        assert forall|x: int| lo <= x < b - 256 * q implies #[trigger] g0.have@[x] by {
            let p = (256 * q + x) as nat;
            assert(self.view().contains_key(p));
            self.lemma_of_view(p);
            lemma_page_of(q, x as nat);
        }
        assert forall|i: int| 0 <= i < b - a implies #[trigger] run(self.view(), a, (b - a) as nat)[i] == g0.bytes@[lo
            + i] by {
            let p = (a + i) as nat;
            lemma_page_of(q, (lo + i) as nat);
            assert(self.view().contains_key(p));
        }
        assert(run(self.view(), a, (b - a) as nat) =~= g0.bytes@.subrange(lo as int, b - 256 * q));
    }

    /// Every held position is at or past `base`.
    proof fn lemma_from_base(&self)
        ensures
            from(self.view(), self.base as nat) == self.view(),
    {
        assert(from(self.view(), self.base as nat) =~= self.view());
    }

    /// A held position is flagged in its page, fewer than `np` pages past the base page.
    proof fn lemma_of_view(&self, p: nat)
        requires
            self.inv(),
            self.view().contains_key(p),
        ensures
            self.rel(p) < self.np,
            p % 256 < 256,
            p == self.pos(self.rel(p), p % 256),
            self.hj(self.rel(p), p % 256),
            p < VARINT_MAX,
    {
        lemma_dm(p);
        lemma_page_span(self.base as nat, self.w as nat, p);
    }

    proof fn lemma_mem(&self)
        requires
            self.inv(),
        ensures
            self.mem_ok(),
    {
        self.lemma_top(self.np as nat);
        let h = self.top(self.np as nat);
        if h > 0 {
            let j = (h - 1) as nat;
            let g = self.pg(j).unwrap();
            lemma_count_pos(g.have@);
            let i = choose|i: int| 0 <= i < g.have@.len() && g.have@[i];
            assert(self.hj(j, i as nat));
            self.lemma_in_view(j, i as nat);
            lemma_dm(self.base as nat);
            assert(self.pages() * 256 <= self.pos(j, i as nat) + 1 - self.base + 2 * 256);
        }
    }

    /// No slot vector: nothing held, no page.
    proof fn lemma_none(&self)
        requires
            self.slots is None,
        ensures
            self.view() =~= Map::<nat, u8>::empty(),
            self.pages() == 0,
    {
        self.lemma_top(self.np as nat);
    }

    /// Slot `sl(j0)` replaced by `x`: page `j0` is `x`, the others unchanged.
    proof fn lemma_put(r0: Ring, r1: Ring, j0: nat, x: Option<Box<Page>>)
        requires
            r0.inv(),
            j0 < r0.np,
            r1.base == r0.base,
            r1.first == r0.first,
            r1.np == r0.np,
            r1.w == r0.w,
            r0.slots is Some,
            r1.slots is Some,
            r1.slots.unwrap()@ == r0.slots.unwrap()@.update(r0.sl(j0) as int, x),
        ensures
            forall|j: nat| j != j0 ==> #[trigger] r1.pg(j) == r0.pg(j),
            r1.pg(j0) == match x {
                Some(b) => Some(*b),
                None => None::<Page>,
            },
    {
        assert forall|j: nat| j != j0 implies #[trigger] r1.pg(j) == r0.pg(j) by {
            if j < r0.np {
                lemma_sidx_shift(r0.first as nat, r0.np as nat, 0, j);
                lemma_sidx_shift(r0.first as nat, r0.np as nat, 0, j0);
            }
        }
        lemma_sidx_shift(r0.first as nat, r0.np as nat, 0, j0);
    }

    /// `r1` is `r0` with slot `sl(j0)` changed, every other page unchanged.
    spec fn one_page(r0: Ring, r1: Ring, j0: nat) -> bool {
        &&& r0.inv()
        &&& j0 < r0.np
        &&& r1.base == r0.base
        &&& r1.first == r0.first
        &&& r1.np == r0.np
        &&& r1.w == r0.w
        &&& r1.slots is Some
        &&& r1.slots.unwrap().wf()
        &&& r1.slots.unwrap()@.len() == r1.np
        &&& r1.slots.unwrap().cap() == r1.np
        &&& forall|j: nat| j != j0 ==> #[trigger] r1.pg(j) == r0.pg(j)
    }

    /// `fill_page`'s step: page `j0` gains the flags of `[a, b)` with `data`'s bytes (`g0` the page
    /// before, a fresh one if there was none; `g1` after).
    spec fn filled(r0: Ring, r1: Ring, j0: nat, g0: Page, g1: Page, a: nat, b: nat, off: nat, data: Seq<u8>) -> bool {
        &&& Ring::one_page(r0, r1, j0)
        &&& r0.base <= a < b <= r0.base + r0.w
        &&& a / 256 == r0.bp() + j0
        &&& a % 256 < b - 256 * (r0.bp() + j0) <= 256
        &&& off <= a
        &&& b <= off + data.len() <= VARINT_MAX
        &&& r1.pg(j0) == Some(g1)
        &&& g0.have@.len() == 256
        &&& r0.pg(j0) is Some ==> r0.pg(j0) == Some(g0)
        &&& r0.pg(j0) is None ==> g0.have@ == Seq::new(256, |_x: int| false)
        &&& g1.ok()
        &&& g1.have@ == Seq::new(256, |x: int| g0.have@[x] || (a % 256 <= x < b - 256 * (r0.bp() + j0)))
        &&& g1.bytes@ == Seq::new(
            256,
            |x: int|
                if g0.have@[x] || !(a % 256 <= x < b - 256 * (r0.bp() + j0)) {
                    g0.bytes@[x]
                } else {
                    data[a - off + x - a % 256]
                },
        )
    }

    proof fn lemma_fill_inv(r0: Ring, r1: Ring, j0: nat, g0: Page, g1: Page, a: nat, b: nat, off: nat, data: Seq<u8>)
        requires
            Ring::filled(r0, r1, j0, g0, g1, a, b, off, data),
        ensures
            r1.inv(),
    {
        lemma_dm(a);
        lemma_count_one(g1.have@, (a % 256) as int);
        assert forall|j: nat, i: nat| #![trigger r1.hj(j, i)] r1.hj(j, i) && i < 256 implies r1.base <= r1.pos(j, i)
            < r1.base + r1.w && r1.pos(j, i) < VARINT_MAX by {
            if j != j0 {
                assert(r0.hj(j, i));
            } else if g0.have@[i as int] {
                assert(r0.hj(j, i));
            }
        }
        assert forall|j: nat| #[trigger] r1.pg(j) is Some implies r1.pg(j).unwrap().ok() && r1.pg(j).unwrap().held
            > 0 by {
            if j != j0 {
                assert(r0.pg(j) is Some);
            }
        }
    }

    proof fn lemma_fill_point(
        r0: Ring,
        r1: Ring,
        j0: nat,
        g0: Page,
        g1: Page,
        a: nat,
        b: nat,
        off: nat,
        data: Seq<u8>,
        p: nat,
    )
        requires
            Ring::filled(r0, r1, j0, g0, g1, a, b, off, data),
        ensures
            r1.view().contains_key(p) == put(r0.view(), a, off, data.subrange(0, b - off)).contains_key(p),
            r1.view().contains_key(p) ==> r1.view()[p] == put(r0.view(), a, off, data.subrange(0, b - off))[p],
    {
        lemma_dm(a);
        lemma_dm(p);
        if r0.base <= p < r0.base + r0.w {
            lemma_page_span(r0.base as nat, r0.w as nat, p);
            let j = (p / 256 - r0.bp()) as nat;
            r0.lemma_at(p, j);
            r1.lemma_at(p, j);
            if j != j0 {
                assert(!(a <= p < b));
            }
        } else {
            assert(!r0.view().contains_key(p));
            assert(!r1.view().contains_key(p));
        }
    }

    proof fn lemma_fill_page(r0: Ring, r1: Ring, j0: nat, g0: Page, g1: Page, a: nat, b: nat, off: nat, data: Seq<u8>)
        requires
            Ring::filled(r0, r1, j0, g0, g1, a, b, off, data),
        ensures
            r1.inv(),
            r1.view() == put(r0.view(), a, off, data.subrange(0, b - off)),
    {
        Ring::lemma_fill_inv(r0, r1, j0, g0, g1, a, b, off, data);
        let m = put(r0.view(), a, off, data.subrange(0, b - off));
        assert forall|p: nat|
            #![trigger r1.view().contains_key(p)]
            #![trigger m.contains_key(p)]
            r1.view().contains_key(p) == m.contains_key(p) && (m.contains_key(p) ==> r1.view()[p] == m[p]) by {
            Ring::lemma_fill_point(r0, r1, j0, g0, g1, a, b, off, data, p);
        }
        assert(r1.view() =~= m);
    }

    /// `take_page`'s step: page `j0` loses the flags of `[a, b)`, and is freed if none is left.
    spec fn taken(r0: Ring, r1: Ring, j0: nat, g0: Page, g1: Page, a: nat, b: nat) -> bool {
        &&& Ring::one_page(r0, r1, j0)
        &&& r0.base <= a < b <= r0.base + r0.w
        &&& a / 256 == r0.bp() + j0
        &&& a % 256 < b - 256 * (r0.bp() + j0) <= 256
        &&& forall|p: nat| r0.view().contains_key(p) ==> p >= a
        &&& r0.pg(j0) == Some(g0)
        &&& g1.ok()
        &&& g1.bytes@ == g0.bytes@
        &&& g1.have@ == Seq::new(256, |x: int| g0.have@[x] && !(a % 256 <= x < b - 256 * (r0.bp() + j0)))
        &&& g1.held > 0 ==> r1.pg(j0) == Some(g1)
        &&& g1.held == 0 ==> r1.pg(j0) is None
    }

    proof fn lemma_take_inv(r0: Ring, r1: Ring, j0: nat, g0: Page, g1: Page, a: nat, b: nat)
        requires
            Ring::taken(r0, r1, j0, g0, g1, a, b),
        ensures
            r1.inv(),
    {
        assert forall|j: nat, i: nat| #![trigger r1.hj(j, i)] r1.hj(j, i) && i < 256 implies r1.base <= r1.pos(j, i)
            < r1.base + r1.w && r1.pos(j, i) < VARINT_MAX by {
            assert(r0.hj(j, i));
        }
        assert forall|j: nat| #[trigger] r1.pg(j) is Some implies r1.pg(j).unwrap().ok() && r1.pg(j).unwrap().held
            > 0 by {
            if j != j0 {
                assert(r0.pg(j) is Some);
            }
        }
    }

    proof fn lemma_take_point(r0: Ring, r1: Ring, j0: nat, g0: Page, g1: Page, a: nat, b: nat, p: nat)
        requires
            Ring::taken(r0, r1, j0, g0, g1, a, b),
        ensures
            r1.view().contains_key(p) == from(r0.view(), b).contains_key(p),
            r1.view().contains_key(p) ==> r1.view()[p] == from(r0.view(), b)[p],
    {
        lemma_dm(a);
        lemma_dm(p);
        if r0.base <= p < r0.base + r0.w {
            lemma_page_span(r0.base as nat, r0.w as nat, p);
            let j = (p / 256 - r0.bp()) as nat;
            r0.lemma_at(p, j);
            r1.lemma_at(p, j);
            if j == j0 {
                if g1.held == 0 && g1.have@[(p % 256) as int] {
                    lemma_count_one(g1.have@, (p % 256) as int);
                }
            } else if r0.view().contains_key(p) {
                assert(p >= b);
            }
        } else {
            assert(!r0.view().contains_key(p));
            assert(!r1.view().contains_key(p));
        }
    }

    proof fn lemma_take_page(r0: Ring, r1: Ring, j0: nat, g0: Page, g1: Page, a: nat, b: nat)
        requires
            Ring::taken(r0, r1, j0, g0, g1, a, b),
        ensures
            r1.inv(),
            r1.view() == from(r0.view(), b),
    {
        Ring::lemma_take_inv(r0, r1, j0, g0, g1, a, b);
        let m = from(r0.view(), b);
        assert forall|p: nat|
            #![trigger r1.view().contains_key(p)]
            #![trigger m.contains_key(p)]
            r1.view().contains_key(p) == m.contains_key(p) && (m.contains_key(p) ==> r1.view()[p] == m[p]) by {
            Ring::lemma_take_point(r0, r1, j0, g0, g1, a, b, p);
        }
        assert(r1.view() =~= m);
    }

    /// Relative page `j` of a ring whose base moved `dl` pages on (`first` moved with it) is relative page `dl + j` of
    /// the old one, or, past the old ring's last page, empty: the slot held a page below the new base, which holds
    /// nothing.
    proof fn lemma_rebase_pg(r0: Ring, r1: Ring, j: nat)
        requires
            r0.inv(),
            r1.w == r0.w,
            r1.np == r0.np,
            r1.slots == r0.slots,
            r0.base <= r1.base <= r0.base + r0.w,
            r1.first as nat == sidx(r0.first as nat, r0.np as nat, (r1.bp() - r0.bp()) as nat),
            forall|p: nat| r0.view().contains_key(p) ==> p >= r1.base,
            j < r0.np,
        ensures
            r0.bp() <= r1.bp(),
            r1.bp() - r0.bp() < r0.np,
            r1.pg(j) == if r1.bp() - r0.bp() + j < r0.np {
                r0.pg((r1.bp() - r0.bp() + j) as nat)
            } else {
                None::<Page>
            },
    {
        lemma_page_span(r0.base as nat, r0.w as nat, r1.base as nat);
        let dl = (r1.bp() - r0.bp()) as nat;
        lemma_sidx_shift(r0.first as nat, r0.np as nat, dl, j);
        if dl + j >= r0.np {
            let jj = (dl + j - r0.np) as nat;
            if r0.pg(jj) is Some {
                let g = r0.pg(jj).unwrap();
                lemma_count_pos(g.have@);
                let i = choose|i: int| 0 <= i < g.have@.len() && g.have@[i];
                assert(r0.hj(jj, i as nat));
                r0.lemma_in_view(jj, i as nat);
                lemma_dm(r1.base as nat);
                assert(false);
            }
        } else {
            lemma_sidx_shift(r0.first as nat, r0.np as nat, 0, dl + j);
        }
    }

    /// `r1` is `r0` with `base` moved past positions none of which is held, `first` moved with it.
    spec fn rebased(r0: Ring, r1: Ring) -> bool {
        &&& r0.inv()
        &&& r1.w == r0.w
        &&& r1.np == r0.np
        &&& r1.slots == r0.slots
        &&& r0.base <= r1.base <= r0.base + r0.w
        &&& r1.base <= VARINT_MAX
        &&& r1.first as nat == sidx(r0.first as nat, r0.np as nat, (r1.bp() - r0.bp()) as nat)
        &&& forall|p: nat| r0.view().contains_key(p) ==> p >= r1.base
    }

    /// Moving `base` past positions none of which is held keeps `inv`.
    proof fn lemma_rebase_inv(r0: Ring, r1: Ring)
        requires
            Ring::rebased(r0, r1),
        ensures
            r1.inv(),
    {
        lemma_page_span(r0.base as nat, r0.w as nat, r1.base as nat);
        let dl = (r1.bp() - r0.bp()) as nat;
        lemma_sidx_shift(r0.first as nat, r0.np as nat, dl, 0);
        assert forall|j: nat| #[trigger] r1.pg(j) is Some implies r1.pg(j).unwrap().ok() && r1.pg(j).unwrap().held
            > 0 by {
            if j < r0.np {
                Ring::lemma_rebase_pg(r0, r1, j);
                assert(r0.pg(dl + j) is Some);
            }
        }
        assert forall|j: nat, i: nat| #![trigger r1.hj(j, i)] r1.hj(j, i) && i < 256 implies r1.base <= r1.pos(j, i)
            < r1.base + r1.w && r1.pos(j, i) < VARINT_MAX by {
            Ring::lemma_rebase_pg(r0, r1, j);
            assert(r0.hj(dl + j, i));
            assert(r0.pos(dl + j, i) == r1.pos(j, i));
            r0.lemma_in_view(dl + j, i);
        }
    }

    /// A position the moved ring holds, the old one holds, with the same byte.
    proof fn lemma_rebase_fwd(r0: Ring, r1: Ring, p: nat)
        requires
            Ring::rebased(r0, r1),
            r1.inv(),
            r1.view().contains_key(p),
        ensures
            r0.view().contains_key(p),
            r1.view()[p] == r0.view()[p],
    {
        lemma_page_span(r0.base as nat, r0.w as nat, r1.base as nat);
        let dl = (r1.bp() - r0.bp()) as nat;
        r1.lemma_of_view(p);
        Ring::lemma_rebase_pg(r0, r1, r1.rel(p));
        assert(r0.hj(dl + r1.rel(p), p % 256));
        r0.lemma_in_view(dl + r1.rel(p), p % 256);
    }

    /// A position the old ring holds, the moved one holds.
    proof fn lemma_rebase_back(r0: Ring, r1: Ring, p: nat)
        requires
            Ring::rebased(r0, r1),
            r0.view().contains_key(p),
        ensures
            r1.view().contains_key(p),
    {
        lemma_page_span(r0.base as nat, r0.w as nat, r1.base as nat);
        let dl = (r1.bp() - r0.bp()) as nat;
        r0.lemma_of_view(p);
        lemma_page_span(r1.base as nat, r1.w as nat, p);
        Ring::lemma_rebase_pg(r0, r1, (r0.rel(p) - dl) as nat);
    }

    /// Moving `base` past positions none of which is held keeps the view.
    proof fn lemma_rebase(r0: Ring, r1: Ring)
        requires
            Ring::rebased(r0, r1),
        ensures
            r1.inv(),
            r1.view() == r0.view(),
    {
        Ring::lemma_rebase_inv(r0, r1);
        assert forall|p: nat|
            #![trigger r1.view().contains_key(p)]
            #![trigger r0.view().contains_key(p)]
            r1.view().contains_key(p) == r0.view().contains_key(p) && (r0.view().contains_key(p) ==> r1.view()[p]
                == r0.view()[p]) by {
            if r1.view().contains_key(p) {
                Ring::lemma_rebase_fwd(r0, r1, p);
            }
            if r0.view().contains_key(p) {
                Ring::lemma_rebase_back(r0, r1, p);
            }
        }
        assert(r1.view() =~= r0.view());
    }

    /// What `wf` gives callers: `base` and the window in range, every held position in the window and below
    /// `VARINT_MAX`, and memory following the bytes held (`pages() * PAGE <= span + 2 * PAGE`).
    pub proof fn lemma_wf(&self)
        requires
            self.wf(),
        ensures
            self.base_spec() <= VARINT_MAX,
            self.window() <= MAX_RECV_WINDOW,
            forall|p: nat| #[trigger]
                self.view().contains_key(p) ==> self.base_spec() <= p < self.base_spec() + self.window() && p
                    < VARINT_MAX,
            self.pages() == 0 || exists|p: nat|
                self.view().contains_key(p) && self.pages() * PAGE <= p + 1 - self.base_spec() + 2 * PAGE,
    {
        assert forall|p: nat| #[trigger] self.view().contains_key(p) implies self.base_spec() <= p < self.base_spec()
            + self.window() && p < VARINT_MAX by {
            self.lemma_of_view(p);
        }
    }

    /// An empty ring for window `w`: no slot vector yet.
    pub fn new(w: u64) -> (r: Ring)
        requires
            w <= MAX_RECV_WINDOW,
        ensures
            r.wf(),
            r.view() == Map::<nat, u8>::empty(),
            r.base_spec() == 0,
            r.window() == w,
            r.pages() == 0,
            r.slots_none(),
    {
        let r = Ring { base: 0, first: 0, np: ((w + (PAGE - 1)) / PAGE) as usize + 1, w, slots: None };
        proof {
            vstd::arithmetic::div_mod::lemma_div_is_ordered((w + 255) as int, (MAX_RECV_WINDOW + 255) as int, 256);
            r.lemma_none();
        }
        r
    }

    /// The slot of position `p`'s page.
    fn slot(&self, p: u64) -> (s: usize)
        requires
            self.inv(),
            self.base <= p < self.base + self.w,
        ensures
            s < self.np,
            s as nat == self.sl(self.rel(p as nat)),
            self.rel(p as nat) < self.np,
            self.bp() + self.rel(p as nat) == p as nat / 256,
    {
        proof {
            lemma_page_span(self.base as nat, self.w as nat, p as nat);
        }
        let i = (p / PAGE - self.base / PAGE) as usize;
        let s = self.first + i;
        if s >= self.np {
            s - self.np
        } else {
            s
        }
    }

    /// Position `p` is held.
    fn has(&self, p: u64) -> (r: bool)
        requires
            self.inv(),
            self.base <= p < self.base + self.w,
        ensures
            r == self.view().contains_key(p as nat),
    {
        match &self.slots {
            None => false,
            Some(v) => {
                let s = self.slot(p);
                match v.index(s) {
                    Some(g) => {
                        proof {
                            lemma_dm(p as nat);
                            assert(self.pg(self.rel(p as nat)) is Some);
                        }
                        *g.have.index((p % PAGE) as usize)
                    },
                    None => false,
                }
            },
        }
    }

    /// The byte at `base` is held: `deliver` would hand over at least one. O(1).
    pub fn ready(&self) -> (r: bool)
        requires
            self.wf(),
        ensures
            r == self.view().contains_key(self.base_spec()),
    {
        if self.w == 0 {
            false
        } else {
            self.has(self.base)
        }
    }

    /// The slot vector, all `None`: `np + 1` units, once per stream.
    fn alloc_slots(&mut self) -> (r: Ghost<nat>)
        requires
            old(self).inv(),
            old(self).slots is None,
        ensures
            final(self).inv(),
            final(self).slots is Some,
            final(self).base == old(self).base,
            final(self).w == old(self).w,
            final(self).view() == old(self).view(),
            r@ <= NP_MAX,
    {
        let ghost mut work: nat = 1;
        let np = self.np;
        proof {
            vstd::arithmetic::div_mod::lemma_div_is_ordered(
                (self.w + 255) as int,
                (MAX_RECV_WINDOW + 255) as int,
                256,
            );
            self.lemma_none();
        }
        let mut v: CapVec<Option<Box<Page>>> = CapVec::new(np);
        let mut i: usize = 0;
        while i < np
            invariant
                v.wf(),
                v.cap() == np,
                i <= np <= 257,
                v@.len() == i,
                forall|k: int| 0 <= k < i ==> v@[k] is None,
                work == 1 + i,
            decreases np - i,
        {
            v.push(None);
            i = i + 1;
            proof {
                work = work + 1;
            }
        }
        self.slots = Some(v);
        proof {
            assert forall|j: nat| #[trigger] self.pg(j) is None by {}
            assert(self.view() =~= Map::<nat, u8>::empty());
        }
        Ghost(work)
    }

    /// Writes the not-yet-held positions of `[a, b)`, all in one page, from `data` (at `off`).
    fn fill_page(&mut self, a: u64, b: u64, off: u64, data: &[u8]) -> (r: Ghost<nat>)
        requires
            old(self).inv(),
            old(self).slots is Some,
            old(self).base <= a < b <= old(self).base + old(self).w,
            a / 256 == (b - 1) as nat / 256,
            off <= a,
            b <= off + data@.len() <= VARINT_MAX,
        ensures
            final(self).inv(),
            final(self).slots is Some,
            final(self).base == old(self).base,
            final(self).w == old(self).w,
            final(self).first == old(self).first,
            final(self).np == old(self).np,
            final(self).view() == put(old(self).view(), a as nat, off as nat, data@.subrange(0, b - off)),
            r@ <= 3 * (b - a) + 520,
    {
        let ghost mut work: nat = 0;
        let s = self.slot(a);
        let q = a / PAGE;
        let ghost j0 = self.rel(a as nat);
        proof {
            lemma_dm(a as nat);
            lemma_dm((b - 1) as nat);
        }
        let lo = (a - q * PAGE) as usize;
        let hi = (b - q * PAGE) as usize;
        let mut v = self.slots.take().unwrap();
        let mut cur: Option<Box<Page>> = None;
        v.set_and_swap(s, &mut cur);
        let mut g = match cur {
            Some(g) => {
                proof {
                    assert(old(self).pg(j0) is Some);
                }
                g
            },
            None => {
                let (g, Ghost(c1)) = new_page();
                proof {
                    work = work + c1;
                }
                g
            },
        };
        let ghost g0 = *g;
        let Ghost(c2) = g.write_new(lo, hi, data, (a - off) as usize);
        proof {
            work = work + c2 + 2;
        }
        let mut back = Some(g);
        let ghost x = back;
        v.set_and_swap(s, &mut back);
        self.slots = Some(v);
        proof {
            assert(self.slots.unwrap()@ =~= old(self).slots.unwrap()@.update(s as int, x));
            Ring::lemma_put(*old(self), *self, j0, x);
            Ring::lemma_fill_page(
                *old(self),
                *self,
                j0,
                g0,
                *x.unwrap(),
                a as nat,
                b as nat,
                off as nat,
                data@,
            );
        }
        Ghost(work)
    }

    /// Writes `data` at `off`: the positions at or past `base` not yet held take its bytes (the first writer wins).
    /// Costs `O(d + PAGE)`, plus the slot vector on the first byte.
    pub fn insert_bytes(&mut self, off: u64, data: &[u8]) -> (r: Ghost<nat>)
        requires
            old(self).wf(),
            off + data@.len() <= old(self).base_spec() + old(self).window(),
            off + data@.len() <= VARINT_MAX,
        ensures
            final(self).wf(),
            final(self).base_spec() == old(self).base_spec(),
            final(self).window() == old(self).window(),
            final(self).view() == put(old(self).view(), old(self).base_spec(), off as nat, data@),
            r@ <= c_ri() * (data@.len() + 2 * PAGE) + (if old(self).slots_none() {
                NP_MAX as nat
            } else {
                0
            }),
    {
        hide(Ring::inv);
        hide(Ring::view);
        hide(Ring::mem_ok);
        hide(put);
        let ghost mut work: nat = 0;
        let end = off + data.len() as u64;
        let lo = if off < self.base {
            self.base
        } else {
            off
        };
        if lo >= end {
            proof {
                lemma_put_none(old(self).view(), old(self).base as nat, off as nat, data@);
            }
            return Ghost(work);
        }
        if self.slots.is_none() {
            let Ghost(c) = self.alloc_slots();
            proof {
                work = work + c;
            }
        }
        let ghost w0 = work;
        let mut pos = lo;
        proof {
            lemma_put_none(old(self).view(), old(self).base as nat, off as nat, data@.subrange(0, lo - off));
        }
        while pos < end
            invariant
                self.inv(),
                self.slots is Some,
                self.base == old(self).base,
                self.w == old(self).w,
                lo == if off < old(self).base {
                    old(self).base
                } else {
                    off
                },
                lo <= pos <= end,
                end == off + data@.len(),
                end <= self.base + self.w,
                end <= VARINT_MAX,
                self.view() == put(old(self).view(), old(self).base as nat, off as nat, data@.subrange(0, pos - off)),
                pos > lo && pos < end ==> pos as nat % 256 == 0,
                met(lo as nat, pos as nat) * 256 <= pos - lo + 510,
                work <= w0 + 3 * (pos - lo) + 521 * met(lo as nat, pos as nat),
                w0 <= if old(self).slots_none() {
                    NP_MAX as nat
                } else {
                    0
                },
            decreases end - pos,
        {
            let q = pos / PAGE;
            proof {
                lemma_dm(pos as nat);
            }
            let nb = (q + 1) * PAGE;
            let nxt = if nb < end {
                nb
            } else {
                end
            };
            proof {
                lemma_walk(lo as nat, pos as nat, end as nat, q as nat, nxt as nat);
            }
            let Ghost(c) = self.fill_page(pos, nxt, off, data);
            proof {
                work = work + c + 1;
                lemma_put_step(old(self).view(), old(self).base as nat, off as nat, data@, pos as nat, nxt as nat);
            }
            pos = nxt;
        }
        proof {
            assert(data@.subrange(0, end - off) =~= data@);
            lemma_insert_cost(work, w0, data@.len(), (end - lo) as nat, met(lo as nat, end as nat));
            self.lemma_mem();
        }
        Ghost(work)
    }

    /// Takes the positions of `[a, b)`, all held and in one page, none held below `a`, into `out`; frees the page if
    /// it holds nothing more.
    fn take_page(&mut self, a: u64, b: u64, out: &mut CapVec<u8>) -> (r: Ghost<nat>)
        requires
            old(self).inv(),
            old(self).base <= a < b <= old(self).base + old(self).w,
            a / 256 == (b - 1) as nat / 256,
            forall|p: nat| a <= p < b ==> old(self).view().contains_key(p),
            forall|p: nat| old(self).view().contains_key(p) ==> p >= a,
            old(out).wf(),
            old(out)@.len() + (b - a) <= old(out).cap(),
        ensures
            final(self).inv(),
            final(self).base == old(self).base,
            final(self).w == old(self).w,
            final(self).first == old(self).first,
            final(self).np == old(self).np,
            final(self).slots is Some,
            final(self).view() == from(old(self).view(), b as nat),
            final(out).wf(),
            final(out).cap() == old(out).cap(),
            final(out)@ == old(out)@ + run(old(self).view(), a as nat, (b - a) as nat),
            r@ <= 3 * (b - a) + 8,
    {
        hide(Ring::view);
        hide(from);
        hide(run);
        let ghost mut work: nat = 0;
        let s = self.slot(a);
        let q = a / PAGE;
        let ghost j0 = self.rel(a as nat);
        proof {
            lemma_dm(a as nat);
            lemma_dm((b - 1) as nat);
        }
        let lo = (a - q * PAGE) as usize;
        let hi = (b - q * PAGE) as usize;
        let ghost g0 = old(self).pg(j0).unwrap();
        proof {
            old(self).lemma_take_src(a as nat, b as nat);
        }
        let mut v = self.slots.take().unwrap();
        let mut cur: Option<Box<Page>> = None;
        v.set_and_swap(s, &mut cur);
        let mut g = cur.unwrap();
        let Ghost(c) = g.take_held(lo, hi, out);
        proof {
            work = work + c + 2;
            lemma_count_le(g.have@);
        }
        let ghost g1 = *g;
        if g.held == 0 {
            // Dropping `g` frees the page's three buffers.
            self.slots = Some(v);
            proof {
                work = work + 3;
                Ring::lemma_put(*old(self), *self, j0, None);
            }
        } else {
            let mut back = Some(g);
            let ghost x = back;
            v.set_and_swap(s, &mut back);
            self.slots = Some(v);
            proof {
                assert(self.slots.unwrap()@ =~= old(self).slots.unwrap()@.update(s as int, x));
                Ring::lemma_put(*old(self), *self, j0, x);
            }
        }
        proof {
            Ring::lemma_take_page(*old(self), *self, j0, g0, g1, a as nat, b as nat);
        }
        Ghost(work)
    }

    /// The run of held positions from `base`: at most `max` and at most `w` long.
    fn scan(&self, max: u64) -> (r: (u64, Ghost<nat>))
        requires
            self.inv(),
        ensures
            r.0 <= max,
            r.0 <= self.w,
            forall|p: nat| self.base <= p < self.base + r.0 ==> self.view().contains_key(p),
            r.0 < max ==> !self.view().contains_key((self.base + r.0) as nat),
            r.1@ <= max + 1,
    {
        let ghost mut work: nat = 0;
        let mut k: u64 = 0;
        let mut go = true;
        while go && k < max && k < self.w
            invariant
                self.inv(),
                k <= max,
                k <= self.w,
                forall|p: nat| self.base <= p < self.base + k ==> self.view().contains_key(p),
                !go ==> k < max && !self.view().contains_key((self.base + k) as nat),
                work <= k + if go {
                    0nat
                } else {
                    1nat
                },
            decreases (max - k) as int + if go {
                1int
            } else {
                0int
            },
        {
            if self.has(self.base + k) {
                k = k + 1;
            } else {
                go = false;
            }
            proof {
                work = work + 1;
            }
        }
        (k, Ghost(work))
    }

    /// Moves `base` to `nb`, past positions none of which is held, and `first` to `nb`'s page.
    fn rebase(&mut self, nb: u64)
        requires
            old(self).inv(),
            old(self).base <= nb <= old(self).base + old(self).w,
            nb <= VARINT_MAX,
            forall|p: nat| old(self).view().contains_key(p) ==> p >= nb,
        ensures
            final(self).inv(),
            final(self).base == nb,
            final(self).w == old(self).w,
            final(self).view() == old(self).view(),
    {
        proof {
            lemma_page_span(self.base as nat, self.w as nat, nb as nat);
        }
        let f = self.first + (nb / PAGE - self.base / PAGE) as usize;
        self.first = if f >= self.np {
            f - self.np
        } else {
            f
        };
        self.base = nb;
        proof {
            Ring::lemma_rebase(*old(self), *self);
        }
    }

    /// Hands over the run of held positions from `base`, at most `max` bytes, in an exact `CapVec`, and frees each
    /// page that holds nothing past it. Costs `O(max + max/PAGE)`.
    pub fn deliver(&mut self, max: u64) -> (r: (CapVec<u8>, Ghost<nat>))
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).window() == old(self).window(),
            r.0.wf(),
            r.0.cap() == r.0@.len(),
            r.0@.len() <= max,
            forall|p: nat|
                old(self).base_spec() <= p < old(self).base_spec() + r.0@.len() ==> old(self).view().contains_key(p),
            r.0@.len() < max ==> !old(self).view().contains_key(old(self).base_spec() + r.0@.len()),
            r.0@ == run(old(self).view(), old(self).base_spec(), r.0@.len()),
            final(self).base_spec() == old(self).base_spec() + r.0@.len(),
            final(self).view() == from(old(self).view(), old(self).base_spec() + r.0@.len()),
            r.1@ <= c_rd() * (max + max as nat / (PAGE as nat) + 2),
    {
        hide(Ring::inv);
        hide(Ring::view);
        hide(Ring::mem_ok);
        hide(from);
        hide(run);
        let ghost mut work: nat = 0;
        let (k, Ghost(c0)) = self.scan(max);
        proof {
            self.lemma_inv_facts();
            work = work + c0 + 1;
        }
        let mut out: CapVec<u8> = CapVec::new(k as usize);
        let end = self.base + k;
        let ghost base = self.base;
        let mut pos = self.base;
        proof {
            old(self).lemma_from_base();
            lemma_run_empty(old(self).view(), base as nat);
            if k > 0 {
                old(self).lemma_of_view((base + k - 1) as nat);
            }
        }
        while pos < end
            invariant
                self.inv(),
                self.base == base,
                self.w == old(self).w,
                base == old(self).base,
                base <= pos <= end,
                end == base + k,
                k <= self.w,
                end <= VARINT_MAX,
                forall|p: nat| base <= p < end ==> old(self).view().contains_key(p),
                self.view() == from(old(self).view(), pos as nat),
                out.wf(),
                out.cap() == k,
                out@ == run(old(self).view(), base as nat, (pos - base) as nat),
                out@.len() == pos - base,
                pos > base && pos < end ==> pos as nat % 256 == 0,
                met(base as nat, pos as nat) * 256 <= pos - base + 510,
                work <= c0 + 1 + 3 * (pos - base) + 9 * met(base as nat, pos as nat),
            decreases end - pos,
        {
            let q = pos / PAGE;
            proof {
                lemma_dm(pos as nat);
            }
            let nb = (q + 1) * PAGE;
            let nxt = if nb < end {
                nb
            } else {
                end
            };
            proof {
                lemma_walk(base as nat, pos as nat, end as nat, q as nat, nxt as nat);
                lemma_from_run(old(self).view(), base as nat, pos as nat, end as nat);
            }
            let ghost o0 = out@;
            let Ghost(c) = self.take_page(pos, nxt, &mut out);
            proof {
                work = work + c + 1;
                lemma_take_step(old(self).view(), base as nat, pos as nat, nxt as nat, o0);
            }
            pos = nxt;
        }
        proof {
            lemma_from_run(old(self).view(), base as nat, end as nat, end as nat);
        }
        self.rebase(end);
        proof {
            lemma_deliver_cost(work, max as nat, k as nat, c0, met(base as nat, end as nat));
            self.lemma_mem();
        }
        (out, Ghost(work))
    }
}

} // verus!

impl Ring {
    /// Test support: the pages allocated.
    #[doc(hidden)]
    pub fn page_count(&self) -> usize {
        match &self.slots {
            Some(v) => v.as_slice().iter().filter(|s| s.is_some()).count(),
            None => 0,
        }
    }

    /// Test support: the slot vector exists (some byte has landed).
    #[doc(hidden)]
    pub fn has_slots(&self) -> bool {
        self.slots.is_some()
    }
}
