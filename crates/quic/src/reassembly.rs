//! Stream reassembly (RFC 9000 §2.2): ranges received in any order are buffered past the
//! delivered offset in a page ring (`quic::ring`, 9b2 D11) and popped as an ordered byte stream,
//! at most `max` bytes per call. The first bytes received at an offset win. STREAM data uses it;
//! CRYPTO data, whose span no flow control bounds, uses `frags`.
use vstd::prelude::*;
use crate::ring::*;
// Used only in ghost code, which a plain `cargo build` erases.
#[allow(unused_imports)]
use crate::frags::*;
// Used only in ghost code, which a plain `cargo build` erases.
#[allow(unused_imports)]
use wire::varint::*;

verus! {

broadcast use vstd::set_lib::range_set_properties;

/// The bytes received, by offset: each insertion adds only offsets not already received.
pub open spec fn rfc_received(ins: Seq<(nat, Seq<u8>)>) -> Map<nat, u8>
    decreases ins.len(),
{
    if ins.len() == 0 {
        Map::empty()
    } else {
        let m = rfc_received(ins.drop_last());
        let o = ins.last().0;
        let d = ins.last().1;
        Map::new(
            m.dom() + Set::<nat>::range(o, o + d.len()),
            |k: nat|
                if m.contains_key(k) {
                    m[k]
                } else {
                    d[k - o]
                },
        )
    }
}

/// Some insertion covers offset `o`.
pub open spec fn covered(ins: Seq<(nat, Seq<u8>)>, o: nat) -> bool {
    exists|j: int| #![trigger ins[j]] 0 <= j < ins.len() && ins[j].0 <= o < ins[j].0 + ins[j].1.len()
}

/// The least offset not received (total: see `lemma_contiguous_exists`).
pub open spec fn rfc_contiguous(m: Map<nat, u8>) -> nat {
    choose|n: nat| !m.contains_key(n) && forall|j: nat| j < n ==> m.contains_key(j)
}

/// The first `n` bytes.
pub open spec fn rfc_prefix(m: Map<nat, u8>, n: nat) -> Seq<u8> {
    Seq::new(n, |i: int| m[i as nat])
}

/// One step of `rfc_received`.
pub proof fn lemma_received_push(ins: Seq<(nat, Seq<u8>)>, o: nat, d: Seq<u8>)
    ensures
        forall|k: nat|
            #[trigger] rfc_received(ins.push((o, d))).contains_key(k) <==> rfc_received(
                ins,
            ).contains_key(k) || o <= k < o + d.len(),
        forall|k: nat|
            #[trigger] rfc_received(ins.push((o, d))).contains_key(k) ==> rfc_received(
                ins.push((o, d)),
            )[k] == if rfc_received(ins).contains_key(k) {
                rfc_received(ins)[k]
            } else {
                d[k - o]
            },
{
    assert(ins.push((o, d)).drop_last() =~= ins);
}

/// `n` is the least offset not received.
pub proof fn lemma_contiguous_is(m: Map<nat, u8>, n: nat)
    requires
        !m.contains_key(n),
        forall|j: nat| j < n ==> m.contains_key(j),
    ensures
        rfc_contiguous(m) == n,
{
    let c = rfc_contiguous(m);
    assert(!m.contains_key(c) && forall|j: nat| j < c ==> m.contains_key(j));
    if c < n {
        assert(m.contains_key(c));
    } else if c > n {
        assert(m.contains_key(n));
    }
}

/// The least offset not received is at most any offset not received.
pub proof fn lemma_contiguous_le(m: Map<nat, u8>, b: nat)
    requires
        !m.contains_key(b),
    ensures
        !m.contains_key(rfc_contiguous(m)),
        forall|j: nat| j < rfc_contiguous(m) ==> m.contains_key(j),
        rfc_contiguous(m) <= b,
    decreases b,
{
    if forall|j: nat| j < b ==> m.contains_key(j) {
        lemma_contiguous_is(m, b);
    } else {
        let j = choose|j: nat| j < b && !m.contains_key(j);
        lemma_contiguous_le(m, j);
    }
}

/// `rfc_contiguous` is total: a `Map` has a finite domain, so some offset is not a key.
pub proof fn lemma_contiguous_exists(m: Map<nat, u8>)
    ensures
        !m.contains_key(rfc_contiguous(m)),
        forall|j: nat| j < rfc_contiguous(m) ==> m.contains_key(j),
{
    let r = Set::<nat>::range(0, m.dom().len() + 1);
    if forall|b: nat| #[trigger] r.contains(b) ==> m.dom().contains(b) {
        vstd::set_lib::lemma_len_subset(r, m.dom());
        assert(false);
    }
    let b = choose|b: nat| #[trigger] r.contains(b) && !m.dom().contains(b);
    lemma_contiguous_le(m, b);
}

/// More received never lowers the least offset not received.
pub proof fn lemma_contiguous_mono(m1: Map<nat, u8>, m2: Map<nat, u8>)
    requires
        forall|k: nat| #[trigger] m1.contains_key(k) ==> m2.contains_key(k),
    ensures
        rfc_contiguous(m1) <= rfc_contiguous(m2),
{
    lemma_contiguous_exists(m1);
    lemma_contiguous_exists(m2);
    if rfc_contiguous(m2) < rfc_contiguous(m1) {
        assert(m1.contains_key(rfc_contiguous(m2)));
    }
}

/// Every insertion is consistent with `s`: the keys are the covered offsets, valued from `s`.
proof fn lemma_received_consistent(ins: Seq<(nat, Seq<u8>)>, s: Seq<u8>)
    requires
        forall|j: int|
            #![trigger ins[j]]
            0 <= j < ins.len() ==> ins[j].0 + ins[j].1.len() <= s.len() && ins[j].1 == s.subrange(
                ins[j].0 as int,
                (ins[j].0 + ins[j].1.len()) as int,
            ),
    ensures
        forall|k: nat| #[trigger] rfc_received(ins).contains_key(k) <==> covered(ins, k),
        forall|k: nat| #[trigger] rfc_received(ins).contains_key(k) ==> k < s.len() && rfc_received(ins)[k] == s[k as int],
    decreases ins.len(),
{
    if ins.len() > 0 {
        let p = ins.drop_last();
        let (o, d) = ins.last();
        assert forall|j: int| #![trigger p[j]] 0 <= j < p.len() implies p[j].0 + p[j].1.len() <= s.len()
            && p[j].1 == s.subrange(p[j].0 as int, (p[j].0 + p[j].1.len()) as int) by {
            assert(p[j] == ins[j]);
        }
        lemma_received_consistent(p, s);
        assert(ins =~= p.push((o, d)));
        lemma_received_push(p, o, d);
        let last = ins.len() - 1;
        assert(ins[last] == (o, d));
        assert forall|k: nat| #[trigger] rfc_received(ins).contains_key(k) <==> covered(ins, k) by {
            if covered(p, k) {
                let j = choose|j: int| #![trigger p[j]] 0 <= j < p.len() && p[j].0 <= k < p[j].0 + p[j].1.len();
                assert(p[j] == ins[j]);
            }
            if covered(ins, k) {
                let j = choose|j: int| #![trigger ins[j]] 0 <= j < ins.len() && ins[j].0 <= k < ins[j].0 + ins[j].1.len();
                if j < last {
                    assert(p[j] == ins[j]);
                }
            }
        }
        assert forall|k: nat| #[trigger] rfc_received(ins).contains_key(k) implies rfc_received(
            ins,
        )[k] == s[k as int] && k < s.len() by {
            if !rfc_received(p).contains_key(k) {
                assert(d[k - o] == s.subrange(o as int, (o + d.len()) as int)[k - o]);
            }
        }
    }
}

/// When every insertion is consistent with `s`, the bytes delivered depend only on the set of
/// ranges received, not on their order or duplication.
pub proof fn theorem_reassembly_order_free(ins: Seq<(nat, Seq<u8>)>, s: Seq<u8>)
    requires
        forall|j: int|
            #![trigger ins[j]]
            0 <= j < ins.len() ==> ins[j].0 + ins[j].1.len() <= s.len() && ins[j].1 == s.subrange(
                ins[j].0 as int,
                (ins[j].0 + ins[j].1.len()) as int,
            ),
    ensures
        forall|o: nat| #[trigger] rfc_received(ins).contains_key(o) <==> covered(ins, o),
        rfc_prefix(rfc_received(ins), rfc_contiguous(rfc_received(ins))) == s.take(
            rfc_contiguous(rfc_received(ins)) as int,
        ),
{
    lemma_received_consistent(ins, s);
    lemma_prefix_of(rfc_received(ins), s);
}

/// A map whose keys are offsets of `s`, valued from `s`, has its contiguous prefix in `s`.
proof fn lemma_prefix_of(m: Map<nat, u8>, s: Seq<u8>)
    requires
        forall|k: nat| #[trigger] m.contains_key(k) ==> k < s.len() && m[k] == s[k as int],
    ensures
        rfc_prefix(m, rfc_contiguous(m)) == s.take(rfc_contiguous(m) as int),
{
    lemma_contiguous_le(m, s.len());
    let c = rfc_contiguous(m);
    assert forall|i: int| 0 <= i < c implies #[trigger] rfc_prefix(m, c)[i] == s.take(c as int)[i] by {
        assert(m.contains_key(i as nat));
    }
    assert(rfc_prefix(m, c) =~= s.take(c as int));
}

/// `put` of a frame on the bytes received from `b` on is the bytes received with the frame, from `b` on.
pub proof fn lemma_from_put(ins: Seq<(nat, Seq<u8>)>, b: nat, off: nat, d: Seq<u8>)
    ensures
        put(from(rfc_received(ins), b), b, off, d) == from(rfc_received(ins.push((off, d))), b),
{
    lemma_received_push(ins, off, d);
    let m = rfc_received(ins);
    let m2 = rfc_received(ins.push((off, d)));
    let l = put(from(m, b), b, off, d);
    let r = from(m2, b);
    assert forall|k: nat| l.contains_key(k) <==> r.contains_key(k) by {}
    assert forall|k: nat| l.contains_key(k) implies l[k] == r[k] by {}
    assert(l =~= r);
}

/// The out-of-order buffer of one stream (9b2 D12): a page ring (`quic::ring`) holding the bytes received at or past
/// `base`, the next offset to deliver, `end`, one past the last byte held (or `base`), and `cnt`, the offsets received
/// (delivered ones included), so "all data received" is one comparison.
pub struct Reassembly {
    r: Ring,
    end: u64,
    cnt: u64,
    ins: Ghost<Seq<(nat, Seq<u8>)>>,
}

impl Reassembly {
    /// Every `(offset, bytes)` inserted, in order.
    pub closed spec fn inserted(&self) -> Seq<(nat, Seq<u8>)> {
        self.ins@
    }

    /// The delivered offset.
    pub closed spec fn base(&self) -> nat {
        self.r.base_spec()
    }

    /// The stream window the ring holds: offsets `[base, base + window)`.
    pub closed spec fn window(&self) -> nat {
        self.r.window()
    }

    pub closed spec fn buf_len_spec(&self) -> usize {
        (self.end - self.r.base_spec()) as usize
    }

    /// The ring's pages allocated, `PAGE` positions each.
    pub closed spec fn pages(&self) -> nat {
        self.r.pages()
    }

    pub closed spec fn wf(&self) -> bool {
        let m = rfc_received(self.ins@);
        &&& self.r.wf()
        &&& self.r.view() == from(m, self.r.base_spec())
        &&& self.r.base_spec() <= rfc_contiguous(m)
        &&& self.r.base_spec() <= self.end <= self.r.base_spec() + self.r.window()
        &&& self.end <= VARINT_MAX
        &&& forall|k: nat| #[trigger] m.contains_key(k) ==> k < self.end
        &&& self.end > self.r.base_spec() ==> m.contains_key((self.end - 1) as nat)
        &&& self.cnt as nat == m.dom().len()
    }

    /// The invariant, in terms of the accessors.
    pub proof fn lemma_wf(&self)
        requires
            self.wf(),
        ensures
            self.base() + self.buf_len() <= VARINT_MAX,
            self.base() <= rfc_contiguous(rfc_received(self.inserted())),
            forall|k: nat| #[trigger]
                rfc_received(self.inserted()).contains_key(k) ==> k < self.base()
                    + self.buf_len(),
            self.buf_len() <= self.window() <= MAX_RECV_WINDOW,
            // Memory follows the bytes held (D11): `pages · PAGE <= span + 2 · PAGE`, none when nothing is held.
            self.pages() * PAGE <= self.buf_len() + 2 * PAGE,
            self.buf_len() == 0 ==> self.pages() == 0,
    {
        self.r.lemma_wf();
        let m = rfc_received(self.ins@);
        if self.r.pages() > 0 {
            let p = choose|p: nat|
                self.r.view().contains_key(p) && self.r.pages() * PAGE <= p + 1 - self.r.base_spec() + 2 * PAGE;
            assert(from(m, self.r.base_spec()).contains_key(p));
            assert(m.contains_key(p));
        }
    }

    /// The window ends at a received byte: no unreceived slot past the last byte held.
    pub closed spec fn tight(&self) -> bool {
        self.buf_len() > 0 ==> rfc_received(self.inserted()).contains_key(
            (self.base() + self.buf_len() - 1) as nat,
        )
    }

    /// Every `wf` buffer is tight: `end` is one past a received byte.
    pub proof fn lemma_tight(&self)
        requires
            self.wf(),
        ensures
            self.tight(),
    {
        hide(rfc_contiguous);
        hide(from);
    }

    pub proof fn lemma_new_tight(&self)
        requires
            self.wf(),
            self.buf_len() == 0,
        ensures
            self.tight(),
    {
    }

    /// `insert` of non-empty data keeps the window tight (every `wf` one is).
    pub proof fn lemma_insert_tight(a: Reassembly, b: Reassembly, off: u64, d: Seq<u8>)
        requires
            a.wf(),
            a.tight(),
            b.wf(),
            d.len() > 0,
            off + d.len() > a.base(),
            b.inserted() == a.inserted().push((off as nat, d)),
            b.base() == a.base(),
            b.base() + b.buf_len() <= if a.base() + a.buf_len() >= off + d.len() {
                a.base() + a.buf_len()
            } else {
                off + d.len()
            },
        ensures
            b.tight(),
    {
        hide(rfc_received);
        hide(rfc_contiguous);
        hide(from);
        b.lemma_tight();
    }

    /// `pop` keeps the window tight (every `wf` one is).
    pub proof fn lemma_pop_tight(a: Reassembly, b: Reassembly)
        requires
            a.wf(),
            a.tight(),
            b.wf(),
            b.inserted() == a.inserted(),
            b.base() + b.buf_len() == a.base() + a.buf_len(),
            b.base() >= a.base(),
        ensures
            b.tight(),
    {
        hide(rfc_received);
        hide(rfc_contiguous);
        hide(from);
        b.lemma_tight();
    }

    /// `insert` of data ending inside the window keeps it tight (every `wf` one is).
    pub proof fn lemma_insert_tight_within(a: Reassembly, b: Reassembly, off: u64, d: Seq<u8>)
        requires
            a.wf(),
            a.tight(),
            b.wf(),
            off + d.len() <= a.base() + a.buf_len(),
            b.inserted() == a.inserted().push((off as nat, d)),
            b.base() == a.base(),
            b.base() + b.buf_len() <= a.base() + a.buf_len(),
        ensures
            b.tight(),
    {
        hide(rfc_received);
        hide(rfc_contiguous);
        hide(from);
        b.lemma_tight();
    }

    /// An empty buffer for window `w`: no ring memory until the first byte.
    pub fn new(w: u64) -> (r: Reassembly)
        requires
            w <= MAX_RECV_WINDOW,
        ensures
            r.wf(),
            r.inserted() == Seq::<(nat, Seq<u8>)>::empty(),
            r.base() == 0,
            r.buf_len() == 0,
            r.window() == w,
            r.pages() == 0,
    {
        let r = Reassembly { r: Ring::new(w), end: 0, cnt: 0, ins: Ghost(Seq::empty()) };
        proof {
            let m = rfc_received(r.ins@);
            lemma_contiguous_exists(m);
            assert(from(m, 0) =~= Map::<nat, u8>::empty());
            assert(m.dom() =~= Set::<nat>::empty());
        }
        r
    }

    pub fn base_exec(&self) -> (r: u64)
        requires
            self.wf(),
        ensures
            r == self.base(),
    {
        self.r.base_exec()
    }

    #[verifier::when_used_as_spec(buf_len_spec)]
    pub fn buf_len(&self) -> (r: usize)
        requires
            self.wf(),
        ensures
            r == self.buf_len_spec(),
    {
        proof {
            self.r.lemma_wf();
        }
        (self.end - self.r.base_exec()) as usize
    }

    /// The byte at `base` was received: `pop` would hand over at least one. O(1).
    pub fn ready(&self) -> (r: bool)
        requires
            self.wf(),
        ensures
            r == (rfc_contiguous(rfc_received(self.inserted())) > self.base()),
    {
        let r = self.r.ready();
        proof {
            let m = rfc_received(self.ins@);
            let b = self.r.base_spec();
            lemma_contiguous_exists(m);
            assert(from(m, b).contains_key(b) == m.contains_key(b));
            if rfc_contiguous(m) > b {
                assert(m.contains_key(b));
            }
        }
        r
    }

    /// Every offset below `f` was received, given none at or past `f` was: "Data Recvd" once `f` is
    /// the final size. O(1).
    pub fn complete_to(&self, f: u64) -> (r: bool)
        requires
            self.wf(),
            forall|k: nat| #[trigger] rfc_received(self.inserted()).contains_key(k) ==> k < f,
        ensures
            r == (rfc_contiguous(rfc_received(self.inserted())) == f),
    {
        proof {
            let m = rfc_received(self.ins@);
            let all = Set::<nat>::range(0, f as nat);
            assert forall|k: nat| #[trigger] m.dom().contains(k) implies all.contains(k) by {
                assert(rfc_received(self.inserted()).contains_key(k));
            }
            lemma_contiguous_exists(m);
            if self.cnt == f {
                vstd::set_lib::lemma_subset_equality(m.dom(), all);
                assert(!m.contains_key(f as nat));
                lemma_contiguous_is(m, f as nat);
            }
            if rfc_contiguous(m) == f {
                assert forall|k: nat| #[trigger] all.contains(k) implies m.dom().contains(k) by {
                    assert(m.contains_key(k));
                }
                assert(m.dom() =~= all);
            }
        }
        self.cnt == f
    }

    /// The offsets of `[lo, end)` not yet received, `lo` at or past `base` (split from `insert`). Costs `end - lo`.
    fn count_new(&self, lo: u64, end: u64) -> (r: (u64, Ghost<nat>))
        requires
            self.wf(),
            self.base() <= lo <= end <= self.base() + self.window(),
        ensures
            r.0 as nat == Set::<nat>::range(lo as nat, end as nat).filter(
                |q: nat| !rfc_received(self.inserted()).contains_key(q),
            ).len(),
            r.0 <= end - lo,
            r.1@ <= end - lo,
    {
        let ghost m = rfc_received(self.ins@);
        let ghost nf = |q: nat| !m.contains_key(q);
        let ghost mut work: nat = 0;
        let mut p = lo;
        let mut fresh: u64 = 0;
        proof {
            assert(Set::<nat>::range(lo as nat, lo as nat).filter(nf) =~= Set::<nat>::empty());
        }
        while p < end
            invariant
                self.wf(),
                m == rfc_received(self.ins@),
                nf == (|q: nat| !m.contains_key(q)),
                self.base() <= lo <= p <= end <= self.base() + self.window(),
                fresh as nat == Set::<nat>::range(lo as nat, p as nat).filter(nf).len(),
                fresh <= p - lo,
                work == p - lo,
            decreases end - p,
        {
            let ghost s0 = Set::<nat>::range(lo as nat, p as nat).filter(nf);
            let h = self.r.holds(p);
            let ghost s1 = Set::<nat>::range(lo as nat, (p + 1) as nat).filter(nf);
            proof {
                assert(from(m, self.base()).contains_key(p as nat) == m.contains_key(p as nat));
                assert(!s0.contains(p as nat));
                assert(nf(p as nat) == !h);
                assert forall|q: nat| #[trigger] s1.contains(q) == (s0.contains(q) || (q == p && nf(q))) by {
                    assert(Set::<nat>::range(lo as nat, (p + 1) as nat).contains(q) == (lo <= q < p + 1));
                    assert(Set::<nat>::range(lo as nat, p as nat).contains(q) == (lo <= q < p));
                }
            }
            if !h {
                proof {
                    assert(s1 =~= s0.insert(p as nat));
                }
                fresh = fresh + 1;
            } else {
                proof {
                    assert(s1 =~= s0);
                }
            }
            p = p + 1;
            proof {
                work = work + 1;
            }
        }
        (fresh, Ghost(work))
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-2.2
    //# Data that has already been received can be
    //# discarded.
    // The MAY that follows (different data at the same offset as PROTOCOL_VIOLATION) is
    // declined: the first bytes received win, and later different bytes are discarded.
    /// Buffers `data` at `off` in the ring. Bytes below `base`, or at an offset already held, are dropped. The caller
    /// keeps `off + data.len()` within the window. Costs the ring's insert: `O(d + PAGE)`, plus the slot vector on the
    /// stream's first byte.
    pub fn insert(&mut self, off: u64, data: &[u8]) -> (r: Ghost<nat>)
        requires
            old(self).wf(),
            off + data@.len() <= VARINT_MAX,
            off + data@.len() <= old(self).base() + old(self).window(),
        ensures
            final(self).wf(),
            final(self).inserted() == old(self).inserted().push((off as nat, data@)),
            final(self).base() == old(self).base(),
            final(self).window() == old(self).window(),
            final(self).base() + final(self).buf_len() <= if old(self).base() + old(self).buf_len()
                >= off + data@.len() {
                old(self).base() + old(self).buf_len()
            } else {
                off + data@.len()
            },
            // An empty insert is a no-op but for the log, which records no byte.
            data@.len() == 0 ==> {
                &&& final(self).buf_len() == old(self).buf_len()
                &&& final(self).pages() == old(self).pages()
                &&& rfc_received(final(self).inserted()) == rfc_received(old(self).inserted())
                &&& old(self).tight() ==> final(self).tight()
            },
            r@ <= (c_ri() + 1) * (data@.len() + 2 * PAGE) + NP_MAX,
    {
        let ghost m = rfc_received(self.ins@);
        let ghost b = self.r.base_spec();
        let end = off + data.len() as u64;
        let base = self.r.base_exec();
        let lo = if off < base {
            base
        } else {
            off
        };
        let (fresh, Ghost(c0)) = if lo < end {
            self.count_new(lo, end)
        } else {
            (0, Ghost(0))
        };
        proof {
            // The frame's offsets not received are those at or past `lo`: below `base` all are.
            let rr = Set::<nat>::range(off as nat, end as nat);
            let nf = |q: nat| !m.contains_key(q);
            let df = rr.difference(m.dom());
            if lo < end {
                assert(df =~= Set::<nat>::range(lo as nat, end as nat).filter(nf)) by {
                    lemma_contiguous_exists(m);
                }
            } else {
                assert(df =~= Set::<nat>::empty()) by {
                    lemma_contiguous_exists(m);
                }
            }
            lemma_received_push(old(self).ins@, off as nat, data@);
            let m2 = rfc_received(old(self).ins@.push((off as nat, data@)));
            assert(m2.dom() =~= m.dom() + df);
            vstd::set_lib::lemma_set_disjoint_lens(m.dom(), df);
            let top = if end > old(self).end { end } else { old(self).end };
            assert(m2.dom().subset_of(Set::<nat>::range(0, top as nat)));
            vstd::set_lib::lemma_len_subset(m2.dom(), Set::<nat>::range(0, top as nat));
        }
        self.cnt = self.cnt + fresh;
        // An empty frame records its offset only: no ring memory for it.
        let Ghost(c) = if data.len() > 0 {
            self.r.insert_bytes(off, data)
        } else {
            Ghost(0)
        };
        if data.len() > 0 && end > self.end {
            self.end = end;
        }
        self.ins = Ghost(self.ins@.push((off as nat, data@)));
        proof {
            let m2 = rfc_received(self.ins@);
            lemma_from_put(old(self).ins@, b, off as nat, data@);
            lemma_received_push(old(self).ins@, off as nat, data@);
            lemma_contiguous_exists(m);
            lemma_contiguous_exists(m2);
            if rfc_contiguous(m2) < b {
                assert(m.contains_key(rfc_contiguous(m2)));
            }
            if data@.len() > 0 && end > old(self).end {
                assert(m2.contains_key((end - 1) as nat));
            } else if self.end > b {
                assert(m.contains_key((self.end - 1) as nat));
            }
            if data@.len() == 0 {
                assert(m2 =~= m);
            }
            let d = data@.len();
            assert((c_ri() + 1) * (d + 2 * PAGE) == c_ri() * (d + 2 * PAGE) + d + 2 * PAGE) by (nonlinear_arith);
        }
        Ghost(c + c0)
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-2.2
    //# Endpoints MUST be able to deliver stream data to an application as an
    //# ordered byte stream.
    /// Hands over the contiguous bytes from `base`, at most `max`, in one exact allocation, and advances `base` past
    /// them; pages past delivery are freed. Costs the ring's deliver: `O(max + max/PAGE)`, nothing amortized.
    pub fn pop(&mut self, max: u64) -> (r: (Vec<u8>, Ghost<nat>))
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).inserted() == old(self).inserted(),
            final(self).window() == old(self).window(),
            final(self).base() == old(self).base() + r.0@.len(),
            final(self).base() + final(self).buf_len() == old(self).base() + old(self).buf_len(),
            r.0@.len() == if old(self).base() + max <= rfc_contiguous(rfc_received(old(self).inserted())) {
                max as nat
            } else {
                (rfc_contiguous(rfc_received(old(self).inserted())) - old(self).base()) as nat
            },
            r.0@ == rfc_prefix(rfc_received(old(self).inserted()), final(self).base()).subrange(
                old(self).base() as int,
                final(self).base() as int,
            ),
            r.1@ <= c_rd() * (max + max as nat / (PAGE as nat) + 2),
    {
        let ghost m = rfc_received(self.ins@);
        let ghost b = self.r.base_spec();
        proof {
            lemma_contiguous_exists(m);
            self.r.lemma_wf();
        }
        let (v, Ghost(c)) = self.r.deliver(max);
        let ghost k = v@.len();
        proof {
            let n = rfc_contiguous(m);
            assert forall|p: nat| b <= p < b + k implies m.contains_key(p) by {
                assert(old(self).r.view().contains_key(p));
            }
            assert forall|p: nat| p < b + k implies m.contains_key(p) by {
                if p >= b {
                    assert(old(self).r.view().contains_key(p));
                }
            }
            if k < max {
                assert(!from(m, b).contains_key(b + k));
                assert(!m.contains_key(b + k));
                lemma_contiguous_is(m, b + k);
            } else if b + k > n {
                assert(m.contains_key(n));
            }
            // `end` is not received, so delivery stops at or before it.
            assert(!m.contains_key(self.end as nat));
            if b + k > self.end {
                assert(m.contains_key(self.end as nat));
            }
            assert(from(from(m, b), b + k) =~= from(m, b + k));
            assert(v@ =~= rfc_prefix(m, b + k).subrange(b as int, (b + k) as int)) by {
                assert forall|i: int| 0 <= i < k implies #[trigger] v@[i] == m[(b + i) as nat] by {
                    assert(from(m, b).contains_key((b + i) as nat));
                }
            }
        }
        (v.into_vec(), Ghost(c))
    }
}

} // verus!

impl Reassembly {
    /// Test support: the ring's pages allocated (Verus counts them as `pages()`; a page is 256 bytes and 256 flags).
    #[doc(hidden)]
    pub fn page_count(&self) -> usize {
        self.r.page_count()
    }
}
