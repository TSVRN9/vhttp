//! Stream reassembly (RFC 9000 §2.2): ranges received in any order are buffered past the
//! delivered offset and popped as an ordered byte stream. The first bytes received at an
//! offset win. Shared by STREAM and CRYPTO data.
use vstd::prelude::*;
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

/// Out-of-order buffer: `buf[i]`/`have[i]` describe offset `base + i`; everything below
/// `base` was delivered.
pub struct Reassembly {
    base: u64,
    buf: Vec<u8>,
    have: Vec<bool>,
    ins: Ghost<Seq<(nat, Seq<u8>)>>,
}

impl Reassembly {
    /// Every `(offset, bytes)` inserted, in order.
    pub closed spec fn inserted(&self) -> Seq<(nat, Seq<u8>)> {
        self.ins@
    }

    /// The delivered offset.
    pub closed spec fn base(&self) -> nat {
        self.base as nat
    }

    pub closed spec fn buf_len_spec(&self) -> usize {
        self.buf@.len() as usize
    }

    pub closed spec fn wf(&self) -> bool {
        let m = rfc_received(self.ins@);
        &&& self.buf@.len() == self.have@.len()
        &&& self.base + self.buf@.len() <= VARINT_MAX
        &&& forall|i: int|
            0 <= i < self.have@.len() ==> (#[trigger] self.have@[i] <==> m.contains_key(
                (self.base + i) as nat,
            ))
        &&& forall|i: int|
            0 <= i < self.buf@.len() && self.have@[i] ==> #[trigger] self.buf@[i] == m[(self.base
                + i) as nat]
        &&& self.base <= rfc_contiguous(m)
        &&& forall|k: nat| #[trigger] m.contains_key(k) ==> k < self.base + self.buf@.len()
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
    {
    }

    pub fn new() -> (r: Reassembly)
        ensures
            r.wf(),
            r.inserted() == Seq::<(nat, Seq<u8>)>::empty(),
            r.base() == 0,
            r.buf_len() == 0,
    {
        let r = Reassembly { base: 0, buf: Vec::new(), have: Vec::new(), ins: Ghost(Seq::empty()) };
        proof {
            lemma_contiguous_exists(rfc_received(r.ins@));
        }
        r
    }

    pub fn base_exec(&self) -> (r: u64)
        ensures
            r == self.base(),
    {
        self.base
    }

    #[verifier::when_used_as_spec(buf_len_spec)]
    pub fn buf_len(&self) -> (r: usize)
        ensures
            r == self.buf_len_spec(),
    {
        self.buf.len()
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-2.2
    //# Data that has already been received can be
    //# discarded.
    // The MAY that follows (different data at the same offset as PROTOCOL_VIOLATION) is
    // declined: the first bytes received win, and later different bytes are discarded.
    /// Buffers `data` at `off`. Bytes below `base`, or at an offset already held, are dropped.
    /// The caller bounds `off + data.len()`, which bounds the buffer.
    pub fn insert(&mut self, off: u64, data: &[u8])
        requires
            old(self).wf(),
            off + data@.len() <= VARINT_MAX,
        ensures
            final(self).wf(),
            final(self).inserted() == old(self).inserted().push((off as nat, data@)),
            final(self).base() == old(self).base(),
            final(self).base() + final(self).buf_len() <= if old(self).base() + old(self).buf_len()
                >= off + data@.len() {
                old(self).base() + old(self).buf_len()
            } else {
                off + data@.len()
            },
    {
        let ghost m = rfc_received(self.ins@);
        let ghost hw = (old(self).base + old(self).buf@.len()) as int;
        let end = off + data.len() as u64;
        while self.base + (self.buf.len() as u64) < end
            invariant
                self.wf(),
                self.ins@ == old(self).ins@,
                self.base == old(self).base,
                end == off + data@.len(),
                end <= VARINT_MAX,
                self.base + self.buf@.len() <= if hw >= end {
                    hw
                } else {
                    end as int
                },
            decreases end - (self.base + self.buf@.len()),
        {
            self.buf.push(0);
            self.have.push(false);
        }
        let ghost len = self.buf@.len();
        let mut j: usize = if off >= self.base {
            0
        } else if self.base - off < data.len() as u64 {
            (self.base - off) as usize
        } else {
            data.len()
        };
        while j < data.len()
            invariant
                self.ins@ == old(self).ins@,
                self.base == old(self).base,
                m == rfc_received(self.ins@),
                self.buf@.len() == len,
                self.have@.len() == len,
                self.base + len <= VARINT_MAX,
                end == off + data@.len(),
                end <= self.base + len,
                j <= data@.len(),
                j < data@.len() ==> self.base <= off + j,
                self.base <= rfc_contiguous(m),
                forall|k: nat| #[trigger] m.contains_key(k) ==> k < self.base + len,
                forall|i: int|
                    0 <= i < len ==> (#[trigger] self.have@[i] <==> (m.contains_key(
                        (self.base + i) as nat,
                    ) || (off <= self.base + i < off + j))),
                forall|i: int|
                    0 <= i < len && self.have@[i] ==> #[trigger] self.buf@[i] == if m.contains_key(
                        (self.base + i) as nat,
                    ) {
                        m[(self.base + i) as nat]
                    } else {
                        data@[self.base + i - off]
                    },
            decreases data@.len() - j,
        {
            let idx = (off + j as u64 - self.base) as usize;
            if !self.have[idx] {
                self.buf[idx] = data[j];
                self.have[idx] = true;
            }
            j = j + 1;
        }
        self.ins = Ghost(self.ins@.push((off as nat, data@)));
        proof {
            let m2 = rfc_received(self.ins@);
            lemma_received_push(old(self).ins@, off as nat, data@);
            lemma_contiguous_exists(m);
            lemma_contiguous_exists(m2);
            if rfc_contiguous(m2) < self.base {
                assert(m.contains_key(rfc_contiguous(m2)));
            }
            assert(self.buf@.len() == self.have@.len());
            assert(self.base + self.buf@.len() <= VARINT_MAX);
            assert(forall|i: int|
                0 <= i < self.have@.len() ==> (#[trigger] self.have@[i] <==> m2.contains_key(
                    (self.base + i) as nat,
                )));
            assert(forall|i: int|
                0 <= i < self.buf@.len() && self.have@[i] ==> #[trigger] self.buf@[i] == m2[(self.base
                    + i) as nat]);
            assert(self.base <= rfc_contiguous(m2));
            assert(forall|k: nat| #[trigger] m2.contains_key(k) ==> k < self.base + self.buf@.len());
        }
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-2.2
    //# Endpoints MUST be able to deliver stream data to an application as an
    //# ordered byte stream.
    /// Appends the contiguous bytes past `base` to `out` and advances `base` past them.
    pub fn pop(&mut self, out: &mut Vec<u8>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).inserted() == old(self).inserted(),
            final(self).base() == rfc_contiguous(rfc_received(old(self).inserted())),
            final(self).base() + final(self).buf_len() == old(self).base() + old(self).buf_len(),
            final(out)@ == old(out)@ + rfc_prefix(
                rfc_received(old(self).inserted()),
                final(self).base(),
            ).subrange(old(self).base() as int, final(self).base() as int),
    {
        let ghost m = rfc_received(self.ins@);
        let mut n: usize = 0;
        while n < self.have.len() && self.have[n]
            invariant
                *self == *old(self),
                n <= self.have@.len(),
                forall|k: int| 0 <= k < n ==> #[trigger] self.have@[k],
            decreases self.have@.len() - n,
        {
            n = n + 1;
        }
        // ponytail: O(buffered) copy per delivery; keep a start index with lazy compaction if profiling shows it.
        let ghost head = self.buf@.subrange(0, n as int);
        let tail = self.buf.split_off(n);
        out.append(&mut self.buf);
        self.buf = tail;
        let htail = self.have.split_off(n);
        self.have = htail;
        self.base = self.base + n as u64;
        proof {
            let b = old(self).base as nat;
            lemma_contiguous_exists(m);
            assert forall|j: nat| j < b + n implies m.contains_key(j) by {
                if j >= b {
                    assert(old(self).have@[j - b]);
                }
            }
            if n < old(self).have@.len() {
                assert(!old(self).have@[n as int]);
            }
            lemma_contiguous_is(m, b + n as nat);
            assert(head =~= rfc_prefix(m, b + n as nat).subrange(b as int, b + n)) by {
                assert forall|k: int| 0 <= k < n implies head[k] == m[(b + k) as nat] by {
                    assert(old(self).have@[k]);
                }
            }
            assert forall|i: int| 0 <= i < self.have@.len() implies #[trigger] self.have@[i]
                == old(self).have@[i + n] by {}
        }
    }
}

} // verus!
