//! CRYPTO streams (RFC 9000 §7.5, §19.6): per encryption level, the received bytes not yet read, in
//! order or not, in one sparse store (`Frags`), so memory follows the bytes held, not the offsets
//! they span, and a frame copies no in-order byte: `read` takes them lazily. CRYPTO data has no flow
//! control (§4).
use vstd::prelude::*;
use byteq::capvec::CapVec;
use crate::avl::Tree;
use crate::codes::*;
use crate::conn::B_PUMP;
use crate::frags::*;
// Used only in ghost code, which a plain `cargo build` erases.
#[allow(unused_imports)]
use crate::reassembly::*;
#[allow(unused_imports)]
use wire::varint::*;

verus! {

broadcast use vstd::set_lib::range_set_properties;

//= https://www.rfc-editor.org/rfc/rfc9000#section-7.5
//# Implementations MUST support buffering at least 4096 bytes of data
//# received in out-of-order CRYPTO frames.
// shortcut: a fixed 16 KiB of out-of-order bytes held (§7.5's floor is 4096); grow during the handshake only if real ClientHellos need it.
/// Out-of-order bytes held (positions received past `crypto_contiguous`) are at most this.
pub const MAX_CRYPTO_BUFFER: u64 = 16384;

/// Our own limit: the out-of-order bytes held form at most this many runs, one fragment each.
pub const MAX_CRYPTO_RANGES: usize = 4096;

/// The end of the in-order CRYPTO data received: every byte below it has been received, and the
/// byte at it has not. Bytes received past it are the out-of-order data of RFC 9000 §7.5.
pub open spec fn crypto_contiguous(s: CryptoStream) -> nat {
    rfc_contiguous(rfc_received(s.inserted_frames()))
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-7.5
//# Implementations MUST support buffering at least 4096 bytes of data
//# received in out-of-order CRYPTO frames.
/// The positions received past the contiguous end once `d` at `off` is in: the data held from
/// out-of-order CRYPTO frames.
pub open spec fn ooo_received(s: CryptoStream, off: u64, d: Seq<u8>) -> Set<nat> {
    let m = rfc_received(s.inserted_frames().push((off as nat, d)));
    m.dom().filter(|p: nat| p > rfc_contiguous(m))
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-7.5
//# Implementations MUST support buffering at least 4096 bytes of data
//# received in out-of-order CRYPTO frames.
/// The number of out-of-order bytes held once `d` at `off` is in.
pub open spec fn ooo_held(s: CryptoStream, off: u64, d: Seq<u8>) -> nat {
    ooo_received(s, off, d).len()
}

/// The number of maximal runs they form.
pub open spec fn ooo_runs(s: CryptoStream, off: u64, d: Seq<u8>) -> nat {
    runs(ooo_received(s, off, d))
}

/// The errors `on_crypto` may return: CRYPTO_BUFFER_EXCEEDED when a non-empty frame would take
/// the out-of-order bytes held past `MAX_CRYPTO_BUFFER`, or their runs past `MAX_CRYPTO_RANGES`.
/// Only the frame's positions count, not its bytes (`lemma_ooo_bytes_free`). During the
/// handshake the close is required; after it, closing is the chosen one of two MAYs.
//= https://www.rfc-editor.org/rfc/rfc9000#section-7.5
//# If an endpoint does not expand its buffer, it MUST close
//# the connection with a CRYPTO_BUFFER_EXCEEDED error code.
//= https://www.rfc-editor.org/rfc/rfc9000#section-7.5
//# Once the handshake completes, if an endpoint is unable to buffer all
//# data in a CRYPTO frame, it MAY discard that CRYPTO frame and all
//# CRYPTO frames received in the future, or it MAY close the connection
//# with a CRYPTO_BUFFER_EXCEEDED error code.
pub open spec fn crypto_allowed_err(s: CryptoStream, offset: u64, len: nat, c: u64) -> bool {
    let d = Seq::new(len, |_i: int| 0u8);
    &&& c == CRYPTO_BUFFER_EXCEEDED
    &&& len > 0
    &&& ooo_held(s, offset, d) > MAX_CRYPTO_BUFFER || ooo_runs(s, offset, d) > MAX_CRYPTO_RANGES as nat
}

/// The out-of-order positions depend on the frame's length, not its bytes.
pub proof fn lemma_ooo_bytes_free(s: CryptoStream, off: u64, d: Seq<u8>)
    ensures
        ooo_received(s, off, d) == ooo_received(s, off, Seq::new(d.len(), |_i: int| 0u8)),
{
    let z = Seq::new(d.len(), |_i: int| 0u8);
    let m1 = rfc_received(s.inserted_frames().push((off as nat, d)));
    let m2 = rfc_received(s.inserted_frames().push((off as nat, z)));
    lemma_received_push(s.inserted_frames(), off as nat, d);
    lemma_received_push(s.inserted_frames(), off as nat, z);
    assert(m1.dom() =~= m2.dom());
    lemma_contiguous_exists(m1);
    lemma_contiguous_is(m2, rfc_contiguous(m1));
    assert(ooo_received(s, off, d) =~= ooo_received(s, off, z));
}

/// `crypto_allowed_err` is not vacuous: an empty frame is never refused, no other code is
/// allowed, and on a stream that has received nothing a one-byte frame is not refused.
proof fn lemma_crypto_allowed_err_rejects(s: CryptoStream, offset: u64)
    ensures
        !crypto_allowed_err(s, offset, 0, CRYPTO_BUFFER_EXCEEDED),
        !crypto_allowed_err(s, offset, 1, PROTOCOL_VIOLATION),
        s.inserted_frames() == Seq::<(nat, Seq<u8>)>::empty() ==> !crypto_allowed_err(s, 1, 1, CRYPTO_BUFFER_EXCEEDED),
{
    if s.inserted_frames() == Seq::<(nat, Seq<u8>)>::empty() {
        let e = Seq::<(nat, Seq<u8>)>::empty();
        let b = Seq::new(1, |_i: int| 0u8);
        lemma_received_push(e, 1, b);
        let m = rfc_received(e.push((1nat, b)));
        assert(rfc_received(e) =~= Map::<nat, u8>::empty());
        lemma_contiguous_is(m, 0);
        assert(ooo_received(s, 1, b) =~= Set::<nat>::range(1, 2));
        crate::frags::lemma_runs_le_len(ooo_received(s, 1, b));
    }
}

/// And it allows the refusal: with 16384 out-of-order bytes held, a frame adding a 16385th may
/// close.
proof fn lemma_crypto_allowed_err_16385(s: CryptoStream)
    requires
        s.inserted_frames() == Seq::<(nat, Seq<u8>)>::empty().push((1nat, Seq::new(16384, |_i: int| 0u8))),
    ensures
        ooo_held(s, 16385, Seq::new(1, |_i: int| 0u8)) == 16385,
        crypto_allowed_err(s, 16385, 1, CRYPTO_BUFFER_EXCEEDED),
{
    let e = Seq::<(nat, Seq<u8>)>::empty();
    let a = Seq::new(16384, |_i: int| 0u8);
    let b = Seq::new(1, |_i: int| 0u8);
    lemma_received_push(e, 1, a);
    lemma_received_push(s.inserted_frames(), 16385, b);
    let m = rfc_received(s.inserted_frames().push((16385nat, b)));
    assert(rfc_received(e) =~= Map::<nat, u8>::empty());
    lemma_contiguous_is(m, 0);
    assert(ooo_received(s, 16385, b) =~= Set::<nat>::range(1, 16386));
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-7.5
//# Implementations MUST support buffering at least 4096 bytes of data
//# received in out-of-order CRYPTO frames.
/// The floor: a frame after which at most 4096 out-of-order bytes are held is never refused,
/// however far past the contiguous end they lie and however much in-order data is unread. Each
/// run holds a byte, so the runs are at most 4096 too.
pub proof fn lemma_crypto_floor(s: CryptoStream, offset: u64, d: Seq<u8>)
    requires
        // Stated over the RFC set itself, not through `ooo_held`, so that a redefinition of the
        // predicate's quantities cannot carry the floor with it (rule 1d).
        rfc_received(s.inserted_frames().push((offset as nat, d))).dom().filter(
            |p: nat| p > rfc_contiguous(rfc_received(s.inserted_frames().push((offset as nat, d)))),
        ).len() <= 4096,
    ensures
        forall|c: u64| !#[trigger] crypto_allowed_err(s, offset, d.len(), c),
{
    let m = rfc_received(s.inserted_frames().push((offset as nat, d)));
    assert(ooo_received(s, offset, d) =~= m.dom().filter(|p: nat| p > rfc_contiguous(m)));
    lemma_ooo_bytes_free(s, offset, d);
    lemma_runs_le_len(ooo_received(s, offset, d));
}

/// The positions of `s` past `c`.
pub open spec fn above(s: Set<nat>, c: nat) -> Set<nat> {
    s.filter(|k: nat| k > c)
}

/// How many bytes `read(max)` takes: `max`, or every unread in-order byte if fewer.
pub open spec fn crypto_take(s: CryptoStream, max: u64) -> nat {
    if max as nat <= crypto_contiguous(s) - s.base_spec() {
        max as nat
    } else {
        (crypto_contiguous(s) - s.base_spec()) as nat
    }
}

/// The CRYPTO stream of one encryption level.
pub struct CryptoStream {
    /// The read offset.
    base: u64,
    /// `crypto_contiguous`, kept so a frame costs O(1) plus the bytes it touches.
    contig: u64,
    /// The end of the received data.
    hi: u64,
    /// The received bytes at or past `base`: the unread in-order ones, `[base, contig)`, and the
    /// out-of-order ones past `contig`. Read lazily (`read`), so a frame copies no in-order byte.
    st: Frags,
    /// The teardown slot: retired stores (`retire`), freed a bounded piece per call (`free_some`). Its keys are
    /// all below `base`, so a store retired onto a full slot joins it in O(log n).
    td: Tree<CapVec<u8>>,
    /// Every insertion since the last `retire`, which records the bytes below its base (read,
    /// but not data received anew) as zeros.
    ins: Ghost<Seq<(nat, Seq<u8>)>>,
    /// Every insertion `on_crypto` made, kept across `retire`: what was really received.
    hist: Ghost<Seq<(nat, Seq<u8>)>>,
}

impl CryptoStream {
    /// The insertions since the last `retire`, its record of the bytes below its base first.
    pub closed spec fn inserted_frames(&self) -> Seq<(nat, Seq<u8>)> {
        self.ins@
    }

    /// The read offset.
    pub closed spec fn base_spec(&self) -> nat {
        self.base as nat
    }

    /// From the read offset to the end of the received data.
    pub closed spec fn buf_len_spec(&self) -> nat {
        (self.hi - self.base) as nat
    }

    pub closed spec fn history(&self) -> Seq<(nat, Seq<u8>)> {
        self.hist@
    }

    /// The positions held at or past the read offset: unread in-order and out-of-order bytes.
    pub closed spec fn held_spec(&self) -> nat {
        self.st.held() as nat
    }

    /// The nodes in the teardown slot.
    pub closed spec fn td_nodes(&self) -> nat {
        crate::avl::seq(self.td).len()
    }

    /// Byte `p` arrived in a CRYPTO frame. `inserted_frames()` also holds `retire`'s record of the bytes
    /// below its base, which were read but are not data received anew.
    pub closed spec fn received(&self, p: nat) -> bool {
        rfc_received(self.hist@).contains_key(p)
    }

    /// Read to the contiguous end: no in-order byte is left unread.
    pub open spec fn drained(&self) -> bool {
        self.base_spec() == crypto_contiguous(*self)
    }

    /// The end of the received data: the read offset plus the buffered span.
    pub open spec fn end_spec(&self) -> nat {
        self.base_spec() + self.buf_len_spec()
    }

    /// The store holds the received bytes at or past `base`; `hi` is the end of the received data;
    /// the out-of-order bytes (past `contig`) are at most `MAX_CRYPTO_BUFFER` in at most
    /// `MAX_CRYPTO_RANGES` runs; the teardown slot's keys lie below `base`, at most `base` of them.
    spec fn core(&self) -> bool {
        let m = rfc_received(self.ins@);
        &&& self.st.wf()
        &&& crate::avl::wf(self.td)
        &&& self.base <= self.contig <= self.hi <= VARINT_MAX
        &&& self.contig as nat == rfc_contiguous(m)
        &&& forall|k: nat| #[trigger] m.contains_key(k) ==> k < self.hi
        &&& self.hi > self.contig ==> m.contains_key((self.hi - 1) as nat)
        &&& forall|p: nat| #[trigger] self.st.view().contains_key(p) <==> m.contains_key(p) && p >= self.base
        &&& forall|p: nat| #[trigger] self.st.view().contains_key(p) ==> self.st.view()[p] == m[p]
        &&& above(m.dom(), self.contig as nat).len() <= MAX_CRYPTO_BUFFER
        &&& runs(above(m.dom(), self.contig as nat)) <= MAX_CRYPTO_RANGES
        &&& crate::avl::keys_lt(self.td, self.base)
        &&& crate::avl::seq(self.td).len() <= self.base
    }

    /// `core`, and the record of what arrived: the byte before the end arrived, and every byte
    /// that arrived is in `inserted_frames()`.
    pub closed spec fn wf(&self) -> bool {
        &&& self.core()
        &&& self.end_spec() > 0 ==> self.received((self.end_spec() - 1) as nat)
        &&& forall|p: nat| #[trigger] self.received(p) ==> rfc_received(self.ins@).contains_key(p)
    }

    /// `core`'s consequences: the received bytes end at `hi`, and the byte before it was received;
    /// the store holds the in-order run `[base, contig)` and the out-of-order bytes.
    proof fn lemma_core(&self)
        requires
            self.core(),
        ensures
            self.base <= self.contig <= self.hi <= VARINT_MAX,
            forall|k: nat| #[trigger] rfc_received(self.ins@).contains_key(k) ==> k < self.hi,
            self.hi > 0 ==> rfc_received(self.ins@).contains_key((self.hi - 1) as nat),
            !rfc_received(self.ins@).contains_key(self.contig as nat),
            forall|k: nat| k < self.contig ==> #[trigger] rfc_received(self.ins@).contains_key(k),
            self.st.held() == (self.contig - self.base) + above(rfc_received(self.ins@).dom(), self.contig as nat).len(),
            self.st.held() <= (self.contig - self.base) + MAX_CRYPTO_BUFFER,
            self.hi <= self.base ==> self.st.held() == 0,
    {
        let m = rfc_received(self.ins@);
        lemma_contiguous_exists(m);
        if self.hi == self.contig && self.contig > 0 {
            assert(m.contains_key((self.contig - 1) as nat));
        }
        self.st.lemma_wf();
        lemma_store(self.st.view().dom(), m, self.base as nat, self.contig as nat);
        if self.hi <= self.base {
            assert(above(m.dom(), self.contig as nat) =~= Set::<nat>::empty());
        }
    }

    /// The invariant, in terms of the accessors.
    pub proof fn lemma_wf(&self)
        requires
            self.wf(),
        ensures
            self.base_spec() <= crypto_contiguous(*self) <= self.end_spec() <= VARINT_MAX,
            forall|k: nat| #[trigger]
                rfc_received(self.inserted_frames()).contains_key(k) ==> k < self.end_spec(),
            self.end_spec() > 0 ==> self.received((self.end_spec() - 1) as nat),
            forall|p: nat| #[trigger] self.received(p) ==> p < self.end_spec(),
            // The memory bound: the unread in-order bytes plus at most MAX_CRYPTO_BUFFER more.
            self.held_spec() <= (crypto_contiguous(*self) - self.base_spec()) + MAX_CRYPTO_BUFFER,
            self.drained() ==> self.held_spec() <= MAX_CRYPTO_BUFFER,
            self.end_spec() <= self.base_spec() ==> self.held_spec() == 0,
    {
        self.lemma_core();
    }

    pub fn new() -> (r: CryptoStream)
        ensures
            r.wf(),
            r.inserted_frames() == Seq::<(nat, Seq<u8>)>::empty(),
            r.base_spec() == 0,
            crypto_contiguous(r) == 0,
            r.held_spec() == 0,
            r.td_nodes() == 0,
    {
        let r = CryptoStream {
            base: 0,
            contig: 0,
            hi: 0,
            st: Frags::new(),
            td: None,
            ins: Ghost(Seq::empty()),
            hist: Ghost(Seq::empty()),
        };
        proof {
            let m = rfc_received(r.ins@);
            assert(m =~= Map::<nat, u8>::empty());
            assert(rfc_received(r.hist@) =~= Map::<nat, u8>::empty());
            lemma_contiguous_is(m, 0);
            assert(above(m.dom(), 0) =~= Set::<nat>::empty());
            assert(starts(Set::<nat>::empty()) =~= Set::<nat>::empty());
        }
        r
    }

    /// Nothing buffered, everything below the end read, and `history` kept: what an Initial
    /// discard leaves, for the end check of RFC 9001 §4.1.3, and what a closed connection leaves
    /// (TLS reads no more). The store moves to the teardown slot, no byte copied; onto a full slot
    /// (never met: a level retires once while open, D6) it joins in O(log n), the slot's keys being below the store's.
    pub fn retire(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).base_spec() == old(self).end_spec(),
            final(self).buf_len_spec() == 0,
            final(self).history() == old(self).history(),
            forall|p: nat| #[trigger] final(self).received(p) == old(self).received(p),
            crypto_contiguous(*final(self)) == old(self).end_spec(),
            final(self).held_spec() == 0,
            final(self).td_nodes() <= old(self).td_nodes() + old(self).held_spec(),
    {
        proof {
            self.lemma_core();
            self.st.lemma_nodes_le_held();
            self.st.lemma_wf();
            lemma_held_span(self.st.view().dom(), self.base as nat, self.hi as nat);
        }
        let end = self.hi;
        let ghost a = *self;
        let ghost d = Seq::new(end as nat, |_i: int| 0u8);
        let mut s = Frags::new();
        core::mem::swap(&mut self.st, &mut s);
        let t = s.into_tree();
        let ghost tg = t;
        if self.td.is_none() {
            self.td = t;
        } else {
            let mut slot: Tree<CapVec<u8>> = None;
            core::mem::swap(&mut self.td, &mut slot);
            proof {
                assert forall|i: int, j: int|
                    0 <= i < crate::avl::seq(slot).len() && 0 <= j < crate::avl::seq(t).len() implies #[trigger] crate::avl::seq(
                    slot,
                )[i].0 < #[trigger] crate::avl::seq(t)[j].0 by {
                    assert(a.st.view().contains_key(crate::avl::seq(t)[j].0 as nat));
                }
                vstd::arithmetic::power2::lemma2_to64_rest();
            }
            let (j, _c) = crate::avl::join2(slot, t);
            self.td = j;
        }
        self.base = end;
        self.contig = end;
        self.ins = Ghost(Seq::<(nat, Seq<u8>)>::empty().push((0nat, d)));
        proof {
            let m = rfc_received(self.ins@);
            lemma_received_push(Seq::<(nat, Seq<u8>)>::empty(), 0, d);
            assert(rfc_received(Seq::<(nat, Seq<u8>)>::empty()) =~= Map::<nat, u8>::empty());
            lemma_contiguous_is(m, end as nat);
            self.st.lemma_wf();
            self.st.lemma_nodes_le_held();
            assert(above(m.dom(), end as nat) =~= Set::<nat>::empty());
            assert(starts(Set::<nat>::empty()) =~= Set::<nat>::empty());
            let n = crate::avl::seq(a.td).len();
            assert(crate::avl::seq(self.td) == crate::avl::seq(a.td) + crate::avl::seq(tg));
            assert forall|i: int| 0 <= i < crate::avl::seq(self.td).len() implies #[trigger] crate::avl::seq(self.td)[i].0
                < end by {
                if i < n {
                    assert(crate::avl::seq(self.td)[i] == crate::avl::seq(a.td)[i]);
                } else {
                    assert(crate::avl::seq(self.td)[i] == crate::avl::seq(tg)[i - n]);
                    assert(a.st.view().contains_key(crate::avl::seq(tg)[i - n].0 as nat));
                }
            }
            assert forall|p: nat| #[trigger] self.received(p) implies m.contains_key(p) by {
                assert(a.received(p));
            }
            if self.end_spec() > 0 {
                assert(a.received((a.end_spec() - 1) as nat));
            }
        }
    }

    /// A CRYPTO frame's `offset` and `data`.
    pub fn on_crypto(&mut self, offset: u64, data: &[u8]) -> (r: Result<(), u64>)
        requires
            old(self).wf(),
            offset + data@.len() <= VARINT_MAX,
        ensures
            final(self).wf(),
            r is Err <==> crypto_allowed_err(*old(self), offset, data@.len(), CRYPTO_BUFFER_EXCEEDED),
            r is Err ==> r == Err::<(), u64>(CRYPTO_BUFFER_EXCEEDED),
            r matches Err(c) ==> crypto_allowed_err(*old(self), offset, data@.len(), c),
            (r is Err || offset + data@.len() <= old(self).base_spec() || data@.len() == 0)
                ==> *final(self) == *old(self),
            (r is Ok && offset + data@.len() > old(self).base_spec() && data@.len() > 0) ==> {
                &&& final(self).inserted_frames() == old(self).inserted_frames().push((offset as nat, data@))
                &&& final(self).base_spec() == old(self).base_spec()
            },
            // The record of what arrived only grows, and so does its end.
            forall|p: nat| #[trigger] old(self).received(p) ==> final(self).received(p),
            final(self).end_spec() >= old(self).end_spec(),
            // At most one position held per byte of the frame.
            final(self).held_spec() <= old(self).held_spec() + data@.len(),
            final(self).td_nodes() == old(self).td_nodes(),
    {
        let end = offset + data.len() as u64;
        if end <= self.base {
            //= https://www.rfc-editor.org/rfc/rfc9000#section-7.5
            //# Packets containing
            //# discarded CRYPTO frames MUST be acknowledged because the packet has
            //# been received and processed by the transport even though the CRYPTO
            //# frame was discarded.
            // Already read: not an error, so the packet is processed and acknowledged. The
            // post-handshake option to discard frames that don't fit (a MAY) is declined: a
            // non-empty frame past the limits always closes the connection, below.
            proof {
                lemma_same(*self, offset, data@);
            }
            return Ok(());
        }
        if data.len() == 0 {
            // No bytes: nothing is buffered, so the buffer is not exceeded at any offset
            // (RFC 9000 §7.5), and the end is not moved past what was received (RFC 9001 §4.1.3).
            return Ok(());
        }
        let ghost a = *self;
        if end <= self.contig {
            // Every byte already received: nothing new is held.
            self.ins = Ghost(self.ins@.push((offset as nat, data@)));
            self.hist = Ghost(self.hist@.push((offset as nat, data@)));
            proof {
                lemma_same(a, offset, data@);
                lemma_hist_step(a, *self, offset, data@);
            }
            return Ok(());
        }
        if offset > self.contig {
            self.on_ooo(offset, data)
        } else {
            self.on_fill(offset, data);
            Ok(())
        }
    }

    /// `on_crypto` for non-empty data all past the contiguous end, which therefore stays: the
    /// limits are checked before the bytes are taken (split from `on_crypto` for the rlimit). The
    /// store's count includes the in-order run `[base, contig)`, a run of its own since `contig`
    /// is not held: the out-of-order bytes are the rest (`lemma_ooo_count`).
    #[verifier::spinoff_prover]
    fn on_ooo(&mut self, offset: u64, data: &[u8]) -> (r: Result<(), u64>)
        requires
            old(self).wf(),
            offset + data@.len() <= VARINT_MAX,
            offset > old(self).contig,
            data@.len() > 0,
        ensures
            r is Err <==> crypto_allowed_err(*old(self), offset, data@.len(), CRYPTO_BUFFER_EXCEEDED),
            r is Err ==> r == Err::<(), u64>(CRYPTO_BUFFER_EXCEEDED) && *final(self) == *old(self),
            r is Ok ==> stepped(*final(self), *old(self), offset, data@),
    {
        hide(rfc_received);
        hide(rfc_contiguous);
        hide(put);
        hide(ooo_held);
        hide(ooo_runs);
        hide(ooo_received);
        hide(runs);
        hide(above);
        let ghost a = *self;
        let (h, c) = self.st.after_insert(self.contig, offset, data);
        proof {
            lemma_ooo_count(a, offset, data@);
        }
        let run: usize = if self.contig > self.base {
            1
        } else {
            0
        };
        if h - (self.contig - self.base) > MAX_CRYPTO_BUFFER || c - run > MAX_CRYPTO_RANGES {
            //= https://www.rfc-editor.org/rfc/rfc9000#section-7.5
            //# If an endpoint does not expand its buffer, it MUST close
            //# the connection with a CRYPTO_BUFFER_EXCEEDED error code.
            return Err(CRYPTO_BUFFER_EXCEEDED);
        }
        self.st.insert(self.contig, offset, data);
        let end = offset + data.len() as u64;
        if end > self.hi {
            self.hi = end;
        }
        self.ins = Ghost(self.ins@.push((offset as nat, data@)));
        self.hist = Ghost(self.hist@.push((offset as nat, data@)));
        proof {
            lemma_ooo_post(a, *self, offset, data@);
            lemma_hist_step(a, *self, offset, data@);
        }
        Ok(())
    }

    /// `on_crypto` for data reaching the contiguous end: the frame goes into the store, and the
    /// contiguous end moves to the end of the run there (`run_end_w`); no byte is copied out. What
    /// stays out of order is a subset of what was, so nothing is refused (`lemma_fill_post`). The
    /// walk meets at most `d/K + 133` chunks (split from `on_crypto` for the rlimit).
    #[verifier::spinoff_prover]
    fn on_fill(&mut self, offset: u64, data: &[u8])
        requires
            old(self).wf(),
            offset + data@.len() <= VARINT_MAX,
            offset <= old(self).contig < offset + data@.len(),
        ensures
            !crypto_allowed_err(*old(self), offset, data@.len(), CRYPTO_BUFFER_EXCEEDED),
            stepped(*final(self), *old(self), offset, data@),
    {
        hide(rfc_received);
        hide(rfc_contiguous);
        let ghost a = *self;
        self.st.insert(self.contig, offset, data);
        let (r, Ghost(c)) = self.st.run_end_w(self.contig);
        let end = offset + data.len() as u64;
        self.contig = r;
        if end > self.hi {
            self.hi = end;
        }
        self.ins = Ghost(self.ins@.push((offset as nat, data@)));
        self.hist = Ghost(self.hist@.push((offset as nat, data@)));
        proof {
            lemma_fill_post(a, *self, offset, data@);
            lemma_hist_step(a, *self, offset, data@);
            // The walk's cost: `[contig, r)` is held and spans at most `d + MAX_CRYPTO_BUFFER`.
            self.st.lemma_chunks_in_held(a.contig as nat, r as nat);
            lemma_walk_chunks((r - a.contig) as nat, data@.len());
            assert(c <= c_re1() * (self.st.tree_ht() + 1) + c_re2() * (data@.len() / (K as nat) + 133));
        }
    }

    /// Moves `min(max, unread)` in-order bytes into the empty `out`, an exact buffer for them; returns its cost
    /// (`Frags::take_front_c`), linear in the bytes it may take.
    pub fn read(&mut self, max: u64, out: &mut CapVec<u8>) -> (r: Ghost<nat>)
        requires
            old(self).wf(),
            old(out).wf(),
            old(out)@.len() == 0,
            old(out).cap() >= crypto_take(*old(self), max),
        ensures
            final(self).wf(),
            final(out).wf(),
            final(out).cap() == old(out).cap(),
            final(self).base_spec() == old(self).base_spec() + crypto_take(*old(self), max),
            final(out)@ == rfc_prefix(
                rfc_received(old(self).inserted_frames()),
                old(self).base_spec() + crypto_take(*old(self), max),
            ).subrange(old(self).base_spec() as int, (old(self).base_spec() + crypto_take(*old(self), max)) as int),
            final(self).end_spec() == old(self).end_spec(),
            final(self).inserted_frames() == old(self).inserted_frames(),
            final(self).history() == old(self).history(),
            forall|p: nat| #[trigger] final(self).received(p) == old(self).received(p),
            final(self).held_spec() + crypto_take(*old(self), max) == old(self).held_spec(),
            final(self).td_nodes() == old(self).td_nodes(),
            r@ <= 18 * crypto_take(*old(self), max) + 5608,
    {
        proof {
            self.lemma_core();
        }
        let u = self.contig - self.base;
        let k = if max < u {
            max
        } else {
            u
        };
        let ghost a = *self;
        let (r, Ghost(c)) = self.st.take_front_c(self.base, k, out);
        proof {
            if r < a.base + k {
                assert(a.st.view().contains_key(r as nat));
            }
        }
        self.base = r;
        proof {
            let m = rfc_received(self.ins@);
            assert forall|i: int| 0 <= i < k implies #[trigger] out@[i] == m[(a.base + i) as nat] by {
                assert(a.st.view().contains_key((a.base + i) as nat));
            }
            assert(out@ =~= rfc_prefix(m, (a.base + k) as nat).subrange(a.base as int, a.base + k));
            self.st.lemma_wf();
            a.st.lemma_wf();
            self.st.lemma_nodes_le_held();
            a.st.lemma_nodes_le_held();
            lemma_store(self.st.view().dom(), m, r as nat, a.contig as nat);
            lemma_store(a.st.view().dom(), m, a.base as nat, a.contig as nat);
            if self.end_spec() > 0 {
                assert(a.received((a.end_spec() - 1) as nat));
            }
            assert(self.st.wf());
            assert(self.base <= self.contig <= self.hi <= VARINT_MAX);
            assert(forall|p: nat| #[trigger] self.st.view().contains_key(p) <==> m.contains_key(p) && p >= self.base);
            assert(forall|p: nat| #[trigger] self.st.view().contains_key(p) ==> self.st.view()[p] == m[p]);
            assert(self.core());
            assert(self.hist == a.hist && self.ins == a.ins && self.hi == a.hi);
            assert(forall|p: nat| #[trigger] self.received(p) == a.received(p));
        }
        Ghost(c)
    }

    /// The unread in-order bytes.
    pub fn unread(&self) -> (r: u64)
        requires
            self.wf(),
        ensures
            r == crypto_contiguous(*self) - self.base_spec(),
    {
        self.contig - self.base
    }

    /// The teardown slot holds a retired store.
    pub fn has_td(&self) -> (r: bool)
        ensures
            r == (self.td_nodes() > 0),
    {
        self.td.is_some()
    }

    /// Frees part of the teardown slot: at least one node while any remain, at most `B_PUMP` units of work.
    pub fn free_some(&mut self) -> (r: Ghost<nat>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            old(self).td_nodes() > 0 ==> final(self).td_nodes() < old(self).td_nodes(),
            final(self).td_nodes() <= old(self).td_nodes(),
            r@ <= B_PUMP,
            final(self).base_spec() == old(self).base_spec(),
            final(self).buf_len_spec() == old(self).buf_len_spec(),
            final(self).inserted_frames() == old(self).inserted_frames(),
            final(self).history() == old(self).history(),
            final(self).held_spec() == old(self).held_spec(),
            crypto_contiguous(*final(self)) == crypto_contiguous(*old(self)),
            forall|p: nat| #[trigger] final(self).received(p) == old(self).received(p),
    {
        proof {
            assert(crate::avl::c_pop() * 127 + 2 <= B_PUMP);
        }
        let ghost a = *self;
        let Ghost(c) = crate::avl::pop_some(&mut self.td, B_PUMP);
        proof {
            assert(self.st == a.st);
            assert(crate::avl::wf(self.td));
            assert forall|i: int| 0 <= i < crate::avl::seq(self.td).len() implies #[trigger] crate::avl::seq(self.td)[i].0
                < self.base by {
                let n = crate::avl::seq(a.td).len() - crate::avl::seq(self.td).len();
                assert(crate::avl::seq(self.td)[i] == crate::avl::seq(a.td)[i + n]);
            }
            assert(self.core());
            assert(self.hist == a.hist && self.ins == a.ins && self.base == a.base && self.hi == a.hi);
            assert(self.end_spec() == a.end_spec());
            assert(forall|p: nat| #[trigger] self.received(p) == a.received(p));
            assert(self.wf());
        }
        Ghost(c)
    }

    /// The read offset.
    pub fn start(&self) -> (r: u64)
        ensures
            r == self.base_spec(),
    {
        self.base
    }

    /// The end of the received data: the read offset plus the buffered span.
    pub fn end(&self) -> (r: u64)
        requires
            self.wf(),
        ensures
            r == self.base_spec() + self.buf_len_spec(),
    {
        proof {
            self.lemma_core();
        }
        self.hi
    }
}

/// The positions held and the teardown slots' nodes of three streams, a connection's levels: what `pump_backlog`
/// works off. Closed, so the connection's frames carry it as one term.
pub closed spec fn backlog3(i: CryptoStream, h: CryptoStream, o: CryptoStream) -> nat {
    i.held_spec() + i.td_nodes() + h.held_spec() + h.td_nodes() + o.held_spec() + o.td_nodes()
}

pub proof fn lemma_backlog3(i: CryptoStream, h: CryptoStream, o: CryptoStream)
    ensures
        backlog3(i, h, o) == i.held_spec() + i.td_nodes() + h.held_spec() + h.td_nodes() + o.held_spec() + o.td_nodes(),
{
}

/// A store holding exactly `m`'s positions at or past `b`, all of `[b, c)` and not `c`: the in-order run then
/// the positions past `c`, a run of its own.
proof fn lemma_store(v: Set<nat>, m: Map<nat, u8>, b: nat, c: nat)
    requires
        b <= c,
        forall|p: nat| #[trigger] v.contains(p) <==> m.contains_key(p) && p >= b,
        forall|k: nat| k < c ==> #[trigger] m.contains_key(k),
        !m.contains_key(c),
    ensures
        above(v, c) == above(m.dom(), c),
        v.len() == (c - b) + above(m.dom(), c).len(),
        runs(v) == runs(above(m.dom(), c)) + (if b < c { 1nat } else { 0nat }),
{
    let a = above(m.dom(), c);
    let r = Set::<nat>::range(b, c);
    assert(above(v, c) =~= a);
    assert(v =~= r + a);
    assert(r.disjoint(a));
    vstd::set_lib::lemma_set_disjoint_lens(r, a);
    let sb = if b < c {
        Set::<nat>::empty().insert(b)
    } else {
        Set::<nat>::empty()
    };
    assert(starts(v) =~= starts(a) + sb) by {
        assert forall|p: nat| #[trigger] starts(v).contains(p) implies (starts(a) + sb).contains(p) by {
            if p < c {
                if p > b {
                    assert(v.contains((p - 1) as nat));
                }
            } else {
                assert(p > c);
                assert(a.contains(p));
                if p > 0 && a.contains((p - 1) as nat) {
                    assert(v.contains((p - 1) as nat));
                }
            }
        }
        assert forall|p: nat| #[trigger] (starts(a) + sb).contains(p) implies starts(v).contains(p) by {
            if starts(a).contains(p) {
                assert(p > c);
                if v.contains((p - 1) as nat) {
                    assert(p - 1 != c);
                    assert(a.contains((p - 1) as nat));
                }
            } else {
                assert(p == b);
                if p > 0 && v.contains((p - 1) as nat) {
                    assert(p - 1 >= b);
                }
            }
        }
    }
    assert(starts(a).disjoint(sb));
    vstd::set_lib::lemma_set_disjoint_lens(starts(a), sb);
}

/// Positions held in `[b, h)` are at most `h - b`.
proof fn lemma_held_span(v: Set<nat>, b: nat, h: nat)
    requires
        b <= h,
        forall|p: nat| #[trigger] v.contains(p) ==> b <= p < h,
    ensures
        v.len() <= h - b,
{
    assert(v.subset_of(Set::<nat>::range(b, h)));
    vstd::set_lib::lemma_len_subset(v, Set::<nat>::range(b, h));
}

/// `on_fill`'s span: `[contig, r)` holds at most `2 + (d + MAX_CRYPTO_BUFFER)/K` chunk starts, at most `d/K + 130`.
proof fn lemma_walk_chunks(w: nat, d: nat)
    requires
        w <= d + MAX_CRYPTO_BUFFER,
    ensures
        2 + w / (K as nat) + 1 <= d / (K as nat) + 133,
{
    vstd::arithmetic::div_mod::lemma_div_is_ordered(w as int, (d + MAX_CRYPTO_BUFFER) as int, K as int);
    vstd::arithmetic::div_mod::lemma_hoist_over_denominator(d as int, 128, K as nat);
}

/// `b` is `a` after taking `d` at `off`: `wf`, the insertion recorded, the read offset kept, the
/// record of what arrived and its end only grown, at most one position held per byte, the slot kept.
spec fn stepped(b: CryptoStream, a: CryptoStream, off: u64, d: Seq<u8>) -> bool {
    &&& b.wf()
    &&& b.ins@ == a.ins@.push((off as nat, d))
    &&& b.base == a.base
    &&& forall|p: nat| #[trigger] a.received(p) ==> b.received(p)
    &&& b.end_spec() >= a.end_spec()
    &&& b.st.held() <= a.st.held() + d.len()
    &&& b.td == a.td
}

/// `d` at `off` holds no byte not already received: the received bytes, and so the out-of-order
/// ones, stay as they are, and nothing is refused.
proof fn lemma_same(a: CryptoStream, off: u64, d: Seq<u8>)
    requires
        a.wf(),
        d.len() == 0 || off + d.len() <= a.contig,
    ensures
        rfc_received(a.ins@.push((off as nat, d))) == rfc_received(a.ins@),
        forall|c: u64| !#[trigger] crypto_allowed_err(a, off, d.len(), c),
{
    let m = rfc_received(a.ins@);
    let m2 = rfc_received(a.ins@.push((off as nat, d)));
    a.lemma_core();
    lemma_received_push(a.ins@, off as nat, d);
    assert(m2 =~= m);
    if d.len() > 0 {
        lemma_ooo_bytes_free(a, off, d);
        assert(ooo_received(a, off, d) =~= above(m.dom(), a.contig as nat));
    }
}

/// The out-of-order positions once `d` at `off` (all past the contiguous end) is in: the store's after `put`, less
/// the in-order run `[base, contig)`, which therefore counts `contig − base` positions and one run if not empty.
proof fn lemma_ooo_count(a: CryptoStream, off: u64, d: Seq<u8>)
    requires
        a.wf(),
        off > a.contig,
        d.len() > 0,
    ensures
        rfc_contiguous(rfc_received(a.ins@.push((off as nat, d)))) == a.contig,
        put(a.st.view(), a.contig as nat, off as nat, d).dom().len() == (a.contig - a.base) + ooo_held(
            a,
            off,
            Seq::new(d.len(), |_i: int| 0u8),
        ),
        runs(put(a.st.view(), a.contig as nat, off as nat, d).dom()) == ooo_runs(a, off, Seq::new(d.len(), |_i: int| 0u8))
            + (if a.base < a.contig { 1nat } else { 0nat }),
        ooo_received(a, off, Seq::new(d.len(), |_i: int| 0u8)) == above(
            rfc_received(a.ins@.push((off as nat, d))).dom(),
            a.contig as nat,
        ),
{
    hide(put);
    hide(rfc_received);
    hide(rfc_contiguous);
    let m2 = rfc_received(a.ins@.push((off as nat, d)));
    let pm = put(a.st.view(), a.contig as nat, off as nat, d);
    lemma_put_dom(a, off, d);
    lemma_store(pm.dom(), m2, a.base as nat, a.contig as nat);
    lemma_ooo_bytes_free(a, off, d);
    assert(ooo_received(a, off, d) =~= above(m2.dom(), a.contig as nat));
}

/// `lemma_ooo_count`'s store after `put`: the received bytes at or past `base`, around the unchanged contiguous end.
proof fn lemma_put_dom(a: CryptoStream, off: u64, d: Seq<u8>)
    requires
        a.wf(),
        off > a.contig,
        d.len() > 0,
    ensures
        rfc_contiguous(rfc_received(a.ins@.push((off as nat, d)))) == a.contig,
        forall|p: nat| #[trigger] put(a.st.view(), a.contig as nat, off as nat, d).dom().contains(p)
            <==> rfc_received(a.ins@.push((off as nat, d))).contains_key(p) && p >= a.base,
        forall|k: nat| k < a.contig ==> #[trigger] rfc_received(a.ins@.push((off as nat, d))).contains_key(k),
        !rfc_received(a.ins@.push((off as nat, d))).contains_key(a.contig as nat),
{
    let m2 = rfc_received(a.ins@.push((off as nat, d)));
    let pm = put(a.st.view(), a.contig as nat, off as nat, d);
    a.lemma_core();
    lemma_received_push(a.ins@, off as nat, d);
    lemma_contiguous_is(m2, a.contig as nat);
    assert forall|p: nat| #[trigger] pm.dom().contains(p) <==> m2.contains_key(p) && p >= a.base by {
        if m2.contains_key(p) && p >= a.base && !(off <= p < off + d.len()) {
            assert(a.st.view().contains_key(p));
        }
    }
}

/// `on_ooo`'s state after taking out-of-order `d` at `off` is `core`.
proof fn lemma_ooo_post(a: CryptoStream, b: CryptoStream, off: u64, d: Seq<u8>)
    requires
        a.wf(),
        off > a.contig,
        d.len() > 0,
        off + d.len() <= VARINT_MAX,
        b.st.wf(),
        b.st.view() == put(a.st.view(), a.contig as nat, off as nat, d),
        b.st.held() == put(a.st.view(), a.contig as nat, off as nat, d).dom().len(),
        ooo_held(a, off, Seq::new(d.len(), |_i: int| 0u8)) <= MAX_CRYPTO_BUFFER,
        ooo_runs(a, off, Seq::new(d.len(), |_i: int| 0u8)) <= MAX_CRYPTO_RANGES,
        b.base == a.base,
        b.contig == a.contig,
        b.hi == (if off + d.len() > a.hi { (off + d.len()) as u64 } else { a.hi }),
        b.ins@ == a.ins@.push((off as nat, d)),
        b.td == a.td,
    ensures
        b.core(),
        b.st.held() <= a.st.held() + d.len(),
{
    let pm = put(a.st.view(), a.contig as nat, off as nat, d);
    lemma_ooo_count(a, off, d);
    lemma_ooo_views(a, b, off, d);
    assert(pm.dom() =~= a.st.view().dom() + Set::<nat>::range(off as nat, (off + d.len()) as nat));
    vstd::set_lib::lemma_len_union(a.st.view().dom(), Set::<nat>::range(off as nat, (off + d.len()) as nat));
    a.st.lemma_wf();
}

/// `lemma_ooo_post`'s view part: the store holds the received bytes at or past `base`, `hi` is their end.
proof fn lemma_ooo_views(a: CryptoStream, b: CryptoStream, off: u64, d: Seq<u8>)
    requires
        a.wf(),
        off > a.contig,
        d.len() > 0,
        off + d.len() <= VARINT_MAX,
        b.st.view() == put(a.st.view(), a.contig as nat, off as nat, d),
        b.base == a.base,
        b.contig == a.contig,
        b.hi == (if off + d.len() > a.hi { (off + d.len()) as u64 } else { a.hi }),
        b.ins@ == a.ins@.push((off as nat, d)),
    ensures
        forall|k: nat| #[trigger] rfc_received(b.ins@).contains_key(k) ==> k < b.hi,
        b.hi > b.contig ==> rfc_received(b.ins@).contains_key((b.hi - 1) as nat),
        forall|p: nat| #[trigger] b.st.view().contains_key(p) <==> rfc_received(b.ins@).contains_key(p) && p >= b.base,
        forall|p: nat| #[trigger] b.st.view().contains_key(p) ==> b.st.view()[p] == rfc_received(b.ins@)[p],
{
    let m = rfc_received(a.ins@);
    let m2 = rfc_received(b.ins@);
    a.lemma_core();
    lemma_received_push(a.ins@, off as nat, d);
    if b.hi > b.contig && !(off <= b.hi - 1 < off + d.len()) {
        assert(m.contains_key((a.hi - 1) as nat));
    }
    assert forall|p: nat| #[trigger] b.st.view().contains_key(p) <==> m2.contains_key(p) && p >= b.base by {
        if m2.contains_key(p) && p >= b.base && !(off <= p < off + d.len()) {
            assert(a.st.view().contains_key(p));
        }
    }
    assert forall|p: nat| #[trigger] b.st.view().contains_key(p) implies b.st.view()[p] == m2[p] by {
        if a.st.view().contains_key(p) {
            assert(m.contains_key(p));
        } else if m.contains_key(p) {
            assert(p < a.base);
        }
    }
}

/// After `insert` and `run_end_w` (`r` the new contiguous end), the state is `core`: what stays out of order is a
/// subset of what was, cut at `r`, so nothing is refused; `[contig, r)` spans at most `d + MAX_CRYPTO_BUFFER`.
proof fn lemma_fill_post(a: CryptoStream, b: CryptoStream, off: u64, d: Seq<u8>)
    requires
        a.wf(),
        off <= a.contig < off + d.len(),
        off + d.len() <= VARINT_MAX,
        b.st.wf(),
        b.st.view() == put(a.st.view(), a.contig as nat, off as nat, d),
        b.st.held() == put(a.st.view(), a.contig as nat, off as nat, d).dom().len(),
        a.contig <= b.contig <= VARINT_MAX,
        forall|k: nat| a.contig <= k < b.contig ==> #[trigger] b.st.view().contains_key(k),
        !b.st.view().contains_key(b.contig as nat),
        b.base == a.base,
        b.hi == (if off + d.len() > a.hi { (off + d.len()) as u64 } else { a.hi }),
        b.ins@ == a.ins@.push((off as nat, d)),
        b.td == a.td,
    ensures
        b.core(),
        b.st.held() <= a.st.held() + d.len(),
        b.contig - a.contig <= d.len() + MAX_CRYPTO_BUFFER,
        forall|c: u64| !#[trigger] crypto_allowed_err(a, off, d.len(), c),
{
    hide(rfc_received);
    hide(rfc_contiguous);
    let m = rfc_received(a.ins@);
    let m2 = rfc_received(b.ins@);
    let r = b.contig as nat;
    let e = (off + d.len()) as nat;
    a.lemma_core();
    lemma_received_push(a.ins@, off as nat, d);
    lemma_fill_core(a, b, off, d);
    // What stays out of order is what was, cut at `r`.
    let oa = above(m.dom(), a.contig as nat);
    let ob = above(m2.dom(), r);
    assert forall|k: nat| #[trigger] ob.contains(k) <==> oa.contains(k) && k > r by {
        if ob.contains(k) && !m.contains_key(k) {
            assert(off <= k < e);
            assert(b.st.view().contains_key(k));
        }
    }
    assert(ob.subset_of(oa));
    vstd::set_lib::lemma_len_subset(ob, oa);
    lemma_runs_cut(oa, ob, r);
    // `[contig, r)` lies in the frame or the old out-of-order bytes.
    let span = Set::<nat>::range(a.contig as nat, r);
    let fr = Set::<nat>::range(off as nat, e);
    assert(span.subset_of(fr + oa)) by {
        assert forall|k: nat| #[trigger] span.contains(k) implies (fr + oa).contains(k) by {
            assert(b.st.view().contains_key(k));
            if !(off <= k < e) {
                assert(a.st.view().contains_key(k));
                assert(k != a.contig);
            }
        }
    }
    vstd::set_lib::lemma_len_subset(span, fr + oa);
    vstd::set_lib::lemma_len_union(fr, oa);
    // At most one position held per byte.
    let pm = put(a.st.view(), a.contig as nat, off as nat, d);
    assert(pm.dom().subset_of(a.st.view().dom() + fr));
    vstd::set_lib::lemma_len_subset(pm.dom(), a.st.view().dom() + fr);
    vstd::set_lib::lemma_len_union(a.st.view().dom(), fr);
    a.st.lemma_wf();
    // Nothing is refused.
    lemma_ooo_bytes_free(a, off, d);
    assert(ooo_received(a, off, d) =~= ob);
}

/// `lemma_fill_post`'s `core` part: the store holds `m2` at or past `base`, `r` is `m2`'s contiguous end, `hi` its
/// end.
proof fn lemma_fill_core(a: CryptoStream, b: CryptoStream, off: u64, d: Seq<u8>)
    requires
        a.wf(),
        off <= a.contig < off + d.len(),
        off + d.len() <= VARINT_MAX,
        b.st.wf(),
        b.st.view() == put(a.st.view(), a.contig as nat, off as nat, d),
        a.contig <= b.contig <= VARINT_MAX,
        forall|k: nat| a.contig <= k < b.contig ==> #[trigger] b.st.view().contains_key(k),
        !b.st.view().contains_key(b.contig as nat),
        b.base == a.base,
        b.hi == (if off + d.len() > a.hi { (off + d.len()) as u64 } else { a.hi }),
        b.ins@ == a.ins@.push((off as nat, d)),
        b.td == a.td,
    ensures
        rfc_contiguous(rfc_received(b.ins@)) == b.contig,
        b.contig >= off + d.len(),
        b.contig <= b.hi,
        forall|k: nat| #[trigger] rfc_received(b.ins@).contains_key(k) ==> k < b.hi,
        b.hi > b.contig ==> rfc_received(b.ins@).contains_key((b.hi - 1) as nat),
        forall|p: nat| #[trigger] b.st.view().contains_key(p) <==> rfc_received(b.ins@).contains_key(p) && p >= b.base,
        forall|p: nat| #[trigger] b.st.view().contains_key(p) ==> b.st.view()[p] == rfc_received(b.ins@)[p],
{
    hide(rfc_received);
    hide(rfc_contiguous);
    let m = rfc_received(a.ins@);
    let m2 = rfc_received(b.ins@);
    let r = b.contig as nat;
    let e = (off + d.len()) as nat;
    a.lemma_core();
    lemma_received_push(a.ins@, off as nat, d);
    assert forall|p: nat| #[trigger] b.st.view().contains_key(p) <==> m2.contains_key(p) && p >= b.base by {
        if m2.contains_key(p) && p >= b.base && !(off <= p < e) {
            assert(a.st.view().contains_key(p));
        }
        if m2.contains_key(p) && p >= b.base && off <= p < a.contig {
            assert(m.contains_key(p));
            assert(a.st.view().contains_key(p));
        }
    }
    assert forall|p: nat| #[trigger] b.st.view().contains_key(p) implies b.st.view()[p] == m2[p] by {
        if a.st.view().contains_key(p) {
            assert(m.contains_key(p));
        } else if m.contains_key(p) {
            assert(p < a.base);
        }
    }
    if r < e {
        assert(b.st.view().contains_key(r));
    }
    assert forall|k: nat| k < r implies #[trigger] m2.contains_key(k) by {
        if k >= a.contig {
            assert(b.st.view().contains_key(k));
        }
    }
    lemma_contiguous_is(m2, r);
    if r > b.hi {
        assert(b.st.view().contains_key(b.hi as nat));
    }
    if b.hi > b.contig && !(off <= b.hi - 1 < e) {
        assert(m.contains_key((a.hi - 1) as nat));
    }
}

/// An insertion of `d` at `off` that `b` holds keeps the record of what arrived: the byte before
/// the new end lies in `d`, or the end did not move.
proof fn lemma_hist_step(a: CryptoStream, b: CryptoStream, off: u64, d: Seq<u8>)
    requires
        a.wf(),
        b.core(),
        b.ins@ == a.ins@.push((off as nat, d)),
        b.hist@ == a.hist@.push((off as nat, d)),
        b.base == a.base,
    ensures
        b.wf(),
        forall|p: nat| #[trigger] a.received(p) ==> b.received(p),
        b.end_spec() >= a.end_spec(),
{
    a.lemma_core();
    b.lemma_core();
    lemma_received_push(a.ins@, off as nat, d);
    lemma_received_push(a.hist@, off as nat, d);
    if a.end_spec() > 0 {
        assert(rfc_received(b.ins@).contains_key((a.hi - 1) as nat));
    }
    let e = b.end_spec();
    if e > 0 && !(off <= e - 1 < off + d.len()) {
        assert(rfc_received(b.ins@).contains_key((e - 1) as nat));
        assert(rfc_received(a.ins@).contains_key((e - 1) as nat));
        assert(e == a.end_spec());
    }
    assert forall|p: nat| #[trigger] b.received(p) implies rfc_received(b.ins@).contains_key(p) by {
        if !(off <= p < off + d.len()) {
            assert(a.received(p));
        }
    }
}

} // verus!

impl CryptoStream {
    /// Test support: the allocated capacities of the store and of the teardown slot. Verus models `Vec` length, not
    /// capacity (TRUSTED.md).
    #[doc(hidden)]
    pub fn capacities(&self) -> (usize, usize) {
        fn go(t: &Tree<CapVec<u8>>) -> usize {
            match t {
                None => 0,
                Some(b) => std::mem::size_of::<crate::avl::Node<CapVec<u8>>>() + b.val.capacity() + go(&b.left) + go(
                    &b.right,
                ),
            }
        }
        (self.st.capacity(), go(&self.td))
    }
}

const _: () = assert!(MAX_CRYPTO_BUFFER >= 4096);
