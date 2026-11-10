//! CRYPTO streams (RFC 9000 §7.5, §19.6): per encryption level, the unread in-order bytes in one
//! buffer and the out-of-order bytes in a sparse store (`Frags`), so memory follows the bytes held,
//! not the offsets they span. CRYPTO data has no flow control (§4).
use vstd::prelude::*;
use crate::codes::*;
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

/// The CRYPTO stream of one encryption level.
pub struct CryptoStream {
    /// The unread in-order bytes, `[base, contig)`.
    buf: Vec<u8>,
    /// The read offset.
    base: u64,
    /// `crypto_contiguous`, kept so a frame costs O(1) plus the bytes it touches.
    contig: u64,
    /// The out-of-order bytes: those received past `contig`.
    ooo: Frags,
    /// Every insertion since the last `restart`, which records the bytes below its base (read,
    /// but not data received anew) as zeros.
    ins: Ghost<Seq<(nat, Seq<u8>)>>,
    /// Every insertion `on_crypto` made, kept across `restart`: what was really received.
    hist: Ghost<Seq<(nat, Seq<u8>)>>,
}

impl CryptoStream {
    /// The insertions since the last `restart`, its record of the bytes below its base first.
    pub closed spec fn inserted_frames(&self) -> Seq<(nat, Seq<u8>)> {
        self.ins@
    }

    /// The read offset.
    pub closed spec fn base_spec(&self) -> nat {
        self.base as nat
    }

    /// From the read offset to the end of the received data.
    pub closed spec fn buf_len_spec(&self) -> nat {
        (self.hi() - self.base) as nat
    }

    pub closed spec fn history(&self) -> Seq<(nat, Seq<u8>)> {
        self.hist@
    }

    /// Byte `p` arrived in a CRYPTO frame. `inserted_frames()` also holds `restart`'s record of the bytes
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

    /// The end of the last out-of-order byte held, else the contiguous end.
    spec fn hi(&self) -> nat {
        if self.ooo.count() > 0 {
            self.ooo.hi_spec()
        } else {
            self.contig as nat
        }
    }

    /// The buffer holds the unread in-order bytes, `[base, contig)`; `ooo` holds the bytes
    /// received past `contig`, at most `MAX_CRYPTO_BUFFER` of them in at most
    /// `MAX_CRYPTO_RANGES` runs.
    spec fn core(&self) -> bool {
        let m = rfc_received(self.ins@);
        &&& self.ooo.wf()
        &&& self.base <= self.contig <= VARINT_MAX
        &&& self.contig as nat == rfc_contiguous(m)
        &&& self.buf@.len() == self.contig - self.base
        &&& forall|i: int| 0 <= i < self.buf@.len() ==> #[trigger] self.buf@[i] == m[(self.base + i) as nat]
        &&& forall|p: nat| #[trigger] self.ooo.view().contains_key(p) <==> m.contains_key(p) && p > self.contig
        &&& forall|p: nat| #[trigger] self.ooo.view().contains_key(p) ==> self.ooo.view()[p] == m[p]
        // The memory bound: the unread in-order bytes plus at most MAX_CRYPTO_BUFFER more, in at
        // most MAX_CRYPTO_RANGES fragments.
        &&& self.buf@.len() + self.ooo.held() <= (self.contig - self.base) + MAX_CRYPTO_BUFFER
        &&& self.ooo.count() <= MAX_CRYPTO_RANGES
    }

    /// `core`, and the record of what arrived: the byte before the end arrived, and every byte
    /// that arrived is in `inserted_frames()`.
    pub closed spec fn wf(&self) -> bool {
        &&& self.core()
        &&& self.end_spec() > 0 ==> self.received((self.end_spec() - 1) as nat)
        &&& forall|p: nat| #[trigger] self.received(p) ==> rfc_received(self.ins@).contains_key(p)
    }

    /// `core`'s consequences: the received bytes end at `hi`, and the byte before it was received.
    proof fn lemma_core(&self)
        requires
            self.core(),
        ensures
            self.base <= self.contig <= self.hi() <= VARINT_MAX,
            forall|k: nat| #[trigger] rfc_received(self.ins@).contains_key(k) ==> k < self.hi(),
            self.hi() > 0 ==> rfc_received(self.ins@).contains_key((self.hi() - 1) as nat),
            !rfc_received(self.ins@).contains_key(self.contig as nat),
            forall|k: nat| k < self.contig ==> #[trigger] rfc_received(self.ins@).contains_key(k),
            self.ooo.held() <= MAX_CRYPTO_BUFFER,
    {
        let m = rfc_received(self.ins@);
        self.ooo.lemma_wf();
        lemma_contiguous_exists(m);
        assert forall|k: nat| #[trigger] m.contains_key(k) implies k < self.hi() by {
            if k > self.contig {
                assert(self.ooo.view().contains_key(k));
            }
        }
        if self.ooo.count() > 0 {
            assert(self.ooo.view().contains_key((self.ooo.hi_spec() - 1) as nat));
        } else if self.contig > 0 {
            assert(m.contains_key((self.contig - 1) as nat));
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
    {
        self.lemma_core();
    }

    pub fn new() -> (r: CryptoStream)
        ensures
            r.wf(),
            r.inserted_frames() == Seq::<(nat, Seq<u8>)>::empty(),
            r.base_spec() == 0,
            crypto_contiguous(r) == 0,
    {
        let r = CryptoStream {
            buf: Vec::new(),
            base: 0,
            contig: 0,
            ooo: Frags::new(),
            ins: Ghost(Seq::empty()),
            hist: Ghost(Seq::empty()),
        };
        proof {
            assert(rfc_received(r.ins@) =~= Map::<nat, u8>::empty());
            assert(rfc_received(r.hist@) =~= Map::<nat, u8>::empty());
            lemma_contiguous_is(rfc_received(r.ins@), 0);
            r.ooo.lemma_wf();
        }
        r
    }

    /// Nothing buffered, everything below the end read, and `history` kept: what an Initial
    /// discard leaves, for the end check of RFC 9001 §4.1.3.
    pub fn restart(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).base_spec() == old(self).end_spec(),
            final(self).buf_len_spec() == 0,
            final(self).history() == old(self).history(),
            forall|p: nat| #[trigger] final(self).received(p) == old(self).received(p),
            crypto_contiguous(*final(self)) == old(self).end_spec(),
    {
        proof {
            self.lemma_core();
        }
        let end = self.end();
        let ghost a = *self;
        let ghost d = Seq::new(end as nat, |_i: int| 0u8);
        self.buf = Vec::new();
        self.base = end;
        self.contig = end;
        self.ooo = Frags::new();
        self.ins = Ghost(Seq::<(nat, Seq<u8>)>::empty().push((0nat, d)));
        proof {
            let m = rfc_received(self.ins@);
            lemma_received_push(Seq::<(nat, Seq<u8>)>::empty(), 0, d);
            assert(rfc_received(Seq::<(nat, Seq<u8>)>::empty()) =~= Map::<nat, u8>::empty());
            lemma_contiguous_is(m, end as nat);
            self.ooo.lemma_wf();
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
    /// limits are checked before the bytes are taken (split from `on_crypto` for the rlimit).
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
        let ghost a = *self;
        let (h, c) = self.ooo.after_insert(self.contig, offset, data);
        proof {
            lemma_ooo_set(a, offset, data@);
        }
        if h > MAX_CRYPTO_BUFFER || c > MAX_CRYPTO_RANGES {
            //= https://www.rfc-editor.org/rfc/rfc9000#section-7.5
            //# If an endpoint does not expand its buffer, it MUST close
            //# the connection with a CRYPTO_BUFFER_EXCEEDED error code.
            return Err(CRYPTO_BUFFER_EXCEEDED);
        }
        self.ooo.insert(self.contig, offset, data);
        self.ins = Ghost(self.ins@.push((offset as nat, data@)));
        self.hist = Ghost(self.hist@.push((offset as nat, data@)));
        proof {
            lemma_ooo_post(a, *self, offset, data@);
            lemma_hist_step(a, *self, offset, data@);
        }
        Ok(())
    }

    /// `on_crypto` for data reaching the contiguous end: the run from there becomes in-order
    /// data, and what stays out of order is a subset of what was, so nothing is refused
    /// (`lemma_fill_post`; split from `on_crypto` for the rlimit).
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
        self.ooo.insert(self.contig, offset, data);
        let ghost mid = self.ooo;
        let r = self.ooo.take_front(self.contig, &mut self.buf);
        self.contig = r;
        proof {
            lemma_fill_post(a, mid, *self, offset, data@);
        }
        self.ins = Ghost(self.ins@.push((offset as nat, data@)));
        self.hist = Ghost(self.hist@.push((offset as nat, data@)));
        proof {
            lemma_fill_core(a, mid, *self, offset, data@);
            lemma_hist_step(a, *self, offset, data@);
        }
    }

    /// Appends the newly contiguous CRYPTO bytes to `out`.
    pub fn read(&mut self, out: &mut Vec<u8>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).inserted_frames() == old(self).inserted_frames(),
            forall|p: nat| #[trigger] final(self).received(p) == old(self).received(p),
            final(self).base_spec() == rfc_contiguous(rfc_received(old(self).inserted_frames())),
            final(self).base_spec() + final(self).buf_len_spec() == old(self).base_spec() + old(
                self,
            ).buf_len_spec(),
            final(out)@ == old(out)@ + rfc_prefix(
                rfc_received(old(self).inserted_frames()),
                final(self).base_spec(),
            ).subrange(old(self).base_spec() as int, final(self).base_spec() as int),
    {
        proof {
            self.lemma_core();
        }
        let ghost b = self.buf@;
        out.append(&mut self.buf);
        // A fresh `Vec`: drained space must not keep its allocation.
        self.buf = Vec::new();
        self.base = self.contig;
        proof {
            let m = rfc_received(self.ins@);
            assert(b =~= rfc_prefix(m, self.contig as nat).subrange(old(self).base as int, self.contig as int));
            assert(self.end_spec() == old(self).end_spec());
            assert(self.core());
            assert(self.hist == old(self).hist);
            if self.end_spec() > 0 {
                assert(old(self).received((old(self).end_spec() - 1) as nat));
            }
            assert forall|p: nat| #[trigger] self.received(p) implies m.contains_key(p) by {
                assert(old(self).received(p));
            }
        }
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
        if self.ooo.count() > 0 {
            self.ooo.hi()
        } else {
            self.contig
        }
    }
}

/// `b` is `a` after taking `d` at `off`: `wf`, the insertion recorded, the read offset kept, and
/// the record of what arrived and its end only grown.
spec fn stepped(b: CryptoStream, a: CryptoStream, off: u64, d: Seq<u8>) -> bool {
    &&& b.wf()
    &&& b.ins@ == a.ins@.push((off as nat, d))
    &&& b.base == a.base
    &&& forall|p: nat| #[trigger] a.received(p) ==> b.received(p)
    &&& b.end_spec() >= a.end_spec()
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
        assert(ooo_received(a, off, d) =~= a.ooo.view().dom());
        a.ooo.lemma_wf();
    }
}

/// `d` at `off`, all past the contiguous end, leaves it where it is: the out-of-order bytes are
/// `put`'s.
proof fn lemma_ooo_set(a: CryptoStream, off: u64, d: Seq<u8>)
    requires
        a.wf(),
        off > a.contig,
        d.len() > 0,
    ensures
        rfc_contiguous(rfc_received(a.ins@.push((off as nat, d)))) == a.contig,
        ooo_received(a, off, Seq::new(d.len(), |_i: int| 0u8)) == put(a.ooo.view(), a.contig as nat, off as nat, d).dom(),
{
    let m = rfc_received(a.ins@);
    let m2 = rfc_received(a.ins@.push((off as nat, d)));
    a.lemma_core();
    lemma_received_push(a.ins@, off as nat, d);
    lemma_contiguous_is(m2, a.contig as nat);
    lemma_ooo_bytes_free(a, off, d);
    assert(ooo_received(a, off, d) =~= put(a.ooo.view(), a.contig as nat, off as nat, d).dom());
}

/// `put`'s out-of-order bytes after `d` at `off` are the received ones, at or past the old
/// contiguous end.
proof fn lemma_put_bytes(a: CryptoStream, off: u64, d: Seq<u8>)
    requires
        a.wf(),
    ensures
        forall|k: nat| #[trigger] put(a.ooo.view(), a.contig as nat, off as nat, d).contains_key(k)
            ==> k >= a.contig && rfc_received(a.ins@.push((off as nat, d))).contains_key(k)
            && put(a.ooo.view(), a.contig as nat, off as nat, d)[k] == rfc_received(
            a.ins@.push((off as nat, d)),
        )[k],
{
    let pm = put(a.ooo.view(), a.contig as nat, off as nat, d);
    let m = rfc_received(a.ins@);
    let m2 = rfc_received(a.ins@.push((off as nat, d)));
    a.lemma_core();
    lemma_received_push(a.ins@, off as nat, d);
    assert forall|k: nat| #[trigger] pm.contains_key(k) implies k >= a.contig && m2.contains_key(k)
        && pm[k] == m2[k] by {
        if a.ooo.view().contains_key(k) {
            assert(m.contains_key(k));
            assert(m2.contains_key(k));
        } else {
            assert(off <= k < off + d.len());
            assert(m2.contains_key(k));
            if m.contains_key(k) && k > a.contig {
                assert(a.ooo.view().contains_key(k));
            }
        }
    }
}

/// `on_crypto`'s state after taking out-of-order `d` at `off` is `core`.
proof fn lemma_ooo_post(a: CryptoStream, b: CryptoStream, off: u64, d: Seq<u8>)
    requires
        a.wf(),
        off > a.contig,
        d.len() > 0,
        b.ooo.wf(),
        b.ooo.view() == put(a.ooo.view(), a.contig as nat, off as nat, d),
        b.ooo.held() == put(a.ooo.view(), a.contig as nat, off as nat, d).dom().len(),
        b.ooo.count() == runs(put(a.ooo.view(), a.contig as nat, off as nat, d).dom()),
        ooo_held(a, off, Seq::new(d.len(), |_i: int| 0u8)) <= MAX_CRYPTO_BUFFER,
        ooo_runs(a, off, Seq::new(d.len(), |_i: int| 0u8)) <= MAX_CRYPTO_RANGES,
        b.buf == a.buf,
        b.base == a.base,
        b.contig == a.contig,
        b.ins@ == a.ins@.push((off as nat, d)),
    ensures
        b.core(),
{
    let m = rfc_received(a.ins@);
    let m2 = rfc_received(b.ins@);
    a.lemma_core();
    lemma_ooo_set(a, off, d);
    lemma_put_bytes(a, off, d);
    lemma_received_push(a.ins@, off as nat, d);
    assert forall|i: int| 0 <= i < b.buf@.len() implies #[trigger] b.buf@[i] == m2[(b.base + i) as nat] by {
        assert(b.buf@[i] == a.buf@[i]);
        assert(m.contains_key((b.base + i) as nat));
        assert(m2.contains_key((b.base + i) as nat));
    }
    assert forall|p: nat| #[trigger] b.ooo.view().contains_key(p) implies b.ooo.view()[p] == m2[p] by {
        assert(put(a.ooo.view(), a.contig as nat, off as nat, d).contains_key(p));
    }
}

/// After `insert` and `take_front` (`mid` between them), what stays out of order is what was,
/// cut at the new contiguous end `b.contig`: no more bytes and no more runs, so nothing is refused.
proof fn lemma_fill_post(a: CryptoStream, mid: Frags, b: CryptoStream, off: u64, d: Seq<u8>)
    requires
        a.wf(),
        off <= a.contig < off + d.len(),
        mid.wf(),
        mid.view() == put(a.ooo.view(), a.contig as nat, off as nat, d),
        b.ooo.wf(),
        a.contig <= b.contig <= VARINT_MAX,
        forall|k: nat| a.contig <= k < b.contig ==> #[trigger] mid.view().contains_key(k),
        !mid.view().contains_key(b.contig as nat),
        forall|k: nat| #[trigger] b.ooo.view().contains_key(k) <==> mid.view().contains_key(k) && k > b.contig,
        forall|k: nat| #[trigger] b.ooo.view().contains_key(k) ==> b.ooo.view()[k] == mid.view()[k],
    ensures
        rfc_contiguous(rfc_received(a.ins@.push((off as nat, d)))) == b.contig,
        b.contig >= off + d.len(),
        forall|k: nat| #[trigger]
            b.ooo.view().contains_key(k) <==> rfc_received(a.ins@.push((off as nat, d))).contains_key(k) && k > b.contig,
        forall|k: nat| b.ooo.view().contains_key(k) ==> #[trigger] a.ooo.view().contains_key(k),
        b.ooo.held() <= a.ooo.held(),
        b.ooo.count() <= a.ooo.count(),
        forall|c: u64| !#[trigger] crypto_allowed_err(a, off, d.len(), c),
{
    hide(rfc_received);
    hide(rfc_contiguous);
    let m = rfc_received(a.ins@);
    let m2 = rfc_received(a.ins@.push((off as nat, d)));
    let r = b.contig as nat;
    let e = off + d.len();
    a.lemma_core();
    a.ooo.lemma_wf();
    b.ooo.lemma_wf();
    lemma_received_push(a.ins@, off as nat, d);
    if r < e {
        assert(mid.view().contains_key(r));
    }
    assert forall|k: nat| k < r implies #[trigger] m2.contains_key(k) by {
        if k >= a.contig {
            assert(mid.view().contains_key(k));
        }
    }
    if m2.contains_key(r) {
        if r > a.contig {
            if m.contains_key(r) {
                assert(a.ooo.view().contains_key(r));
            }
        }
    }
    lemma_contiguous_is(m2, r);
    assert(b.ooo.view().dom().subset_of(a.ooo.view().dom()));
    vstd::set_lib::lemma_len_subset(b.ooo.view().dom(), a.ooo.view().dom());
    lemma_runs_cut(a.ooo.view().dom(), b.ooo.view().dom(), r);
    lemma_ooo_bytes_free(a, off, d);
    assert(ooo_received(a, off, d) =~= b.ooo.view().dom());
}

/// `on_crypto`'s state after a frame reaching the contiguous end (`mid` between `insert` and
/// `take_front`) is `core`.
proof fn lemma_fill_core(a: CryptoStream, mid: Frags, b: CryptoStream, off: u64, d: Seq<u8>)
    requires
        a.wf(),
        off <= a.contig < off + d.len(),
        mid.view() == put(a.ooo.view(), a.contig as nat, off as nat, d),
        b.ooo.wf(),
        b.base == a.base,
        b.ins@ == a.ins@.push((off as nat, d)),
        rfc_contiguous(rfc_received(b.ins@)) == b.contig,
        a.contig <= b.contig <= VARINT_MAX,
        forall|k: nat| #[trigger]
            b.ooo.view().contains_key(k) <==> rfc_received(b.ins@).contains_key(k) && k > b.contig,
        forall|k: nat| #[trigger] b.ooo.view().contains_key(k) ==> mid.view().contains_key(k) && b.ooo.view()[k] == mid.view()[k],
        b.ooo.held() <= a.ooo.held(),
        b.ooo.count() <= a.ooo.count(),
        b.buf@ == a.buf@ + Seq::new((b.contig - a.contig) as nat, |i: int| mid.view()[(a.contig + i) as nat]),
        forall|k: nat| a.contig <= k < b.contig ==> #[trigger] mid.view().contains_key(k),
    ensures
        b.core(),
{
    hide(rfc_received);
    hide(rfc_contiguous);
    let m = rfc_received(a.ins@);
    let m2 = rfc_received(b.ins@);
    let pm = mid.view();
    lemma_put_bytes(a, off, d);
    lemma_fill_buf(a, mid, b.buf@, b.contig as nat, off, d);
    assert forall|p: nat| #[trigger] b.ooo.view().contains_key(p) implies b.ooo.view()[p] == m2[p] by {
        assert(pm.contains_key(p));
    }
}

/// The in-order buffer after a frame reaching the contiguous end holds the received bytes.
proof fn lemma_fill_buf(a: CryptoStream, mid: Frags, buf: Seq<u8>, r: nat, off: u64, d: Seq<u8>)
    requires
        a.wf(),
        mid.view() == put(a.ooo.view(), a.contig as nat, off as nat, d),
        a.contig <= r,
        buf == a.buf@ + Seq::new((r - a.contig) as nat, |i: int| mid.view()[(a.contig + i) as nat]),
        forall|k: nat| a.contig <= k < r ==> #[trigger] mid.view().contains_key(k),
    ensures
        forall|i: int| 0 <= i < buf.len() ==> #[trigger] buf[i] == rfc_received(a.ins@.push((off as nat, d)))[(a.base + i) as nat],
{
    hide(rfc_received);
    hide(rfc_contiguous);
    let m = rfc_received(a.ins@);
    let m2 = rfc_received(a.ins@.push((off as nat, d)));
    let pm = mid.view();
    a.lemma_core();
    lemma_put_bytes(a, off, d);
    lemma_received_push(a.ins@, off as nat, d);
    assert forall|i: int| 0 <= i < buf.len() implies #[trigger] buf[i] == m2[(a.base + i) as nat] by {
        if i < a.buf@.len() {
            assert(buf[i] == a.buf@[i]);
            assert(m.contains_key((a.base + i) as nat));
            assert(m2.contains_key((a.base + i) as nat));
        } else {
            let k = (a.contig + (i - a.buf@.len())) as nat;
            assert(buf[i] == pm[k]);
            assert(pm.contains_key(k));
        }
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
        assert(rfc_received(b.ins@).contains_key((a.hi() - 1) as nat));
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
    /// Test support: the allocated capacities of the in-order buffer and of the out-of-order
    /// store. Verus models `Vec` length, not capacity (TRUSTED.md).
    #[doc(hidden)]
    pub fn capacities(&self) -> (usize, usize) {
        (self.buf.capacity(), self.ooo.capacity())
    }
}

const _: () = assert!(MAX_CRYPTO_BUFFER >= 4096);
