//! The HTTP/3 server connection over QUIC: `Connection`'s stream events go to `H3Conn`, in order and
//! one call each, and `H3Conn`'s outputs go back to `Connection`'s streams.
//!
//! `H3Conn` emits whole writes and `stream_write` takes a prefix, so unaccepted bytes wait in a FIFO
//! with an offset. `send_response` is refused (`Busy`) while anything waits, so h3 never commits a
//! response that can't be buffered. h3's own answers (a 501 or 421) queue regardless, one per stream
//! at most; they leave the queue when the stream's sending part is reset, so the queue is bounded by
//! the bidi streams QUIC holds open.
//!
//! Caller obligations:
//! - `pump` after any change made through `conn_mut`, with the `poll_transmit` loop after it.
//! - Drain `app` after each call that fills it: its only bound is the stream windows per datagram.
use vstd::prelude::*;
use vstd::slice::slice_subrange;
use wire::varint::VARINT_MAX;

use h3::codes::*;
// Glob: the specs here exist only in ghost code, which a plain `cargo build` erases.
#[allow(unused_imports)]
use h3::conn::*;
use h3::limits::MIN_PEER_UNI_STREAMS;
use h3::message::Response;

use crate::conn::*;
use crate::datagram::*;
use crate::lifecycle::Phase;
#[allow(unused_imports)]
use crate::payload::PacketKind;
#[allow(unused_imports)]
use crate::recv_stream::*;

verus! {

/// What the application is told. `H3` carries only `Request`, `RequestBody` and `RequestEnd`.
pub enum AppEvent {
    H3(Output),
    /// The peer reset this request stream; any body seen so far was cut short.
    Aborted(u64),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SendError {
    /// Earlier output is still waiting for send-buffer room; h3 was not called.
    Busy,
    /// h3 refused the response (a stream it can't answer, or an invalid response).
    Rejected,
}

pub open spec fn app_ok(e: AppEvent) -> bool {
    match e {
        AppEvent::H3(o) => o is Request || o is RequestBody || o is RequestEnd,
        AppEvent::Aborted(_) => true,
    }
}

/// `a1` is `a0` and then events the application may see.
pub open spec fn app_grew(a0: Seq<AppEvent>, a1: Seq<AppEvent>) -> bool {
    &&& a0.len() <= a1.len()
    &&& forall|i: int| 0 <= i < a0.len() ==> a1[i] == #[trigger] a0[i]
    &&& forall|i: int| a0.len() <= i < a1.len() ==> app_ok(#[trigger] a1[i])
}

proof fn lemma_app_trans(a0: Seq<AppEvent>, a1: Seq<AppEvent>, a2: Seq<AppEvent>)
    requires
        app_grew(a0, a1),
        app_grew(a1, a2),
    ensures
        app_grew(a0, a2),
{
    assert forall|i: int| a0.len() <= i < a2.len() implies app_ok(#[trigger] a2[i]) by {
        if i < a1.len() {
            assert(a2[i] == a1[i]);
            assert(app_ok(a1[i]));
        }
    }
    assert forall|i: int| 0 <= i < a0.len() implies a2[i] == #[trigger] a0[i] by {
        assert(a1[i] == a0[i]);
        assert(a2[i] == a1[i]);
    }
}

/// The h3 method for this event was called, once, taking `h0` to `h1` and `o0` to `o1`.
pub open spec fn one_call(h0: H3Conn, h1: H3Conn, e: SpecStreamEvent, o0: Seq<Output>, o1: Seq<Output>) -> bool {
    match e {
        SpecStreamEvent::Data { id, data, fin } => {
            &&& step(h0, h1, o0, o1)
            &&& frame(h0, h1, Some(id))
            &&& !h0.closed() && id % 4 == 0 ==> req_call(h0, h1, id, data, fin, added(o0, o1))
            &&& !h0.closed() && id % 4 == 2 ==> uni_fed(h0, h1, id, data, fin, added(o0, o1))
        },
        SpecStreamEvent::Reset { id, .. } => {
            &&& step(h0, h1, o0, o1)
            &&& frame(h0, h1, Some(id))
            &&& !h0.closed() && id % 4 == 0 ==> added(o0, o1) == reset_outs(id, h0.req_state(id)) && !h1.req_known(id)
        },
        SpecStreamEvent::StopSending { id, .. } => {
            &&& step(h0, h1, o0, o1)
            &&& frame(h0, h1, Some(id))
            &&& !h0.closed() ==> !h1.req_respondable(id)
            &&& !h0.closed() && id == 3 ==> added(o0, o1) == seq![SpecOutput::CloseConnection { code: H3_CLOSED_CRITICAL_STREAM }]
        },
    }
}

/// `evs` were passed to h3 in order, each to exactly one method call, taking `h0` to `h1`.
pub open spec fn fed(h0: H3Conn, evs: Seq<SpecStreamEvent>, h1: H3Conn) -> bool
    decreases evs.len(),
{
    if evs.len() == 0 {
        h1 == h0
    } else {
        exists|hm: H3Conn, o0: Seq<Output>, o1: Seq<Output>|
            #[trigger] one_call(hm, h1, evs.last(), o0, o1) && fed(h0, evs.drop_last(), hm)
    }
}

struct Pending {
    id: u64,
    data: Vec<u8>,
    off: usize,
    fin: bool,
}

/// What of `p` is still to be written, if it is on stream `j`.
spec fn piece(p: Pending, j: u64) -> Seq<u8> {
    if p.id == j {
        p.data@.skip(p.off as int)
    } else {
        Seq::empty()
    }
}

spec fn tails(s: Seq<Pending>, j: u64) -> Seq<u8>
    decreases s.len(),
{
    if s.len() == 0 {
        Seq::empty()
    } else {
        tails(s.drop_last(), j) + piece(s.last(), j)
    }
}

spec fn offs_ok(s: Seq<Pending>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> (#[trigger] s[i]).off <= s[i].data@.len()
}

proof fn lemma_tails_push(s: Seq<Pending>, p: Pending, j: u64)
    ensures
        tails(s.push(p), j) == tails(s, j) + piece(p, j),
{
    assert(s.push(p).drop_last() =~= s);
}

proof fn lemma_tails_take(s: Seq<Pending>, i: int, j: u64)
    requires
        0 <= i < s.len(),
    ensures
        tails(s.take(i + 1), j) == tails(s.take(i), j) + piece(s[i], j),
{
    assert(s.take(i + 1) =~= s.take(i).push(s[i]));
    lemma_tails_push(s.take(i), s[i], j);
}

proof fn lemma_tails_head(s: Seq<Pending>, j: u64)
    requires
        s.len() > 0,
    ensures
        tails(s, j) == piece(s[0], j) + tails(s.remove(0), j),
    decreases s.len(),
{
    if s.len() == 1 {
        assert(s.remove(0) =~= Seq::<Pending>::empty());
        assert(s.drop_last() =~= Seq::<Pending>::empty());
        assert(tails(s, j) =~= piece(s[0], j) + Seq::<u8>::empty());
    } else {
        let d = s.drop_last();
        lemma_tails_head(d, j);
        assert(d.remove(0) =~= s.remove(0).drop_last());
        assert(s.remove(0).last() == s.last());
        assert(tails(s, j) =~= piece(s[0], j) + tails(s.remove(0), j));
    }
}

proof fn lemma_writes_take(s: Seq<Output>, i: int, j: u64)
    requires
        0 <= i < s.len(),
    ensures
        writes_on(outs_view(s.take(i + 1)), j) == writes_on(outs_view(s.take(i)), j) + write_of(s[i]@, j),
{
    let a = outs_view(s.take(i + 1));
    assert(a.drop_last() =~= outs_view(s.take(i)));
    assert(a.last() == s[i]@);
}

/// The bytes of one output on stream `j`.
spec fn write_of(o: SpecOutput, j: u64) -> Seq<u8> {
    match o {
        SpecOutput::StreamWrite { stream_id, data, .. } => if stream_id == j {
            data
        } else {
            Seq::empty()
        },
        _ => Seq::empty(),
    }
}

/// The codes h3 emits are its constants, but no contract of h3's says so.
fn wire_code(c: u64) -> (r: u64)
    ensures
        r <= VARINT_MAX,
{
    if c <= VARINT_MAX {
        c
    } else {
        H3_INTERNAL_ERROR
    }
}

/// `v` without the entries of stream `id`.
fn kept(v: Vec<Pending>, id: u64) -> (r: Vec<Pending>)
    requires
        offs_ok(v@),
    ensures
        offs_ok(r@),
        r@.len() <= v@.len(),
        tails(r@, id) == Seq::<u8>::empty(),
        forall|j: u64| j != id ==> #[trigger] tails(r@, j) == tails(v@, j),
{
    let ghost a = v@;
    let mut r: Vec<Pending> = Vec::new();
    proof {
        assert(tails(r@, id) =~= Seq::<u8>::empty());
    }
    for p in it: v
        invariant
            it.seq() == a,
            offs_ok(a),
            offs_ok(r@),
            r@.len() <= it.index(),
            tails(r@, id) == Seq::<u8>::empty(),
            forall|j: u64| j != id ==> #[trigger] tails(r@, j) == tails(a.take(it.index() as int), j),
    {
        let ghost i = it.index();
        let ghost r0 = r@;
        proof {
            assert(a[i] == p);
            assert(p.off <= p.data@.len());
        }
        if p.id != id {
            r.push(p);
        }
        proof {
            assert forall|j: u64| j != id implies #[trigger] tails(r@, j) == tails(a.take(i + 1), j) by {
                lemma_tails_take(a, i, j);
                assert(tails(r0, j) == tails(a.take(i), j));
                if a[i].id != id {
                    assert(r@ =~= r0.push(a[i]));
                    lemma_tails_push(r0, a[i], j);
                } else {
                    assert(piece(a[i], j) =~= Seq::<u8>::empty());
                    assert(tails(r@, j) =~= tails(a.take(i), j) + piece(a[i], j));
                }
            }
            if a[i].id != id {
                assert(r@ =~= r0.push(a[i]));
                lemma_tails_push(r0, a[i], id);
                assert(tails(r@, id) =~= Seq::<u8>::empty());
            }
        }
    }
    proof {
        assert(a.take(a.len() as int) =~= a);
    }
    r
}

/// A QUIC connection and the HTTP/3 connection on top of it.
pub struct H3Server {
    conn: Connection,
    h3: H3Conn,
    started: bool,
    pending: Vec<Pending>,
    /// Per stream, every byte h3 has emitted.
    emitted: Ghost<spec_fn(u64) -> Seq<u8>>,
    /// Per stream, every byte passed to `Connection::stream_write`.
    written: Ghost<spec_fn(u64) -> Seq<u8>>,
    /// The streams whose queue was purged.
    dropped: Ghost<Set<u64>>,
}

impl H3Server {
    pub closed spec fn wf(&self) -> bool {
        &&& self.conn.wf()
        &&& self.h3.wf()
        &&& offs_ok(self.pending@)
    }

    /// Every emitted byte of a stream with nothing dropped was written or is queued, in order.
    spec fn log_ok(&self) -> bool {
        forall|j: u64|
            !self.dropped@.contains(j) ==> (self.written@)(j) + #[trigger] tails(self.pending@, j) == (self.emitted@)(j)
    }

    /// The write history, kept apart from `wf` because it is ghost and spans calls.
    /// - `log_ok`;
    /// - stream 3's log is h3's own account of its control stream;
    /// - h3 is untouched until `started`, which `start` sets.
    pub closed spec fn history_ok(&self) -> bool {
        &&& self.log_ok()
        &&& (self.emitted@)(3) == self.h3.ctrl_bytes()
        &&& !self.started ==> !self.h3.closed() && self.h3.ctrl_bytes().len() == 0
    }

    pub closed spec fn conn_spec(&self) -> Connection {
        self.conn
    }

    pub closed spec fn h3_spec(&self) -> H3Conn {
        self.h3
    }

    pub closed spec fn started_spec(&self) -> bool {
        self.started
    }

    pub closed spec fn idle_spec(&self) -> bool {
        self.pending@.len() == 0
    }

    /// The bytes on stream `id` h3 has emitted.
    pub closed spec fn emitted(&self, id: u64) -> Seq<u8> {
        (self.emitted@)(id)
    }

    /// The bytes on stream `id` passed to `stream_write`.
    pub closed spec fn written(&self, id: u64) -> Seq<u8> {
        (self.written@)(id)
    }

    /// Stream `id`'s queue was purged: h3 reset the stream, the peer stopped it, or `stream_write`
    /// refused it.
    pub closed spec fn dropped(&self, id: u64) -> bool {
        self.dropped@.contains(id)
    }

    /// Per stream, what `stream_write` got is a prefix of what h3 emitted, unless entries were dropped.
    pub proof fn lemma_written_prefix(&self, id: u64)
        requires
            self.history_ok(),
            !self.dropped(id),
        ensures
            self.written(id).len() <= self.emitted(id).len(),
            self.emitted(id).take(self.written(id).len() as int) == self.written(id),
    {
        let w = (self.written@)(id);
        let t = tails(self.pending@, id);
        assert((self.emitted@)(id) == w + t);
        assert((w + t).take(w.len() as int) =~= w);
    }

    pub fn new(conn: Connection) -> (s: H3Server)
        requires
            conn.wf(),
        ensures
            s.wf(),
            s.history_ok(),
            s.conn_spec() == conn,
            !s.started_spec(),
            s.idle_spec(),
    {
        let h3 = H3Conn::new();
        let s = H3Server {
            conn,
            h3,
            started: false,
            pending: Vec::new(),
            emitted: Ghost(|j: u64| Seq::<u8>::empty()),
            written: Ghost(|j: u64| Seq::<u8>::empty()),
            dropped: Ghost(Set::empty()),
        };
        proof {
            assert forall|j: u64| !s.dropped@.contains(j) implies (s.written@)(j) + #[trigger] tails(s.pending@, j)
                == (s.emitted@)(j) by {
                assert(tails(s.pending@, j) =~= Seq::<u8>::empty());
                assert((s.written@)(j) + tails(s.pending@, j) =~= (s.emitted@)(j));
            }
        }
        s
    }

    pub fn conn(&self) -> (r: &Connection)
        requires
            self.wf(),
        ensures
            *r == self.conn_spec(),
            r.wf(),
    {
        &self.conn
    }

    /// The TLS boundary and `poll_transmit`. Call `pump` after any change made through it.
    pub fn conn_mut(&mut self) -> (r: &mut Connection)
        requires
            old(self).wf(),
        ensures
            *r == old(self).conn_spec(),
            r.wf(),
            final(self).conn_spec() == *final(r),
            final(r).wf() ==> final(self).wf(),
            final(self).history_ok() == old(self).history_ok(),
            final(self).h3_spec() == old(self).h3_spec(),
            final(self).started_spec() == old(self).started_spec(),
            final(self).idle_spec() == old(self).idle_spec(),
    {
        &mut self.conn
    }

    /// Nothing is waiting, so `send_response` won't be `Busy`.
    pub fn can_send(&self) -> (r: bool)
        ensures
            r == self.idle_spec(),
    {
        self.pending.len() == 0
    }

    /// Throws away the entries of stream `id`, into a fresh `Vec`.
    #[verifier::spinoff_prover]
    fn purge(&mut self, id: u64)
        requires
            offs_ok(old(self).pending@),
            old(self).log_ok(),
        ensures
            offs_ok(final(self).pending@),
            final(self).log_ok(),
            final(self).pending@.len() <= old(self).pending@.len(),
            final(self).conn == old(self).conn,
            final(self).h3 == old(self).h3,
            final(self).started == old(self).started,
            final(self).emitted == old(self).emitted,
            final(self).written == old(self).written,
            final(self).dropped@ == old(self).dropped@.insert(id),
            tails(final(self).pending@, id) == Seq::<u8>::empty(),
    {
        let mut taken: Vec<Pending> = Vec::new();
        core::mem::swap(&mut self.pending, &mut taken);
        let ghost s0 = taken@;
        self.pending = kept(taken, id);
        let ghost d0 = self.dropped@;
        self.dropped = Ghost(d0.insert(id));
        proof {
            assert forall|j: u64| !self.dropped@.contains(j) implies (self.written@)(j) + #[trigger] tails(
                self.pending@,
                j,
            ) == (self.emitted@)(j) by {
                assert(j != id);
                assert(!d0.contains(j));
                assert(tails(self.pending@, j) == tails(s0, j));
            }
        }
    }

    /// One attempt at the queue's head: `true` if it left the queue and the next may go.
    #[verifier::spinoff_prover]
    fn flush_head(&mut self) -> (more: bool)
        requires
            old(self).conn.wf(),
            offs_ok(old(self).pending@),
            old(self).log_ok(),
            old(self).pending@.len() > 0,
        ensures
            final(self).conn.wf(),
            offs_ok(final(self).pending@),
            final(self).log_ok(),
            more ==> final(self).pending@.len() < old(self).pending@.len(),
            final(self).pending@.len() <= old(self).pending@.len(),
            final(self).h3 == old(self).h3,
            final(self).started == old(self).started,
            final(self).emitted == old(self).emitted,
            final(self).conn.out_log() == old(self).conn.out_log(),
            final(self).conn.events_spec() == old(self).conn.events_spec(),
            // A refused stream has no entry left in the queue.
            forall|j: u64| #[trigger] final(self).dropped@.contains(j) && !old(self).dropped@.contains(j)
                ==> tails(final(self).pending@, j) == Seq::<u8>::empty(),
    {
        let ghost s0 = self.pending@;
        let ghost w0 = self.written@;
        let id = self.pending[0].id;
        let off = self.pending[0].off;
        let fin = self.pending[0].fin;
        let len = self.pending[0].data.len();
        proof {
            assert(s0[0].off <= s0[0].data@.len());
        }
        let tail = slice_subrange(self.pending[0].data.as_slice(), off, len);
        let ghost t = tail@;
        let tail_len = tail.len();
        let r = self.conn.stream_write(id, tail, fin);
        match r {
            Ok(n) => {
                let done = n == tail_len;
                let off1 = off + n;
                if done {
                    self.pending.remove(0);
                } else {
                    self.pending[0].off = off1;
                }
                self.written = Ghost(|j: u64| if j == id { w0(j) + t.take(n as int) } else { w0(j) });
                proof {
                    self.lemma_flushed(s0, w0, id, t, n as int, off1);
                }
                done
            },
            Err(()) => {
                self.pending.remove(0);
                proof {
                    self.lemma_err_removed(s0, id);
                }
                self.dropped = Ghost(self.dropped@.insert(id));
                self.purge(id);
                true
            },
        }
    }

    proof fn lemma_flushed(&self, s0: Seq<Pending>, w0: spec_fn(u64) -> Seq<u8>, id: u64, t: Seq<u8>, n: int, off1: usize)
        requires
            s0.len() > 0,
            offs_ok(s0),
            s0[0].id == id,
            t == s0[0].data@.subrange(s0[0].off as int, s0[0].data@.len() as int),
            0 <= n <= t.len(),
            n == t.len() ==> self.pending@ == s0.remove(0),
            n < t.len() ==> off1 == s0[0].off + n && self.pending@ == s0.update(0, Pending { off: off1, ..s0[0] }),
            forall|j: u64|
                !self.dropped@.contains(j) ==> w0(j) + #[trigger] tails(s0, j) == (self.emitted@)(j),
            forall|j: u64| (#[trigger] (self.written@)(j)) == if j == id { w0(j) + t.take(n) } else { w0(j) },
        ensures
            offs_ok(self.pending@),
            self.log_ok(),
    {
        let s1 = self.pending@;
        assert(s0[0].off <= s0[0].data@.len());
        assert forall|i: int| 0 <= i < s1.len() implies (#[trigger] s1[i]).off <= s1[i].data@.len() by {
            if n == t.len() {
                assert(s1[i] == s0[i + 1]);
            } else if i > 0 {
                assert(s1[i] == s0[i]);
            }
        }
        assert forall|j: u64| !self.dropped@.contains(j) implies (self.written@)(j) + #[trigger] tails(s1, j) == (
        self.emitted@)(j) by {
            lemma_tails_head(s0, j);
            let rest = tails(s0.remove(0), j);
            assert(w0(j) + tails(s0, j) == (self.emitted@)(j));
            if n < t.len() {
                lemma_tails_head(s1, j);
                assert(s1.remove(0) =~= s0.remove(0));
            }
            if j == id {
                assert(piece(s0[0], j) =~= t);
                if n == t.len() {
                    assert((w0(j) + t.take(n)) + rest =~= w0(j) + (t + rest));
                } else {
                    assert(piece(s1[0], j) =~= t.skip(n));
                    assert((w0(j) + t.take(n)) + (t.skip(n) + rest) =~= w0(j) + (t + rest));
                }
            } else {
                assert(piece(s0[0], j) =~= Seq::<u8>::empty());
                assert(Seq::<u8>::empty() + rest =~= rest);
                if n < t.len() {
                    assert(piece(s1[0], j) =~= Seq::<u8>::empty());
                }
            }
        }
    }

    /// After removing an entry of `id` from the queue, only `id`'s log is out of step.
    proof fn lemma_err_removed(&self, s0: Seq<Pending>, id: u64)
        requires
            s0.len() > 0,
            offs_ok(s0),
            s0[0].id == id,
            self.pending@ == s0.remove(0),
            forall|j: u64|
                !self.dropped@.contains(j) ==> (self.written@)(j) + #[trigger] tails(s0, j) == (self.emitted@)(j),
        ensures
            offs_ok(self.pending@),
            forall|j: u64|
                j != id && !self.dropped@.contains(j) ==> (self.written@)(j) + #[trigger] tails(self.pending@, j) == (
                self.emitted@)(j),
    {
        let s1 = self.pending@;
        assert forall|i: int| 0 <= i < s1.len() implies (#[trigger] s1[i]).off <= s1[i].data@.len() by {
            assert(s1[i] == s0[i + 1]);
        }
        assert forall|j: u64| j != id && !self.dropped@.contains(j) implies (self.written@)(j) + #[trigger] tails(s1, j)
            == (self.emitted@)(j) by {
            lemma_tails_head(s0, j);
            assert(piece(s0[0], j) =~= Seq::<u8>::empty());
            assert(Seq::<u8>::empty() + tails(s1, j) =~= tails(s1, j));
            assert((self.written@)(j) + tails(s0, j) == (self.emitted@)(j));
        }
    }

    /// Writes queued output, from the head, until the queue is empty or the send buffer is full.
    #[verifier::spinoff_prover]
    fn flush(&mut self)
        requires
            old(self).conn.wf(),
            offs_ok(old(self).pending@),
            old(self).log_ok(),
        ensures
            final(self).conn.wf(),
            offs_ok(final(self).pending@),
            final(self).log_ok(),
            final(self).h3 == old(self).h3,
            final(self).started == old(self).started,
            final(self).emitted == old(self).emitted,
            final(self).conn.out_log() == old(self).conn.out_log(),
            final(self).conn.events_spec() == old(self).conn.events_spec(),
    {
        // ponytail: one deferred response per connection; per-stream queues if head-of-line blocking matters.
        // ponytail: `Vec::remove(0)` and a whole-queue purge, on at most one entry per open bidi stream
        // (`MAX_LOCAL_STREAMS`) plus one response and control writes; a `VecDeque` if that cap rises.
        while self.pending.len() > 0
            invariant
                self.conn.wf(),
                offs_ok(self.pending@),
                self.log_ok(),
                self.h3 == old(self).h3,
                self.started == old(self).started,
                self.emitted == old(self).emitted,
                self.conn.out_log() == old(self).conn.out_log(),
                self.conn.events_spec() == old(self).conn.events_spec(),
            decreases self.pending@.len(),
        {
            if !self.flush_head() {
                return;
            }
        }
    }

    /// Carries out one of h3's outputs.
    #[verifier::spinoff_prover]
    fn apply_one(&mut self, o: Output, app: &mut Vec<AppEvent>)
        requires
            old(self).conn.wf(),
            offs_ok(old(self).pending@),
            old(self).log_ok(),
        ensures
            final(self).conn.wf(),
            offs_ok(final(self).pending@),
            final(self).log_ok(),
            final(self).h3 == old(self).h3,
            final(self).started == old(self).started,
            final(self).conn.out_log() == old(self).conn.out_log(),
            final(self).conn.events_spec() == old(self).conn.events_spec(),
            forall|j: u64| #[trigger] (final(self).emitted@)(j) == (old(self).emitted@)(j) + write_of(o@, j),
            app_grew(old(app)@, final(app)@),
    {
        let ghost e0 = self.emitted@;
        let ghost a0 = app@;
        let ghost o_view = o@;
        match o {
            Output::StreamWrite { stream_id, data, fin } => {
                let ghost d = data@;
                let ghost s0 = self.pending@;
                self.pending.push(Pending { id: stream_id, data, off: 0, fin });
                self.emitted = Ghost(|j: u64| if j == stream_id { e0(j) + d } else { e0(j) });
                proof {
                    let p = self.pending@.last();
                    assert(self.pending@ =~= s0.push(p));
                    assert forall|i: int| 0 <= i < self.pending@.len() implies (#[trigger] self.pending@[i]).off
                        <= self.pending@[i].data@.len() by {
                        if i < s0.len() {
                            assert(self.pending@[i] == s0[i]);
                        }
                    }
                    assert forall|j: u64| !self.dropped@.contains(j) implies (self.written@)(j) + #[trigger] tails(
                        self.pending@,
                        j,
                    ) == (self.emitted@)(j) by {
                        lemma_tails_push(s0, p, j);
                        assert((self.written@)(j) + tails(s0, j) == e0(j));
                        if j == stream_id {
                            assert(p.data@.skip(0) =~= d);
                            assert((self.written@)(j) + (tails(s0, j) + d) =~= e0(j) + d);
                        } else {
                            assert(piece(p, j) =~= Seq::<u8>::empty());
                            assert(tails(s0, j) + piece(p, j) =~= tails(s0, j));
                        }
                    }
                }
                self.flush();
                proof {
                    assert forall|j: u64| #[trigger] (self.emitted@)(j) == e0(j) + write_of(o_view, j) by {
                        if j != stream_id {
                            assert(e0(j) + Seq::<u8>::empty() =~= e0(j));
                        }
                    }
                }
            },
            Output::ResetStream { stream_id, code } => {
                self.purge(stream_id);
                let c = wire_code(code);
                self.conn.stream_reset(stream_id, c);
                proof {
                    self.lemma_no_write(e0, o_view);
                }
            },
            Output::StopSending { stream_id, code } => {
                let c = wire_code(code);
                self.conn.stream_stop_sending(stream_id, c);
                proof {
                    self.lemma_no_write(e0, o_view);
                }
            },
            Output::CloseConnection { code } => {
                let c = wire_code(code);
                let now = self.conn.now();
                let none: Vec<u8> = Vec::new();
                self.conn.close(c, true, none.as_slice(), now);
                proof {
                    self.lemma_no_write(e0, o_view);
                }
            },
            Output::Request { stream_id, head } => {
                app.push(AppEvent::H3(Output::Request { stream_id, head }));
                proof {
                    self.lemma_no_write(e0, o_view);
                }
            },
            Output::RequestBody { stream_id, data } => {
                app.push(AppEvent::H3(Output::RequestBody { stream_id, data }));
                proof {
                    self.lemma_no_write(e0, o_view);
                }
            },
            Output::RequestEnd { stream_id, trailers } => {
                app.push(AppEvent::H3(Output::RequestEnd { stream_id, trailers }));
                proof {
                    self.lemma_no_write(e0, o_view);
                }
            },
        }
    }

    proof fn lemma_no_write(&self, e0: spec_fn(u64) -> Seq<u8>, o: SpecOutput)
        requires
            !(o is StreamWrite),
            self.emitted@ == e0,
        ensures
            forall|j: u64| #[trigger] (self.emitted@)(j) == e0(j) + write_of(o, j),
    {
        assert forall|j: u64| #[trigger] (self.emitted@)(j) == e0(j) + write_of(o, j) by {
            assert(e0(j) + Seq::<u8>::empty() =~= e0(j));
        }
    }

    /// Carries out h3's outputs, in order.
    #[verifier::spinoff_prover]
    fn apply(&mut self, outs: Vec<Output>, app: &mut Vec<AppEvent>)
        requires
            old(self).conn.wf(),
            offs_ok(old(self).pending@),
            old(self).log_ok(),
        ensures
            final(self).conn.wf(),
            offs_ok(final(self).pending@),
            final(self).log_ok(),
            final(self).h3 == old(self).h3,
            final(self).started == old(self).started,
            final(self).conn.out_log() == old(self).conn.out_log(),
            final(self).conn.events_spec() == old(self).conn.events_spec(),
            forall|j: u64| #[trigger] (final(self).emitted@)(j) == (old(self).emitted@)(j) + writes_on(outs_view(outs@), j),
            app_grew(old(app)@, final(app)@),
    {
        let ghost s = outs@;
        let ghost e0 = self.emitted@;
        let ghost a0 = app@;
        proof {
            assert forall|j: u64| #[trigger] (self.emitted@)(j) == e0(j) + writes_on(outs_view(s.take(0)), j) by {
                assert(outs_view(s.take(0)) =~= Seq::<SpecOutput>::empty());
                assert(e0(j) + Seq::<u8>::empty() =~= e0(j));
            }
        }
        for o in it: outs
            invariant
                it.seq() == s,
                self.conn.wf(),
                offs_ok(self.pending@),
                self.log_ok(),
                self.h3 == old(self).h3,
                self.started == old(self).started,
                self.conn.out_log() == old(self).conn.out_log(),
                self.conn.events_spec() == old(self).conn.events_spec(),
                forall|j: u64| #[trigger] (self.emitted@)(j) == e0(j) + writes_on(outs_view(s.take(it.index() as int)), j),
                app_grew(a0, app@),
        {
            let ghost i = it.index() as int;
            let ghost e1 = self.emitted@;
            let ghost a1 = app@;
            proof {
                assert(s[i] == o);
            }
            self.apply_one(o, app);
            proof {
                lemma_app_trans(a0, a1, app@);
                assert forall|j: u64| #[trigger] (self.emitted@)(j) == e0(j) + writes_on(outs_view(s.take(i + 1)), j) by {
                    lemma_writes_take(s, i, j);
                    assert(e1(j) == e0(j) + writes_on(outs_view(s.take(i)), j));
                    assert((self.emitted@)(j) =~= e0(j) + (writes_on(outs_view(s.take(i)), j) + write_of(s[i]@, j)));
                }
            }
        }
        proof {
            assert(s.take(s.len() as int) =~= s);
        }
    }

    /// One event to one h3 method, then its outputs.
    #[verifier::spinoff_prover]
    fn feed(&mut self, e: StreamEvent, app: &mut Vec<AppEvent>)
        requires
            old(self).wf(),
            old(self).history_ok(),
            old(self).started,
        ensures
            final(self).wf(),
            final(self).history_ok(),
            final(self).started,
            final(self).conn.out_log() == old(self).conn.out_log(),
            final(self).conn.events_spec() == old(self).conn.events_spec(),
            exists|o0: Seq<Output>, o1: Seq<Output>| #[trigger] one_call(old(self).h3, final(self).h3, e@, o0, o1),
            app_grew(old(app)@, final(app)@),
    {
        let ghost h0 = self.h3;
        let ghost e_view = e@;
        let ghost e0 = self.emitted@;
        let ghost a0 = app@;
        let mut outs: Vec<Output> = Vec::new();
        let ghost o0 = outs@;
        let mut aborted: Option<u64> = None;
        match e {
            StreamEvent::Data { id, data, fin } => {
                self.h3.on_stream_data(id, data.as_slice(), fin, &mut outs);
            },
            StreamEvent::Reset { id, code } => {
                self.h3.on_stream_reset(id, code, &mut outs);
                if id % 4 == 0 {
                    aborted = Some(id);
                }
            },
            StreamEvent::StopSending { id, code } => {
                self.h3.on_stop_sending(id, code, &mut outs);
                // QUIC has reset this sending part, and may forget the stream and re-credit it. An
                // answer h3 queued must not outlive that, or a peer holding back the ACKs of the head
                // grows the queue for ever: CONNECT, STOP_SENDING, ACK the RESET_STREAM, again.
                self.purge(id);
            },
        }
        let ghost o1 = outs@;
        let ghost s1 = outs@;
        proof {
            assert(one_call(h0, self.h3, e_view, o0, o1));
            assert(s1.skip(0) =~= s1);
            assert(added(o0, o1) =~= outs_view(s1));
        }
        self.apply(outs, app);
        // E7: every peer reset of a request stream. Over-reporting after a completed request is harmless.
        if let Some(id) = aborted {
            let ghost a1 = app@;
            app.push(AppEvent::Aborted(id));
            proof {
                assert(app_grew(a1, app@));
                lemma_app_trans(a0, a1, app@);
            }
        }
    }

    /// Feeds the events of this `poll_stream_events`, in order.
    #[verifier::spinoff_prover]
    fn feed_all(&mut self, evs: Vec<StreamEvent>, app: &mut Vec<AppEvent>)
        requires
            old(self).wf(),
            old(self).history_ok(),
            old(self).started,
        ensures
            final(self).wf(),
            final(self).history_ok(),
            final(self).started,
            final(self).conn.out_log() == old(self).conn.out_log(),
            final(self).conn.events_spec() == old(self).conn.events_spec(),
            fed(old(self).h3, event_views(evs@), final(self).h3),
            app_grew(old(app)@, final(app)@),
    {
        let ghost s = evs@;
        let ghost h0 = self.h3;
        let ghost a0 = app@;
        proof {
            assert(event_views(s.take(0)) =~= Seq::<SpecStreamEvent>::empty());
        }
        for e in it: evs
            invariant
                it.seq() == s,
                self.wf(),
                self.history_ok(),
                self.started,
                self.conn.out_log() == old(self).conn.out_log(),
                self.conn.events_spec() == old(self).conn.events_spec(),
                fed(h0, event_views(s.take(it.index() as int)), self.h3),
                app_grew(a0, app@),
        {
            let ghost i = it.index() as int;
            let ghost hm = self.h3;
            let ghost a1 = app@;
            proof {
                assert(s[i] == e);
            }
            self.feed(e, app);
            proof {
                lemma_app_trans(a0, a1, app@);
                let v = event_views(s.take(i + 1));
                assert(v.drop_last() =~= event_views(s.take(i)));
                assert(v.last() == s[i]@);
                let (o0, o1) = choose|o0: Seq<Output>, o1: Seq<Output>| #[trigger] one_call(hm, self.h3, s[i]@, o0, o1);
                assert(one_call(hm, self.h3, v.last(), o0, o1) && fed(h0, v.drop_last(), hm));
            }
        }
        proof {
            assert(s.take(s.len() as int) =~= s);
        }
    }

    /// Opens HTTP/3 once the transport can send, then flushes and feeds h3 every queued stream event.
    #[verifier::spinoff_prover]
    pub fn pump(&mut self, app: &mut Vec<AppEvent>)
        requires
            old(self).wf(),
            old(self).history_ok(),
        ensures
            final(self).wf(),
            final(self).history_ok(),
            final(self).conn_spec().out_log() == old(self).conn_spec().out_log(),
            app_grew(old(app)@, final(app)@),
            // 2b obligation 2: nothing reaches h3 before `start`.
            !final(self).started_spec() ==> final(self).h3_spec() == old(self).h3_spec()
                && final(self).conn_spec().events_spec() == old(self).conn_spec().events_spec(),
            !old(self).started_spec() && !(old(self).conn_spec().live(PacketKind::OneRtt)
                && old(self).conn_spec().phase_spec() is Open) ==> !final(self).started_spec(),
            old(self).started_spec() ==> final(self).started_spec(),
            // 2b obligation 1: every event, in order, one h3 call each, and none left behind.
            final(self).started_spec() ==> final(self).conn_spec().events_spec().len() == 0,
            old(self).started_spec() ==> fed(
                old(self).h3_spec(),
                event_views(old(self).conn_spec().events_spec()),
                final(self).h3_spec(),
            ),
            !old(self).started_spec() && final(self).started_spec() ==> exists|hs: H3Conn|
                #[trigger] hs.ctrl_bytes() == ctrl_preamble() && fed(
                    hs,
                    event_views(old(self).conn_spec().events_spec()),
                    final(self).h3_spec(),
                ),
    {
        let ghost a0 = app@;
        if !self.started {
            if !(self.conn.handshake_complete() && matches!(self.conn.phase(), Phase::Open)) {
                return;
            }
            let limit = match self.conn.peer_uni_limit() {
                Some(l) => l,
                None => 0,
            };
            //= https://www.rfc-editor.org/rfc/rfc9114#section-6.2
            //# Therefore, the transport parameters sent by both clients
            //# and servers MUST allow the peer to create at least three
            //# unidirectional streams.
            //
            // `started` stays false, so the phase gate above keeps h3 unstarted and undrained for good.
            if limit < MIN_PEER_UNI_STREAMS {
                let now = self.conn.now();
                let none: Vec<u8> = Vec::new();
                self.conn.close(H3_GENERAL_PROTOCOL_ERROR, true, none.as_slice(), now);
                return;
            }
            let mut outs: Vec<Output> = Vec::new();
            self.h3.start(&mut outs);
            let ghost s1 = outs@;
            self.started = true;
            self.apply(outs, app);
            proof {
                assert(s1.skip(0) =~= s1);
                assert(self.h3.ctrl_bytes() == (self.emitted@)(3));
            }
        }
        self.flush();
        // One poll is the drain: only `on_frame` pushes events, and nothing `feed` calls reaches it
        // (the `events_spec` ensures of `close`, `stream_write`, `stream_reset`, `stream_stop_sending`).
        let mut evs: Vec<StreamEvent> = Vec::new();
        self.conn.poll_stream_events(&mut evs);
        proof {
            assert(evs@ =~= old(self).conn.events_spec());
        }
        let ghost a1 = app@;
        self.feed_all(evs, app);
        proof {
            lemma_app_trans(a0, a1, app@);
        }
    }

    /// `Busy`, without calling h3, while anything is queued. `Rejected` before h3 has started too:
    /// its control stream opens first, and no request can have arrived.
    #[verifier::spinoff_prover]
    pub fn send_response(&mut self, id: u64, resp: &Response, app: &mut Vec<AppEvent>) -> (r: Result<(), SendError>)
        requires
            old(self).wf(),
            old(self).history_ok(),
        ensures
            final(self).wf(),
            final(self).history_ok(),
            final(self).conn_spec().out_log() == old(self).conn_spec().out_log(),
            final(self).started_spec() == old(self).started_spec(),
            app_grew(old(app)@, final(app)@),
            r is Err && r->Err_0 == SendError::Busy ==> final(self).h3_spec() == old(self).h3_spec()
                && final(self).conn_spec() == old(self).conn_spec() && !old(self).idle_spec(),
            old(self).idle_spec() == !(r is Err && r->Err_0 == SendError::Busy),
    {
        if self.pending.len() != 0 {
            return Err(SendError::Busy);
        }
        if !self.started {
            return Err(SendError::Rejected);
        }
        let ghost e0 = self.emitted@;
        let mut outs: Vec<Output> = Vec::new();
        match self.h3.send_response(id, resp, &mut outs) {
            Ok(()) => {
                let ghost s1 = outs@;
                self.apply(outs, app);
                proof {
                    assert(s1.skip(0) =~= s1);
                }
                Ok(())
            },
            Err(()) => {
                proof {
                    assert(outs@ == Seq::<Output>::empty());
                    assert(outs@.skip(0) =~= outs@);
                    assert(writes_on(outs_view(outs@), 3) =~= Seq::<u8>::empty());
                    assert(self.h3.ctrl_bytes() =~= e0(3));
                }
                Err(SendError::Rejected)
            },
        }
    }

    /// `Connection::on_datagram`, then `pump`.
    #[verifier::spinoff_prover]
    pub fn on_datagram(
        &mut self,
        path: PathId,
        datagram_len: usize,
        packets: Vec<PlainPacket>,
        now: u64,
        rand: &[u8; RAND_LEN],
        app: &mut Vec<AppEvent>,
    )
        requires
            old(self).wf(),
            old(self).history_ok(),
            forall|i: int| 0 <= i < packets@.len() ==> plain_wf(#[trigger] packets@[i]@),
        ensures
            final(self).wf(),
            final(self).history_ok(),
            final(self).conn_spec().out_log() == old(self).conn_spec().out_log(),
            final(self).started_spec() ==> final(self).conn_spec().events_spec().len() == 0,
            app_grew(old(app)@, final(app)@),
    {
        self.conn.on_datagram(path, datagram_len, packets, now, rand);
        self.pump(app);
    }

    /// `Connection::on_timeout`, then `pump`.
    #[verifier::spinoff_prover]
    pub fn on_timeout(&mut self, now: u64, rand: &[u8; RAND_LEN], app: &mut Vec<AppEvent>)
        requires
            old(self).wf(),
            old(self).history_ok(),
        ensures
            final(self).wf(),
            final(self).history_ok(),
            final(self).conn_spec().out_log() == old(self).conn_spec().out_log(),
            final(self).started_spec() ==> final(self).conn_spec().events_spec().len() == 0,
            app_grew(old(app)@, final(app)@),
    {
        self.conn.on_timeout(now, rand);
        self.pump(app);
    }

    /// Sends GOAWAY. A no-op before h3 has started: no request can have arrived, and a write now
    /// would be refused and lose the SETTINGS h3 emits only once.
    #[verifier::spinoff_prover]
    pub fn shutdown(&mut self, app: &mut Vec<AppEvent>)
        requires
            old(self).wf(),
            old(self).history_ok(),
        ensures
            final(self).wf(),
            final(self).history_ok(),
            final(self).conn_spec().out_log() == old(self).conn_spec().out_log(),
            final(self).started_spec() == old(self).started_spec(),
            app_grew(old(app)@, final(app)@),
    {
        if !self.started {
            return;
        }
        let mut outs: Vec<Output> = Vec::new();
        self.h3.shutdown(&mut outs);
        let ghost s1 = outs@;
        self.apply(outs, app);
        proof {
            assert(s1.skip(0) =~= s1);
        }
    }
}

} // verus!

impl H3Server {
    /// Bytes waiting to be written.
    #[doc(hidden)]
    pub fn pending_bytes(&self) -> usize {
        self.pending.iter().fold(0usize, |a, e| a.saturating_add(e.data.len() - e.off))
    }
}
