//! The sending part of a stream (RFC 9000 §3.1): buffered application data sent in STREAM
//! chunks under the peer's stream data limit (§4.1), retransmitted unchanged when lost (§2.2),
//! and abandoned with RESET_STREAM (§3.3, §3.5).
use vstd::prelude::*;
use vstd::slice::{slice_subrange, slice_to_vec};
use crate::flow::*;
use wire::varint::*;

verus! {

/// Figure 2's send states.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum SendState {
    Ready,
    Send,
    DataSent,
    DataRecvd,
    ResetSent,
    ResetRecvd,
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-3.1
//# Sending the first STREAM or STREAM_DATA_BLOCKED frame causes a
//# sending part of a stream to enter the "Send" state.
//= https://www.rfc-editor.org/rfc/rfc9000#section-3.1
//# After the application indicates that all stream data has been sent
//# and a STREAM frame containing the FIN bit is sent, the sending part
//# of the stream enters the "Data Sent" state.
//= https://www.rfc-editor.org/rfc/rfc9000#section-3.1
//# Once all stream data has been successfully acknowledged, the sending
//# part of the stream enters the "Data Recvd" state, which is a terminal
//# state.
//= https://www.rfc-editor.org/rfc/rfc9000#section-3.1
//# From any state that is one of "Ready", "Send", or "Data Sent", an
//# application can signal that it wishes to abandon transmission of
//# stream data.  Alternatively, an endpoint might receive a STOP_SENDING
//# frame from its peer.  In either case, the endpoint sends a
//# RESET_STREAM frame, which causes the stream to enter the "Reset Sent"
//# state.
//= https://www.rfc-editor.org/rfc/rfc9000#section-3.1
//# Once a packet containing a RESET_STREAM has been acknowledged, the
//# sending part of the stream enters the "Reset Recvd" state, which is a
//# terminal state.
/// Figure 2's edges.
pub open spec fn send_edge(a: SendState, b: SendState) -> bool {
    ||| a is Ready && b is Send
    ||| a is Send && b is DataSent
    ||| a is DataSent && b is DataRecvd
    ||| (a is Ready || a is Send || a is DataSent) && b is ResetSent
    ||| a is ResetSent && b is ResetRecvd
}

/// One call moves along at most two edges: one emission may take Ready to Send to Data Sent.
pub open spec fn send_step_ok(a: SendState, b: SendState) -> bool {
    a == b || send_edge(a, b) || exists|c: SendState| send_edge(a, c) && send_edge(c, b)
}

/// One STREAM frame's worth of data: `new_bytes` of it were never sent before.
#[derive(Debug, PartialEq, Eq)]
pub struct Chunk {
    pub off: u64,
    pub data: Vec<u8>,
    pub fin: bool,
    pub new_bytes: u64,
}

pub struct SpecChunk {
    pub off: u64,
    pub data: Seq<u8>,
    pub fin: bool,
    pub new_bytes: u64,
}

impl View for Chunk {
    type V = SpecChunk;

    open spec fn view(&self) -> SpecChunk {
        SpecChunk { off: self.off, data: self.data@, fin: self.fin, new_bytes: self.new_bytes }
    }
}

/// Every range is non-empty and inside `[lo, hi)`.
pub open spec fn in_bounds(v: Seq<(u64, u64)>, lo: u64, hi: u64) -> bool {
    forall|i: int| #![trigger v[i]] 0 <= i < v.len() ==> lo <= v[i].0 < v[i].1 <= hi
}

/// Every range is disjoint from `[s, e)`.
pub open spec fn avoids(v: Seq<(u64, u64)>, s: u64, e: u64) -> bool {
    forall|i: int| #![trigger v[i]] 0 <= i < v.len() ==> v[i].1 <= s || v[i].0 >= e
}

// ponytail: O(ranges) sorted-Vec range sets; interval tree if loss patterns make them long.
/// Adds `[s, e)` to a sorted, merged range list. Order and merging are exec behavior (tested);
/// only the bounds are proven.
fn range_insert(
    v: &mut Vec<(u64, u64)>,
    s: u64,
    e: u64,
    Ghost(lo): Ghost<u64>,
    Ghost(hi): Ghost<u64>,
)
    requires
        lo <= s < e <= hi,
        in_bounds(old(v)@, lo, hi),
    ensures
        in_bounds(final(v)@, lo, hi),
{
    let mut out: Vec<(u64, u64)> = Vec::new();
    let mut s = s;
    let mut e = e;
    let mut placed = false;
    let mut i: usize = 0;
    while i < v.len()
        invariant
            in_bounds(v@, lo, hi),
            in_bounds(out@, lo, hi),
            lo <= s < e <= hi,
            i <= v@.len(),
        decreases v@.len() - i,
    {
        let (a, b) = v[i];
        if b < s {
            out.push((a, b));
        } else if a > e || placed {
            if !placed {
                out.push((s, e));
                placed = true;
            }
            out.push((a, b));
        } else {
            // Overlapping or adjacent: merge.
            if a < s {
                s = a;
            }
            if b > e {
                e = b;
            }
        }
        i = i + 1;
    }
    if !placed {
        out.push((s, e));
    }
    *v = out;
}

/// Removes `[s, e)` from every range, splitting where needed.
fn range_remove(
    v: &mut Vec<(u64, u64)>,
    s: u64,
    e: u64,
    Ghost(lo): Ghost<u64>,
    Ghost(hi): Ghost<u64>,
)
    requires
        s < e,
        in_bounds(old(v)@, lo, hi),
    ensures
        in_bounds(final(v)@, lo, hi),
        avoids(final(v)@, s, e),
{
    let mut out: Vec<(u64, u64)> = Vec::new();
    let mut i: usize = 0;
    while i < v.len()
        invariant
            in_bounds(v@, lo, hi),
            in_bounds(out@, lo, hi),
            avoids(out@, s, e),
            i <= v@.len(),
        decreases v@.len() - i,
    {
        let (a, b) = v[i];
        if a < s {
            out.push((a, if b < s { b } else { s }));
        }
        if b > e {
            out.push((if a > e { a } else { e }, b));
        }
        i = i + 1;
    }
    *v = out;
}

/// `min(off + len, end)`, without overflow.
fn clamp_end(off: u64, len: u64, end: u64) -> (r: u64)
    ensures
        r <= end,
        off < end ==> r == if len > end - off { end as int } else { off + len },
{
    if off >= end || len > end - off {
        end
    } else {
        off + len
    }
}

/// The sending part of one stream.
pub struct SendStream {
    state: SendState,
    /// The bytes `[acked_base, written)`.
    buf: Vec<u8>,
    acked_base: u64,
    written: u64,
    sent_end: u64,
    fin_written: bool,
    fin_acked: bool,
    acked: Vec<(u64, u64)>,
    lost: Vec<(u64, u64)>,
    fin_lost: bool,
    credit: SendCredit,
    /// The RESET_STREAM's error code and final size, once reset.
    reset: Option<(u64, u64)>,
    reset_pending: bool,
    all_written: Ghost<Seq<u8>>,
}

pub open spec fn is_reset(a: SendState) -> bool {
    a is ResetSent || a is ResetRecvd
}

/// No STREAM frames are sent from these states (§3.3).
pub open spec fn no_data(a: SendState) -> bool {
    a is DataRecvd || is_reset(a)
}

/// What a returned chunk guarantees, between the stream before (`s1`) and after (`s2`).
pub open spec fn chunk_ok(
    s1: SendStream,
    s2: SendStream,
    c: SpecChunk,
    max_len: u64,
    conn_avail: u64,
) -> bool {
    let end = c.off + c.data.len();
    &&& end <= s1.all_written().len()
    &&& c.data == s1.all_written().subrange(c.off as int, end)
    &&& c.fin ==> end == s1.all_written().len() && s1.fin_written_spec()
    &&& c.data.len() > 0 || c.fin
    &&& c.data.len() <= max_len
    &&& c.new_bytes <= conn_avail
    &&& s2.sent_end() == s1.sent_end() + c.new_bytes
    &&& s1.next_off() == Some(c.off)
    &&& !(s2.state() is Ready)
}

impl SendStream {
    /// Every byte the application has written, in order.
    pub closed spec fn all_written(&self) -> Seq<u8> {
        self.all_written@
    }

    pub closed spec fn state(&self) -> SendState {
        self.state
    }

    pub closed spec fn fin_written_spec(&self) -> bool {
        self.fin_written
    }

    pub closed spec fn acked_base_spec(&self) -> u64 {
        self.acked_base
    }

    pub closed spec fn fin_acked_spec(&self) -> bool {
        self.fin_acked
    }

    /// The RESET_STREAM's `(code, final size)`, once reset.
    pub closed spec fn reset_spec(&self) -> Option<(u64, u64)> {
        self.reset
    }

    /// The end of the contiguously acknowledged prefix. The buffer is trimmed to it lazily, so
    /// `acked_base` (the buffer's start) may lag behind.
    pub closed spec fn acked_point_spec(&self) -> u64 {
        if self.acked@.len() > 0 && self.acked@[0].0 == self.acked_base {
            self.acked@[0].1
        } else {
            self.acked_base
        }
    }

    pub closed spec fn buffered_spec(&self) -> nat {
        self.buf@.len()
    }

    pub closed spec fn sent_end_spec(&self) -> u64 {
        self.sent_end
    }

    pub closed spec fn max_spec(&self) -> u64 {
        self.credit.max_spec()
    }

    /// A FIN is still to be sent: not yet, or again after a loss.
    pub closed spec fn fin_owed(&self) -> bool {
        self.fin_written && (self.state is DataSent ==> self.fin_lost)
    }

    pub closed spec fn next_off_spec(&self) -> Option<u64> {
        if no_data(self.state) {
            None
        } else if self.lost@.len() > 0 {
            Some(self.lost@[0].0)
        } else if self.sent_end < self.written || self.fin_owed() {
            Some(self.sent_end)
        } else {
            None
        }
    }

    pub closed spec fn pending_reset_spec(&self) -> Option<(u64, u64)> {
        if self.reset_pending && self.state is ResetSent {
            self.reset
        } else {
            None
        }
    }

    /// `wf` except the clauses `on_data_acked` restores only at its end.
    closed spec fn core(&self) -> bool {
        &&& self.credit.wf()
        &&& self.credit.used_spec() == self.sent_end
        &&& self.sent_end <= self.credit.max_spec()
        &&& self.sent_end <= self.written
        &&& self.written == self.all_written@.len()
        &&& self.written <= VARINT_MAX
        &&& self.acked_base <= self.sent_end
        &&& !is_reset(self.state) ==> self.buf@ == self.all_written@.subrange(
            self.acked_base as int,
            self.written as int,
        )
        &&& is_reset(self.state) ==> self.buf@.len() == 0 && self.lost@.len() == 0
            && self.acked@.len() == 0 && !self.fin_lost && !self.fin_acked
        &&& in_bounds(self.lost@, self.acked_base, self.sent_end)
        &&& in_bounds(self.acked@, self.acked_base, self.sent_end)
        &&& self.state is Ready ==> self.sent_end == 0
        &&& (self.state is DataSent || self.state is DataRecvd) ==> self.fin_written
            && self.sent_end == self.written
        &&& self.fin_lost ==> self.state is DataSent && !self.fin_acked
        &&& self.fin_acked ==> self.state is DataSent || self.state is DataRecvd
        &&& self.state is DataRecvd ==> self.acked_base == self.written && self.fin_acked
        &&& (self.reset is Some <==> is_reset(self.state))
        &&& self.reset matches Some(r) ==> r.0 <= VARINT_MAX && r.1 == self.sent_end
        &&& self.reset_pending ==> self.state is ResetSent
    }

    pub closed spec fn wf(&self) -> bool {
        &&& self.core()
        &&& self.state is DataSent ==> !(self.acked_base == self.written && self.fin_acked)
        // Memory: the buffer is at most twice the bytes past the acknowledged prefix.
        &&& self.buf@.len() <= 2 * (self.written - self.acked_point_spec())
        &&& self.acked_point_spec() == self.written ==> self.acked_base == self.written
    }

    /// The invariant, in terms of the accessors.
    pub proof fn lemma_wf(&self)
        requires
            self.wf(),
        ensures
            self.sent_end() <= self.max(),
            self.sent_end() <= self.all_written().len() <= VARINT_MAX,
            self.acked_base_spec() <= self.sent_end(),
            self.buffered_spec() == if is_reset(self.state()) {
                0
            } else {
                self.all_written().len() - self.acked_base_spec()
            },
            self.state() is Ready ==> self.sent_end() == 0,
            (self.state() is DataSent || self.state() is DataRecvd) ==> self.fin_written_spec()
                && self.sent_end() == self.all_written().len(),
            self.state() is DataSent ==> !(self.acked_base_spec() == self.all_written().len()
                && self.fin_acked_spec()),
            self.state() is DataRecvd ==> self.acked_base_spec() == self.all_written().len()
                && self.fin_acked_spec(),
            self.reset_spec() is Some <==> is_reset(self.state()),
            self.reset_spec() matches Some(r) ==> r.0 <= VARINT_MAX && r.1 == self.sent_end(),
            self.pending_reset() is Some ==> self.state() is ResetSent && self.pending_reset()
                == self.reset_spec(),
            self.next_off() matches Some(o) ==> o <= self.all_written().len(),
            self.acked_base_spec() <= self.acked_point_spec() <= self.all_written().len(),
            self.buffered_spec() <= 2 * (self.all_written().len() - self.acked_point_spec()),
            self.acked_point_spec() == self.all_written().len() <==> self.acked_base_spec()
                == self.all_written().len(),
    {
        self.credit.lemma_wf();
    }

    pub fn new(max: u64) -> (r: SendStream)
        ensures
            r.wf(),
            r.state() is Ready,
            r.all_written() == Seq::<u8>::empty(),
            !r.fin_written_spec(),
            r.sent_end() == 0,
            r.max() == max,
            r.reset_spec() is None,
    {
        let r = SendStream {
            state: SendState::Ready,
            buf: Vec::new(),
            acked_base: 0,
            written: 0,
            sent_end: 0,
            fin_written: false,
            fin_acked: false,
            acked: Vec::new(),
            lost: Vec::new(),
            fin_lost: false,
            credit: SendCredit::new(max),
            reset: None,
            reset_pending: false,
            all_written: Ghost(Seq::empty()),
        };
        proof {
            assert(r.buf@ =~= r.all_written@.subrange(0, 0));
        }
        r
    }

    pub fn state_exec(&self) -> (r: SendState)
        ensures
            r == self.state(),
    {
        self.state
    }

    #[verifier::when_used_as_spec(sent_end_spec)]
    pub fn sent_end(&self) -> (r: u64)
        ensures
            r == self.sent_end_spec(),
    {
        self.sent_end
    }

    /// The peer's stream data limit.
    #[verifier::when_used_as_spec(max_spec)]
    pub fn max(&self) -> (r: u64)
        ensures
            r == self.max_spec(),
    {
        self.credit.max()
    }

    pub fn is_terminal(&self) -> (r: bool)
        ensures
            r == (self.state() is DataRecvd || self.state() is ResetRecvd),
    {
        match self.state {
            SendState::DataRecvd | SendState::ResetRecvd => true,
            _ => false,
        }
    }

    /// Appends application data, with the FIN if `fin`.
    pub fn write(&mut self, data: &[u8], fin: bool) -> (r: Result<(), ()>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            send_step_ok(old(self).state(), final(self).state()),
            r is Err <==> (!(old(self).state() is Ready || old(self).state() is Send)
                || old(self).fin_written_spec() || old(self).all_written().len() + data@.len()
                > VARINT_MAX),
            r is Err ==> *final(self) == *old(self),
            r is Ok ==> {
                &&& final(self).all_written() == old(self).all_written() + data@
                &&& final(self).fin_written_spec() == fin
                &&& final(self).state() == old(self).state()
                &&& final(self).sent_end() == old(self).sent_end()
                &&& final(self).max() == old(self).max()
                &&& final(self).reset_spec() == old(self).reset_spec()
            },
    {
        let open = match self.state {
            SendState::Ready | SendState::Send => true,
            _ => false,
        };
        if !open || self.fin_written || data.len() as u64 > VARINT_MAX - self.written {
            return Err(());
        }
        let ghost aw = self.all_written@;
        self.buf.extend_from_slice(data);
        self.written = self.written + data.len() as u64;
        self.all_written = Ghost(aw + data@);
        self.fin_written = fin;
        proof {
            assert(self.buf@ =~= self.all_written@.subrange(
                self.acked_base as int,
                self.written as int,
            ));
        }
        Ok(())
    }

    /// The next chunk to send, at most `max_len` bytes, with `conn_avail` bytes of connection
    /// credit left: lost ranges first, then new data, then a lone FIN.
    pub fn poll_data(&mut self, max_len: u64, conn_avail: u64) -> (r: Option<Chunk>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            send_step_ok(old(self).state(), final(self).state()),
            final(self).all_written() == old(self).all_written(),
            final(self).fin_written_spec() == old(self).fin_written_spec(),
            final(self).max() == old(self).max(),
            final(self).reset_spec() == old(self).reset_spec(),
            final(self).pending_reset() == old(self).pending_reset(),
            no_data(old(self).state()) ==> r is None,
            r is None ==> *final(self) == *old(self),
            r matches Some(c) ==> chunk_ok(*old(self), *final(self), c@, max_len, conn_avail),
    {
        match self.state {
            //= https://www.rfc-editor.org/rfc/rfc9000#section-3.3
            //# A sender MUST NOT send any of these frames from a terminal state
            //# ("Data Recvd" or "Reset Recvd").
            //= https://www.rfc-editor.org/rfc/rfc9000#section-3.3
            //# A sender MUST NOT send a STREAM or
            //# STREAM_DATA_BLOCKED frame for a stream in the "Reset Sent" state or
            //# any terminal state -- that is, after sending a RESET_STREAM frame.
            SendState::DataRecvd | SendState::ResetSent | SendState::ResetRecvd => return None,
            _ => {},
        }
        if self.lost.len() > 0 {
            self.retransmit(max_len)
        } else {
            self.send_new(max_len, conn_avail)
        }
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-2.2
    //# The data at a given offset MUST NOT change if it is sent
    //# multiple times
    /// The start of the first lost range again, from the buffer of written bytes.
    fn retransmit(&mut self, max_len: u64) -> (r: Option<Chunk>)
        requires
            old(self).wf(),
            old(self).lost@.len() > 0,
            !no_data(old(self).state),
        ensures
            final(self).wf(),
            send_step_ok(old(self).state(), final(self).state()),
            final(self).all_written() == old(self).all_written(),
            final(self).fin_written_spec() == old(self).fin_written_spec(),
            final(self).max() == old(self).max(),
            final(self).reset_spec() == old(self).reset_spec(),
            final(self).pending_reset() == old(self).pending_reset(),
            r is None ==> *final(self) == *old(self),
            r matches Some(c) ==> chunk_ok(*old(self), *final(self), c@, max_len, 0),
    {
        let (s, e) = self.lost[0];
        if max_len == 0 {
            return None;
        }
        let len = if e - s > max_len {
            max_len
        } else {
            e - s
        };
        let end = s + len;
        let ghost aw = self.all_written@;
        let ghost ab = self.acked_base;
        let ghost se = self.sent_end;
        let data = slice_to_vec(
            slice_subrange(
                self.buf.as_slice(),
                (s - self.acked_base) as usize,
                (end - self.acked_base) as usize,
            ),
        );
        proof {
            assert(data@ =~= aw.subrange(s as int, end as int));
        }
        range_remove(&mut self.lost, s, end, Ghost(ab), Ghost(se));
        let fin = end == self.written && self.fin_written;
        if fin {
            self.fin_lost = false;
            self.state = SendState::DataSent;
        }
        Some(Chunk { off: s, data, fin, new_bytes: 0 })
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-4.5
    //# An endpoint MUST NOT send data on a stream at or beyond the final
    //# size.
    /// New bytes from `sent_end`, within every limit, with the FIN once the chunk reaches the
    /// end of the written data; or a lone FIN that is owed.
    fn send_new(&mut self, max_len: u64, conn_avail: u64) -> (r: Option<Chunk>)
        requires
            old(self).wf(),
            old(self).lost@.len() == 0,
            !no_data(old(self).state),
        ensures
            final(self).wf(),
            send_step_ok(old(self).state(), final(self).state()),
            final(self).all_written() == old(self).all_written(),
            final(self).fin_written_spec() == old(self).fin_written_spec(),
            final(self).max() == old(self).max(),
            final(self).reset_spec() == old(self).reset_spec(),
            final(self).pending_reset() == old(self).pending_reset(),
            r is None ==> *final(self) == *old(self),
            r matches Some(c) ==> chunk_ok(*old(self), *final(self), c@, max_len, conn_avail),
    {
        proof {
            self.credit.lemma_wf();
        }
        let mut len = self.written - self.sent_end;
        if len > max_len {
            len = max_len;
        }
        let avail = self.credit.available();
        if len > avail {
            len = avail;
        }
        if len > conn_avail {
            len = conn_avail;
        }
        let off = self.sent_end;
        let end = off + len;
        let owed = self.fin_written && match self.state {
            SendState::DataSent => self.fin_lost,
            _ => true,
        };
        let fin = end == self.written && owed;
        if len == 0 && !fin {
            return None;
        }
        let ghost aw = self.all_written@;
        let ghost old_state = self.state;
        let data = slice_to_vec(
            slice_subrange(
                self.buf.as_slice(),
                (off - self.acked_base) as usize,
                (end - self.acked_base) as usize,
            ),
        );
        proof {
            assert(data@ =~= aw.subrange(off as int, end as int));
        }
        self.credit.consume(len);
        self.sent_end = end;
        if fin {
            self.fin_lost = false;
            self.state = SendState::DataSent;
        } else {
            self.state = SendState::Send;
        }
        proof {
            self.credit.lemma_wf();
            if old_state is Ready && fin {
                assert(send_edge(SendState::Ready, SendState::Send) && send_edge(
                    SendState::Send,
                    SendState::DataSent,
                ));
            }
        }
        Some(Chunk { off, data, fin, new_bytes: len })
    }

    /// The offset `poll_data` would send at next, if it sends anything.
    #[verifier::when_used_as_spec(next_off_spec)]
    pub fn next_off(&self) -> (r: Option<u64>)
        requires
            self.wf(),
        ensures
            r == self.next_off_spec(),
            r matches Some(o) ==> o <= self.all_written().len(),
    {
        match self.state {
            SendState::DataRecvd | SendState::ResetSent | SendState::ResetRecvd => return None,
            _ => {},
        }
        if self.lost.len() > 0 {
            return Some(self.lost[0].0);
        }
        let owed = self.fin_written && match self.state {
            SendState::DataSent => self.fin_lost,
            _ => true,
        };
        if self.sent_end < self.written || owed {
            Some(self.sent_end)
        } else {
            None
        }
    }

    /// How many bytes `poll_data` would send next if nothing else limited it: the first lost
    /// range, else the written bytes not yet sent.
    pub fn want(&self) -> u64
        requires
            self.wf(),
    {
        if self.lost.len() > 0 {
            self.lost[0].1 - self.lost[0].0
        } else {
            self.written - self.sent_end
        }
    }

    /// Whether `write` of `n` bytes would succeed.
    pub fn writable(&self, n: usize) -> (r: bool)
        requires
            self.wf(),
        ensures
            r == ((self.state() is Ready || self.state() is Send) && !self.fin_written_spec()
                && self.all_written().len() + n <= VARINT_MAX),
    {
        let open = match self.state {
            SendState::Ready | SendState::Send => true,
            _ => false,
        };
        open && !self.fin_written && n as u64 <= VARINT_MAX - self.written
    }

    /// Abandons the stream with RESET_STREAM `code` (final size: the bytes sent). `fresh`:
    /// the stream was not already reset or fully acknowledged.
    pub fn reset(&mut self, code: u64) -> (fresh: bool)
        requires
            old(self).wf(),
            code <= VARINT_MAX,
        ensures
            final(self).wf(),
            send_step_ok(old(self).state(), final(self).state()),
            final(self).all_written() == old(self).all_written(),
            final(self).sent_end() == old(self).sent_end(),
            final(self).max() == old(self).max(),
            fresh == (old(self).state() is Ready || old(self).state() is Send
                || old(self).state() is DataSent),
            fresh ==> final(self).state() is ResetSent && final(self).reset_spec() == Some(
                (code, old(self).sent_end()),
            ) && final(self).pending_reset() == Some((code, old(self).sent_end()))
                && final(self).buffered_spec() == 0,
            !fresh ==> *final(self) == *old(self),
    {
        match self.state {
            SendState::Ready | SendState::Send | SendState::DataSent => {},
            _ => return false,
        }
        self.state = SendState::ResetSent;
        self.reset = Some((code, self.sent_end));
        self.reset_pending = true;
        self.buf = Vec::new();
        self.lost = Vec::new();
        self.acked = Vec::new();
        self.fin_lost = false;
        self.fin_acked = false;
        true
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-3.5
    //# An endpoint that receives a STOP_SENDING frame
    //# MUST send a RESET_STREAM frame if the stream is in the "Ready" or
    //# "Send" state.
    /// The peer's STOP_SENDING with `code`: reset at once, copying the code, in Ready, Send and
    /// Data Sent alike.
    pub fn on_stop_sending(&mut self, code: u64) -> (fresh: bool)
        requires
            old(self).wf(),
            code <= VARINT_MAX,
        ensures
            final(self).wf(),
            send_step_ok(old(self).state(), final(self).state()),
            final(self).all_written() == old(self).all_written(),
            final(self).sent_end() == old(self).sent_end(),
            final(self).max() == old(self).max(),
            fresh == (old(self).state() is Ready || old(self).state() is Send
                || old(self).state() is DataSent),
            fresh ==> final(self).state() is ResetSent && final(self).reset_spec() == Some(
                (code, old(self).sent_end()),
            ) && final(self).pending_reset() == Some((code, old(self).sent_end()))
                && final(self).buffered_spec() == 0,
            !fresh ==> *final(self) == *old(self),
    {
        self.reset(code)
    }

    /// The peer's MAX_STREAM_DATA.
    pub fn on_max_stream_data(&mut self, max: u64)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).state() == old(self).state(),
            final(self).all_written() == old(self).all_written(),
            final(self).fin_written_spec() == old(self).fin_written_spec(),
            final(self).sent_end() == old(self).sent_end(),
            final(self).next_off() == old(self).next_off(),
            final(self).reset_spec() == old(self).reset_spec(),
            final(self).pending_reset() == old(self).pending_reset(),
            final(self).max() == if max > old(self).max() {
                max
            } else {
                old(self).max()
            },
    {
        self.credit.on_max(max);
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-3.3
    //# A sender MUST NOT send any of these frames from a terminal state
    //# ("Data Recvd" or "Reset Recvd").
    /// The RESET_STREAM `(code, final size)` to send, if any: only in Reset Sent.
    #[verifier::when_used_as_spec(pending_reset_spec)]
    pub fn pending_reset(&self) -> (r: Option<(u64, u64)>)
        ensures
            r == self.pending_reset_spec(),
    {
        match self.state {
            SendState::ResetSent => if self.reset_pending {
                self.reset
            } else {
                None
            },
            _ => None,
        }
    }

    /// The pending RESET_STREAM was sent.
    pub fn commit_reset(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).state() == old(self).state(),
            final(self).all_written() == old(self).all_written(),
            final(self).sent_end() == old(self).sent_end(),
            final(self).max() == old(self).max(),
            final(self).next_off() == old(self).next_off(),
            final(self).reset_spec() == old(self).reset_spec(),
            final(self).pending_reset() is None,
    {
        self.reset_pending = false;
    }

    /// The frame carrying our RESET_STREAM was lost: send it again, unchanged (§13.3).
    pub fn on_reset_lost(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).state() == old(self).state(),
            final(self).all_written() == old(self).all_written(),
            final(self).sent_end() == old(self).sent_end(),
            final(self).max() == old(self).max(),
            final(self).next_off() == old(self).next_off(),
            final(self).reset_spec() == old(self).reset_spec(),
            final(self).pending_reset() == if old(self).state() is ResetSent {
                old(self).reset_spec()
            } else {
                old(self).pending_reset()
            },
    {
        if let SendState::ResetSent = self.state {
            self.reset_pending = true;
        }
    }

    /// The RESET_STREAM was acknowledged.
    pub fn on_reset_acked(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            send_step_ok(old(self).state(), final(self).state()),
            final(self).state() == if old(self).state() is ResetSent {
                SendState::ResetRecvd
            } else {
                old(self).state()
            },
            final(self).all_written() == old(self).all_written(),
            final(self).sent_end() == old(self).sent_end(),
            final(self).max() == old(self).max(),
            final(self).reset_spec() == old(self).reset_spec(),
            final(self).pending_reset() is None
                || final(self).pending_reset() == old(self).pending_reset(),
    {
        if let SendState::ResetSent = self.state {
            self.state = SendState::ResetRecvd;
            self.reset_pending = false;
        }
    }

    /// The bytes `[off, off + len)`, and the FIN if `fin`, were acknowledged.
    pub fn on_data_acked(&mut self, off: u64, len: u64, fin: bool)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            send_step_ok(old(self).state(), final(self).state()),
            final(self).all_written() == old(self).all_written(),
            final(self).fin_written_spec() == old(self).fin_written_spec(),
            final(self).sent_end() == old(self).sent_end(),
            final(self).max() == old(self).max(),
            final(self).reset_spec() == old(self).reset_spec(),
            final(self).pending_reset() == old(self).pending_reset(),
            final(self).acked_base_spec() >= old(self).acked_base_spec(),
            old(self).state() is DataSent ==> (final(self).state() is DataRecvd <==> (
                final(self).acked_base_spec() == final(self).all_written().len()
                && final(self).fin_acked_spec())),
            !(old(self).state() is DataSent) ==> final(self).state() == old(self).state(),
            (no_data(old(self).state()) || old(self).state() is Ready)
                ==> *final(self) == *old(self),
    {
        match self.state {
            SendState::Send | SendState::DataSent => {},
            _ => return,
        }
        let ghost aw = self.all_written@;
        let ab = self.acked_base;
        let se = self.sent_end;
        let e = clamp_end(off, len, se);
        let s = if off > ab {
            off
        } else {
            ab
        };
        if s < e {
            range_insert(&mut self.acked, s, e, Ghost(ab), Ghost(se));
            range_remove(&mut self.lost, s, e, Ghost(ab), Ghost(se));
        }
        if fin {
            if let SendState::DataSent = self.state {
                self.fin_acked = true;
                self.fin_lost = false;
            }
        }
        // ponytail: the buffer is trimmed only once the acknowledged prefix is at least the
        // tail that `split_off` copies, so each copied byte is paid for by a freed one (O(written)
        // copying in total) at the cost of up to 2x the unacked bytes held; a head index as in
        // Reassembly if that slack matters.
        let ghost pre = *self;
        loop
            invariant
                self.core(),
                self.state == pre.state,
                self.state is Send || self.state is DataSent,
                self.all_written == pre.all_written,
                self.written == pre.written,
                self.sent_end == pre.sent_end,
                se == self.sent_end,
                aw == self.all_written@,
                self.credit == pre.credit,
                self.fin_written == pre.fin_written,
                self.fin_acked == pre.fin_acked,
                self.reset == pre.reset,
                self.reset_pending == pre.reset_pending,
                self.acked_base >= pre.acked_base,
            ensures
                self.acked@.len() == 0 || self.acked@[0].0 != self.acked_base || self.acked@[0].1
                    - self.acked_base < self.written - self.acked@[0].1,
            decreases self.written - self.acked_base,
        {
            if self.acked.len() == 0 || self.acked[0].0 != self.acked_base {
                break;
            }
            let ab = self.acked_base;
            let nb = self.acked[0].1;
            if nb - ab < self.written - nb {
                break;
            }
            if nb == self.written {
                // A fresh vec, not `clear()`: acknowledged space keeps no allocation
                // (TRUSTED.md: proven bounds are lengths, not capacities).
                self.buf = Vec::new();
            } else {
                let t = self.buf.split_off((nb - ab) as usize);
                self.buf = t;
            }
            range_remove(&mut self.acked, 0, nb, Ghost(ab), Ghost(se));
            range_remove(&mut self.lost, 0, nb, Ghost(ab), Ghost(se));
            self.acked_base = nb;
            proof {
                assert(self.buf@ =~= aw.subrange(nb as int, self.written as int));
                assert(in_bounds(self.acked@, nb, se));
                assert(in_bounds(self.lost@, nb, se));
            }
        }
        if let SendState::DataSent = self.state {
            if self.acked_base == self.written && self.fin_acked {
                self.state = SendState::DataRecvd;
            }
        }
    }

    /// The bytes `[off, off + len)`, and the FIN if `fin`, were lost: queue them again.
    pub fn on_data_lost(&mut self, off: u64, len: u64, fin: bool)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).state() == old(self).state(),
            final(self).all_written() == old(self).all_written(),
            final(self).fin_written_spec() == old(self).fin_written_spec(),
            final(self).sent_end() == old(self).sent_end(),
            final(self).max() == old(self).max(),
            final(self).reset_spec() == old(self).reset_spec(),
            final(self).pending_reset() == old(self).pending_reset(),
            final(self).acked_base_spec() == old(self).acked_base_spec(),
            (no_data(old(self).state()) || old(self).state() is Ready)
                ==> *final(self) == *old(self),
    {
        match self.state {
            SendState::Send | SendState::DataSent => {},
            _ => return,
        }
        let ab = self.acked_base;
        let se = self.sent_end;
        let e = clamp_end(off, len, se);
        let s = if off > ab {
            off
        } else {
            ab
        };
        if s < e {
            range_insert(&mut self.lost, s, e, Ghost(ab), Ghost(se));
        }
        if fin && !self.fin_acked {
            if let SendState::DataSent = self.state {
                self.fin_lost = true;
            }
        }
    }
}

} // verus!

impl SendStream {
    /// Test support: the send buffer's allocated capacity. Verus models `Vec` length, not
    /// capacity, so capacity release is checked by test only (TRUSTED.md).
    #[doc(hidden)]
    pub fn buf_capacity(&self) -> usize {
        self.buf.capacity()
    }
}
