//! QUIC credit counters (RFC 9000 §4): the receiver's advertised limit with its pending
//! update, and the sender's peer-granted limit. One rule drives MAX_DATA, MAX_STREAM_DATA
//! and MAX_STREAMS.
use vstd::prelude::*;
// Used only in ghost code, which a plain `cargo build` erases.
#[allow(unused_imports)]
use wire::varint::*;

verus! {

// ponytail: half-window threshold, fixed window; autotune per §4.2 if throughput needs it
/// An update is due once less than half the window remains unconsumed.
pub open spec fn credit_due(limit: u64, consumed: u64, window: u64) -> bool {
    2 * (limit - consumed) < window
}

/// The limit to advertise: a full window past what was consumed, capped.
pub open spec fn credit_target(consumed: u64, window: u64, cap: u64) -> u64 {
    if consumed + window < cap {
        (consumed + window) as u64
    } else {
        cap
    }
}

/// The pending update after `consumed` was reached: a new target if one is due and larger
/// than the limit as sent, else the previous pending value.
pub open spec fn credit_after(limit: u64, consumed: u64, window: u64, cap: u64, prev: Option<u64>) -> Option<
    u64,
> {
    if credit_due(limit, consumed, window) && credit_target(consumed, window, cap) > limit {
        Some(credit_target(consumed, window, cap))
    } else {
        prev
    }
}

/// The value to send again after a loss: `max(prev.unwrap_or(0), limit)`.
pub open spec fn credit_resend(prev: Option<u64>, limit: u64) -> u64 {
    match prev {
        Some(v) => if v > limit {
            v
        } else {
            limit
        },
        None => limit,
    }
}

/// The receiver side of a credit: `limit` is the value as sent, `next` an update not yet sent.
pub struct RecvCredit {
    limit: u64,
    consumed: u64,
    window: u64,
    cap: u64,
    next: Option<u64>,
}

impl RecvCredit {
    pub closed spec fn wf(&self) -> bool {
        &&& self.consumed <= self.limit <= self.cap <= VARINT_MAX
        &&& self.window <= self.cap
        &&& self.next matches Some(v) ==> self.limit <= v <= self.cap
    }

    pub closed spec fn limit_spec(&self) -> u64 {
        self.limit
    }

    pub closed spec fn consumed_spec(&self) -> u64 {
        self.consumed
    }

    pub closed spec fn pending_spec(&self) -> Option<u64> {
        self.next
    }

    pub closed spec fn window_spec(&self) -> u64 {
        self.window
    }

    pub closed spec fn cap_spec(&self) -> u64 {
        self.cap
    }

    /// The invariant, in terms of the accessors.
    pub proof fn lemma_wf(&self)
        requires
            self.wf(),
        ensures
            self.consumed_spec() <= self.limit_spec() <= self.cap_spec() <= VARINT_MAX,
            self.window_spec() <= self.cap_spec(),
            self.pending_spec() matches Some(v) ==> self.limit_spec() <= v <= self.cap_spec(),
    {
    }

    pub fn new(window: u64, cap: u64) -> (r: RecvCredit)
        requires
            window <= cap <= VARINT_MAX,
        ensures
            r.wf(),
            r.limit_spec() == window,
            r.consumed_spec() == 0,
            r.pending_spec() is None,
            r.window_spec() == window,
            r.cap_spec() == cap,
    {
        RecvCredit { limit: window, consumed: 0, window, cap, next: None }
    }

    #[verifier::when_used_as_spec(limit_spec)]
    pub fn limit(&self) -> (r: u64)
        ensures
            r == self.limit_spec(),
    {
        self.limit
    }

    #[verifier::when_used_as_spec(consumed_spec)]
    pub fn consumed(&self) -> (r: u64)
        ensures
            r == self.consumed_spec(),
    {
        self.consumed
    }

    #[verifier::when_used_as_spec(pending_spec)]
    pub fn pending(&self) -> (r: Option<u64>)
        ensures
            r == self.pending_spec(),
    {
        self.next
    }

    /// Counts `n` more units consumed; the update depends on consumption alone.
    pub fn on_consumed(&mut self, n: u64)
        requires
            old(self).wf(),
            old(self).consumed() + n <= old(self).limit(),
        ensures
            final(self).wf(),
            final(self).consumed() == old(self).consumed() + n,
            final(self).limit() == old(self).limit(),
            final(self).window_spec() == old(self).window_spec(),
            final(self).cap_spec() == old(self).cap_spec(),
            final(self).pending() == credit_after(
                old(self).limit(),
                final(self).consumed(),
                old(self).window_spec(),
                old(self).cap_spec(),
                old(self).pending(),
            ),
    {
        self.consumed = self.consumed + n;
        let target = if self.consumed + self.window < self.cap {
            self.consumed + self.window
        } else {
            self.cap
        };
        if 2 * (self.limit - self.consumed) < self.window && target > self.limit {
            self.next = Some(target);
        }
    }

    /// The pending update was sent: it becomes the enforced limit.
    pub fn commit(&mut self)
        requires
            old(self).wf(),
            old(self).pending() is Some,
        ensures
            final(self).wf(),
            final(self).limit() == old(self).pending()->0,
            final(self).pending() is None,
            final(self).consumed() == old(self).consumed(),
            final(self).window_spec() == old(self).window_spec(),
            final(self).cap_spec() == old(self).cap_spec(),
    {
        if let Some(v) = self.next {
            self.limit = v;
        }
        self.next = None;
    }

    /// The frame carrying the limit was lost: send the current value again.
    pub fn on_lost(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).pending() == Some(credit_resend(old(self).pending(), old(self).limit())),
            final(self).limit() == old(self).limit(),
            final(self).consumed() == old(self).consumed(),
            final(self).window_spec() == old(self).window_spec(),
            final(self).cap_spec() == old(self).cap_spec(),
    {
        let cur = match self.next {
            Some(v) => v,
            None => 0,
        };
        self.next = Some(if cur > self.limit { cur } else { self.limit });
    }
}

/// The sender side of a credit (§4.1): the peer's limit and how much of it was used.
pub struct SendCredit {
    max: u64,
    used: u64,
}

impl SendCredit {
    pub closed spec fn wf(&self) -> bool {
        self.used <= self.max
    }

    pub closed spec fn max_spec(&self) -> u64 {
        self.max
    }

    pub closed spec fn used_spec(&self) -> u64 {
        self.used
    }

    pub closed spec fn available_spec(&self) -> u64 {
        (self.max - self.used) as u64
    }

    /// The invariant, in terms of the accessors.
    pub proof fn lemma_wf(&self)
        requires
            self.wf(),
        ensures
            self.used_spec() <= self.max_spec(),
            self.available_spec() == self.max_spec() - self.used_spec(),
    {
    }

    pub fn new(max: u64) -> (r: SendCredit)
        ensures
            r.wf(),
            r.max_spec() == max,
            r.used_spec() == 0,
    {
        SendCredit { max, used: 0 }
    }

    #[verifier::when_used_as_spec(max_spec)]
    pub fn max(&self) -> (r: u64)
        ensures
            r == self.max_spec(),
    {
        self.max
    }

    #[verifier::when_used_as_spec(used_spec)]
    pub fn used(&self) -> (r: u64)
        ensures
            r == self.used_spec(),
    {
        self.used
    }

    #[verifier::when_used_as_spec(available_spec)]
    pub fn available(&self) -> (r: u64)
        requires
            self.wf(),
        ensures
            r == self.available_spec(),
    {
        self.max - self.used
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-4.1
    //# A sender MUST ignore any MAX_STREAM_DATA or MAX_DATA frames that do
    //# not increase flow control limits.
    pub fn on_max(&mut self, v: u64)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).max() == if v > old(self).max() {
                v
            } else {
                old(self).max()
            },
            final(self).used() == old(self).used(),
    {
        if v > self.max {
            self.max = v;
        }
    }

    pub fn consume(&mut self, n: u64)
        requires
            old(self).wf(),
            n <= old(self).available(),
        ensures
            final(self).wf(),
            final(self).max() == old(self).max(),
            final(self).used() == old(self).used() + n,
    {
        self.used = self.used + n;
    }
}

} // verus!
