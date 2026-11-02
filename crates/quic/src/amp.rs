//! The anti-amplification budget (RFC 9000 §8.1): before the client's address is validated,
//! a server sends at most three times the bytes it has received. The ghost trace records
//! every receive, send and validation; `amp_ok` holds at every prefix of it. Sans-IO: the
//! shell reports datagram sizes, 3d2 gates every send on `budget`.
use vstd::prelude::*;

verus! {

/// One event in a connection's life, for the amplification limit.
pub enum AmpEv {
    /// A datagram of this many bytes was received and attributed to the connection.
    Recv(nat),
    /// This many bytes were sent.
    Sent(nat),
    /// The client's address was validated.
    Validated,
}

pub open spec fn recv_sum(t: Seq<AmpEv>) -> nat
    decreases t.len(),
{
    if t.len() == 0 {
        0
    } else {
        recv_sum(t.drop_last()) + match t.last() {
            AmpEv::Recv(n) => n,
            _ => 0,
        }
    }
}

pub open spec fn sent_sum(t: Seq<AmpEv>) -> nat
    decreases t.len(),
{
    if t.len() == 0 {
        0
    } else {
        sent_sum(t.drop_last()) + match t.last() {
            AmpEv::Sent(n) => n,
            _ => 0,
        }
    }
}

pub open spec fn validated_in(t: Seq<AmpEv>) -> bool
    decreases t.len(),
{
    t.len() > 0 && (t.last() is Validated || validated_in(t.drop_last()))
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-8.1
//# Prior to validating the client address, servers MUST NOT send more
//# than three times as many bytes as the number of bytes they have
//# received.
/// §8.1 at every point of the trace: until validation, sent ≤ 3 × received.
pub open spec fn amp_ok(t: Seq<AmpEv>) -> bool {
    forall|i: int|
        #![trigger t.take(i)]
        0 <= i <= t.len() && !validated_in(t.take(i)) ==> sent_sum(t.take(i)) <= 3 * recv_sum(
            t.take(i),
        )
}

/// A send made before any receive is not excused by a later validation: `amp_ok` judges
/// every prefix, not only the whole trace.
pub proof fn lemma_amp_ok_prefixes()
    ensures
        !amp_ok(seq![AmpEv::Sent(1), AmpEv::Validated]),
{
    let t = seq![AmpEv::Sent(1), AmpEv::Validated];
    let p = t.take(1);
    assert(p =~= seq![AmpEv::Sent(1)]);
    assert(p.drop_last() =~= Seq::<AmpEv>::empty());
    assert(p.last() == AmpEv::Sent(1));
    assert(!validated_in(Seq::<AmpEv>::empty()));
    assert(sent_sum(Seq::<AmpEv>::empty()) == 0);
    assert(recv_sum(Seq::<AmpEv>::empty()) == 0);
    assert(!validated_in(p));
    assert(sent_sum(p) == 1);
    assert(recv_sum(p) == 0);
}

/// `amp_ok` extends to `t.push(e)` when the whole new trace satisfies it.
proof fn lemma_amp_push(t: Seq<AmpEv>, e: AmpEv)
    requires
        amp_ok(t),
        !validated_in(t.push(e)) ==> sent_sum(t.push(e)) <= 3 * recv_sum(t.push(e)),
    ensures
        amp_ok(t.push(e)),
{
    let u = t.push(e);
    assert forall|i: int|
        #![trigger u.take(i)]
        0 <= i <= u.len() && !validated_in(u.take(i)) implies sent_sum(u.take(i)) <= 3 * recv_sum(
        u.take(i),
    ) by {
        if i <= t.len() {
            assert(u.take(i) =~= t.take(i));
            // The old prefix, which only `amp_ok`'s every-prefix form provides.
            assert(sent_sum(t.take(i)) <= 3 * recv_sum(t.take(i)));
        } else {
            assert(u.take(i) =~= u);
        }
    }
}

/// The amplification state of one connection.
pub struct AmpBudget {
    recv: u64,
    sent: u64,
    validated: bool,
    trace: Ghost<Seq<AmpEv>>,
}

impl AmpBudget {
    pub closed spec fn wf(&self) -> bool {
        &&& amp_ok(self.trace@)
        &&& self.recv as nat == if recv_sum(self.trace@) > u64::MAX {
            u64::MAX as nat
        } else {
            recv_sum(self.trace@)
        }
        &&& !self.validated ==> self.sent as nat == sent_sum(self.trace@)
        &&& self.validated == validated_in(self.trace@)
    }

    pub closed spec fn trace(&self) -> Seq<AmpEv> {
        self.trace@
    }

    /// `u64::MAX - sent` once validated; before, `min(3·recv - sent, u64::MAX - sent)`.
    pub closed spec fn budget_spec(&self) -> u64 {
        let room = u64::MAX - self.sent;
        if self.validated {
            room as u64
        } else {
            let three = 3 * self.recv - self.sent;
            if three < room {
                three as u64
            } else {
                room as u64
            }
        }
    }

    pub fn new() -> (r: AmpBudget)
        ensures
            r.wf(),
            r.trace() == Seq::<AmpEv>::empty(),
            amp_ok(r.trace()),
            r.budget_spec() == 0,
    {
        let r = AmpBudget { recv: 0, sent: 0, validated: false, trace: Ghost(Seq::empty()) };
        proof {
            assert forall|i: int|
                #![trigger r.trace@.take(i)]
                0 <= i <= r.trace@.len() implies r.trace@.take(i) =~= Seq::<AmpEv>::empty() by {}
        }
        r
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-8.1
    //# For the purposes of
    //# avoiding amplification prior to address validation, servers MUST
    //# count all of the payload bytes received in datagrams that are
    //# uniquely attributed to a single connection.
    /// A datagram of `n` bytes attributed to this connection (3d2 calls it for every one,
    /// processed or discarded). The count saturates at `u64::MAX`.
    pub fn on_recv(&mut self, n: u64)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).trace() == old(self).trace().push(AmpEv::Recv(n as nat)),
            amp_ok(final(self).trace()),
    {
        let ghost t = self.trace@;
        proof {
            assert(t.take(t.len() as int) =~= t);
        }
        self.recv = self.recv.saturating_add(n);
        self.trace = Ghost(t.push(AmpEv::Recv(n as nat)));
        proof {
            let u = t.push(AmpEv::Recv(n as nat));
            assert(u.drop_last() =~= t);
            lemma_amp_push(t, AmpEv::Recv(n as nat));
        }
    }

    /// How many more bytes may be sent now.
    #[verifier::when_used_as_spec(budget_spec)]
    pub fn budget(&self) -> (b: u64)
        requires
            self.wf(),
        ensures
            b == self.budget_spec(),
            !validated_in(self.trace()) ==> sent_sum(self.trace()) + b <= 3 * recv_sum(
                self.trace(),
            ),
    {
        let room = u64::MAX - self.sent;
        if self.validated {
            room
        } else {
            proof {
                let t = self.trace@;
                assert(t.take(t.len() as int) =~= t);
            }
            let three = 3 * (self.recv as u128) - (self.sent as u128);
            if three < room as u128 {
                three as u64
            } else {
                room
            }
        }
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-8.1
    //# Prior to validating the client address, servers MUST NOT send more
    //# than three times as many bytes as the number of bytes they have
    //# received.
    /// `n` bytes were sent, within `budget()`.
    pub fn on_sent(&mut self, n: u64)
        requires
            old(self).wf(),
            n <= old(self).budget(),
        ensures
            final(self).wf(),
            final(self).trace() == old(self).trace().push(AmpEv::Sent(n as nat)),
            amp_ok(final(self).trace()),
    {
        let ghost t = self.trace@;
        proof {
            assert(t.take(t.len() as int) =~= t);
        }
        self.sent = self.sent + n;
        self.trace = Ghost(t.push(AmpEv::Sent(n as nat)));
        proof {
            let u = t.push(AmpEv::Sent(n as nat));
            assert(u.drop_last() =~= t);
            lemma_amp_push(t, AmpEv::Sent(n as nat));
        }
    }

    /// The client's address is validated (§8.1: a Handshake packet was processed).
    pub fn validate(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).trace() == old(self).trace().push(AmpEv::Validated),
            amp_ok(final(self).trace()),
    {
        let ghost t = self.trace@;
        self.validated = true;
        self.trace = Ghost(t.push(AmpEv::Validated));
        proof {
            let u = t.push(AmpEv::Validated);
            assert(u.drop_last() =~= t);
            lemma_amp_push(t, AmpEv::Validated);
        }
    }

    pub fn is_validated(&self) -> (r: bool)
        requires
            self.wf(),
        ensures
            r == validated_in(self.trace()),
    {
        self.validated
    }
}

} // verus!
