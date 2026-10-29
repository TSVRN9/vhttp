//! The idle timeout (RFC 9000 §10.1) and the closing and draining states (§10.2). Sans-IO:
//! the shell supplies times in microseconds and datagram sizes; 3d2 gates every send on
//! `Lifecycle::may_send_close`.
use vstd::prelude::*;
use vstd::slice::{slice_subrange, slice_to_vec};

use crate::amp::*;
use crate::codes::*;
use crate::frame::*;
use crate::payload::*;
#[allow(unused_imports)]
use wire::varint::*;

verus! {

pub open spec fn spec_ms_to_us(ms: u64) -> u64 {
    if ms > u64::MAX / 1000 {
        u64::MAX
    } else {
        (ms * 1000) as u64
    }
}

/// `3·p`, saturating.
pub open spec fn spec_sat3(p: u64) -> u64 {
    if p > u64::MAX / 3 {
        u64::MAX
    } else {
        (3 * p) as u64
    }
}

pub open spec fn spec_sat_add(a: u64, b: u64) -> u64 {
    if a + b > u64::MAX {
        u64::MAX
    } else {
        (a + b) as u64
    }
}

/// The smaller non-zero value, or 0 when both are 0.
pub open spec fn spec_min_nz(a: u64, b: u64) -> u64 {
    if a == 0 {
        b
    } else if b == 0 {
        a
    } else if a < b {
        a
    } else {
        b
    }
}

/// Milliseconds to microseconds, saturating.
pub fn ms_to_us(ms: u64) -> (r: u64)
    ensures
        r == spec_ms_to_us(ms),
{
    if ms > u64::MAX / 1000 {
        u64::MAX
    } else {
        ms * 1000
    }
}

pub(crate) fn sat3(p: u64) -> (r: u64)
    ensures
        r == spec_sat3(p),
{
    if p > u64::MAX / 3 {
        u64::MAX
    } else {
        3 * p
    }
}

pub(crate) fn sat_add(a: u64, b: u64) -> (r: u64)
    ensures
        r == spec_sat_add(a, b),
{
    if b > u64::MAX - a {
        u64::MAX
    } else {
        a + b
    }
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-10.1
//# To avoid excessively small idle timeout periods, endpoints MUST
//# increase the idle timeout period to be at least three times the
//# current Probe Timeout (PTO).
/// The idle timeout in effect: the smaller non-zero of ours and the peer's
/// `max_idle_timeout`, raised to at least `3·pto_us`; None when neither side has one.
pub fn effective_idle_us(local_ms: u64, peer_ms: Option<u64>, pto_us: u64) -> (r: Option<u64>)
    ensures
        r is None <==> (local_ms == 0 && peer_ms.unwrap_or(0) == 0),
        r matches Some(v) ==> {
            &&& v == spec_max(
                spec_ms_to_us(spec_min_nz(local_ms, peer_ms.unwrap_or(0))),
                spec_sat3(pto_us),
            )
            &&& v >= spec_sat3(pto_us)
            &&& (v == u64::MAX || v >= 3 * pto_us)
        },
{
    let p = match peer_ms {
        Some(x) => x,
        None => 0,
    };
    let m = if local_ms == 0 {
        p
    } else if p == 0 {
        local_ms
    } else if local_ms < p {
        local_ms
    } else {
        p
    };
    if m == 0 {
        None
    } else {
        let a = ms_to_us(m);
        let b = sat3(pto_us);
        Some(if a > b {
            a
        } else {
            b
        })
    }
}

pub open spec fn spec_max(a: u64, b: u64) -> u64 {
    if a > b {
        a
    } else {
        b
    }
}

/// When the idle timeout is measured from (§10.1).
pub struct IdleTimer {
    pub last: u64,
    pub eliciting_since_rx: bool,
}

impl IdleTimer {
    pub fn new(now: u64) -> (r: IdleTimer)
        ensures
            r.last == now,
            !r.eliciting_since_rx,
    {
        IdleTimer { last: now, eliciting_since_rx: false }
    }

    /// A packet was successfully processed.
    pub fn on_packet_processed(&mut self, now: u64)
        ensures
            final(self).last == now,
            !final(self).eliciting_since_rx,
    {
        self.last = now;
        self.eliciting_since_rx = false;
    }

    /// An ack-eliciting packet was sent: restarts the timer only if none was sent since the
    /// last packet processed.
    pub fn on_eliciting_sent(&mut self, now: u64)
        ensures
            final(self).last == if old(self).eliciting_since_rx {
                old(self).last
            } else {
                now
            },
            final(self).eliciting_since_rx,
    {
        if !self.eliciting_since_rx {
            self.last = now;
        }
        self.eliciting_since_rx = true;
    }

    pub fn deadline(&self, eff: u64) -> (r: u64)
        ensures
            r == spec_sat_add(self.last, eff),
    {
        sat_add(self.last, eff)
    }
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-10.2.3
//# A CONNECTION_CLOSE of type 0x1d MUST be replaced by a
//# CONNECTION_CLOSE of type 0x1c when sending the frame in Initial or
//# Handshake packets.
//= https://www.rfc-editor.org/rfc/rfc9000#section-10.2.3
//# Endpoints MUST clear the value of the
//# Reason Phrase field and SHOULD use the APPLICATION_ERROR code when
//# converting to a CONNECTION_CLOSE of type 0x1c.
/// The CONNECTION_CLOSE to send in a packet of kind `space`.
pub fn close_frame(app: bool, code: u64, reason: &[u8], space: PacketKind) -> (f: Frame)
    requires
        code <= VARINT_MAX,
        reason.len() <= 64,
    ensures
        frame_wf(f@),
        frame_permitted(spec_frame_type(f@), space),
        f matches Frame::ConnectionClose { app: a, error_code: c, frame_type: t, reason: r } && t
            == 0 && if app && space != PacketKind::OneRtt {
            !a && c == APPLICATION_ERROR && r@.len() == 0
        } else {
            a == app && c == code && r@ == reason@
        },
{
    if app && !matches!(space, PacketKind::OneRtt) {
        Frame::ConnectionClose {
            app: false,
            error_code: APPLICATION_ERROR,
            frame_type: 0,
            reason: Vec::new(),
        }
    } else {
        Frame::ConnectionClose {
            app,
            error_code: code,
            frame_type: 0,
            reason: slice_to_vec(reason),
        }
    }
}

/// The packet spaces a close is sent in, as a sequence.
pub open spec fn spec_close_spaces(i: bool, h: bool, o: bool) -> Seq<PacketKind> {
    (if i {
        seq![PacketKind::Initial]
    } else {
        Seq::empty()
    }) + (if h {
        seq![PacketKind::Handshake]
    } else {
        Seq::empty()
    }) + (if o {
        seq![PacketKind::OneRtt]
    } else {
        Seq::empty()
    })
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-10.2.3
//# After the handshake is confirmed (see
//# Section 4.1.2 of [QUIC-TLS]), an endpoint MUST send any
//# CONNECTION_CLOSE frames in a 1-RTT packet.
/// The spaces to send a CONNECTION_CLOSE in: 1-RTT only once the handshake is confirmed,
/// otherwise every space whose keys we still hold.
pub fn close_spaces(
    confirmed: bool,
    initial_live: bool,
    handshake_live: bool,
    one_rtt_live: bool,
) -> (r: Vec<PacketKind>)
    ensures
        confirmed ==> r@ == seq![PacketKind::OneRtt],
        !confirmed ==> r@ == spec_close_spaces(initial_live, handshake_live, one_rtt_live),
{
    let mut v = Vec::new();
    if confirmed {
        v.push(PacketKind::OneRtt);
        return v;
    }
    if initial_live {
        v.push(PacketKind::Initial);
    }
    if handshake_live {
        v.push(PacketKind::Handshake);
    }
    if one_rtt_live {
        v.push(PacketKind::OneRtt);
    }
    proof {
        assert(v@ =~= spec_close_spaces(initial_live, handshake_live, one_rtt_live));
    }
    v
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Phase {
    Open,
    Closing,
    Draining,
    Closed,
}

pub open spec fn phase_rank(p: Phase) -> int {
    match p {
        Phase::Open => 0,
        Phase::Closing => 1,
        Phase::Draining => 2,
        Phase::Closed => 3,
    }
}

/// The phase order: Open, Closing, Draining, Closed (and Open before Draining).
pub open spec fn phase_le(a: Phase, b: Phase) -> bool {
    phase_rank(a) <= phase_rank(b)
}

// §11: a stateless reset is for a connection with no state; this one keeps its state in
// Closing and Draining.
//= https://www.rfc-editor.org/rfc/rfc9000#section-11
//= type=exception
//= reason=We never send a Stateless Reset.
//# A
//# stateless reset MUST NOT be used by an endpoint that has the state
//# necessary to send a frame on the connection.
/// The connection's lifecycle. `budget` counts only the closing state's own receives and
/// repeat sends; the first CONNECTION_CLOSE is covered by the connection's budget (3d2).
pub struct Lifecycle {
    phase: Phase,
    deadline: Option<u64>,
    close: Option<(bool, u64, Vec<u8>)>,
    first_sent: bool,
    owed: bool,
    budget: AmpBudget,
}

impl Lifecycle {
    pub closed spec fn phase_spec(&self) -> Phase {
        self.phase
    }

    pub closed spec fn deadline_spec(&self) -> Option<u64> {
        self.deadline
    }

    pub closed spec fn close_spec(&self) -> Option<(bool, u64, Seq<u8>)> {
        match self.close {
            Some((a, c, r)) => Some((a, c, r@)),
            None => None,
        }
    }

    pub closed spec fn first_sent_spec(&self) -> bool {
        self.first_sent
    }

    pub closed spec fn owed_spec(&self) -> bool {
        self.owed
    }

    pub closed spec fn budget_trace(&self) -> Seq<AmpEv> {
        self.budget.trace()
    }

    pub closed spec fn wf(&self) -> bool {
        &&& self.budget.wf()
        &&& amp_ok(self.budget.trace())
        &&& self.phase is Closing ==> self.close is Some && self.deadline is Some
        &&& self.phase is Open ==> !self.first_sent
        &&& self.close matches Some((_, c, r)) ==> c <= VARINT_MAX && r@.len() <= 64
    }

    pub closed spec fn within_budget(&self, n: u64) -> bool {
        n <= self.budget.budget()
    }

    /// The closing state's send decision, as the RFC states it.
    pub closed spec fn may_send_spec(&self, n: u64) -> bool {
        self.phase is Closing && self.owed && (!self.first_sent || n <= self.budget.budget())
    }

    pub fn new() -> (r: Lifecycle)
        ensures
            r.wf(),
            r.phase_spec() == Phase::Open,
    {
        Lifecycle {
            phase: Phase::Open,
            deadline: None,
            close: None,
            first_sent: false,
            owed: false,
            budget: AmpBudget::new(),
        }
    }

    #[verifier::when_used_as_spec(phase_spec)]
    pub fn phase(&self) -> (r: Phase)
        ensures
            r == self.phase_spec(),
    {
        self.phase
    }

    #[verifier::when_used_as_spec(deadline_spec)]
    pub fn deadline(&self) -> (r: Option<u64>)
        ensures
            r == self.deadline_spec(),
    {
        self.deadline
    }

    pub fn close_info(&self) -> (r: &Option<(bool, u64, Vec<u8>)>)
        requires
            self.wf(),
        ensures
            r matches Some((a, c, v)) ==> self.close_spec() == Some((*a, *c, v@)),
            r is None ==> self.close_spec() is None,
            r matches Some((_, c, v)) ==> *c <= VARINT_MAX && v@.len() <= 64,
    {
        &self.close
    }

    /// Enter the closing state with this error; only from Open (the first error wins, §11.1).
    pub fn enter_closing(&mut self, now: u64, pto_us: u64, app: bool, code: u64, reason: &[u8])
        requires
            old(self).wf(),
            code <= VARINT_MAX,
        ensures
            final(self).wf(),
            phase_le(old(self).phase_spec(), final(self).phase_spec()),
            old(self).phase_spec() is Open ==> {
                &&& final(self).phase_spec() == Phase::Closing
                &&& final(self).deadline_spec() == Some(spec_sat_add(now, spec_sat3(pto_us)))
                &&& final(self).owed_spec()
                &&& !final(self).first_sent_spec()
                &&& final(self).close_spec() matches Some((a, c, r)) && a == app && c == code
                    && r == reason@.take(if reason@.len() > 64 {
                    64int
                } else {
                    reason@.len() as int
                })
            },
            !(old(self).phase_spec() is Open) ==> {
                &&& final(self).phase_spec() == old(self).phase_spec()
                &&& final(self).deadline_spec() == old(self).deadline_spec()
                &&& final(self).close_spec() == old(self).close_spec()
                &&& final(self).owed_spec() == old(self).owed_spec()
                &&& final(self).first_sent_spec() == old(self).first_sent_spec()
                &&& final(self).budget_trace() == old(self).budget_trace()
            },
            amp_ok(final(self).budget_trace()),
    {
        if let Phase::Open = self.phase {
            // ponytail: 64-byte reason cap.
            let k = if reason.len() > 64 {
                64
            } else {
                reason.len()
            };
            let r = slice_to_vec(slice_subrange(reason, 0, k));
            self.close = Some((app, code, r));
            self.phase = Phase::Closing;
            self.deadline = Some(sat_add(now, sat3(pto_us)));
            self.owed = true;
        }
    }

    /// Enter the draining state (a CONNECTION_CLOSE was received); from Open or Closing.
    pub fn enter_draining(&mut self, now: u64, pto_us: u64)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            phase_le(old(self).phase_spec(), final(self).phase_spec()),
            (old(self).phase_spec() is Open || old(self).phase_spec() is Closing) ==> {
                &&& final(self).phase_spec() == Phase::Draining
                &&& final(self).deadline_spec() == Some(spec_sat_add(now, spec_sat3(pto_us)))
            },
            !(old(self).phase_spec() is Open || old(self).phase_spec() is Closing) ==> {
                &&& final(self).phase_spec() == old(self).phase_spec()
                &&& final(self).deadline_spec() == old(self).deadline_spec()
            },
            final(self).close_spec() == old(self).close_spec(),
            amp_ok(final(self).budget_trace()),
    {
        match self.phase {
            Phase::Open | Phase::Closing => {
                self.phase = Phase::Draining;
                self.deadline = Some(sat_add(now, sat3(pto_us)));
            },
            _ => {},
        }
    }

    pub fn close_silently(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).phase_spec() == Phase::Closed,
            phase_le(old(self).phase_spec(), final(self).phase_spec()),
    {
        self.phase = Phase::Closed;
    }

    /// A datagram of `n` bytes arrived while closing: it counts toward the budget and a
    /// close is owed in reply.
    pub fn on_recv_closing(&mut self, n: u64)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).phase_spec() == old(self).phase_spec(),
            phase_le(old(self).phase_spec(), final(self).phase_spec()),
            final(self).close_spec() == old(self).close_spec(),
            final(self).deadline_spec() == old(self).deadline_spec(),
            final(self).first_sent_spec() == old(self).first_sent_spec(),
            amp_ok(final(self).budget_trace()),
    {
        if let Phase::Closing = self.phase {
            self.budget.on_recv(n);
            self.owed = true;
        }
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-10.2.1
    //# An endpoint in the closing state MUST either discard
    //# packets received from an unvalidated address or limit the cumulative
    //# size of packets it sends to an unvalidated address to three times the
    //# size of packets it receives from that address.
    //= https://www.rfc-editor.org/rfc/rfc9000#section-10.2.1
    //# To avoid being used for an amplification attack,
    //# such endpoints MUST limit the cumulative size of packets it sends to
    //# three times the cumulative size of the packets that are received and
    //# attributed to the connection.
    //= https://www.rfc-editor.org/rfc/rfc9000#section-10.2.2
    //# While otherwise identical to the closing state, an
    //# endpoint in the draining state MUST NOT send any packets.
    //= https://www.rfc-editor.org/rfc/rfc9000#section-10.2.2
    //# An endpoint
    //# MUST NOT send further packets.
    /// A close of `n` bytes may be sent now: only while Closing, only when owed, and after
    /// the first send within the closing budget.
    #[verifier::when_used_as_spec(may_send_spec)]
    pub fn may_send_close(&self, n: u64) -> (r: bool)
        requires
            self.wf(),
        ensures
            r == self.may_send_spec(n),
            r ==> self.phase_spec() is Closing,
            r && self.first_sent_spec() ==> self.within_budget(n),
    {
        match self.phase {
            Phase::Closing => self.owed && (!self.first_sent || n <= self.budget.budget()),
            _ => false,
        }
    }

    pub fn on_close_sent(&mut self, n: u64)
        requires
            old(self).wf(),
            old(self).may_send_spec(n),
        ensures
            final(self).wf(),
            final(self).phase_spec() == old(self).phase_spec(),
            phase_le(old(self).phase_spec(), final(self).phase_spec()),
            !final(self).owed_spec(),
            final(self).first_sent_spec(),
            final(self).close_spec() == old(self).close_spec(),
            final(self).deadline_spec() == old(self).deadline_spec(),
            amp_ok(final(self).budget_trace()),
            old(self).first_sent_spec() ==> final(self).budget_trace()
                == old(self).budget_trace().push(AmpEv::Sent(n as nat)),
    {
        if self.first_sent {
            self.budget.on_sent(n);
        }
        self.first_sent = true;
        self.owed = false;
    }

    pub fn on_timeout(&mut self, now: u64)
        requires
            old(self).wf(),
        ensures
            final(self).close_spec() == old(self).close_spec(),
            final(self).wf(),
            phase_le(old(self).phase_spec(), final(self).phase_spec()),
            (old(self).phase_spec() is Closing || old(self).phase_spec() is Draining)
                && (old(self).deadline_spec() matches Some(d) && now >= d)
                ==> final(self).phase_spec() == Phase::Closed,
    {
        match self.phase {
            Phase::Closing | Phase::Draining => {
                if let Some(d) = self.deadline {
                    if now >= d {
                        self.phase = Phase::Closed;
                    }
                }
            },
            _ => {},
        }
    }
}

} // verus!
