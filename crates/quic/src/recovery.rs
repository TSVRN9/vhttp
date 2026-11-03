//! The loss recovery and congestion control hook (Phase 6 replaces the bodies, RFC 9002, and
//! `conn.rs`'s `fire_pto`, where a PTO drains the in-flight records).
//! Phase 6 keeps the call sites but may extend the signatures (send times and sizes for RTT
//! samples and persistent congestion).
// Used only in ghost code, which a plain `cargo build` erases.
#[allow(unused_imports)]
use crate::payload::*;
use vstd::prelude::*;

verus! {

// ponytail: placeholder recovery — fixed 999 ms initial PTO with doubling, packet-count AIMD window (10..64), PTO declares the space's in-flight data lost, against RFC 9002 §6.2 (a PTO "MUST NOT cause prior unacknowledged packets to be marked as lost"). Phase 6 (RFC 9002) replaces every body; the signatures stay.
/// kInitialRtt (333 ms) + 4 · (333 / 2) ms, the initial PTO of RFC 9002 §6.2.1 (Phase 6).
pub const PLACEHOLDER_PTO_US: u64 = 999_000;

pub const MAX_PTO_BACKOFF: u32 = 6;

pub const INITIAL_CWND_PACKETS: u64 = 10;

/// Ack-eliciting packets in flight at most, across all packet number spaces (3d2's gate sums
/// the three `SentPackets`); so also the memory cap on their records (3d D4).
pub const MAX_INFLIGHT: u64 = 64;

pub const MIN_CWND_PACKETS: u64 = 2;

/// `x + y`, saturating.
pub open spec fn sat_add(x: u64, y: u64) -> u64 {
    if x + y > u64::MAX {
        u64::MAX
    } else {
        (x + y) as u64
    }
}

/// `v << n`, saturating: `n` saturating doublings.
pub open spec fn sat_shl(v: u64, n: nat) -> u64
    decreases n,
{
    if n == 0 {
        v
    } else {
        sat_add(sat_shl(v, (n - 1) as nat), sat_shl(v, (n - 1) as nat))
    }
}

pub proof fn lemma_shl_grows(v: u64, a: nat, b: nat)
    requires
        a <= b,
    ensures
        sat_shl(v, a) <= sat_shl(v, b),
    decreases b - a,
{
    if a < b {
        lemma_shl_grows(v, a, (b - 1) as nat);
    }
}

/// The PTO before backoff: the 1-RTT space adds the peer's max_ack_delay (RFC 9002 §6.2.1).
pub open spec fn pto_base(space: PacketKind, peer_max_ack_delay_us: u64) -> u64 {
    match space {
        PacketKind::OneRtt => sat_add(PLACEHOLDER_PTO_US, peer_max_ack_delay_us),
        _ => PLACEHOLDER_PTO_US,
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Recovery {
    pto_count: u32,
    /// Congestion window, in packets.
    cwnd: u64,
}

impl Recovery {
    pub closed spec fn wf(&self) -> bool {
        &&& MIN_CWND_PACKETS <= self.cwnd <= MAX_INFLIGHT
        &&& self.pto_count <= MAX_PTO_BACKOFF
    }

    pub closed spec fn cwnd_spec(&self) -> u64 {
        self.cwnd
    }

    pub closed spec fn pto_count_spec(&self) -> u32 {
        self.pto_count
    }

    pub closed spec fn pto_us_spec(&self, space: PacketKind, peer_max_ack_delay_us: u64) -> u64 {
        sat_shl(pto_base(space, peer_max_ack_delay_us), self.pto_count as nat)
    }

    /// More PTOs fired, no shorter a PTO.
    pub proof fn lemma_pto_grows(&self, o: Recovery, space: PacketKind, mad: u64)
        requires
            self.pto_count_spec() <= o.pto_count_spec(),
        ensures
            self.pto_us_spec(space, mad) <= o.pto_us_spec(space, mad),
        decreases o.pto_count_spec() - self.pto_count_spec(),
    {
        lemma_shl_grows(pto_base(space, mad), self.pto_count as nat, o.pto_count as nat);
    }

    pub proof fn lemma_pto_pos(&self, space: PacketKind, mad: u64)
        ensures
            self.pto_us_spec(space, mad) >= PLACEHOLDER_PTO_US,
    {
        lemma_shl_grows(pto_base(space, mad), 0, self.pto_count as nat);
    }

    pub proof fn lemma_wf(&self)
        requires
            self.wf(),
        ensures
            MIN_CWND_PACKETS <= self.cwnd_spec() <= MAX_INFLIGHT,
            self.pto_count_spec() <= MAX_PTO_BACKOFF,
    {
    }

    pub fn new() -> (r: Recovery)
        ensures
            r.wf(),
            r.cwnd_spec() == INITIAL_CWND_PACKETS,
            r.pto_count_spec() == 0,
    {
        Recovery { pto_count: 0, cwnd: INITIAL_CWND_PACKETS }
    }

    /// The probe timeout for `space` (RFC 9002 §6.2.1, Phase 6), doubled per PTO fired.
    #[verifier::when_used_as_spec(pto_us_spec)]
    pub fn pto_us(&self, space: PacketKind, peer_max_ack_delay_us: u64) -> (r: u64)
        requires
            self.wf(),
        ensures
            r == self.pto_us_spec(space, peer_max_ack_delay_us),
    {
        let mut d = match space {
            PacketKind::OneRtt => PLACEHOLDER_PTO_US.saturating_add(peer_max_ack_delay_us),
            _ => PLACEHOLDER_PTO_US,
        };
        let mut i: u32 = 0;
        while i < self.pto_count
            invariant
                i <= self.pto_count,
                d == sat_shl(pto_base(space, peer_max_ack_delay_us), i as nat),
            decreases self.pto_count - i,
        {
            d = d.saturating_add(d);
            i = i + 1;
        }
        d
    }

    /// When the PTO for `space` fires: none while the anti-amplification limit blocks
    /// sending (RFC 9002 §6.2.2.1, Phase 6) or with nothing ack-eliciting in flight.
    pub fn pto_deadline(
        &self,
        space: PacketKind,
        last_sent: Option<u64>,
        peer_max_ack_delay_us: u64,
        amp_blocked: bool,
    ) -> (r: Option<u64>)
        requires
            self.wf(),
        ensures
            r == match last_sent {
                Some(t) => if amp_blocked {
                    None
                } else {
                    Some(sat_add(t, self.pto_us_spec(space, peer_max_ack_delay_us)))
                },
                None => None::<u64>,
            },
    {
        match last_sent {
            Some(t) => if amp_blocked {
                None
            } else {
                Some(t.saturating_add(self.pto_us(space, peer_max_ack_delay_us)))
            },
            None => None,
        }
    }

    /// Whether one more ack-eliciting packet fits the congestion window.
    pub fn can_send(&self, inflight_packets: u64) -> (r: bool)
        requires
            self.wf(),
        ensures
            r == (inflight_packets < self.cwnd_spec()),
            r ==> inflight_packets < MAX_INFLIGHT,
    {
        inflight_packets < self.cwnd
    }

    pub fn on_packet_sent(&mut self, _space: PacketKind, _pn: u64, _size: u64, _now: u64)
        requires
            old(self).wf(),
        ensures
            *final(self) == *old(self),
    {
    }

    /// `newly_acked` records were acknowledged: the PTO backoff resets and the window grows
    /// by one packet each, up to `MAX_INFLIGHT` (RFC 9002 §7, Phase 6).
    pub fn on_ack_received(
        &mut self,
        _space: PacketKind,
        newly_acked: usize,
        _ack_delay: u64,
        _now: u64,
    )
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            newly_acked > 0 ==> final(self).pto_count_spec() == 0,
            newly_acked > 0 ==> final(self).cwnd_spec() == vstd::math::min(
                old(self).cwnd_spec() + newly_acked,
                MAX_INFLIGHT as int,
            ),
            newly_acked == 0 ==> *final(self) == *old(self),
    {
        if newly_acked > 0 {
            self.pto_count = 0;
            if newly_acked as u64 >= MAX_INFLIGHT - self.cwnd {
                self.cwnd = MAX_INFLIGHT;
            } else {
                self.cwnd = self.cwnd + newly_acked as u64;
            }
        }
    }

    /// `lost` records were declared lost: the window halves, down to `MIN_CWND_PACKETS`
    /// (the §13.3 congestion action, 3d D6).
    pub fn on_packets_lost(&mut self, _space: PacketKind, lost: usize, _now: u64)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            lost > 0 ==> final(self).cwnd_spec() == if old(self).cwnd_spec() / 2 < MIN_CWND_PACKETS {
                MIN_CWND_PACKETS
            } else {
                old(self).cwnd_spec() / 2
            },
            final(self).pto_count_spec() == old(self).pto_count_spec(),
            lost == 0 ==> *final(self) == *old(self),
    {
        if lost > 0 {
            let h = self.cwnd / 2;
            self.cwnd = if h < MIN_CWND_PACKETS {
                MIN_CWND_PACKETS
            } else {
                h
            };
        }
    }

    /// A PTO fired: the next one waits twice as long, up to `MAX_PTO_BACKOFF` doublings.
    pub fn on_pto_fired(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).pto_count_spec() == if old(self).pto_count_spec() < MAX_PTO_BACKOFF {
                (old(self).pto_count_spec() + 1) as u32
            } else {
                MAX_PTO_BACKOFF
            },
            final(self).cwnd_spec() == old(self).cwnd_spec(),
    {
        if self.pto_count < MAX_PTO_BACKOFF {
            self.pto_count = self.pto_count + 1;
        }
    }

    /// A packet number space was discarded (RFC 9002 §6.4, Phase 6).
    pub fn on_space_discarded(&mut self, _space: PacketKind)
        requires
            old(self).wf(),
        ensures
            *final(self) == *old(self),
    {
    }

    /// The peer's address was validated on a new path: congestion state resets (§9.4).
    pub fn on_path_validated(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).cwnd_spec() == INITIAL_CWND_PACKETS,
            final(self).pto_count_spec() == 0,
    {
        self.pto_count = 0;
        self.cwnd = INITIAL_CWND_PACKETS;
    }
}

} // verus!
