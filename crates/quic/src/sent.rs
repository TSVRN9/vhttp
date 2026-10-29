//! Sent packets, one `SentPackets` per packet number space (RFC 9000 §12.3, §13.1): packet
//! number allocation, the records of ack-eliciting packets in flight, and incoming ACK frames.
//! ACK-only packets are never recorded, so no record waits for an acknowledgment that never
//! comes (3d D5).
use vstd::prelude::*;

use crate::ack::*;
use crate::codes::*;
use crate::frame::*;
// Used only in ghost code, which a plain `cargo build` erases.
#[allow(unused_imports)]
use crate::payload::*;

verus! {

// ponytail: ACK ranges read per incoming frame (D4); older ranges are ignored and those packets later count as lost.
pub const MAX_ACK_RANGES_IN: usize = 64;

/// `a` acknowledges `pn` in its First ACK Range or one of the next `MAX_ACK_RANGES_IN`.
pub open spec fn ack_contains_capped(a: SpecAck, pn: u64) -> bool {
    exists|i: int|
        -1 <= i < vstd::math::min(a.ranges.len() as int, MAX_ACK_RANGES_IN as int) && (#[trigger] ack_range(
            a,
            i,
        )).0 <= pn <= ack_range(a, i).1
}

pub proof fn lemma_capped_implies(a: SpecAck, pn: u64)
    requires
        ack_contains_capped(a, pn),
    ensures
        ack_contains(a, pn),
{
    let i = choose|i: int|
        -1 <= i < vstd::math::min(a.ranges.len() as int, MAX_ACK_RANGES_IN as int) && (#[trigger] ack_range(
            a,
            i,
        )).0 <= pn <= ack_range(a, i).1;
    assert(ack_range(a, i).0 <= pn <= ack_range(a, i).1);
}

/// One ack-eliciting packet in flight. `frames` holds only the retransmittable frames: every
/// frame but PADDING, PING, ACK, CONNECTION_CLOSE, PATH_CHALLENGE and PATH_RESPONSE. `size`
/// is the packet's length on the wire (`out_packet_len`).
#[derive(Debug, PartialEq, Eq)]
pub struct SentPacket {
    pub pn: u64,
    pub time: u64,
    pub size: u64,
    pub ack_eliciting: bool,
    pub frames: Vec<Frame>,
}

pub struct SpecSentPacket {
    pub pn: u64,
    pub time: u64,
    pub size: u64,
    pub ack_eliciting: bool,
    pub frames: Seq<SpecFrame>,
}

impl View for SentPacket {
    type V = SpecSentPacket;

    open spec fn view(&self) -> SpecSentPacket {
        SpecSentPacket {
            pn: self.pn,
            time: self.time,
            size: self.size,
            ack_eliciting: self.ack_eliciting,
            frames: frames_view(self.frames@),
        }
    }
}

/// Some record in `s` has packet number `pn`.
pub open spec fn has_pn(s: Seq<SentPacket>, pn: u64) -> bool {
    exists|i: int| 0 <= i < s.len() && (#[trigger] s[i]).pn == pn
}

/// Packet numbers strictly ascending.
pub open spec fn ascending(s: Seq<SentPacket>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> (#[trigger] s[i]).pn < (#[trigger] s[j]).pn
}

/// The records of `s` that `a` acknowledges (within the range cap), in order.
pub open spec fn acked_of(a: SpecAck, s: Seq<SentPacket>) -> Seq<SentPacket>
    decreases s.len(),
{
    if s.len() == 0 {
        s
    } else if ack_contains_capped(a, s.last().pn) {
        acked_of(a, s.drop_last()).push(s.last())
    } else {
        acked_of(a, s.drop_last())
    }
}

/// The records of `s` that `a` does not acknowledge, in order.
pub open spec fn unacked_of(a: SpecAck, s: Seq<SentPacket>) -> Seq<SentPacket>
    decreases s.len(),
{
    if s.len() == 0 {
        s
    } else if ack_contains_capped(a, s.last().pn) {
        unacked_of(a, s.drop_last())
    } else {
        unacked_of(a, s.drop_last()).push(s.last())
    }
}

/// The packets sent in one packet number space.
pub struct SentPackets {
    next_pn: u64,
    largest_acked: Option<u64>,
    /// Ascending packet number; ack-eliciting packets only.
    inflight: Vec<SentPacket>,
    /// Every packet number handed out by `take_pn` (or skipped by `new_at`).
    issued: Ghost<Set<u64>>,
}

impl SentPackets {
    pub closed spec fn wf(&self) -> bool {
        &&& self.next_pn <= PN_MAX
        &&& forall|p: u64| #[trigger] self.issued@.contains(p) <==> p < self.next_pn
        &&& ascending(self.inflight@)
        &&& forall|i: int|
            0 <= i < self.inflight@.len() ==> {
                &&& (#[trigger] self.inflight@[i]).ack_eliciting
                &&& self.issued@.contains(self.inflight@[i].pn)
            }
        &&& self.largest_acked matches Some(a) ==> a < self.next_pn
    }

    /// Every packet number already used in this space.
    pub closed spec fn issued(&self) -> Set<u64> {
        self.issued@
    }

    pub closed spec fn next_pn_spec(&self) -> u64 {
        self.next_pn
    }

    pub closed spec fn largest_acked_spec(&self) -> Option<u64> {
        self.largest_acked
    }

    /// The records in flight, ascending.
    pub closed spec fn inflight_spec(&self) -> Seq<SentPacket> {
        self.inflight@
    }

    /// The invariant, in terms of the accessors.
    pub proof fn lemma_wf(&self)
        requires
            self.wf(),
        ensures
            self.next_pn_spec() <= PN_MAX,
            forall|p: u64| #[trigger] self.issued().contains(p) <==> p < self.next_pn_spec(),
            ascending(self.inflight_spec()),
            forall|i: int|
                0 <= i < self.inflight_spec().len() ==> {
                    &&& (#[trigger] self.inflight_spec()[i]).ack_eliciting
                    &&& self.issued().contains(self.inflight_spec()[i].pn)
                    &&& self.inflight_spec()[i].pn < self.next_pn_spec()
                },
            self.largest_acked_spec() matches Some(a) ==> a < self.next_pn_spec(),
    {
        assert forall|i: int| 0 <= i < self.inflight_spec().len() implies {
            &&& (#[trigger] self.inflight_spec()[i]).ack_eliciting
            &&& self.issued().contains(self.inflight_spec()[i].pn)
            &&& self.inflight_spec()[i].pn < self.next_pn_spec()
        } by {
            assert(self.issued@.contains(self.inflight@[i].pn));
        }
    }

    pub fn new() -> (r: SentPackets)
        ensures
            r.wf(),
            r.next_pn_spec() == 0,
            r.issued() == Set::<u64>::empty(),
            r.largest_acked_spec() is None,
            r.inflight_spec().len() == 0,
    {
        let r = SentPackets {
            next_pn: 0,
            largest_acked: None,
            inflight: Vec::new(),
            issued: Ghost(Set::empty()),
        };
        assert(r.issued@ =~= Set::<u64>::empty());
        r
    }

    /// Starts at packet number `next`, as if every smaller one were used (tests).
    pub fn new_at(next: u64) -> (r: SentPackets)
        requires
            next <= PN_MAX,
        ensures
            r.wf(),
            r.next_pn_spec() == next,
            r.largest_acked_spec() is None,
            r.inflight_spec().len() == 0,
    {
        proof {
            vstd::set_lib::range_set_properties::<u64>(0, next);
        }
        SentPackets {
            next_pn: next,
            largest_acked: None,
            inflight: Vec::new(),
            issued: Ghost(Set::<u64>::range(0, next)),
        }
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-12.3
    //# Subsequent packets sent in the same packet
    //# number space MUST increase the packet number by at least one.
    //
    //= https://www.rfc-editor.org/rfc/rfc9000#section-12.3
    //# A QUIC endpoint MUST NOT reuse a packet number within the same packet
    //# number space in one connection.
    /// The packet number for the next packet, larger than every one used before.
    pub fn take_pn(&mut self) -> (r: Option<u64>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            (r is Some) == (old(self).next_pn_spec() < PN_MAX),
            r matches Some(n) ==> {
                &&& n == old(self).next_pn_spec()
                &&& final(self).next_pn_spec() == n + 1
                &&& final(self).issued() == old(self).issued().insert(n)
                &&& forall|p: u64| #[trigger] old(self).issued().contains(p) ==> p < n
            },
            r is None ==> final(self).next_pn_spec() == old(self).next_pn_spec(),
            r is None ==> final(self).issued() == old(self).issued(),
            final(self).inflight_spec() == old(self).inflight_spec(),
            final(self).largest_acked_spec() == old(self).largest_acked_spec(),
    {
        if self.next_pn < PN_MAX {
            let n = self.next_pn;
            self.next_pn = n + 1;
            self.issued = Ghost(self.issued@.insert(n));
            assert forall|i: int| 0 <= i < self.inflight@.len() implies {
                &&& (#[trigger] self.inflight@[i]).ack_eliciting
                &&& self.issued@.contains(self.inflight@[i].pn)
            } by {
                assert(old(self).issued@.contains(self.inflight@[i].pn));
            }
            Some(n)
        } else {
            //= https://www.rfc-editor.org/rfc/rfc9000#section-12.3
            //# If the packet number for sending
            //# reaches 2^62-1, the sender MUST close the connection without sending
            //# a CONNECTION_CLOSE frame or any further packets; an endpoint MAY send
            //# a Stateless Reset (Section 10.3) in response to further packets that
            //# it receives.
            None
        }
    }

    /// Records ack-eliciting packet `p`, just sent with the last packet number taken.
    /// ACK-only packets are never recorded (3d D5).
    pub fn on_sent(&mut self, p: SentPacket)
        requires
            old(self).wf(),
            p.ack_eliciting,
            p.pn + 1 == old(self).next_pn_spec(),
            !has_pn(old(self).inflight_spec(), p.pn),
        ensures
            final(self).wf(),
            final(self).inflight_spec() == old(self).inflight_spec().push(p),
            final(self).next_pn_spec() == old(self).next_pn_spec(),
            final(self).issued() == old(self).issued(),
            final(self).largest_acked_spec() == old(self).largest_acked_spec(),
    {
        let ghost s = self.inflight@;
        let ghost pn = p.pn;
        self.inflight.push(p);
        assert forall|i: int| 0 <= i < s.len() implies (#[trigger] s[i]).pn < pn by {
            assert(self.issued@.contains(s[i].pn));
            assert(s[i].pn != pn);
        }
        assert(self.inflight@[s.len() as int].pn == pn);
    }

    // ponytail: O(inflight × 65) per ACK frame; a merge-walk (inflight ascending, ranges descending) if profiling shows it.
    //= https://www.rfc-editor.org/rfc/rfc9000#section-13.1
    //# An endpoint SHOULD treat receipt of an acknowledgment for a packet it
    //# did not send as a connection error of type PROTOCOL_VIOLATION, if it
    //# is able to detect the condition.
    /// Processes an incoming ACK frame: every record it acknowledges (in its first
    /// `MAX_ACK_RANGES_IN + 1` ranges) moves to `out`, ascending. Packet numbers without a
    /// record (ACK-only packets, or records already acknowledged or lost) are ignored.
    pub fn on_ack(&mut self, a: &AckFrame, out: &mut Vec<SentPacket>) -> (r: Result<(), u64>)
        requires
            old(self).wf(),
            rfc_ack_ranges_valid(a.largest, a.first_range, a.ranges@),
        ensures
            final(self).wf(),
            (r is Err) == (a.largest >= old(self).next_pn_spec()),
            r is Err ==> r == Err::<(), u64>(PROTOCOL_VIOLATION) && final(out)@ == old(out)@
                && final(self).inflight_spec() == old(self).inflight_spec()
                && final(self).largest_acked_spec() == old(self).largest_acked_spec(),
            r is Ok ==> {
                &&& final(out)@ == old(out)@ + acked_of(a@, old(self).inflight_spec())
                &&& final(self).inflight_spec() == unacked_of(a@, old(self).inflight_spec())
                &&& forall|i: int|
                    old(out)@.len() <= i < final(out)@.len() ==> {
                        &&& ack_contains(a@, (#[trigger] final(out)@[i]).pn)
                        &&& !has_pn(final(self).inflight_spec(), final(out)@[i].pn)
                    }
                &&& forall|j: int|
                    0 <= j < final(self).inflight_spec().len() ==> !ack_contains_capped(
                        a@,
                        (#[trigger] final(self).inflight_spec()[j]).pn,
                    )
                &&& final(self).largest_acked_spec() == Some(
                    match old(self).largest_acked_spec() {
                        Some(l) => if l > a.largest {
                            l
                        } else {
                            a.largest
                        },
                        None => a.largest,
                    },
                )
            },
            final(self).next_pn_spec() == old(self).next_pn_spec(),
            final(self).issued() == old(self).issued(),
    {
        if a.largest >= self.next_pn {
            return Err(PROTOCOL_VIOLATION);
        }
        let ghost out0 = out@;
        let ghost o = self.inflight@;
        let mut orig: Vec<SentPacket> = Vec::new();
        core::mem::swap(&mut self.inflight, &mut orig);
        let rev = reversed(orig);
        let kept = split_acked(a, rev, out, Ghost(o));
        self.inflight = kept;
        assert forall|j: int| 0 <= j < self.inflight@.len() implies {
            &&& (#[trigger] self.inflight@[j]).ack_eliciting
            &&& self.issued@.contains(self.inflight@[j].pn)
        } by {
            let m = choose|m: int| 0 <= m < o.len() && #[trigger] self.inflight@[j] == o[m];
            assert(o[m] == o[m]);
        }
        self.largest_acked = Some(
            match self.largest_acked {
                Some(l) => if l > a.largest {
                    l
                } else {
                    a.largest
                },
                None => a.largest,
            },
        );
        proof {
            assert forall|i: int| out0.len() <= i < out@.len() implies {
                &&& ack_contains(a@, (#[trigger] out@[i]).pn)
                &&& !has_pn(self.inflight@, out@[i].pn)
            } by {
                lemma_capped_implies(a@, out@[i].pn);
                if has_pn(self.inflight@, out@[i].pn) {
                    let j = choose|j: int|
                        0 <= j < self.inflight@.len() && (#[trigger] self.inflight@[j]).pn
                            == out@[i].pn;
                    assert(!ack_contains_capped(a@, self.inflight@[j].pn));
                }
            }
        }
        Ok(())
    }

    /// Removes and returns the record for `pn`, declared lost (Phase 6 loss detection).
    pub fn on_packet_lost(&mut self, pn: u64) -> (r: Option<SentPacket>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            r matches Some(p) ==> p.pn == pn,
            r matches Some(p) ==> exists|i: int|
                0 <= i < old(self).inflight_spec().len() && #[trigger] old(self).inflight_spec()[i]
                    == p && final(self).inflight_spec() == old(self).inflight_spec().remove(i),
            r is None ==> !has_pn(old(self).inflight_spec(), pn),
            r is None ==> final(self).inflight_spec() == old(self).inflight_spec(),
            final(self).next_pn_spec() == old(self).next_pn_spec(),
            final(self).issued() == old(self).issued(),
            final(self).largest_acked_spec() == old(self).largest_acked_spec(),
    {
        let mut i: usize = 0;
        while i < self.inflight.len()
            invariant
                self.wf(),
                *self == *old(self),
                i <= self.inflight@.len(),
                forall|j: int| 0 <= j < i ==> (#[trigger] self.inflight@[j]).pn != pn,
            decreases self.inflight@.len() - i,
        {
            if self.inflight[i].pn == pn {
                let ghost s = self.inflight@;
                let p = self.inflight.remove(i);
                assert forall|j: int| 0 <= j < self.inflight@.len() implies #[trigger] self.inflight@[j]
                    == if j < i {
                    s[j]
                } else {
                    s[j + 1]
                } by {}
                assert forall|x: int, y: int|
                    0 <= x < y < self.inflight@.len() implies (#[trigger] self.inflight@[x]).pn < (
                #[trigger] self.inflight@[y]).pn by {
                    let xs = if x < i {
                        x
                    } else {
                        x + 1
                    };
                    let ys = if y < i {
                        y
                    } else {
                        y + 1
                    };
                    assert(s[xs].pn < s[ys].pn);
                }
                assert forall|j: int| 0 <= j < self.inflight@.len() implies {
                    &&& (#[trigger] self.inflight@[j]).ack_eliciting
                    &&& self.issued@.contains(self.inflight@[j].pn)
                } by {
                    let js = if j < i {
                        j
                    } else {
                        j + 1
                    };
                    assert(s[js] == self.inflight@[j]);
                }
                assert(old(self).inflight_spec()[i as int] == p);
                return Some(p);
            }
            i = i + 1;
        }
        None
    }

    /// Moves every record to `out` and leaves a fresh, empty list (PTO placeholder loss
    /// declaration and packet number space discard).
    pub fn drain_inflight(&mut self, out: &mut Vec<SentPacket>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(out)@ == old(out)@ + old(self).inflight_spec(),
            final(self).inflight_spec().len() == 0,
            final(self).next_pn_spec() == old(self).next_pn_spec(),
            final(self).issued() == old(self).issued(),
            final(self).largest_acked_spec() == old(self).largest_acked_spec(),
    {
        let mut taken: Vec<SentPacket> = Vec::new();
        core::mem::swap(&mut self.inflight, &mut taken);
        out.append(&mut taken);
    }

    #[verifier::when_used_as_spec(largest_acked_spec)]
    pub fn largest_acked(&self) -> (r: Option<u64>)
        ensures
            r == self.largest_acked_spec(),
    {
        self.largest_acked
    }

    #[verifier::when_used_as_spec(next_pn_spec)]
    pub fn next_pn(&self) -> (r: u64)
        ensures
            r == self.next_pn_spec(),
    {
        self.next_pn
    }

    pub fn inflight_len(&self) -> (r: usize)
        ensures
            r == self.inflight_spec().len(),
    {
        self.inflight.len()
    }

    /// When the newest record in flight was sent.
    pub fn last_sent_time(&self) -> (r: Option<u64>)
        ensures
            r == if self.inflight_spec().len() > 0 {
                Some(self.inflight_spec().last().time)
            } else {
                None::<u64>
            },
    {
        let n = self.inflight.len();
        if n > 0 {
            Some(self.inflight[n - 1].time)
        } else {
            None
        }
    }
}

/// Whether `a` acknowledges `pn` within the range cap. At most `MAX_ACK_RANGES_IN + 1`
/// ranges are read.
fn capped_contains(a: &AckFrame, pn: u64) -> (r: bool)
    requires
        rfc_ack_ranges_valid(a.largest, a.first_range, a.ranges@),
    ensures
        r == ack_contains_capped(a@, pn),
{
    let s0 = a.largest - a.first_range;
    if s0 <= pn && pn <= a.largest {
        assert(ack_range(a@, -1).0 <= pn <= ack_range(a@, -1).1);
        return true;
    }
    let n = if a.ranges.len() < MAX_ACK_RANGES_IN {
        a.ranges.len()
    } else {
        MAX_ACK_RANGES_IN
    };
    let mut s = s0;
    let mut i: usize = 0;
    while i < n
        invariant
            rfc_ack_ranges_valid(a.largest, a.first_range, a.ranges@),
            s0 == a.largest - a.first_range,
            n == vstd::math::min(a.ranges@.len() as int, MAX_ACK_RANGES_IN as int),
            i <= n,
            s == spec_ack_smallest(s0 as int, a.ranges@.take(i as int)),
            !(ack_range(a@, -1).0 <= pn <= ack_range(a@, -1).1),
            forall|j: int|
                0 <= j < i ==> !((#[trigger] ack_range(a@, j)).0 <= pn <= ack_range(a@, j).1),
        decreases n - i,
    {
        let (g, l) = a.ranges[i];
        proof {
            let t = a.ranges@.take(i + 1);
            assert(t + a.ranges@.skip(i + 1) =~= a.ranges@);
            lemma_ranges_prefix(s0 as int, t, a.ranges@.skip(i + 1));
            assert(t.drop_last() =~= a.ranges@.take(i as int));
        }
        let hi = s - g - 2;
        let lo = hi - l;
        assert(ack_range(a@, i as int) == (lo as int, hi as int));
        if lo <= pn && pn <= hi {
            return true;
        }
        s = lo;
        i = i + 1;
    }
    false
}

/// Pops `rev` (the in-flight list `o`, reversed) to walk `o` ascending: acknowledged
/// records go to `out`, the rest to a fresh list, which is returned.
fn split_acked(
    a: &AckFrame,
    rev: Vec<SentPacket>,
    out: &mut Vec<SentPacket>,
    Ghost(o): Ghost<Seq<SentPacket>>,
) -> (kept: Vec<SentPacket>)
    requires
        rfc_ack_ranges_valid(a.largest, a.first_range, a.ranges@),
        rev@.len() == o.len(),
        forall|i: int| 0 <= i < o.len() ==> #[trigger] rev@[i] == o[o.len() - 1 - i],
        ascending(o),
    ensures
        final(out)@ == old(out)@ + acked_of(a@, o),
        kept@ == unacked_of(a@, o),
        ascending(kept@),
        forall|i: int|
            old(out)@.len() <= i < final(out)@.len() ==> ack_contains_capped(
                a@,
                (#[trigger] final(out)@[i]).pn,
            ),
        forall|j: int| 0 <= j < kept@.len() ==> !ack_contains_capped(a@, (#[trigger] kept@[j]).pn),
        forall|j: int| 0 <= j < kept@.len() ==> exists|k: int| 0 <= k < o.len() && #[trigger] kept@[j] == o[k],
{
    let ghost out0 = out@;
    let ghost n = o.len();
    let mut rev = rev;
    let mut kept: Vec<SentPacket> = Vec::new();
    let ghost mut k: int = 0;
    while rev.len() > 0
        invariant
            rfc_ack_ranges_valid(a.largest, a.first_range, a.ranges@),
            n == o.len(),
            ascending(o),
            k + rev@.len() == n,
            0 <= k <= n,
            forall|i: int| 0 <= i < rev@.len() ==> #[trigger] rev@[i] == o[n - 1 - i],
            out@ == out0 + acked_of(a@, o.take(k)),
            kept@ == unacked_of(a@, o.take(k)),
            ascending(kept@),
            k < n ==> forall|j: int| 0 <= j < kept@.len() ==> (#[trigger] kept@[j]).pn < o[k].pn,
            forall|i: int|
                out0.len() <= i < out@.len() ==> ack_contains_capped(a@, (#[trigger] out@[i]).pn),
            forall|j: int| 0 <= j < kept@.len() ==> !ack_contains_capped(a@, (#[trigger] kept@[j]).pn),
            forall|j: int| 0 <= j < kept@.len() ==> exists|m: int| 0 <= m < o.len() && #[trigger] kept@[j] == o[m],
        decreases rev@.len(),
    {
        let ghost r0 = rev@;
        if let Some(p) = rev.pop() {
            assert(p == o[k]);
            proof {
                lemma_split_step(a@, o, k);
            }
            if capped_contains(a, p.pn) {
                out.push(p);
                assert(out@ =~= out0 + acked_of(a@, o.take(k + 1)));
            } else {
                let ghost kl = kept@.len();
                kept.push(p);
                assert(kept@[kl as int] == o[k]);
            }
            proof {
                k = k + 1;
                assert forall|i: int| 0 <= i < rev@.len() implies #[trigger] rev@[i] == o[n - 1 - i] by {
                    assert(rev@[i] == r0[i]);
                }
                if k < n {
                    assert(o[k - 1].pn < o[k].pn);
                }
            }
        }
    }
    assert(o.take(n as int) =~= o);
    kept
}

/// `v` reversed, by popping into a fresh list.
fn reversed(v: Vec<SentPacket>) -> (r: Vec<SentPacket>)
    ensures
        r@.len() == v@.len(),
        forall|i: int| 0 <= i < v@.len() ==> #[trigger] r@[i] == v@[v@.len() - 1 - i],
{
    let ghost o = v@;
    let mut v = v;
    let mut r: Vec<SentPacket> = Vec::new();
    while v.len() > 0
        invariant
            v@.len() + r@.len() == o.len(),
            v@ == o.take(v@.len() as int),
            forall|i: int| 0 <= i < r@.len() ==> #[trigger] r@[i] == o[o.len() - 1 - i],
        decreases v@.len(),
    {
        if let Some(p) = v.pop() {
            r.push(p);
            assert(v@ =~= o.take(v@.len() as int));
        }
    }
    r
}

/// One step of the walk: the first `k + 1` records split as the first `k` plus record `k`.
proof fn lemma_split_step(a: SpecAck, o: Seq<SentPacket>, k: int)
    requires
        0 <= k < o.len(),
    ensures
        acked_of(a, o.take(k + 1)) == if ack_contains_capped(a, o[k].pn) {
            acked_of(a, o.take(k)).push(o[k])
        } else {
            acked_of(a, o.take(k))
        },
        unacked_of(a, o.take(k + 1)) == if ack_contains_capped(a, o[k].pn) {
            unacked_of(a, o.take(k))
        } else {
            unacked_of(a, o.take(k)).push(o[k])
        },
{
    assert(o.take(k + 1).drop_last() =~= o.take(k));
    assert(o.take(k + 1).last() == o[k]);
}

} // verus!
impl SentPackets {
    /// Test support: the in-flight list's allocated capacity. Verus models `Vec` length, not
    /// capacity, so the allocation bound is checked by test only (TRUSTED.md).
    #[doc(hidden)]
    pub fn inflight_capacity(&self) -> usize {
        self.inflight.capacity()
    }
}
