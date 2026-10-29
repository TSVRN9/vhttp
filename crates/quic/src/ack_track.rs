//! Received packet numbers, one `RecvPns` per packet number space (RFC 9000 §12.3, §13.2):
//! duplicate suppression, the ranges an ACK frame reports, and when an ACK is due.
use vstd::prelude::*;
use wire::varint::*;

use crate::ack::*;
// Used only in ghost code, which a plain `cargo build` erases.
#[allow(unused_imports)]
use crate::codes::*;
use crate::payload::*;

verus! {

// ponytail: ranges we *generate*; older ranges are forgotten and their PNs refused (§13.2.3); raise if reordering is deep.
pub const MAX_ACK_RANGES: usize = 32;

/// The longest ACK frame `build_ack` can produce: type, Largest Acknowledged, ACK Delay and
/// First ACK Range (at most 8 bytes each but the type), a one-byte range count, and
/// `MAX_ACK_RANGES - 1` pairs of 8-byte varints. `max_len` this large always gets every range.
pub const FULL_ACK_LEN: usize = 522;

/// `p` lies in one of the inclusive ranges `r`.
pub open spec fn in_ranges(r: Seq<(u64, u64)>, p: u64) -> bool {
    exists|i: int| #![trigger r[i]] 0 <= i < r.len() && r[i].0 <= p <= r[i].1
}

/// Inclusive `(lo, hi)` ranges, highest first, with at least one missing packet number
/// between neighbours.
pub open spec fn ranges_ok(r: Seq<(u64, u64)>) -> bool {
    &&& forall|i: int| #![trigger r[i]] 0 <= i < r.len() ==> r[i].0 <= r[i].1 <= PN_MAX
    &&& forall|i: int| #![trigger r[i]] 0 < i < r.len() ==> r[i].1 + 1 < r[i - 1].0
}

pub open spec fn lo_ge(r: Seq<(u64, u64)>, m: u64) -> bool {
    forall|i: int| #![trigger r[i]] 0 <= i < r.len() ==> r[i].0 >= m
}

/// The range list's part of `RecvPns::wf`: at most `MAX_ACK_RANGES` ranges, all at or above
/// the floor, holding only seen packet numbers, and every seen one is in a range or below
/// the floor.
pub open spec fn ranges_wf(r: Seq<(u64, u64)>, floor: u64, seen: Set<u64>) -> bool {
    &&& r.len() <= MAX_ACK_RANGES
    &&& ranges_inv(r, floor, seen)
}

/// `ranges_wf` without the length bound, which an insertion may exceed by one.
pub open spec fn ranges_inv(r: Seq<(u64, u64)>, floor: u64, seen: Set<u64>) -> bool {
    &&& ranges_ok(r)
    &&& lo_ge(r, floor)
    &&& forall|p: u64| in_ranges(r, p) ==> #[trigger] seen.contains(p)
    &&& forall|p: u64| #[trigger] seen.contains(p) ==> p < floor || in_ranges(r, p)
}

/// What `insert_pn` guarantees: `s` is `r` plus `pn`, still well formed, with the highest
/// range ending at the larger of `r`'s top and `pn`.
pub open spec fn insert_post(r: Seq<(u64, u64)>, s: Seq<(u64, u64)>, pn: u64, m: u64) -> bool {
    &&& ranges_ok(s)
    &&& lo_ge(s, m)
    &&& forall|p: u64| #[trigger] in_ranges(s, p) == (in_ranges(r, p) || p == pn)
    &&& 0 < s.len() <= r.len() + 1
    &&& s.len() == r.len() + 1 && r.len() > 0 && pn > r.last().1 ==> s.last() == r.last()
    &&& s[0].1 == if r.len() > 0 && r[0].1 > pn {
        r[0].1
    } else {
        pn
    }
}

pub open spec fn insert_pre(r: Seq<(u64, u64)>, pn: u64, m: u64) -> bool {
    &&& ranges_ok(r)
    &&& lo_ge(r, m)
    &&& !in_ranges(r, pn)
    &&& m <= pn <= PN_MAX
}

/// `r` with `r[a..b]` replaced by `x`.
#[verifier::opaque]
pub open spec fn splice(r: Seq<(u64, u64)>, a: int, b: int, x: (u64, u64)) -> Seq<(u64, u64)> {
    r.subrange(0, a) + seq![x] + r.subrange(b, r.len() as int)
}

/// The (Gap, ACK Range Length) pairs for `r` (§19.3.1): pair `i` describes range `i + 1`.
pub open spec fn ack_pairs(r: Seq<(u64, u64)>) -> Seq<(u64, u64)> {
    if r.len() == 0 {
        Seq::empty()
    } else {
        Seq::new(
            (r.len() - 1) as nat,
            |i: int| (((r[i].0 - r[i + 1].1) - 2) as u64, (r[i + 1].1 - r[i + 1].0) as u64),
        )
    }
}

/// The ACK frame for the highest `k + 1` ranges of `r`.
pub open spec fn ack_of(r: Seq<(u64, u64)>, k: nat, delay: u64) -> SpecAck {
    SpecAck {
        largest: r[0].1,
        delay,
        first_range: (r[0].1 - r[0].0) as u64,
        ranges: ack_pairs(r).take(k as int),
        ecn: None,
    }
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-13.2.5
//# An endpoint MUST NOT include delays that it
//# does not control when populating the ACK Delay field in an ACK frame.
/// The ACK Delay field: the time since the largest packet number was received, which is all
/// time this endpoint held the acknowledgment, scaled by the exponent. Capped to fit a varint.
pub open spec fn ack_delay_field(now: u64, received: u64, exp: u64) -> u64 {
    if now <= received {
        0
    } else {
        let d = ((now - received) as u64) >> exp;
        if d > VARINT_MAX {
            VARINT_MAX
        } else {
            d
        }
    }
}

/// Received packet numbers in one packet number space.
pub struct RecvPns {
    kind: PacketKind,
    ranges: Vec<(u64, u64)>,
    /// Every packet number below this is refused.
    floor: u64,
    largest: Option<u64>,
    largest_time: u64,
    eliciting_since_ack: u64,
    first_unacked_time: Option<u64>,
    new_since_ack: bool,
    /// The smallest ack-eliciting packet number received since the last ACK was sent.
    unacked_low: Option<u64>,
    seen: Ghost<Set<u64>>,
    /// The ack-eliciting packet numbers received since the last ACK was sent.
    unreported: Ghost<Set<u64>>,
    eliciting_rcvd: Ghost<nat>,
    ack_only_sent: Ghost<nat>,
}

impl RecvPns {
    /// Every packet number processed in this space.
    pub closed spec fn seen(&self) -> Set<u64> {
        self.seen@
    }

    pub closed spec fn wf(&self) -> bool {
        &&& ranges_wf(self.ranges@, self.floor, self.seen@)
        &&& match self.largest {
            Some(l) => {
                &&& self.ranges@.len() > 0
                &&& self.ranges@[0].1 == l
                &&& self.seen@.contains(l)
                &&& forall|p: u64| #[trigger] self.seen@.contains(p) ==> p <= l
            },
            None => self.ranges@.len() == 0 && self.seen@ == Set::<u64>::empty(),
        }
        &&& self.ack_only_sent@ + self.eliciting_since_ack <= self.eliciting_rcvd@
        &&& (self.eliciting_since_ack > 0) == (self.first_unacked_time is Some)
        &&& forall|p: u64| #[trigger] self.unreported@.contains(p) ==> in_ranges(self.ranges@, p)
        &&& match self.unacked_low {
            Some(u) => forall|p: u64| #[trigger] self.unreported@.contains(p) ==> u <= p,
            None => self.unreported@ == Set::<u64>::empty(),
        }
        &&& self.unacked_low is Some ==> self.eliciting_since_ack > 0
    }

    /// The smallest ack-eliciting packet number received since the last ACK was sent.
    pub closed spec fn unacked_low_spec(&self) -> Option<u64> {
        self.unacked_low
    }

    /// The ack-eliciting packet numbers received since the last ACK was sent. None of them
    /// has been dropped from the ranges (`lemma_unreported_acked`).
    pub closed spec fn unreported(&self) -> Set<u64> {
        self.unreported@
    }

    pub closed spec fn kind_spec(&self) -> PacketKind {
        self.kind
    }

    pub closed spec fn largest_spec(&self) -> Option<u64> {
        self.largest
    }

    /// When the largest packet number was received.
    pub closed spec fn largest_time_spec(&self) -> u64 {
        self.largest_time
    }

    /// Ack-eliciting packets received since the last ACK was sent (saturating).
    pub closed spec fn eliciting_since_ack(&self) -> u64 {
        self.eliciting_since_ack
    }

    /// When the first of those arrived.
    pub closed spec fn first_unacked(&self) -> Option<u64> {
        self.first_unacked_time
    }

    /// Ack-eliciting packets received, ever.
    pub closed spec fn eliciting_rcvd(&self) -> nat {
        self.eliciting_rcvd@
    }

    /// ACK-only packets sent, ever.
    pub closed spec fn ack_only_sent(&self) -> nat {
        self.ack_only_sent@
    }

    /// Seen, below the floor, or refused because taking it would drop a range: with the list
    /// full, `pn` below the lowest range, or the lowest range holding an ack-eliciting packet
    /// number no ACK has reported yet.
    pub closed spec fn is_duplicate_spec(&self, pn: u64) -> bool {
        ||| pn < self.floor
        ||| in_ranges(self.ranges@, pn)
        ||| self.ranges@.len() == MAX_ACK_RANGES && (pn < self.ranges@.last().0 || (
        self.unacked_low matches Some(u) && self.ranges@.last().1 >= u))
    }

    pub closed spec fn ack_only_allowed_spec(&self) -> bool {
        self.eliciting_since_ack > 0
    }

    pub closed spec fn has_new_spec(&self) -> bool {
        self.new_since_ack
    }

    /// The ACK frame for the highest `k + 1` remembered ranges, with ACK Delay `delay`.
    pub closed spec fn ack_candidate(&self, k: nat, delay: u64) -> SpecAck {
        ack_of(self.ranges@, k, delay)
    }

    /// Ranges remembered.
    pub closed spec fn range_count(&self) -> nat {
        self.ranges@.len()
    }

    /// The invariant, in terms of the accessors.
    pub proof fn lemma_wf(&self)
        requires
            self.wf(),
        ensures
            self.range_count() <= MAX_ACK_RANGES,
            (self.range_count() > 0) == (self.largest_spec() is Some),
            self.largest_spec() matches Some(l) ==> self.seen().contains(l) && forall|p: u64| #[trigger]
                self.seen().contains(p) ==> p <= l,
            self.largest_spec() is None ==> self.seen() == Set::<u64>::empty(),
            forall|pn: u64| !#[trigger] self.is_duplicate_spec(pn) ==> !self.seen().contains(pn),
            self.ack_only_sent() <= self.eliciting_rcvd(),
            (self.eliciting_since_ack() > 0) == (self.first_unacked() is Some),
            forall|p: u64| #[trigger] self.unreported().contains(p) ==> self.seen().contains(p),
            self.unacked_low_spec() is Some ==> self.eliciting_since_ack() > 0,
            self.unacked_low_spec() is None ==> self.unreported() == Set::<u64>::empty(),
    {
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-13.2.1
    //# Every packet SHOULD be acknowledged at least once, and ack-eliciting
    //# packets MUST be acknowledged at least once within the maximum delay
    //# an endpoint communicated using the max_ack_delay transport parameter;
    //# see Section 18.2.
    /// Every ack-eliciting packet number received since the last ACK was sent is still
    /// reported by the frame for all remembered ranges: no range holding one is dropped.
    pub proof fn lemma_unreported_acked(&self, p: u64, delay: u64)
        requires
            self.wf(),
            self.unreported().contains(p),
        ensures
            self.range_count() > 0,
            ack_contains(self.ack_candidate((self.range_count() - 1) as nat, delay), p),
    {
        let r = self.ranges@;
        let k = (r.len() - 1) as nat;
        let a = ack_of(r, k, delay);
        assert(in_ranges(r, p));
        let j = choose|j: int| #![trigger r[j]] 0 <= j < r.len() && r[j].0 <= p <= r[j].1;
        if j == 0 {
            assert(ack_range(a, -1).0 <= p <= ack_range(a, -1).1);
        } else {
            lemma_ack_range_is(r, k, delay, j - 1);
            assert(ack_range(a, j - 1).0 <= p <= ack_range(a, j - 1).1);
        }
    }

    /// The parts of `wf` that `build_ack` reads.
    proof fn lemma_build_facts(&self)
        requires
            self.wf(),
        ensures
            ranges_wf(self.ranges@, self.floor, self.seen@),
            self.ranges@.len() > 0 ==> self.largest == Some(self.ranges@[0].1),
            self.ranges@.len() == 0 ==> self.largest is None,
    {
    }

    pub fn new(kind: PacketKind) -> (r: RecvPns)
        ensures
            r.wf(),
            r.kind_spec() == kind,
            r.seen() == Set::<u64>::empty(),
            r.largest_spec() is None,
            r.eliciting_since_ack() == 0,
            !r.has_new_spec(),
            r.eliciting_rcvd() == 0,
            r.ack_only_sent() == 0,
            r.unreported() == Set::<u64>::empty(),
    {
        RecvPns {
            kind,
            ranges: Vec::new(),
            floor: 0,
            largest: None,
            largest_time: 0,
            eliciting_since_ack: 0,
            first_unacked_time: None,
            new_since_ack: false,
            unacked_low: None,
            seen: Ghost(Set::empty()),
            unreported: Ghost(Set::empty()),
            eliciting_rcvd: Ghost(0),
            ack_only_sent: Ghost(0),
        }
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-12.3
    //# A receiver MUST discard a newly unprotected packet unless it is
    //# certain that it has not processed another packet with the same packet
    //# number from the same packet number space.
    /// `pn` was processed already, is below the floor where we can no longer tell, or would
    /// force out a range that may hold an unacknowledged ack-eliciting packet.
    #[verifier::when_used_as_spec(is_duplicate_spec)]
    pub fn is_duplicate(&self, pn: u64) -> (d: bool)
        requires
            self.wf(),
        ensures
            d == self.is_duplicate_spec(pn),
            !d ==> !self.seen().contains(pn),
    {
        if pn < self.floor {
            return true;
        }
        let mut i: usize = 0;
        while i < self.ranges.len()
            invariant
                i <= self.ranges@.len(),
                forall|j: int|
                    #![trigger self.ranges@[j]]
                    0 <= j < i ==> !(self.ranges@[j].0 <= pn <= self.ranges@[j].1),
            decreases self.ranges@.len() - i,
        {
            let (lo, hi) = self.ranges[i];
            if lo <= pn && pn <= hi {
                assert(self.ranges@[i as int].0 <= pn <= self.ranges@[i as int].1);
                return true;
            }
            i = i + 1;
        }
        let n = self.ranges.len();
        if n == MAX_ACK_RANGES {
            let (lo, hi) = self.ranges[n - 1];
            if pn < lo {
                return true;
            }
            if let Some(u) = self.unacked_low {
                if hi >= u {
                    return true;
                }
            }
        }
        false
    }

    #[verifier::when_used_as_spec(ack_only_allowed_spec)]
    pub fn ack_only_allowed(&self) -> (r: bool)
        ensures
            r == self.ack_only_allowed_spec(),
    {
        self.eliciting_since_ack > 0
    }

    #[verifier::when_used_as_spec(has_new_spec)]
    pub fn has_new(&self) -> (r: bool)
        ensures
            r == self.has_new_spec(),
    {
        self.new_since_ack
    }

    #[verifier::when_used_as_spec(largest_spec)]
    pub fn largest(&self) -> (r: Option<u64>)
        ensures
            r == self.largest_spec(),
    {
        self.largest
    }

    // ponytail: O(ranges) insert; ranges <= 32.
    /// Records `pn`, processed at `now`.
    pub fn on_packet(&mut self, pn: u64, ack_eliciting: bool, now: u64)
        requires
            old(self).wf(),
            !old(self).is_duplicate(pn),
            pn <= PN_MAX,
        ensures
            final(self).wf(),
            final(self).seen() == old(self).seen().insert(pn),
            final(self).kind_spec() == old(self).kind_spec(),
            final(self).largest() == Some(
                match old(self).largest() {
                    Some(l) => if l > pn {
                        l
                    } else {
                        pn
                    },
                    None => pn,
                },
            ),
            final(self).eliciting_rcvd() == old(self).eliciting_rcvd() + (if ack_eliciting {
                1nat
            } else {
                0nat
            }),
            final(self).ack_only_sent() == old(self).ack_only_sent(),
            ack_eliciting ==> final(self).ack_only_allowed(),
            !ack_eliciting ==> final(self).eliciting_since_ack() == old(self).eliciting_since_ack()
                && final(self).first_unacked() == old(self).first_unacked()
                && final(self).unreported() == old(self).unreported(),
            ack_eliciting ==> final(self).eliciting_since_ack() == (if old(self).eliciting_since_ack()
                < u64::MAX {
                (old(self).eliciting_since_ack() + 1) as u64
            } else {
                old(self).eliciting_since_ack()
            }) && final(self).first_unacked() == (if old(self).first_unacked() is Some {
                old(self).first_unacked()
            } else {
                Some(now)
            }) && final(self).unreported() == old(self).unreported().insert(pn),
            final(self).has_new(),
    {
        let ghost s1 = self.seen@.insert(pn);
        let ghost u1 = if ack_eliciting {
            self.unreported@.insert(pn)
        } else {
            self.unreported@
        };
        proof {
            lemma_not_seen(self.ranges@, self.floor, self.seen@, pn);
            lemma_unreported_pre(self.ranges@, self.unacked_low, self.unreported@, u1, pn);
        }
        add_range(&mut self.ranges, &mut self.floor, pn, Ghost(self.seen@), Ghost(u1));
        let keep = match self.largest {
            Some(l) => l > pn,
            None => false,
        };
        if !keep {
            self.largest = Some(pn);
            self.largest_time = now;
        }
        if ack_eliciting {
            if self.eliciting_since_ack < u64::MAX {
                self.eliciting_since_ack = self.eliciting_since_ack + 1;
            }
            if self.first_unacked_time.is_none() {
                self.first_unacked_time = Some(now);
            }
            let low = match self.unacked_low {
                Some(u) => if u < pn {
                    u
                } else {
                    pn
                },
                None => pn,
            };
            self.unacked_low = Some(low);
            self.eliciting_rcvd = Ghost(self.eliciting_rcvd@ + 1);
        }
        self.new_since_ack = true;
        self.seen = Ghost(s1);
        self.unreported = Ghost(u1);
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-13.2.1
    //# Every packet SHOULD be acknowledged at least once, and ack-eliciting
    //# packets MUST be acknowledged at least once within the maximum delay
    //# an endpoint communicated using the max_ack_delay transport parameter;
    //# see Section 18.2.
    //
    //= https://www.rfc-editor.org/rfc/rfc9000#section-13.2.1
    //# An endpoint MUST acknowledge all ack-eliciting Initial and Handshake
    //# packets immediately and all ack-eliciting 0-RTT and 1-RTT packets
    //# within its advertised max_ack_delay, with the following exception.
    //
    //= https://www.rfc-editor.org/rfc/rfc9000#section-13.2.2
    //# A receiver SHOULD send an ACK frame after receiving at least two ack-
    //# eliciting packets.
    /// When an ACK is due: never without an unacknowledged ack-eliciting packet; at once in
    /// Initial and Handshake, and in 1-RTT after two; else `max_ack_delay` after the first.
    pub fn ack_deadline(&self, max_ack_delay_us: u64) -> (d: Option<u64>)
        requires
            self.wf(),
        ensures
            self.eliciting_since_ack() == 0 ==> d is None,
            self.eliciting_since_ack() > 0 ==> self.first_unacked() is Some && d == Some(
                match self.kind_spec() {
                    PacketKind::OneRtt => if self.eliciting_since_ack() >= 2 {
                        self.first_unacked()->0
                    } else if self.first_unacked()->0 + max_ack_delay_us > u64::MAX {
                        u64::MAX
                    } else {
                        (self.first_unacked()->0 + max_ack_delay_us) as u64
                    },
                    _ => self.first_unacked()->0,
                },
            ),
    {
        if self.eliciting_since_ack == 0 {
            return None;
        }
        match self.first_unacked_time {
            None => None,
            Some(t) => match self.kind {
                PacketKind::OneRtt => if self.eliciting_since_ack >= 2 {
                    Some(t)
                } else if t > u64::MAX - max_ack_delay_us {
                    Some(u64::MAX)
                } else {
                    Some(t + max_ack_delay_us)
                },
                _ => Some(t),
            },
        }
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-13.2.3
    //# If it does not, then older ranges (those with
    //# the smallest packet numbers) are omitted.
    //= https://www.rfc-editor.org/rfc/rfc9000#section-13.2.5
    //# The endpoint encodes this
    //# acknowledgment delay in the ACK Delay field of an ACK frame; see
    //# Section 19.3.
    /// The ACK Delay field: zero in Initial and Handshake, which are acknowledged at once.
    fn ack_delay(&self, now: u64, ack_delay_exponent: u64) -> (d: u64)
        requires
            ack_delay_exponent <= 20,
        ensures
            d == if self.kind_spec() is OneRtt {
                ack_delay_field(now, self.largest_time_spec(), ack_delay_exponent)
            } else {
                0
            },
            d <= VARINT_MAX,
    {
        match self.kind {
            PacketKind::OneRtt => if now <= self.largest_time {
                0
            } else {
                let d = (now - self.largest_time) >> ack_delay_exponent;
                if d > VARINT_MAX {
                    VARINT_MAX
                } else {
                    d
                }
            },
            _ => 0,
        }
    }

    /// An ACK frame for the highest ranges that fit in `max_len` bytes: `None` when nothing
    /// was received or even the First ACK Range does not fit.
    #[verifier::spinoff_prover]
    pub fn build_ack(&self, now: u64, ack_delay_exponent: u64, max_len: usize) -> (r: Option<
        AckFrame,
    >)
        requires
            self.wf(),
            ack_delay_exponent <= 20,
        ensures
            ({
                let delay = if self.kind_spec() is OneRtt {
                    ack_delay_field(now, self.largest_time_spec(), ack_delay_exponent)
                } else {
                    0
                };
                match r {
                    None => self.largest() is None || spec_ack_bytes(
                        self.ack_candidate(0, delay),
                    ).len() > max_len,
                    Some(a) => {
                        let k = a.ranges@.len();
                        &&& a@ == self.ack_candidate(k, delay)
                        &&& k < self.range_count()
                        &&& k + 1 < self.range_count() ==> spec_ack_bytes(
                            self.ack_candidate(k + 1, delay),
                        ).len() > max_len
                        &&& spec_ack_bytes(a@).len() <= max_len
                        &&& Some(a.largest) == self.largest()
                        &&& a.ecn is None
                        &&& ack_encodable(a@)
                        &&& rfc_ack_ranges_valid(a.largest, a.first_range, a.ranges@)
                        &&& forall|pn: u64| #[trigger]
                            ack_contains(a@, pn) ==> self.seen().contains(pn)
                    },
                }
            }),
            max_len >= FULL_ACK_LEN && self.range_count() > 0 ==> (r matches Some(a) && a.ranges@.len()
                + 1 == self.range_count()),
    {
        hide(ranges_wf);
        hide(spec_ack_bytes);
        hide(rfc_ack_ranges_valid);
        hide(ack_encodable);
        hide(ack_contains);
        hide(RecvPns::wf);
        proof {
            self.lemma_build_facts();
            lemma_ranges_wf_ok(self.ranges@, self.floor, self.seen@);
        }
        let n = self.ranges.len();
        if n == 0 {
            return None;
        }
        let (lo0, hi0) = self.ranges[0];
        let delay = self.ack_delay(now, ack_delay_exponent);
        let first = hi0 - lo0;
        let ghost r = self.ranges@;
        proof {
            lemma_ack_len(r, 0, delay);
            lemma_full_ack_fits(r, 0, delay);
            assert(ack_pairs(r).take(0) =~= Seq::<(u64, u64)>::empty());
        }
        let base: usize = 2 + varint_len(hi0) + varint_len(delay) + varint_len(first);
        if base > max_len {
            return None;
        }
        let mut ranges: Vec<(u64, u64)> = Vec::new();
        let mut len = base;
        let mut i: usize = 1;
        let mut full = false;
        while i < n && !full
            invariant
                1 <= i <= n,
                n == r.len(),
                r == self.ranges@,
                n <= MAX_ACK_RANGES,
                ranges_ok(r),
                delay <= VARINT_MAX,
                ranges@ == ack_pairs(r).take(i - 1),
                len == spec_ack_bytes(ack_of(r, (i - 1) as nat, delay)).len(),
                base <= len <= max_len,
                full ==> i < n && spec_ack_bytes(ack_of(r, i as nat, delay)).len() > max_len,
            decreases (n - i) as int + (if full {
                0int
            } else {
                1int
            }),
        {
            let (gap, rl) = ack_pair(&self.ranges, i);
            let pl = varint_len(gap) + varint_len(rl);
            proof {
                lemma_ack_len(r, (i - 1) as nat, delay);
                lemma_ack_len(r, i as nat, delay);
                lemma_pairs_step(r, i - 1);
            }
            if pl > max_len - len {
                full = true;
            } else {
                ranges.push((gap, rl));
                len = len + pl;
                i = i + 1;
            }
        }
        proof {
            lemma_ack_valid(r, (i - 1) as nat, delay);
            lemma_acked_seen(r, self.floor, self.seen@, (i - 1) as nat, delay);
            if max_len >= FULL_ACK_LEN {
                lemma_ack_complete(r, (i - 1) as nat, delay, max_len as int);
            }
        }
        // §13.4 exceptions: see below.
        //= https://www.rfc-editor.org/rfc/rfc9000#section-13.4.1
        //= type=exception
        //= reason=ECN is not accessible (no IP_RECVTOS) and no ECT is set; every ACK has ecn: None.
        //# Even if an endpoint does not set an ECT field in packets it sends,
        //# the endpoint MUST provide feedback about ECN markings it receives, if
        //# these are accessible.
        //
        //= https://www.rfc-editor.org/rfc/rfc9000#section-13.4.2.1
        //= type=exception
        //= reason=ECN is not accessible (no IP_RECVTOS) and no ECT is set; every ACK has ecn: None.
        //# An endpoint MUST NOT fail ECN validation as a result of
        //# processing an ACK frame that does not increase the largest
        //# acknowledged packet number.
        //
        //= https://www.rfc-editor.org/rfc/rfc9000#section-13.4.2.2
        //= type=exception
        //= reason=ECN is not accessible (no IP_RECVTOS) and no ECT is set; every ACK has ecn: None.
        //# If validation fails, then the endpoint MUST disable ECN.
        //
        //= https://www.rfc-editor.org/rfc/rfc9000#section-13.4.2.2
        //= type=exception
        //= reason=ECN is not accessible (no IP_RECVTOS) and no ECT is set; every ACK has ecn: None.
        //# Network routing and path elements can
        //# change mid-connection; an endpoint MUST disable ECN if validation
        //# later fails.
        Some(AckFrame { largest: hi0, delay, first_range: first, ranges, ecn: None })
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-13.2.1
    //# Since packets containing only ACK frames are not congestion
    //# controlled, an endpoint MUST NOT send more than one such packet in
    //# response to receiving an ack-eliciting packet.
    //
    //= https://www.rfc-editor.org/rfc/rfc9000#section-13.2.1
    //# An endpoint MUST NOT send a non-ack-eliciting packet in response to a
    //# non-ack-eliciting packet, even if there are packet gaps that precede
    //# the received packet.
    //
    //= https://www.rfc-editor.org/rfc/rfc9000#section-13.2.1
    //# In
    //# that case, an endpoint MUST NOT send an ack-eliciting frame in all
    //# packets that would otherwise be non-ack-eliciting, to avoid an
    //# infinite feedback loop of acknowledgments.
    /// An ACK frame from this space was sent; `ack_only` when its packet was ACK-only.
    /// An ACK-only packet needs an ack-eliciting packet since the last ACK, so
    /// `ack_only_sent() <= eliciting_rcvd()` (both MUST NOTs above). Nothing here adds an
    /// ack-eliciting frame to a packet that would otherwise be non-ack-eliciting.
    pub fn on_ack_sent(&mut self, ack_only: bool)
        requires
            old(self).wf(),
            ack_only ==> old(self).ack_only_allowed(),
        ensures
            final(self).wf(),
            final(self).seen() == old(self).seen(),
            final(self).kind_spec() == old(self).kind_spec(),
            final(self).largest() == old(self).largest(),
            final(self).eliciting_since_ack() == 0,
            final(self).unreported() == Set::<u64>::empty(),
            !final(self).has_new(),
            final(self).eliciting_rcvd() == old(self).eliciting_rcvd(),
            final(self).ack_only_sent() == old(self).ack_only_sent() + (if ack_only {
                1nat
            } else {
                0nat
            }),
    {
        self.eliciting_since_ack = 0;
        self.first_unacked_time = None;
        self.new_since_ack = false;
        self.unacked_low = None;
        self.unreported = Ghost(Set::empty());
        if ack_only {
            self.ack_only_sent = Ghost(self.ack_only_sent@ + 1);
        }
    }
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-19.3.1
//# The value of the Gap field establishes the largest packet number
//# value for the subsequent ACK Range using the following formula:
/// The (Gap, ACK Range Length) pair describing range `i`, below range `i - 1`.
fn ack_pair(v: &Vec<(u64, u64)>, i: usize) -> (g: (u64, u64))
    requires
        ranges_ok(v@),
        0 < i < v@.len(),
    ensures
        g == ack_pairs(v@)[i - 1],
{
    hide(ack_pairs);
    proof {
        lemma_pair_at(v@, i - 1);
    }
    let (plo, _) = v[i - 1];
    let (lo, hi) = v[i];
    assert(v@[i as int].1 + 1 < v@[i - 1].0);
    (plo - hi - 2, hi - lo)
}

/// Adds `pn` to the ranges, dropping the lowest range past `MAX_ACK_RANGES` and raising the
/// floor above it. `unrep` (the unreported packet numbers, `pn` possibly among them) stays
/// inside the ranges: the caller refuses any `pn` that would force out a range holding one.
fn add_range(
    v: &mut Vec<(u64, u64)>,
    floor: &mut u64,
    pn: u64,
    Ghost(seen): Ghost<Set<u64>>,
    Ghost(unrep): Ghost<Set<u64>>,
)
    requires
        ranges_wf(old(v)@, *old(floor), seen),
        !(pn < *old(floor) || in_ranges(old(v)@, pn)),
        pn <= PN_MAX,
        forall|p: u64| #[trigger] unrep.contains(p) ==> in_ranges(old(v)@, p) || p == pn,
        old(v)@.len() == MAX_ACK_RANGES ==> pn >= old(v)@.last().0 && forall|p: u64|
            #[trigger] unrep.contains(p) && p != pn ==> p > old(v)@.last().1,
    ensures
        ranges_wf(final(v)@, *final(floor), seen.insert(pn)),
        final(v)@.len() > 0,
        final(v)@[0].1 == if old(v)@.len() > 0 && old(v)@[0].1 > pn {
            old(v)@[0].1
        } else {
            pn
        },
        forall|p: u64| #[trigger] unrep.contains(p) ==> in_ranges(final(v)@, p),
{
    hide(ranges_wf);
    hide(ranges_inv);
    hide(insert_post);
    let ghost r0 = v@;
    proof {
        lemma_insert_ready(r0, *floor, seen, pn);
    }
    insert_pn(v, pn, Ghost(*floor));
    let ghost mid = v@;
    proof {
        lemma_insert_inv(r0, mid, *floor, seen, pn, unrep);
    }
    if v.len() > MAX_ACK_RANGES {
        match v.pop() {
            Some((_, hi)) => {
                //= https://www.rfc-editor.org/rfc/rfc9000#section-13.2.3
                //# A receiver MUST retain an ACK Range unless it can ensure that it will
                //# not subsequently accept packets with numbers in that range.
                //
                //= https://www.rfc-editor.org/rfc/rfc9000#section-13.2.3
                //# Receivers can discard all ACK Ranges, but they MUST retain the
                //# largest packet number that has been successfully processed, as that
                //# is used to recover packet numbers from subsequent packets; see
                //# Section 17.1.
                // The lowest range goes; the floor refuses it and the gap below it, and
                // `RecvPns::largest` is kept apart from the ranges.
                proof {
                    lemma_drop_lowest(mid, *floor, seen.insert(pn));
                    lemma_drop_keeps(r0, mid, *floor, pn, unrep);
                }
                *floor = hi + 1;
            },
            None => {},
        }
    }
}

/// Adds `pn` to the ranges in place: extend a neighbour, bridge two, or insert a new one.
fn insert_pn(v: &mut Vec<(u64, u64)>, pn: u64, Ghost(m): Ghost<u64>)
    requires
        insert_pre(old(v)@, pn, m),
    ensures
        insert_post(old(v)@, final(v)@, pn, m),
{
    hide(insert_pre);
    hide(insert_post);
    let ghost r = v@;
    let n = v.len();
    let mut i: usize = 0;
    while i < n && v[i].1 > pn
        invariant
            n == v@.len(),
            v@ == r,
            i <= n,
            forall|j: int| #![trigger r[j]] 0 <= j < i ==> r[j].1 > pn,
        decreases n - i,
    {
        i = i + 1;
    }
    proof {
        lemma_position(r, i as int, pn, m);
    }
    let above = i > 0 && v[i - 1].0 - 1 == pn;
    let below = i < n && pn > 0 && v[i].1 == pn - 1;
    if above && below {
        let lo = v[i].0;
        let hi = v[i - 1].1;
        v.set(i - 1, (lo, hi));
        v.remove(i);
        proof {
            lemma_merge(r, i as int, pn, m);
        }
    } else if above {
        let hi = v[i - 1].1;
        v.set(i - 1, (pn, hi));
        proof {
            lemma_extend_down(r, i as int, pn, m);
        }
    } else if below {
        let lo = v[i].0;
        v.set(i, (lo, pn));
        proof {
            lemma_extend_up(r, i as int, pn, m);
        }
    } else {
        v.insert(i, (pn, pn));
        proof {
            lemma_new_range(r, i as int, pn, m);
        }
    }
}

// =============================================================================
// Proofs
// =============================================================================

pub open spec fn inr(x: (u64, u64), p: u64) -> bool {
    x.0 <= p <= x.1
}

/// `x` covers exactly `pn` and the ranges `r[a..b]` (at most two).
pub open spec fn covers(r: Seq<(u64, u64)>, a: int, b: int, x: (u64, u64), pn: u64) -> bool {
    forall|p: u64| #[trigger]
        inr(x, p) == (p == pn || (a < b && inr(r[a], p)) || (a + 1 < b && inr(r[a + 1], p)))
}

/// Where each element of a splice comes from.
proof fn lemma_splice_index(r: Seq<(u64, u64)>, a: int, b: int, x: (u64, u64))
    requires
        0 <= a <= b <= r.len(),
    ensures
        ({
            let s = splice(r, a, b, x);
            &&& s.len() == r.len() + 1 - (b - a)
            &&& forall|k: int| #![trigger s[k]] 0 <= k < s.len() ==> s[k] == if k < a {
                r[k]
            } else if k == a {
                x
            } else {
                r[k + b - a - 1]
            }
        }),
{
    reveal(splice);
}

/// Element `k` of a splice.
proof fn lemma_splice_at(r: Seq<(u64, u64)>, a: int, b: int, x: (u64, u64), k: int)
    requires
        0 <= a <= b <= r.len(),
        0 <= k < r.len() + 1 - (b - a),
    ensures
        splice(r, a, b, x).len() == r.len() + 1 - (b - a),
        splice(r, a, b, x)[k] == if k < a {
            r[k]
        } else if k == a {
            x
        } else {
            r[k + b - a - 1]
        },
{
    reveal(splice);
}

proof fn lemma_splice_ok(r: Seq<(u64, u64)>, a: int, b: int, x: (u64, u64), m: u64)
    requires
        ranges_ok(r),
        lo_ge(r, m),
        0 <= a <= b <= r.len(),
        b <= a + 2,
        m <= x.0 <= x.1 <= PN_MAX,
        a > 0 ==> x.1 + 1 < r[a - 1].0,
        b < r.len() ==> r[b].1 + 1 < x.0,
    ensures
        ranges_ok(splice(r, a, b, x)),
        lo_ge(splice(r, a, b, x), m),
{
    let s = splice(r, a, b, x);
    let n = r.len() + 1 - (b - a);
    lemma_splice_at(r, a, b, x, 0);
    assert forall|k: int| #![trigger s[k]] 0 <= k < s.len() implies s[k].0 <= s[k].1 <= PN_MAX
        && s[k].0 >= m by {
        lemma_splice_at(r, a, b, x, k);
    }
    assert forall|k: int| #![trigger s[k]] 0 < k < s.len() implies s[k].1 + 1 < s[k - 1].0 by {
        lemma_splice_at(r, a, b, x, k);
        lemma_splice_at(r, a, b, x, k - 1);
    }
}

proof fn lemma_splice_cover(r: Seq<(u64, u64)>, a: int, b: int, x: (u64, u64), pn: u64)
    requires
        0 <= a <= b <= r.len(),
        b <= a + 2,
        inr(x, pn),
        covers(r, a, b, x, pn),
    ensures
        forall|p: u64| #[trigger]
            in_ranges(splice(r, a, b, x), p) == (in_ranges(r, p) || p == pn),
{
    let s = splice(r, a, b, x);
    lemma_splice_index(r, a, b, x);
    assert forall|p: u64| in_ranges(s, p) implies #[trigger] in_ranges(r, p) || p == pn by {
        let k = choose|k: int| #![trigger s[k]] 0 <= k < s.len() && s[k].0 <= p <= s[k].1;
        if k < a {
            assert(r[k] == s[k]);
        } else if k == a {
            assert(inr(x, p));
            if a < b && inr(r[a], p) {
                assert(in_ranges(r, p));
            } else if a + 1 < b && inr(r[a + 1], p) {
                assert(in_ranges(r, p));
            }
        } else {
            assert(r[k + b - a - 1] == s[k]);
        }
    }
    assert forall|p: u64| in_ranges(r, p) || p == pn implies #[trigger] in_ranges(s, p) by {
        if p == pn {
            assert(s[a] == x);
        } else {
            let j = choose|j: int| #![trigger r[j]] 0 <= j < r.len() && r[j].0 <= p <= r[j].1;
            if j < a {
                assert(s[j] == r[j]);
            } else if j < b {
                if j == a {
                    assert(inr(r[a], p));
                } else {
                    assert(inr(r[a + 1], p));
                }
                assert(inr(x, p));
                assert(s[a] == x);
            } else {
                assert(s[j - (b - a - 1)] == r[j]);
            }
        }
    }
}

/// Splicing `x` over `r[a..b]` is an insertion of `pn` when `x` covers `pn` and those ranges.
proof fn lemma_splice_insert(r: Seq<(u64, u64)>, a: int, b: int, x: (u64, u64), pn: u64, m: u64)
    requires
        ranges_ok(r),
        lo_ge(r, m),
        0 <= a <= b <= r.len(),
        b <= a + 2,
        m <= x.0 <= pn <= x.1 <= PN_MAX,
        a > 0 ==> x.1 + 1 < r[a - 1].0,
        b < r.len() ==> r[b].1 + 1 < x.0,
        covers(r, a, b, x, pn),
        r.len() > 0 && r[0].1 > pn ==> a > 0 || x.1 == r[0].1,
        !(r.len() > 0 && r[0].1 > pn) ==> a == 0 && x.1 == pn,
    ensures
        insert_post(r, splice(r, a, b, x), pn, m),
{
    lemma_splice_ok(r, a, b, x, m);
    lemma_splice_cover(r, a, b, x, pn);
    let s = splice(r, a, b, x);
    lemma_splice_at(r, a, b, x, 0);
    if s.len() == r.len() + 1 && r.len() > 0 && pn > r.last().1 {
        assert(a == b);
        if a == r.len() {
            assert(x.1 + 1 < r[a - 1].0);
        } else {
            lemma_splice_at(r, a, b, x, s.len() - 1);
        }
    }
}

/// After the search loop: range `i - 1` lies above `pn` and range `i` below it.
proof fn lemma_position(r: Seq<(u64, u64)>, i: int, pn: u64, m: u64)
    requires
        insert_pre(r, pn, m),
        0 <= i <= r.len(),
        forall|j: int| #![trigger r[j]] 0 <= j < i ==> r[j].1 > pn,
        !(i < r.len() && r[i].1 > pn),
    ensures
        i > 0 ==> r[i - 1].0 > pn && r[0].1 > pn,
        i < r.len() ==> r[i].1 < pn,
        forall|j: int| #![trigger r[j]] 0 <= j < i ==> r[j].0 > pn,
{
    assert forall|j: int| #![trigger r[j]] 0 <= j < i implies r[j].0 > pn by {
        if r[j].0 <= pn {
            assert(in_ranges(r, pn));
        }
    }
    if i < r.len() && r[i].1 == pn {
        assert(in_ranges(r, pn));
    }
}

proof fn lemma_eq_merge(r: Seq<(u64, u64)>, i: int, x: (u64, u64))
    requires
        0 < i < r.len(),
    ensures
        r.update(i - 1, x).remove(i) == splice(r, i - 1, i + 1, x),
{
    reveal(splice);
    assert(r.update(i - 1, x).remove(i) =~= splice(r, i - 1, i + 1, x));
}

proof fn lemma_eq_update(r: Seq<(u64, u64)>, i: int, x: (u64, u64))
    requires
        0 <= i < r.len(),
    ensures
        r.update(i, x) == splice(r, i, i + 1, x),
{
    reveal(splice);
    assert(r.update(i, x) =~= splice(r, i, i + 1, x));
}

proof fn lemma_eq_insert(r: Seq<(u64, u64)>, i: int, x: (u64, u64))
    requires
        0 <= i <= r.len(),
    ensures
        r.insert(i, x) == splice(r, i, i, x),
{
    reveal(splice);
    assert(r.insert(i, x) =~= splice(r, i, i, x));
}

/// `pn` bridges ranges `i - 1` and `i`.
proof fn lemma_merge(r: Seq<(u64, u64)>, i: int, pn: u64, m: u64)
    requires
        insert_pre(r, pn, m),
        0 < i < r.len(),
        r[i - 1].0 - 1 == pn,
        pn > 0 && r[i].1 == pn - 1,
        i > 0 ==> r[0].1 > pn,
    ensures
        ({
            let x = (r[i].0, r[i - 1].1);
            insert_post(r, r.update(i - 1, x).remove(i), pn, m)
        }),
{
    hide(insert_post);
    let x = (r[i].0, r[i - 1].1);
    lemma_eq_merge(r, i, x);
    if i > 1 {
        assert(r[i - 1].1 + 1 < r[i - 2].0);
    }
    if i + 1 < r.len() {
        assert(r[i + 1].1 + 1 < r[i].0);
    }
    assert(r[0].1 > pn);
    lemma_splice_insert(r, i - 1, i + 1, x, pn, m);
}

/// `pn` lies just below range `i - 1`.
proof fn lemma_extend_down(r: Seq<(u64, u64)>, i: int, pn: u64, m: u64)
    requires
        insert_pre(r, pn, m),
        0 < i <= r.len(),
        r[i - 1].0 - 1 == pn,
        i < r.len() ==> r[i].1 < pn && !(pn > 0 && r[i].1 == pn - 1),
        i > 0 ==> r[0].1 > pn,
    ensures
        insert_post(r, r.update(i - 1, (pn, r[i - 1].1)), pn, m),
{
    hide(insert_post);
    let x = (pn, r[i - 1].1);
    lemma_eq_update(r, i - 1, x);
    if i > 1 {
        assert(r[i - 1].1 + 1 < r[i - 2].0);
    }
    assert(r[0].1 > pn);
    lemma_splice_insert(r, i - 1, i, x, pn, m);
}

/// `pn` lies just above range `i`.
proof fn lemma_extend_up(r: Seq<(u64, u64)>, i: int, pn: u64, m: u64)
    requires
        insert_pre(r, pn, m),
        0 <= i < r.len(),
        pn > 0 && r[i].1 == pn - 1,
        i > 0 ==> r[i - 1].0 > pn && r[i - 1].0 - 1 != pn,
        i > 0 ==> r[0].1 > pn,
    ensures
        insert_post(r, r.update(i, (r[i].0, pn)), pn, m),
{
    hide(insert_post);
    let x = (r[i].0, pn);
    lemma_eq_update(r, i, x);
    if i + 1 < r.len() {
        assert(r[i + 1].1 + 1 < r[i].0);
    }
    if i > 0 {
        assert(r[0].1 > pn);
    }
    lemma_splice_insert(r, i, i + 1, x, pn, m);
}

/// `pn` touches no range: a new one goes in at `i`.
proof fn lemma_new_range(r: Seq<(u64, u64)>, i: int, pn: u64, m: u64)
    requires
        insert_pre(r, pn, m),
        0 <= i <= r.len(),
        i > 0 ==> r[i - 1].0 > pn && r[i - 1].0 - 1 != pn,
        i < r.len() ==> r[i].1 < pn && !(pn > 0 && r[i].1 == pn - 1),
        i > 0 ==> r[0].1 > pn,
    ensures
        insert_post(r, r.insert(i, (pn, pn)), pn, m),
{
    hide(insert_post);
    let x = (pn, pn);
    lemma_eq_insert(r, i, x);
    assert(ranges_ok(r) && lo_ge(r, m));
    assert(i > 0 ==> x.1 + 1 < r[i - 1].0);
    assert(i < r.len() ==> r[i].1 + 1 < x.0);
    assert(covers(r, i, i, x, pn));
    assert(r.len() > 0 && r[0].1 > pn ==> i > 0 || x.1 == r[0].1);
    assert(!(r.len() > 0 && r[0].1 > pn) ==> i == 0 && x.1 == pn);
    lemma_splice_insert(r, i, i, x, pn, m);
}

/// `pn` was not seen: it is at or above the floor and in no range.
proof fn lemma_not_seen(r: Seq<(u64, u64)>, floor: u64, seen: Set<u64>, pn: u64)
    requires
        ranges_wf(r, floor, seen),
        !(pn < floor || in_ranges(r, pn)),
    ensures
        !seen.contains(pn),
{
}

/// `add_range`'s precondition gives `insert_pn`'s.
proof fn lemma_insert_ready(r: Seq<(u64, u64)>, floor: u64, seen: Set<u64>, pn: u64)
    requires
        ranges_wf(r, floor, seen),
        !(pn < floor || in_ranges(r, pn)),
        pn <= PN_MAX,
    ensures
        insert_pre(r, pn, floor),
        r.len() <= MAX_ACK_RANGES,
{
}

/// After `insert_pn`: the range invariant for the seen set with `pn` added, the unreported
/// numbers inside the ranges, and the shape facts `add_range` returns.
proof fn lemma_insert_inv(
    r0: Seq<(u64, u64)>,
    r1: Seq<(u64, u64)>,
    floor: u64,
    seen: Set<u64>,
    pn: u64,
    unrep: Set<u64>,
)
    requires
        ranges_wf(r0, floor, seen),
        insert_post(r0, r1, pn, floor),
        forall|p: u64| #[trigger] unrep.contains(p) ==> in_ranges(r0, p) || p == pn,
    ensures
        ranges_inv(r1, floor, seen.insert(pn)),
        r1.len() <= MAX_ACK_RANGES ==> ranges_wf(r1, floor, seen.insert(pn)),
        0 < r1.len() <= r0.len() + 1,
        r0.len() <= MAX_ACK_RANGES,
        r1[0].1 == if r0.len() > 0 && r0[0].1 > pn {
            r0[0].1
        } else {
            pn
        },
        forall|p: u64| #[trigger] unrep.contains(p) ==> in_ranges(r1, p),
        r1.len() == r0.len() + 1 && r0.len() > 0 && pn > r0.last().1 ==> r1.last() == r0.last(),
{
    let s1 = seen.insert(pn);
    assert forall|p: u64| #[trigger] s1.contains(p) implies p < floor || in_ranges(r1, p) by {
        if p != pn {
            assert(seen.contains(p));
        }
    }
    assert forall|p: u64| in_ranges(r1, p) implies #[trigger] s1.contains(p) by {
        if p != pn {
            assert(in_ranges(r0, p));
        }
    }
    assert forall|p: u64| #[trigger] unrep.contains(p) implies in_ranges(r1, p) by {
        assert(in_ranges(r0, p) || p == pn);
    }
}

/// The dropped range held no unreported number: they all lie above the old lowest range,
/// which is what goes.
proof fn lemma_drop_keeps(r0: Seq<(u64, u64)>, r1: Seq<(u64, u64)>, floor: u64, pn: u64, unrep: Set<u64>)
    requires
        r1.len() == r0.len() + 1 && r0.len() > 0 && pn > r0.last().1 ==> r1.last() == r0.last(),
        r0.len() == MAX_ACK_RANGES,
        r1.len() == MAX_ACK_RANGES + 1,
        !in_ranges(r0, pn),
        pn >= r0.last().0,
        forall|p: u64| #[trigger] unrep.contains(p) && p != pn ==> p > r0.last().1,
        forall|p: u64| #[trigger] unrep.contains(p) ==> in_ranges(r1, p),
    ensures
        forall|p: u64| #[trigger] unrep.contains(p) ==> in_ranges(r1.drop_last(), p),
{
    let n = r0.len() - 1;
    if pn <= r0[n].1 {
        assert(in_ranges(r0, pn));
    }
    assert(r1.last() == r0.last());
    let t = r1.drop_last();
    assert forall|p: u64| #[trigger] unrep.contains(p) implies in_ranges(t, p) by {
        let j = choose|j: int| #![trigger r1[j]] 0 <= j < r1.len() && r1[j].0 <= p <= r1[j].1;
        if j < t.len() {
            assert(t[j] == r1[j]);
        } else {
            assert(r1[j] == r0[n]);
        }
    }
}

/// `on_packet`'s refusal rule gives `add_range`'s condition on the unreported numbers.
proof fn lemma_unreported_pre(
    r: Seq<(u64, u64)>,
    low: Option<u64>,
    unrep: Set<u64>,
    u1: Set<u64>,
    pn: u64,
)
    requires
        forall|p: u64| #[trigger] unrep.contains(p) ==> in_ranges(r, p),
        match low {
            Some(u) => forall|p: u64| #[trigger] unrep.contains(p) ==> u <= p,
            None => unrep == Set::<u64>::empty(),
        },
        u1 == unrep || u1 == unrep.insert(pn),
        !(r.len() == MAX_ACK_RANGES && (pn < r.last().0 || (low matches Some(u) && r.last().1
            >= u))),
    ensures
        forall|p: u64| #[trigger] u1.contains(p) ==> in_ranges(r, p) || p == pn,
        r.len() == MAX_ACK_RANGES ==> pn >= r.last().0 && forall|p: u64|
            #[trigger] u1.contains(p) && p != pn ==> p > r.last().1,
{
    assert forall|p: u64| #[trigger] u1.contains(p) implies in_ranges(r, p) || p == pn by {
        if p != pn {
            assert(unrep.contains(p));
        }
    }
    if r.len() == MAX_ACK_RANGES {
        assert forall|p: u64| #[trigger] u1.contains(p) && p != pn implies p > r.last().1 by {
            assert(unrep.contains(p));
        }
    }
}

/// Ranges further down lie lower.
proof fn lemma_sorted_trans(r: Seq<(u64, u64)>, i: int, j: int)
    requires
        ranges_ok(r),
        0 <= i < j < r.len(),
    ensures
        r[j].1 + 1 < r[i].0,
    decreases j - i,
{
    if j > i + 1 {
        lemma_sorted_trans(r, i, j - 1);
        assert(r[j].1 + 1 < r[j - 1].0);
    }
}

/// Popping the lowest of `MAX_ACK_RANGES + 1` ranges and raising the floor to just above it
/// keeps every invariant that mentions the ranges.
proof fn lemma_drop_lowest(r: Seq<(u64, u64)>, floor: u64, seen: Set<u64>)
    requires
        r.len() == MAX_ACK_RANGES + 1,
        ranges_inv(r, floor, seen),
    ensures
        ranges_wf(r.drop_last(), (r.last().1 + 1) as u64, seen),
        r.drop_last()[0] == r[0],
        r.last().1 < PN_MAX + 1,
{
    lemma_drop_floor(r);
    assert(r.last() == r[r.len() - 1]);
    lemma_drop_seen(r, floor, seen);
}

/// Every kept range lies above the new floor.
proof fn lemma_drop_floor(r: Seq<(u64, u64)>)
    requires
        r.len() == MAX_ACK_RANGES + 1,
        ranges_ok(r),
    ensures
        ranges_ok(r.drop_last()),
        lo_ge(r.drop_last(), (r.last().1 + 1) as u64),
        r.drop_last()[0] == r[0],
        r.last().1 < PN_MAX + 1,
{
    let t = r.drop_last();
    let f = (r.last().1 + 1) as u64;
    let n = r.len() - 1;
    assert forall|i: int| #![trigger t[i]] 0 <= i < t.len() implies t[i].0 >= f by {
        lemma_sorted_trans(r, i, n);
    }
}

/// The seen-set conjuncts survive the drop, with the floor just above the dropped range.
proof fn lemma_drop_seen(r: Seq<(u64, u64)>, floor: u64, seen: Set<u64>)
    requires
        r.len() == MAX_ACK_RANGES + 1,
        floor <= r.last().0 <= r.last().1 <= PN_MAX,
        forall|p: u64| #[trigger] seen.contains(p) ==> p < floor || in_ranges(r, p),
        forall|p: u64| in_ranges(r, p) ==> #[trigger] seen.contains(p),
    ensures
        forall|p: u64| #[trigger]
            seen.contains(p) ==> p < (r.last().1 + 1) as u64 || in_ranges(r.drop_last(), p),
        forall|p: u64| in_ranges(r.drop_last(), p) ==> #[trigger] seen.contains(p),
{
    let t = r.drop_last();
    let f = (r.last().1 + 1) as u64;
    let n = r.len() - 1;
    assert forall|p: u64| #[trigger] seen.contains(p) implies p < f || in_ranges(t, p) by {
        if in_ranges(r, p) {
            let j = choose|j: int| #![trigger r[j]] 0 <= j < r.len() && r[j].0 <= p <= r[j].1;
            if j < n {
                assert(t[j] == r[j]);
            }
        } else {
            assert(p < floor);
        }
    }
    assert forall|p: u64| in_ranges(t, p) implies #[trigger] seen.contains(p) by {
        let j = choose|j: int| #![trigger t[j]] 0 <= j < t.len() && t[j].0 <= p <= t[j].1;
        assert(r[j] == t[j]);
    }
}

/// Walking the first `k` pairs down from range 0 ends at range `k`, through non-negative
/// bounds only.
proof fn lemma_walk(r: Seq<(u64, u64)>, k: nat)
    requires
        ranges_ok(r),
        k < r.len(),
    ensures
        spec_ack_smallest(r[0].0 as int, ack_pairs(r).take(k as int)) == r[k as int].0,
        rfc_ack_ranges_from(r[0].0 as int, ack_pairs(r).take(k as int)),
    decreases k,
{
    let g = ack_pairs(r);
    if k == 0 {
        assert(g.take(0) =~= Seq::<(u64, u64)>::empty());
    } else {
        lemma_walk(r, (k - 1) as nat);
        let t = g.take(k as int);
        assert(t.drop_last() =~= g.take(k - 1));
        assert(t.last() == g[k - 1]);
        assert(r[k as int].1 + 1 < r[k - 1].0);
    }
}

/// Range `i` of `build_ack`'s frame is range `i + 1` of `r`.
proof fn lemma_ack_range_is(r: Seq<(u64, u64)>, k: nat, delay: u64, i: int)
    requires
        ranges_ok(r),
        k < r.len(),
        0 <= i < k,
    ensures
        ack_range(ack_of(r, k, delay), i) == (r[i + 1].0 as int, r[i + 1].1 as int),
{
    let a = ack_of(r, k, delay);
    let g = ack_pairs(r);
    lemma_walk(r, i as nat);
    assert(a.ranges.take(i) =~= g.take(i));
    assert(a.ranges[i] == g[i]);
    assert(r[i + 1].1 + 1 < r[i].0);
}

/// `build_ack`'s frame has valid ranges and fits its varints.
proof fn lemma_ack_valid(r: Seq<(u64, u64)>, k: nat, delay: u64)
    requires
        ranges_ok(r),
        k < r.len(),
        r.len() <= MAX_ACK_RANGES,
        delay <= VARINT_MAX,
    ensures
        ({
            let a = ack_of(r, k, delay);
            &&& rfc_ack_ranges_valid(a.largest, a.first_range, a.ranges)
            &&& ack_encodable(a)
        }),
{
    let a = ack_of(r, k, delay);
    let g = ack_pairs(r);
    lemma_walk(r, k);
    assert(a.largest - a.first_range == r[0].0);
    assert forall|i: int| #![trigger a.ranges[i]] 0 <= i < a.ranges.len() implies a.ranges[i].0
        <= VARINT_MAX && a.ranges[i].1 <= VARINT_MAX by {
        assert(a.ranges[i] == g[i]);
        assert(r[i + 1].1 + 1 < r[i].0);
    }
}

/// `build_ack`'s frame acknowledges only packet numbers the ranges hold.
proof fn lemma_build_ack_sound(r: Seq<(u64, u64)>, k: nat, delay: u64)
    requires
        ranges_ok(r),
        k < r.len(),
    ensures
        forall|pn: u64| #[trigger] ack_contains(ack_of(r, k, delay), pn) ==> in_ranges(r, pn),
{
    let a = ack_of(r, k, delay);
    assert forall|pn: u64| #[trigger] ack_contains(a, pn) implies in_ranges(r, pn) by {
        let i = choose|i: int|
            -1 <= i < a.ranges.len() && (#[trigger] ack_range(a, i)).0 <= pn <= ack_range(a, i).1;
        if i >= 0 {
            lemma_ack_range_is(r, k, delay, i);
            assert(r[i + 1].0 <= pn <= r[i + 1].1);
        } else {
            assert(r[0].0 <= pn <= r[0].1);
        }
    }
}

/// The frame acknowledges only seen packet numbers.
proof fn lemma_acked_seen(r: Seq<(u64, u64)>, floor: u64, seen: Set<u64>, k: nat, delay: u64)
    requires
        ranges_wf(r, floor, seen),
        k < r.len(),
    ensures
        forall|pn: u64| #[trigger] ack_contains(ack_of(r, k, delay), pn) ==> seen.contains(pn),
{
    lemma_build_ack_sound(r, k, delay);
    assert forall|pn: u64| #[trigger] ack_contains(ack_of(r, k, delay), pn) implies seen.contains(
        pn,
    ) by {
        assert(in_ranges(r, pn));
    }
}

/// The range-list facts `build_ack` needs.
proof fn lemma_ranges_wf_ok(r: Seq<(u64, u64)>, floor: u64, seen: Set<u64>)
    requires
        ranges_wf(r, floor, seen),
    ensures
        ranges_ok(r),
        r.len() <= MAX_ACK_RANGES,
{
}

/// The frame's encoded length: type, Largest Acknowledged, ACK Delay, the one-byte range
/// count, First ACK Range, then the pairs.
proof fn lemma_ack_len(r: Seq<(u64, u64)>, k: nat, delay: u64)
    requires
        ranges_ok(r),
        k < r.len(),
        r.len() <= MAX_ACK_RANGES,
        delay <= VARINT_MAX,
    ensures
        spec_ack_bytes(ack_of(r, k, delay)).len() == 2 + rfc_varint_min_len(r[0].1)
            + rfc_varint_min_len(delay) + rfc_varint_min_len((r[0].1 - r[0].0) as u64)
            + spec_pairs_bytes(ack_pairs(r).take(k as int)).len(),
{
    let a = ack_of(r, k, delay);
    theorem_serialize_matches_rfc(FRAME_ACK);
    theorem_serialize_matches_rfc(a.largest);
    theorem_serialize_matches_rfc(delay);
    theorem_serialize_matches_rfc(k as u64);
    theorem_serialize_matches_rfc(a.first_range);
    assert(spec_ecn_bytes(None) =~= Seq::<u8>::empty());
}

/// Pair `k` of `ack_pairs(r)`.
proof fn lemma_pair_at(r: Seq<(u64, u64)>, k: int)
    requires
        0 <= k,
        k + 1 < r.len(),
    ensures
        ack_pairs(r)[k] == (((r[k].0 - r[k + 1].1) - 2) as u64, (r[k + 1].1 - r[k + 1].0) as u64),
{
}

/// The pairs take at most 16 bytes each.
proof fn lemma_pairs_len_bound(r: Seq<(u64, u64)>, k: nat)
    requires
        ranges_ok(r),
        k < r.len(),
    ensures
        spec_pairs_bytes(ack_pairs(r).take(k as int)).len() <= 16 * k,
    decreases k,
{
    if k == 0 {
        assert(ack_pairs(r).take(0) =~= Seq::<(u64, u64)>::empty());
    } else {
        lemma_pairs_len_bound(r, (k - 1) as nat);
        lemma_pairs_step(r, k - 1);
    }
}

/// With `FULL_ACK_LEN` bytes of room, the longest fitting prefix is every range.
proof fn lemma_ack_complete(r: Seq<(u64, u64)>, k: nat, delay: u64, max_len: int)
    requires
        ranges_ok(r),
        k < r.len(),
        r.len() <= MAX_ACK_RANGES,
        delay <= VARINT_MAX,
        max_len >= FULL_ACK_LEN,
        k + 1 < r.len() ==> spec_ack_bytes(ack_of(r, k + 1, delay)).len() > max_len,
    ensures
        k + 1 == r.len(),
{
    if k + 1 < r.len() {
        lemma_full_ack_fits(r, k + 1, delay);
    }
}

/// Every candidate frame fits in `FULL_ACK_LEN` bytes.
proof fn lemma_full_ack_fits(r: Seq<(u64, u64)>, k: nat, delay: u64)
    requires
        ranges_ok(r),
        k < r.len(),
        r.len() <= MAX_ACK_RANGES,
        delay <= VARINT_MAX,
    ensures
        spec_ack_bytes(ack_of(r, k, delay)).len() <= FULL_ACK_LEN,
{
    lemma_ack_len(r, k, delay);
    lemma_pairs_len_bound(r, k);
}

/// One more pair adds exactly its two varints.
proof fn lemma_pairs_step(r: Seq<(u64, u64)>, k: int)
    requires
        ranges_ok(r),
        0 <= k,
        k + 1 < r.len(),
    ensures
        spec_pairs_bytes(ack_pairs(r).take(k + 1)).len() == spec_pairs_bytes(
            ack_pairs(r).take(k),
        ).len() + rfc_varint_min_len(ack_pairs(r)[k].0) + rfc_varint_min_len(ack_pairs(r)[k].1),
        ack_pairs(r)[k] == (((r[k].0 - r[k + 1].1) - 2) as u64, (r[k + 1].1 - r[k + 1].0) as u64),
{
    let g = ack_pairs(r);
    assert(g.take(k + 1) =~= g.take(k).push(g[k]));
    lemma_pairs_bytes_snoc(g.take(k), g[k]);
    assert(r[k + 1].1 + 1 < r[k].0);
    theorem_serialize_matches_rfc(g[k].0);
    theorem_serialize_matches_rfc(g[k].1);
}

} // verus!
impl RecvPns {
    /// Test support: the range list's allocated capacity. Verus models `Vec` length, not
    /// capacity, so the allocation bound is checked by test only (TRUSTED.md).
    #[doc(hidden)]
    pub fn ranges_capacity(&self) -> usize {
        self.ranges.capacity()
    }
}
