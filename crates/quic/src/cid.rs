//! Connection IDs (RFC 9000 §5.1, §19.15, §19.16): the CIDs we issue to the peer
//! (`LocalCids`, with their stateless reset tokens, §10.3.2) and the CIDs the peer issues to
//! us (`PeerCids`). Every CID and reset token we issue is fresh shell randomness (getrandom),
//! never derived from a static key, and no stateless reset is ever sent (3d D9).
use vstd::prelude::*;
use vstd::slice::{slice_subrange, slice_to_vec};
// Used only in ghost code (VARINT_MAX), which a plain `cargo build` erases.
#[allow(unused_imports)]
use wire::varint::*;

use crate::codes::*;
use crate::frame::*;

verus! {

//= https://www.rfc-editor.org/rfc/rfc9000#section-5.1
//= type=exception
//= reason=Our connection IDs are 8 bytes (LOCAL_CID_LEN); we never use zero-length connection IDs.
//# An
//# endpoint MUST NOT use the same IP address and port for multiple
//# concurrent connections with zero-length connection IDs, unless it is
//# certain that those protocol features are not in use.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-10.3.2
//= type=exception
//= reason=No static key: each token is fresh shell randomness per connection ID, and no stateless reset is ever sent.
//# An endpoint that uses this design MUST
//# either use the same connection ID length for all connections or
//# encode the length of the connection ID such that it can be recovered
//# without state.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-10.3.2
//= type=exception
//= reason=No static key: each token is fresh shell randomness per connection ID, and no stateless reset is ever sent.
//# This method for
//# choosing the stateless reset token means that the combination of
//# connection ID and static key MUST NOT be used for another connection.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-10.3.2
//= type=exception
//= reason=No static key: each token is fresh shell randomness per connection ID, and no stateless reset is ever sent.
//# A connection ID from a connection
//# that is reset by revealing the stateless reset token MUST NOT be
//# reused for new connections at nodes that share a static key.
/// The length of every connection ID we issue.
pub const LOCAL_CID_LEN: usize = 8;

/// At most this many of our CIDs are active at once, whatever the peer's limit.
pub const ISSUE_CAP_ACTIVE: u64 = 4;

// ponytail: lifetime cap (§5.1.1 MAY); raise if long-lived peers rotate CIDs often.
pub const ISSUE_CAP_LIFETIME: usize = 16;

/// The highest local `active_connection_id_limit` that `local_tp_ok` allows.
pub const PEER_CID_CAP: u64 = 8;

// =============================================================================
// Our connection IDs
// =============================================================================

/// One of our active CIDs: (sequence number, CID, stateless reset token).
pub type LocalEntry = (u64, [u8; 8], [u8; 16]);

pub open spec fn local_has_seq(a: Seq<LocalEntry>, s: u64) -> bool {
    exists|i: int| 0 <= i < a.len() && (#[trigger] a[i]).0 == s
}

pub open spec fn local_has_cid(a: Seq<LocalEntry>, c: Seq<u8>) -> bool {
    exists|i: int| 0 <= i < a.len() && (#[trigger] a[i]).1@ == c
}

pub open spec fn ever_has_cid(v: Seq<([u8; 8], [u8; 16])>, c: Seq<u8>) -> bool {
    exists|i: int| 0 <= i < v.len() && (#[trigger] v[i]).0@ == c
}

pub open spec fn ever_has_token(v: Seq<([u8; 8], [u8; 16])>, t: Seq<u8>) -> bool {
    exists|i: int| 0 <= i < v.len() && (#[trigger] v[i]).1@ == t
}

/// The connection IDs we issue. Sequence number `s` names `ever[s]`; seq 0 is our handshake
/// Source Connection ID, whose token goes in our `stateless_reset_token` transport parameter.
#[derive(Debug, PartialEq, Eq)]
pub struct LocalCids {
    /// Issued and not retired by the peer, ascending sequence number.
    active: Vec<LocalEntry>,
    /// Every (CID, token) ever issued, indexed by sequence number.
    ever: Vec<([u8; 8], [u8; 16])>,
    next_seq: u64,
    /// The highest sequence number sent to the peer (seq 0 travels in the handshake).
    max_sent: u64,
    /// Sequence numbers whose NEW_CONNECTION_ID frame is owed, each still active.
    pending: Vec<u64>,
}

impl LocalCids {
    pub closed spec fn wf(&self) -> bool {
        &&& self.ever@.len() <= ISSUE_CAP_LIFETIME
        &&& self.next_seq == self.ever@.len()
        &&& self.max_sent < self.next_seq
        &&& forall|i: int, j: int|
            0 <= i < j < self.ever@.len() ==> (#[trigger] self.ever@[i]).0@ != (
            #[trigger] self.ever@[j]).0@ && self.ever@[i].1@ != self.ever@[j].1@
        &&& self.active@.len() <= ISSUE_CAP_ACTIVE
        &&& forall|i: int, j: int|
            0 <= i < j < self.active@.len() ==> (#[trigger] self.active@[i]).0 < (
            #[trigger] self.active@[j]).0
        &&& forall|i: int|
            0 <= i < self.active@.len() ==> {
                &&& (#[trigger] self.active@[i]).0 < self.next_seq
                &&& self.ever@[self.active@[i].0 as int] == (self.active@[i].1, self.active@[i].2)
            }
        &&& self.pending@.no_duplicates()
        &&& forall|i: int|
            0 <= i < self.pending@.len() ==> local_has_seq(self.active@, #[trigger] self.pending@[i])
    }

    /// Active CIDs (issued, not retired), ascending sequence number.
    pub closed spec fn active_spec(&self) -> Seq<LocalEntry> {
        self.active@
    }

    /// Every (CID, token) ever issued, by sequence number.
    pub closed spec fn ever_spec(&self) -> Seq<([u8; 8], [u8; 16])> {
        self.ever@
    }

    /// The CID issued under each sequence number in `[0, next_seq)`.
    pub open spec fn issued(&self) -> Seq<Seq<u8>> {
        self.ever_spec().map_values(|e: ([u8; 8], [u8; 16])| e.0@)
    }

    pub closed spec fn next_seq_spec(&self) -> u64 {
        self.next_seq
    }

    pub closed spec fn max_sent_spec(&self) -> u64 {
        self.max_sent
    }

    pub closed spec fn pending_spec(&self) -> Seq<u64> {
        self.pending@
    }

    pub open spec fn is_active_spec(&self, cid: &[u8]) -> bool {
        local_has_cid(self.active_spec(), cid@)
    }

    /// The invariant, in terms of the accessors.
    pub proof fn lemma_wf(&self)
        requires
            self.wf(),
        ensures
            self.issued().len() == self.next_seq_spec(),
            self.next_seq_spec() <= ISSUE_CAP_LIFETIME,
            self.max_sent_spec() < self.next_seq_spec(),
            forall|i: int, j: int|
                0 <= i < j < self.issued().len() ==> #[trigger] self.issued()[i]
                    != #[trigger] self.issued()[j],
            forall|i: int, j: int|
                0 <= i < j < self.ever_spec().len() ==> (#[trigger] self.ever_spec()[i]).1@ != (
                #[trigger] self.ever_spec()[j]).1@,
            self.active_spec().len() <= ISSUE_CAP_ACTIVE,
            forall|i: int|
                0 <= i < self.active_spec().len() ==> {
                    &&& (#[trigger] self.active_spec()[i]).0 < self.next_seq_spec()
                    &&& self.issued()[self.active_spec()[i].0 as int]
                        == self.active_spec()[i].1@
                },
            forall|i: int|
                0 <= i < self.pending_spec().len() ==> local_has_seq(
                    self.active_spec(),
                    #[trigger] self.pending_spec()[i],
                ),
            self.pending_spec().len() <= ISSUE_CAP_LIFETIME,
    {
        assert forall|i: int, j: int| 0 <= i < j < self.issued().len() implies #[trigger] self.issued()[i]
            != #[trigger] self.issued()[j] by {
            assert(self.ever@[i].0@ != self.ever@[j].0@);
        }
        lemma_distinct_below(self.pending@, self.next_seq, self.active@);
    }

    pub fn new(cid0: [u8; 8], token0: [u8; 16]) -> (r: LocalCids)
        ensures
            r.wf(),
            r.active_spec() == seq![(0u64, cid0, token0)],
            r.issued() == seq![cid0@],
            r.next_seq_spec() == 1,
            r.max_sent_spec() == 0,
            r.pending_spec().len() == 0,
    {
        let mut active = Vec::new();
        active.push((0u64, cid0, token0));
        let mut ever = Vec::new();
        ever.push((cid0, token0));
        let r = LocalCids { active, ever, next_seq: 1, max_sent: 0, pending: Vec::new() };
        assert(r.active@ =~= seq![(0u64, cid0, token0)]);
        assert(r.issued() =~= seq![cid0@]);
        r
    }

    /// Whether `cid` or `token` was ever issued.
    fn ever_has(&self, cid: &[u8; 8], token: &[u8; 16]) -> (r: bool)
        ensures
            r == (ever_has_cid(self.ever@, cid@) || ever_has_token(self.ever@, token@)),
    {
        let mut i: usize = 0;
        while i < self.ever.len()
            invariant
                i <= self.ever@.len(),
                forall|j: int|
                    0 <= j < i ==> (#[trigger] self.ever@[j]).0@ != cid@ && self.ever@[j].1@
                        != token@,
            decreases self.ever@.len() - i,
        {
            let e = self.ever[i];
            if eq_bytes(e.0.as_slice(), cid.as_slice()) || eq_bytes(
                e.1.as_slice(),
                token.as_slice(),
            ) {
                assert(self.ever@[i as int] == e);
                return true;
            }
            i += 1;
        }
        false
    }

    /// The index of the active entry with sequence number `s`.
    fn find_seq(&self, s: u64) -> (r: Option<usize>)
        ensures
            r matches Some(i) ==> i < self.active@.len() && self.active@[i as int].0 == s,
            r is None ==> !local_has_seq(self.active@, s),
    {
        let mut i: usize = 0;
        while i < self.active.len()
            invariant
                i <= self.active@.len(),
                forall|j: int| 0 <= j < i ==> (#[trigger] self.active@[j]).0 != s,
            decreases self.active@.len() - i,
        {
            if self.active[i].0 == s {
                return Some(i);
            }
            i += 1;
        }
        None
    }

    /// The index of the active entry with CID `cid`.
    fn find_cid(&self, cid: &[u8]) -> (r: Option<usize>)
        ensures
            r matches Some(i) ==> i < self.active@.len() && self.active@[i as int].1@ == cid@,
            r is None ==> !local_has_cid(self.active@, cid@),
    {
        let mut i: usize = 0;
        while i < self.active.len()
            invariant
                i <= self.active@.len(),
                forall|j: int| 0 <= j < i ==> (#[trigger] self.active@[j]).1@ != cid@,
            decreases self.active@.len() - i,
        {
            if eq_bytes(self.active[i].1.as_slice(), cid) {
                return Some(i);
            }
            i += 1;
        }
        None
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-5.1
    //# Connection IDs MUST NOT contain any information that can be used by
    //# an external observer (that is, one that does not cooperate with the
    //# issuer) to correlate them with other connection IDs for the same
    //# connection.
    //
    //= https://www.rfc-editor.org/rfc/rfc9000#section-5.1
    //# As a trivial example, this means the same connection ID
    //# MUST NOT be issued more than once on the same connection.
    //
    //= https://www.rfc-editor.org/rfc/rfc9000#section-10.3.2
    //# The stateless reset token MUST be difficult to guess.
    //
    //= https://www.rfc-editor.org/rfc/rfc9000#section-10.3.2
    //# The same stateless reset token MUST NOT be used for multiple
    //# connection IDs.
    //
    //= https://www.rfc-editor.org/rfc/rfc9000#section-5.1.1
    //# The sequence number on
    //# each newly issued connection ID MUST increase by 1.
    //
    //= https://www.rfc-editor.org/rfc/rfc9000#section-5.1.1
    //# An endpoint MUST NOT
    //# provide more connection IDs than the peer's limit.
    /// Issues CID `rand[0..8]` with reset token `rand[8..24]` (fresh shell randomness, so
    /// neither carries information about the other CIDs) under the next sequence number, and
    /// queues its NEW_CONNECTION_ID frame. Refused when it would make more active CIDs than
    /// `min(peer_limit, ISSUE_CAP_ACTIVE)` (seq 0 included), when the lifetime cap is reached,
    /// or when the CID or the token was issued before (the caller retries with new randomness).
    pub fn issue(&mut self, rand: &[u8], peer_limit: u64) -> (r: bool)
        requires
            old(self).wf(),
            rand@.len() >= 24,
        ensures
            final(self).wf(),
            r == (old(self).active_spec().len() < peer_limit && old(self).active_spec().len()
                < ISSUE_CAP_ACTIVE && old(self).ever_spec().len() < ISSUE_CAP_LIFETIME
                && !ever_has_cid(old(self).ever_spec(), rand@.subrange(0, 8)) && !ever_has_token(
                old(self).ever_spec(),
                rand@.subrange(8, 24),
            )),
            r ==> {
                &&& final(self).active_spec().len() == old(self).active_spec().len() + 1
                &&& final(self).active_spec().drop_last() == old(self).active_spec()
                &&& final(self).active_spec().last().0 == old(self).next_seq_spec()
                &&& final(self).active_spec().last().1@ == rand@.subrange(0, 8)
                &&& final(self).active_spec().last().2@ == rand@.subrange(8, 24)
                &&& final(self).issued() == old(self).issued().push(rand@.subrange(0, 8))
                &&& final(self).next_seq_spec() == old(self).next_seq_spec() + 1
                &&& final(self).pending_spec() == old(self).pending_spec().push(
                    old(self).next_seq_spec(),
                )
                &&& final(self).max_sent_spec() == old(self).max_sent_spec()
            },
            r ==> final(self).active_spec().len() <= peer_limit,
            !r ==> *final(self) == *old(self),
    {
        let n = self.active.len();
        if n as u64 >= peer_limit || n as u64 >= ISSUE_CAP_ACTIVE || self.ever.len()
            >= ISSUE_CAP_LIFETIME {
            return false;
        }
        let mut cid = [0u8; 8];
        cid.copy_from_slice(slice_subrange(rand, 0, 8));
        let mut token = [0u8; 16];
        token.copy_from_slice(slice_subrange(rand, 8, 24));
        assert(cid@ == rand@.subrange(0, 8));
        assert(token@ == rand@.subrange(8, 24));
        if self.ever_has(&cid, &token) {
            return false;
        }
        let ghost a0 = self.active@;
        let ghost e0 = self.ever@;
        let ghost p0 = self.pending@;
        let seq = self.next_seq;
        self.active.push((seq, cid, token));
        self.ever.push((cid, token));
        self.pending.push(seq);
        self.next_seq = seq + 1;
        proof {
            assert forall|i: int, j: int| 0 <= i < j < self.ever@.len() implies (
            #[trigger] self.ever@[i]).0@ != (#[trigger] self.ever@[j]).0@ && self.ever@[i].1@
                != self.ever@[j].1@ by {
                if j == e0.len() {
                    assert(self.ever@[i] == e0[i]);
                }
            }
            assert forall|i: int| 0 <= i < self.active@.len() implies {
                &&& (#[trigger] self.active@[i]).0 < self.next_seq
                &&& self.ever@[self.active@[i].0 as int] == (self.active@[i].1, self.active@[i].2)
            } by {
                if i < a0.len() {
                    assert(self.active@[i] == a0[i]);
                }
            }
            assert forall|i: int| 0 <= i < self.pending@.len() implies local_has_seq(
                self.active@,
                #[trigger] self.pending@[i],
            ) by {
                if i < p0.len() {
                    let w = choose|w: int| 0 <= w < a0.len() && (#[trigger] a0[w]).0 == p0[i];
                    assert(self.active@[w] == a0[w]);
                } else {
                    assert(self.active@[a0.len() as int].0 == seq);
                }
            }
            assert forall|i: int| 0 <= i < p0.len() implies #[trigger] p0[i] != seq by {
                let w = choose|w: int| 0 <= w < a0.len() && (#[trigger] a0[w]).0 == p0[i];
            }
            assert(self.pending@.no_duplicates()) by {
                assert forall|i: int, j: int|
                    0 <= i < self.pending@.len() && 0 <= j < self.pending@.len() && i
                        != j implies self.pending@[i] != self.pending@[j] by {
                    if i < p0.len() && j < p0.len() {
                        assert(p0[i] != p0[j]);
                    } else if i < p0.len() {
                        assert(p0[i] != seq);
                    } else {
                        assert(p0[j] != seq);
                    }
                }
            }
            assert(self.active@.drop_last() =~= a0);
            assert(self.issued() =~= old(self).issued().push(rand@.subrange(0, 8)));
        }
        true
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-19.15
    //= type=exception
    //= reason=Our connection IDs are 8 bytes (LOCAL_CID_LEN); we never use zero-length connection IDs.
    //# An endpoint MUST NOT send this frame if it currently requires that
    //# its peer send packets with a zero-length Destination Connection ID.
    /// The NEW_CONNECTION_ID frame owed for the first pending sequence number (Retire Prior
    /// To 0: we never ask the peer to retire).
    pub fn pending_frame(&self) -> (r: Option<Frame>)
        requires
            self.wf(),
        ensures
            (r is None) == (self.pending_spec().len() == 0),
            r matches Some(f) ==> {
                &&& frame_wf(f@)
                &&& exists|i: int|
                    0 <= i < self.active_spec().len() && (#[trigger] self.active_spec()[i]).0
                        == self.pending_spec()[0] && f@ == (SpecFrame::NewConnectionId {
                        seq: self.active_spec()[i].0,
                        retire_prior_to: 0,
                        cid: self.active_spec()[i].1@,
                        reset_token: self.active_spec()[i].2@,
                    })
            },
    {
        if self.pending.len() == 0 {
            return None;
        }
        let s = self.pending[0];
        match self.find_seq(s) {
            Some(i) => {
                let e = self.active[i];
                assert(e.0 < ISSUE_CAP_LIFETIME);
                assert(e.1@.len() == 8 && e.2@.len() == 16);
                assert(self.active_spec()[i as int].0 == self.pending_spec()[0]);
                Some(
                    Frame::NewConnectionId {
                        seq: e.0,
                        retire_prior_to: 0,
                        cid: slice_to_vec(e.1.as_slice()),
                        reset_token: e.2,
                    },
                )
            },
            None => {
                proof {
                    assert(local_has_seq(self.active@, self.pending@[0]));
                }
                None
            },
        }
    }

    /// The frame from `pending_frame` was put in a packet: dequeue it and record it as sent.
    pub fn commit_pending(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            old(self).pending_spec().len() == 0 ==> *final(self) == *old(self),
            old(self).pending_spec().len() > 0 ==> {
                &&& final(self).pending_spec() == old(self).pending_spec().drop_first()
                &&& final(self).max_sent_spec() == if old(self).pending_spec()[0] > old(self).max_sent_spec() {
                    old(self).pending_spec()[0]
                } else {
                    old(self).max_sent_spec()
                }
            },
            final(self).active_spec() == old(self).active_spec(),
            final(self).ever_spec() == old(self).ever_spec(),
            final(self).next_seq_spec() == old(self).next_seq_spec(),
    {
        if self.pending.len() == 0 {
            return;
        }
        let ghost p0 = self.pending@;
        let s = self.pending.remove(0);
        proof {
            assert(local_has_seq(self.active@, p0[0]));
            assert(self.pending@ =~= p0.drop_first());
            assert forall|i: int| 0 <= i < self.pending@.len() implies local_has_seq(
                self.active@,
                #[trigger] self.pending@[i],
            ) by {
                assert(self.pending@[i] == p0[i + 1]);
            }
            assert forall|i: int, j: int|
                0 <= i < self.pending@.len() && 0 <= j < self.pending@.len() && i
                    != j implies self.pending@[i] != self.pending@[j] by {
                assert(p0[i + 1] != p0[j + 1]);
            }
        }
        if s > self.max_sent {
            self.max_sent = s;
        }
    }

    /// A packet carrying the NEW_CONNECTION_ID frame for `seq` was lost: owe it again if the
    /// CID is still active and the frame is not already owed. Seq 0 travels in the handshake,
    /// never in a NEW_CONNECTION_ID frame.
    pub fn on_frame_lost(&mut self, seq: u64)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).pending_spec() == if seq != 0 && local_has_seq(
                old(self).active_spec(),
                seq,
            ) && !old(self).pending_spec().contains(seq) {
                old(self).pending_spec().push(seq)
            } else {
                old(self).pending_spec()
            },
            final(self).active_spec() == old(self).active_spec(),
            final(self).ever_spec() == old(self).ever_spec(),
            final(self).next_seq_spec() == old(self).next_seq_spec(),
            final(self).max_sent_spec() == old(self).max_sent_spec(),
    {
        if seq == 0 {
            return;
        }
        if self.find_seq(seq).is_none() || contains_u64(&self.pending, seq) {
            return;
        }
        let ghost p0 = self.pending@;
        self.pending.push(seq);
        proof {
            assert forall|i: int| 0 <= i < self.pending@.len() implies local_has_seq(
                self.active@,
                #[trigger] self.pending@[i],
            ) by {
                if i < p0.len() {
                    assert(self.pending@[i] == p0[i]);
                }
            }
            assert forall|i: int, j: int|
                0 <= i < self.pending@.len() && 0 <= j < self.pending@.len() && i
                    != j implies self.pending@[i] != self.pending@[j] by {
                if i < p0.len() && j < p0.len() {
                    assert(p0[i] != p0[j]);
                } else if i < p0.len() {
                    assert(p0.contains(p0[i]));
                } else if j < p0.len() {
                    assert(p0.contains(p0[j]));
                }
            }
        }
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-19.16
    //# Receipt of a RETIRE_CONNECTION_ID frame containing a sequence number
    //# greater than any previously sent to the peer MUST be treated as a
    //# connection error of type PROTOCOL_VIOLATION.
    //
    //= https://www.rfc-editor.org/rfc/rfc9000#section-19.16
    //# The sequence number specified in a RETIRE_CONNECTION_ID frame MUST
    //# NOT refer to the Destination Connection ID field of the packet in
    //# which the frame is contained.
    //
    //= https://www.rfc-editor.org/rfc/rfc9000#section-19.16
    //= type=exception
    //= reason=Our connection IDs are 8 bytes (LOCAL_CID_LEN); we never use zero-length connection IDs.
    //# An endpoint that provides a zero-
    //# length connection ID MUST treat receipt of a RETIRE_CONNECTION_ID
    //# frame as a connection error of type PROTOCOL_VIOLATION.
    /// RETIRE_CONNECTION_ID(`seq`) arrived in a packet whose Destination Connection ID is
    /// `packet_dcid`. A sequence number above every one sent, or one naming `packet_dcid`
    /// itself, is PROTOCOL_VIOLATION. Otherwise an active CID is retired and returned (the
    /// caller unroutes it and may issue a replacement); retiring twice is harmless.
    pub fn on_retire(&mut self, seq: u64, packet_dcid: &[u8]) -> (r: Result<Option<[u8; 8]>, u64>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            (r == Err::<Option<[u8; 8]>, u64>(PROTOCOL_VIOLATION)) <==> (seq > old(self).max_sent_spec() || exists|i: int|
                0 <= i < old(self).active_spec().len() && (#[trigger] old(self).active_spec()[i]).0
                    == seq && old(self).active_spec()[i].1@ == packet_dcid@),
            r is Err ==> r == Err::<Option<[u8; 8]>, u64>(PROTOCOL_VIOLATION) && *final(self)
                == *old(self),
            r matches Ok(Some(c)) ==> exists|i: int|
                0 <= i < old(self).active_spec().len() && (#[trigger] old(self).active_spec()[i]).0
                    == seq && old(self).active_spec()[i].1 == c && final(self).active_spec()
                    == old(self).active_spec().remove(i),
            r matches Ok(None) ==> !local_has_seq(old(self).active_spec(), seq) && *final(self)
                == *old(self),
            r is Ok ==> !local_has_seq(final(self).active_spec(), seq),
            r is Ok ==> forall|x: u64|
                #[trigger] final(self).pending_spec().contains(x) <==> old(self).pending_spec().contains(x) && x != seq,
            final(self).ever_spec() == old(self).ever_spec(),
            final(self).next_seq_spec() == old(self).next_seq_spec(),
            final(self).max_sent_spec() == old(self).max_sent_spec(),
    {
        if seq > self.max_sent {
            return Err(PROTOCOL_VIOLATION);
        }
        let i = match self.find_seq(seq) {
            Some(i) => i,
            None => {
                proof {
                    assert forall|x: u64| #[trigger]
                        self.pending@.contains(x) implies x != seq by {
                        let k = choose|k: int| 0 <= k < self.pending@.len() && self.pending@[k] == x;
                        assert(local_has_seq(self.active@, self.pending@[k]));
                    }
                }
                return Ok(None);
            },
        };
        if eq_bytes(self.active[i].1.as_slice(), packet_dcid) {
            assert(self.active_spec()[i as int].0 == seq);
            return Err(PROTOCOL_VIOLATION);
        }
        proof {
            assert forall|j: int|
                0 <= j < self.active@.len() && (#[trigger] self.active@[j]).0 == seq implies j
                == i by {
                if j < i {
                    assert(self.active@[j].0 < self.active@[i as int].0);
                } else if j > i {
                    assert(self.active@[i as int].0 < self.active@[j].0);
                }
            }
        }
        let ghost a0 = self.active@;
        let ghost p0 = self.pending@;
        let e = self.active.remove(i);
        proof {
            lemma_remove_ascending(a0, i as int);
            assert forall|j: int| 0 <= j < p0.len() implies (#[trigger] p0[j]) == seq
                || local_has_seq(self.active@, p0[j]) by {
                let w = choose|w: int| 0 <= w < a0.len() && (#[trigger] a0[w]).0 == p0[j];
                if w != i {
                    let wn = if w < i { w } else { w - 1 };
                    assert(self.active@[wn] == a0[w]);
                }
            }
        }
        self.unpend(seq);
        proof {
            assert forall|j: int| 0 <= j < self.active@.len() implies {
                &&& (#[trigger] self.active@[j]).0 < self.next_seq
                &&& self.ever@[self.active@[j].0 as int] == (self.active@[j].1, self.active@[j].2)
            } by {
                let jo = if j < i { j } else { j + 1 };
                assert(self.active@[j] == a0[jo]);
            }
            assert(old(self).active_spec()[i as int].0 == seq);
            assert(old(self).active_spec()[i as int].1 == e.1);
            assert(self.active_spec() == old(self).active_spec().remove(i as int));
        }
        Ok(Some(e.1))
    }

    /// Removes `seq` from `pending` (after `active.remove(i)` with `active[i].0 == seq`).
    fn unpend(&mut self, seq: u64)
        requires
            old(self).pending@.no_duplicates(),
            forall|i: int|
                0 <= i < old(self).pending@.len() ==> (#[trigger] old(self).pending@[i]) == seq
                    || local_has_seq(old(self).active@, old(self).pending@[i]),
        ensures
            final(self).active@ == old(self).active@,
            final(self).ever@ == old(self).ever@,
            final(self).next_seq == old(self).next_seq,
            final(self).max_sent == old(self).max_sent,
            final(self).pending@.no_duplicates(),
            forall|x: u64| #[trigger]
                final(self).pending@.contains(x) <==> old(self).pending@.contains(x) && x != seq,
            forall|i: int|
                0 <= i < final(self).pending@.len() ==> local_has_seq(
                    final(self).active@,
                    #[trigger] final(self).pending@[i],
                ),
    {
        let ghost p0 = self.pending@;
        match index_of_u64(&self.pending, seq) {
            Some(k) => {
                self.pending.remove(k);
                proof {
                    assert forall|x: u64| #[trigger]
                        self.pending@.contains(x) <==> p0.contains(x) && x != seq by {
                        if self.pending@.contains(x) {
                            let m = choose|m: int| 0 <= m < self.pending@.len() && self.pending@[m] == x;
                            let mo = if m < k { m } else { m + 1 };
                            assert(p0[mo] == x);
                            assert(mo != k);
                        }
                        if p0.contains(x) && x != seq {
                            let m = choose|m: int| 0 <= m < p0.len() && p0[m] == x;
                            assert(m != k);
                            let mn = if m < k { m } else { m - 1 };
                            assert(self.pending@[mn] == x);
                        }
                    }
                    assert forall|i: int|
                        0 <= i < self.pending@.len() implies local_has_seq(
                        self.active@,
                        #[trigger] self.pending@[i],
                    ) by {
                        let io = if i < k { i } else { i + 1 };
                        assert(self.pending@[i] == p0[io]);
                        assert(p0[io] != p0[k as int]);
                    }
                    assert forall|i: int, j: int|
                        0 <= i < self.pending@.len() && 0 <= j < self.pending@.len() && i
                            != j implies self.pending@[i] != self.pending@[j] by {
                        let io = if i < k { i } else { i + 1 };
                        let jo = if j < k { j } else { j + 1 };
                        assert(p0[io] != p0[jo]);
                    }
                }
            },
            None => {
                proof {
                    assert forall|i: int|
                        0 <= i < self.pending@.len() implies local_has_seq(
                        self.active@,
                        #[trigger] self.pending@[i],
                    ) by {
                        assert(p0.contains(p0[i]));
                    }
                }
            },
        }
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-5.1.1
    //# When an endpoint issues a connection ID, it MUST accept packets that
    //# carry this connection ID for the duration of the connection or until
    //# its peer invalidates the connection ID via a RETIRE_CONNECTION_ID
    //# frame (Section 19.16).
    #[verifier::when_used_as_spec(is_active_spec)]
    /// Whether `cid` is one of our active CIDs: packets carrying it are accepted (§5.1.1; the
    /// gate is wired in 3d2). An issued CID stays active until `on_retire` removes it.
    pub fn is_active(&self, cid: &[u8]) -> (r: bool)
        ensures
            r == self.is_active_spec(cid),
    {
        self.find_cid(cid).is_some()
    }

    /// The sequence number of active CID `cid`.
    pub fn seq_of(&self, cid: &[u8]) -> (r: Option<u64>)
        ensures
            r matches Some(s) ==> exists|i: int|
                0 <= i < self.active_spec().len() && (#[trigger] self.active_spec()[i]).0 == s
                    && self.active_spec()[i].1@ == cid@,
            r is None ==> !local_has_cid(self.active_spec(), cid@),
    {
        match self.find_cid(cid) {
            Some(i) => {
                assert(self.active_spec()[i as int].1@ == cid@);
                Some(self.active[i].0)
            },
            None => None,
        }
    }

    pub fn active_len(&self) -> (r: usize)
        ensures
            r == self.active_spec().len(),
    {
        self.active.len()
    }
}

/// Removing one entry keeps the sequence numbers ascending and drops its sequence number.
proof fn lemma_remove_ascending(a: Seq<LocalEntry>, i: int)
    requires
        0 <= i < a.len(),
        forall|x: int, y: int| 0 <= x < y < a.len() ==> (#[trigger] a[x]).0 < (#[trigger] a[y]).0,
    ensures
        forall|x: int, y: int|
            0 <= x < y < a.remove(i).len() ==> (#[trigger] a.remove(i)[x]).0 < (#[trigger] a.remove(
                i,
            )[y]).0,
        !local_has_seq(a.remove(i), a[i].0),
        forall|j: int|
            0 <= j < a.remove(i).len() ==> #[trigger] a.remove(i)[j] == if j < i {
                a[j]
            } else {
                a[j + 1]
            },
{
    let r = a.remove(i);
    assert forall|x: int, y: int| 0 <= x < y < r.len() implies (#[trigger] r[x]).0 < (
    #[trigger] r[y]).0 by {
        let xo = if x < i { x } else { x + 1 };
        let yo = if y < i { y } else { y + 1 };
        assert(r[x] == a[xo] && r[y] == a[yo]);
    }
    if local_has_seq(r, a[i].0) {
        let j = choose|j: int| 0 <= j < r.len() && (#[trigger] r[j]).0 == a[i].0;
        let jo = if j < i { j } else { j + 1 };
        assert(r[j] == a[jo]);
    }
}

/// A duplicate-free list of active sequence numbers below `n` has at most `n` entries.
proof fn lemma_distinct_below(s: Seq<u64>, n: u64, a: Seq<LocalEntry>)
    requires
        s.no_duplicates(),
        forall|i: int| 0 <= i < s.len() ==> local_has_seq(a, #[trigger] s[i]),
        forall|i: int| 0 <= i < a.len() ==> (#[trigger] a[i]).0 < n,
        n <= ISSUE_CAP_LIFETIME,
    ensures
        s.len() <= ISSUE_CAP_LIFETIME,
{
    s.unique_seq_to_set();
    vstd::set_lib::range_set_properties::<u64>(0, n);
    assert forall|x: u64| s.to_set().contains(x) implies Set::<u64>::range(0, n).contains(x) by {
        let i = choose|i: int| 0 <= i < s.len() && s[i] == x;
        assert(local_has_seq(a, s[i]));
    }
    vstd::set_lib::lemma_len_subset(s.to_set(), Set::<u64>::range(0, n));
}

// =============================================================================
// The peer's connection IDs
// =============================================================================

/// One of the peer's active CIDs: (sequence number, CID, stateless reset token, used by us).
/// Seq 0 (the peer's handshake Source Connection ID) has no token.
pub type PeerEntry = (u64, Vec<u8>, Option<[u8; 16]>, bool);

pub open spec fn tok_is(o: Option<[u8; 16]>, t: Seq<u8>) -> bool {
    o matches Some(x) && x@ == t
}

/// Entry `x` is exactly NEW_CONNECTION_ID{s, c, t} (a repeat).
pub open spec fn same_at(x: PeerEntry, s: u64, c: Seq<u8>, t: Seq<u8>) -> bool {
    x.0 == s && x.1@ == c && tok_is(x.2, t)
}

/// Entry `x` contradicts NEW_CONNECTION_ID{s, c, t}: same sequence number with another CID or
/// token, or another sequence number with the same CID or token.
pub open spec fn clash_at(x: PeerEntry, s: u64, c: Seq<u8>, t: Seq<u8>) -> bool {
    if x.0 == s {
        !(x.1@ == c && tok_is(x.2, t))
    } else {
        x.1@ == c || tok_is(x.2, t)
    }
}

pub open spec fn peer_same(e: Seq<PeerEntry>, s: u64, c: Seq<u8>, t: Seq<u8>) -> bool {
    exists|i: int| 0 <= i < e.len() && same_at(#[trigger] e[i], s, c, t)
}

pub open spec fn peer_clash(e: Seq<PeerEntry>, s: u64, c: Seq<u8>, t: Seq<u8>) -> bool {
    exists|i: int| 0 <= i < e.len() && clash_at(#[trigger] e[i], s, c, t)
}

pub open spec fn peer_has_seq(e: Seq<PeerEntry>, s: u64) -> bool {
    exists|i: int| 0 <= i < e.len() && (#[trigger] e[i]).0 == s
}

pub open spec fn peer_has_cid(e: Seq<PeerEntry>, c: Seq<u8>) -> bool {
    exists|i: int| 0 <= i < e.len() && (#[trigger] e[i]).1@ == c
}

pub open spec fn peer_used(e: Seq<PeerEntry>, s: u64) -> bool {
    exists|i: int| 0 <= i < e.len() && (#[trigger] e[i]).0 == s && e[i].3
}

/// Some active CID we have used carries reset token `t` (§10.3.1).
pub open spec fn reset_match(e: Seq<PeerEntry>, t: Seq<u8>) -> bool {
    exists|i: int| 0 <= i < e.len() && (#[trigger] e[i]).3 && tok_is(e[i].2, t)
}

/// How many entries have a sequence number below `rpt`.
pub open spec fn count_below(e: Seq<PeerEntry>, rpt: u64) -> nat
    decreases e.len(),
{
    if e.len() == 0 {
        0
    } else {
        count_below(e.drop_last(), rpt) + if e.last().0 < rpt {
            1nat
        } else {
            0nat
        }
    }
}

/// The sequence numbers `a, a + 1, ..., b - 1` (empty when `b <= a`).
pub open spec fn seq_range(a: u64, b: u64) -> Seq<u64> {
    Seq::new(
        if b > a {
            (b - a) as nat
        } else {
            0nat
        },
        |i: int| (a + i) as u64,
    )
}

/// Sequence numbers strictly ascending.
pub open spec fn peer_sorted(e: Seq<PeerEntry>) -> bool {
    forall|i: int, j: int| 0 <= i < j < e.len() ==> (#[trigger] e[i]).0 < (#[trigger] e[j]).0
}

/// No two entries share a CID or a reset token.
pub open spec fn peer_distinct(e: Seq<PeerEntry>) -> bool {
    forall|i: int, j: int|
        0 <= i < j < e.len() ==> (#[trigger] e[i]).1@ != (#[trigger] e[j]).1@ && !(e[i].2 matches Some(
            x,
        ) && tok_is(e[j].2, x@))
}

/// Every CID at most 20 bytes, every sequence number at least `lrpt`.
pub open spec fn peer_shape(e: Seq<PeerEntry>, lrpt: u64) -> bool {
    forall|i: int| 0 <= i < e.len() ==> (#[trigger] e[i]).1@.len() <= MAX_CID_LEN && e[i].0 >= lrpt
}

/// The connection IDs the peer issued to us (§5.1.2, §19.15).
pub struct PeerCids {
    /// The peer's handshake Source Connection ID was empty: we send zero-length DCIDs.
    zero_len: bool,
    /// Active CIDs, ascending sequence number.
    active: Vec<PeerEntry>,
    /// The sequence number of the CID we send with on the handshake path.
    current: u64,
    largest_rpt: u64,
    /// RETIRE_CONNECTION_ID frames owed, and sent but not yet acknowledged.
    retire_pending: Vec<u64>,
    retire_unacked: Vec<u64>,
    /// Every NEW_CONNECTION_ID the peer sent (and seq 0), by sequence number.
    received: Ghost<Map<u64, (Seq<u8>, Option<[u8; 16]>)>>,
    /// Sequence numbers whose RETIRE_CONNECTION_ID was acknowledged.
    acked: Ghost<Set<u64>>,
}

impl PeerCids {
    /// Everything but "at least one entry, and `current` names a used one".
    closed spec fn wf_parts(&self) -> bool {
        let e = self.active@;
        &&& e.len() <= PEER_CID_CAP
        &&& peer_sorted(e)
        &&& peer_distinct(e)
        &&& peer_shape(e, self.largest_rpt)
        &&& self.largest_rpt <= VARINT_MAX
        &&& self.retire_pending@.len() + self.retire_unacked@.len() <= 2 * PEER_CID_CAP
        &&& forall|i: int|
            0 <= i < self.retire_pending@.len() ==> #[trigger] self.retire_pending@[i]
                < self.largest_rpt
        &&& forall|i: int|
            0 <= i < self.retire_unacked@.len() ==> #[trigger] self.retire_unacked@[i]
                < self.largest_rpt
        &&& forall|i: int|
            0 <= i < e.len() ==> self.received@.dom().contains((#[trigger] e[i]).0)
                && self.received@[e[i].0] == (e[i].1@, e[i].2)
        &&& forall|s: u64| #[trigger]
            self.received@.dom().contains(s) ==> peer_has_seq(e, s)
                || self.retire_pending@.contains(s) || self.retire_unacked@.contains(s)
                || self.acked@.contains(s)
        &&& forall|s: u64| s < self.largest_rpt ==> #[trigger] self.retired(s)
    }

    pub closed spec fn wf(&self) -> bool {
        &&& self.wf_parts()
        &&& 1 <= self.active@.len()
        &&& peer_used(self.active@, self.current)
    }

    /// Active entries, ascending sequence number.
    pub closed spec fn entries(&self) -> Seq<PeerEntry> {
        self.active@
    }

    pub closed spec fn zero_len_spec(&self) -> bool {
        self.zero_len
    }

    pub closed spec fn current_spec(&self) -> u64 {
        self.current
    }

    pub closed spec fn largest_rpt_spec(&self) -> u64 {
        self.largest_rpt
    }

    pub closed spec fn retire_pending_spec(&self) -> Seq<u64> {
        self.retire_pending@
    }

    pub closed spec fn retire_unacked_spec(&self) -> Seq<u64> {
        self.retire_unacked@
    }

    /// Every CID the peer gave us, by sequence number (never forgotten, §5.1.2).
    pub closed spec fn received(&self) -> Map<u64, (Seq<u8>, Option<[u8; 16]>)> {
        self.received@
    }

    pub closed spec fn acked(&self) -> Set<u64> {
        self.acked@
    }

    pub open spec fn backlog(&self) -> nat {
        self.retire_pending_spec().len() + self.retire_unacked_spec().len()
    }

    pub open spec fn retire_queued(&self, s: u64) -> bool {
        self.retire_pending_spec().contains(s) || self.retire_unacked_spec().contains(s)
    }

    /// We have queued, sent or had acknowledged a RETIRE_CONNECTION_ID for `s`. Every
    /// sequence number below the largest Retire Prior To is retired (`wf`).
    pub open spec fn retired(&self, s: u64) -> bool {
        self.retire_queued(s) || self.acked().contains(s)
    }

    /// How many sequence numbers an increase of the largest Retire Prior To to `rpt` retires
    /// (every seq in `[largest_rpt, rpt)`, received or not).
    pub open spec fn retire_count(&self, rpt: u64) -> nat {
        if rpt > self.largest_rpt_spec() {
            (rpt - self.largest_rpt_spec()) as nat
        } else {
            0
        }
    }

    pub open spec fn is_active_spec(&self, cid: &[u8]) -> bool {
        peer_has_cid(self.entries(), cid@)
    }

    /// NEW_CONNECTION_ID{seq, rpt} would exceed `local_limit` active CIDs after retiring
    /// (§5.1.1), or `2 * local_limit` retirements in need of sending or acknowledgment (§5.1.2).
    pub open spec fn cid_limit_hit(&self, seq: u64, rpt: u64, local_limit: u64) -> bool {
        if seq < self.largest_rpt_spec() {
            false
        } else {
            let k = count_below(self.entries(), rpt);
            self.entries().len() + 1 - k > local_limit || self.backlog() + self.retire_count(rpt)
                > 2 * local_limit
        }
    }

    /// An exact repeat whose increased Retire Prior To would exceed `2 * local_limit`
    /// retirements outstanding (§5.1.2 MAY).
    pub open spec fn repeat_limit_hit(&self, rpt: u64, local_limit: u64) -> bool {
        rpt > self.largest_rpt_spec() && self.backlog() + self.retire_count(rpt) > 2 * local_limit
    }

    /// The invariant, in terms of the accessors.
    pub proof fn lemma_wf(&self)
        requires
            self.wf(),
        ensures
            1 <= self.entries().len() <= PEER_CID_CAP,
            self.backlog() <= 2 * PEER_CID_CAP,
            peer_sorted(self.entries()),
            peer_distinct(self.entries()),
            peer_shape(self.entries(), self.largest_rpt_spec()),
            peer_used(self.entries(), self.current_spec()),
            forall|s: u64| #[trigger]
                self.received().dom().contains(s) ==> peer_has_seq(self.entries(), s)
                    || self.retire_queued(s) || self.acked().contains(s),
            forall|s: u64| s < self.largest_rpt_spec() ==> #[trigger] self.retired(s),
            forall|s: u64, c: Seq<u8>, t: Seq<u8>|
                #[trigger] peer_same(self.entries(), s, c, t) ==> !peer_clash(
                    self.entries(),
                    s,
                    c,
                    t,
                ),
    {
        assert forall|s: u64, c: Seq<u8>, t: Seq<u8>| #[trigger]
            peer_same(self.entries(), s, c, t) implies !peer_clash(self.entries(), s, c, t) by {
            lemma_same_not_clash(self.active@, s, c, t);
        }
    }

    pub fn new(scid0: &[u8]) -> (r: PeerCids)
        requires
            scid0@.len() <= MAX_CID_LEN,
        ensures
            r.wf(),
            r.zero_len_spec() == (scid0@.len() == 0),
            r.entries().len() == 1,
            r.entries()[0].0 == 0 && r.entries()[0].1@ == scid0@ && r.entries()[0].2 is None
                && r.entries()[0].3,
            r.current_spec() == 0,
            r.largest_rpt_spec() == 0,
            r.backlog() == 0,
    {
        let mut active: Vec<PeerEntry> = Vec::new();
        active.push((0u64, slice_to_vec(scid0), None, true));
        let r = PeerCids {
            zero_len: scid0.len() == 0,
            active,
            current: 0,
            largest_rpt: 0,
            retire_pending: Vec::new(),
            retire_unacked: Vec::new(),
            received: Ghost(Map::empty().insert(0u64, (scid0@, None))),
            acked: Ghost(Set::empty()),
        };
        assert(r.active@[0].0 == 0u64);
        r
    }

    /// Raises the largest Retire Prior To to `rpt`: queues a RETIRE_CONNECTION_ID for every
    /// seq in `[largest_rpt, rpt)`, received or not (each is below a seq the peer sent, so the
    /// peer issued it), and drops the first `k` entries (the active ones among them).
    fn retire_prefix(&mut self, k: usize, rpt: u64)
        requires
            old(self).wf_parts(),
            rpt <= VARINT_MAX,
            k <= old(self).active@.len(),
            forall|j: int| 0 <= j < k ==> (#[trigger] old(self).active@[j]).0 < rpt,
            forall|j: int|
                k <= j < old(self).active@.len() ==> (#[trigger] old(self).active@[j]).0 >= rpt,
            old(self).retire_pending@.len() + old(self).retire_unacked@.len() + (if rpt > old(
                self).largest_rpt {
                rpt - old(self).largest_rpt
            } else {
                0
            }) <= 2 * PEER_CID_CAP,
        ensures
            final(self).wf_parts(),
            final(self).active@ == old(self).active@.skip(k as int),
            final(self).retire_pending@ == old(self).retire_pending@ + seq_range(
                old(self).largest_rpt,
                rpt,
            ),
            final(self).largest_rpt == if rpt > old(self).largest_rpt {
                rpt
            } else {
                old(self).largest_rpt
            },
            final(self).retire_unacked == old(self).retire_unacked,
            final(self).current == old(self).current,
            final(self).zero_len == old(self).zero_len,
            final(self).received == old(self).received,
            final(self).acked == old(self).acked,
    {
        let ghost e0 = self.active@;
        let ghost rp0 = self.retire_pending@;
        let ghost l0 = self.largest_rpt;
        let mut s = self.largest_rpt;
        while s < rpt
            invariant
                l0 <= s,
                s <= if rpt > l0 {
                    rpt
                } else {
                    l0
                },
                self.retire_pending@ == rp0 + seq_range(l0, s),
            decreases rpt - s,
        {
            self.retire_pending.push(s);
            assert(seq_range(l0, (s + 1) as u64) =~= seq_range(l0, s).push(s));
            s = s + 1;
        }
        proof {
            if rpt > l0 {
                assert(s == rpt);
            } else {
                assert(seq_range(l0, s) =~= seq_range(l0, rpt));
            }
        }
        let tail = self.active.split_off(k);
        self.active = tail;
        if rpt > self.largest_rpt {
            self.largest_rpt = rpt;
        }
        proof {
            let e = self.active@;
            let p = seq_range(l0, rpt);
            let rp = self.retire_pending@;
            assert(e =~= e0.skip(k as int));
            assert forall|j: int| 0 <= j < e.len() implies #[trigger] e[j] == e0[j + k] by {}
            assert forall|j: int| 0 <= j < rp.len() implies #[trigger] rp[j] < self.largest_rpt by {
                if j >= rp0.len() {
                    assert(rp[j] == p[j - rp0.len()]);
                }
            }
            // Every seq in [l0, rpt) is now pending.
            assert forall|x: u64| l0 <= x < rpt implies rp.contains(x) by {
                assert(rp[rp0.len() + (x - l0)] == x);
            }
            assert forall|x: u64| rp0.contains(x) implies rp.contains(x) by {
                let w = choose|w: int| 0 <= w < rp0.len() && rp0[w] == x;
                assert(rp[w] == x);
            }
            assert forall|x: u64| #[trigger] self.received@.dom().contains(x) implies peer_has_seq(e, x)
                || rp.contains(x) || self.retire_unacked@.contains(x) || self.acked@.contains(x) by {
                if peer_has_seq(e0, x) {
                    let w = choose|w: int| 0 <= w < e0.len() && (#[trigger] e0[w]).0 == x;
                    if w < k {
                        assert(l0 <= x < rpt);
                    } else {
                        assert(e[w - k] == e0[w]);
                    }
                }
            }
            assert forall|x: u64| x < self.largest_rpt implies #[trigger] self.retired(x) by {
                if x < l0 {
                    assert(old(self).retired(x));
                }
            }
        }
    }

    /// Inserts the new entry (seq, cid, token, unused) in sequence order.
    fn insert_entry(&mut self, seq: u64, cid: &[u8], token: [u8; 16])
        requires
            old(self).wf_parts(),
            old(self).active@.len() < PEER_CID_CAP,
            !peer_has_seq(old(self).active@, seq),
            !peer_clash(old(self).active@, seq, cid@, token@),
            seq >= old(self).largest_rpt,
            1 <= cid@.len() <= MAX_CID_LEN,
        ensures
            final(self).wf_parts(),
            final(self).active@.len() == old(self).active@.len() + 1,
            peer_same(final(self).active@, seq, cid@, token@),
            forall|s: u64| #[trigger]
                peer_has_seq(final(self).active@, s) <==> peer_has_seq(old(self).active@, s) || s
                    == seq,
            forall|c: Seq<u8>| #[trigger]
                peer_has_cid(final(self).active@, c) <==> peer_has_cid(old(self).active@, c) || c
                    == cid@,
            forall|s: u64| #[trigger]
                peer_used(final(self).active@, s) <==> peer_used(old(self).active@, s),
            final(self).current == old(self).current,
            final(self).largest_rpt == old(self).largest_rpt,
            final(self).retire_pending == old(self).retire_pending,
            final(self).retire_unacked == old(self).retire_unacked,
            final(self).zero_len == old(self).zero_len,
            final(self).acked == old(self).acked,
    {
        let ghost e0 = self.active@;
        let mut pos: usize = 0;
        while pos < self.active.len() && self.active[pos].0 < seq
            invariant
                e0 == self.active@,
                pos <= e0.len(),
                forall|j: int| 0 <= j < pos ==> (#[trigger] e0[j]).0 < seq,
            decreases e0.len() - pos,
        {
            pos = pos + 1;
        }
        let x: PeerEntry = (seq, slice_to_vec(cid), Some(token), false);
        let ghost xv = x;
        self.active.insert(pos, x);
        self.received = Ghost(self.received@.insert(seq, (cid@, Some(token))));
        proof {
            if pos < e0.len() {
                assert(e0[pos as int].0 != seq);
            }
            lemma_insert_sorted(e0, pos as int, xv);
            lemma_insert_distinct(e0, pos as int, xv, cid@, token@);
            lemma_insert_members(e0, pos as int, xv);
            lemma_insert_index(e0, pos as int, xv);
            assert forall|x: u64| x < self.largest_rpt implies #[trigger] self.retired(x) by {
                assert(old(self).retired(x));
            }
            let e = self.active@;
            assert(e[pos as int] == xv);
            assert(same_at(e[pos as int], seq, cid@, token@));
            assert forall|i: int| 0 <= i < e.len() implies self.received@.dom().contains(
                (#[trigger] e[i]).0,
            ) && self.received@[e[i].0] == (e[i].1@, e[i].2) by {
                if i != pos {
                    let io = if i < pos { i } else { i - 1 };
                    assert(e[i] == e0[io]);
                    assert(e0[io].0 != seq);
                }
            }
            assert forall|s: u64| #[trigger] self.received@.dom().contains(s) implies peer_has_seq(e, s)
                || self.retire_pending@.contains(s) || self.retire_unacked@.contains(s)
                || self.acked@.contains(s) by {
                if s == seq {
                    assert(e[pos as int].0 == seq);
                } else {
                    assert(old(self).received@.dom().contains(s));
                }
            }
        }
    }

    /// If `current` was retired, the lowest active CID becomes current and is marked used.
    fn fix_current(&mut self)
        requires
            old(self).wf_parts(),
            1 <= old(self).active@.len(),
        ensures
            final(self).wf(),
            final(self).active@.len() == old(self).active@.len(),
            forall|i: int|
                0 <= i < final(self).active@.len() ==> (#[trigger] final(self).active@[i]).0 == old(self).active@[i].0 && final(self).active@[i].1 == old(self).active@[i].1 && final(self).active@[i].2 == old(self).active@[i].2,
            forall|s: u64| #[trigger]
                peer_has_seq(final(self).active@, s) <==> peer_has_seq(old(self).active@, s),
            forall|c: Seq<u8>| #[trigger]
                peer_has_cid(final(self).active@, c) <==> peer_has_cid(old(self).active@, c),
            forall|s: u64| #[trigger]
                peer_used(final(self).active@, s) <==> peer_used(old(self).active@, s) || s
                    == final(self).current,
            peer_has_seq(old(self).active@, old(self).current) ==> final(self).current == old(self).current,
            !peer_has_seq(old(self).active@, old(self).current) ==> forall|s: u64|
                peer_has_seq(final(self).active@, s) ==> final(self).current <= s,
            final(self).largest_rpt == old(self).largest_rpt,
            final(self).retire_pending == old(self).retire_pending,
            final(self).retire_unacked == old(self).retire_unacked,
            final(self).zero_len == old(self).zero_len,
            final(self).received == old(self).received,
            final(self).acked == old(self).acked,
    {
        let ghost e0 = self.active@;
        let mut i: usize = 0;
        while i < self.active.len()
            invariant
                e0 == self.active@,
                *self == *old(self),
                old(self).wf_parts(),
                i <= e0.len(),
                forall|j: int| 0 <= j < i ==> (#[trigger] e0[j]).0 != self.current,
            decreases e0.len() - i,
        {
            if self.active[i].0 == self.current {
                if !self.active[i].3 {
                    // `wf_parts` alone does not say `current` is used; mark it.
                    let e = self.active.remove(i);
                    self.active.insert(i, (e.0, e.1, e.2, true));
                    proof {
                        let e1 = self.active@;
                        assert(e1 =~= e0.update(i as int, (e.0, e.1, e.2, true)));
                        lemma_mark_parts(*old(self), *self, i as int);
                        lemma_update_used(e0, i as int, self.largest_rpt);
                        lemma_used_after_mark(e0, i as int);
                        assert(e1[i as int].0 == self.current && e1[i as int].3);
                        assert(peer_has_seq(e0, self.current));
                    }
                    return;
                }
                proof {
                    assert(e0[i as int].0 == self.current && e0[i as int].3);
                    assert(peer_used(e0, self.current));
                    assert(peer_has_seq(e0, self.current));
                    assert forall|s: u64| #[trigger] peer_used(e0, s) <==> peer_used(e0, s) || s
                        == self.current by {}
                }
                return;
            }
            i = i + 1;
        }
        let e = self.active.remove(0);
        let s = e.0;
        self.active.insert(0, (e.0, e.1, e.2, true));
        self.current = s;
        proof {
            let e1 = self.active@;
            assert(e1 =~= e0.update(0, (e.0, e.1, e.2, true)));
            lemma_mark_parts(*old(self), *self, 0);
            lemma_update_used(e0, 0, self.largest_rpt);
            lemma_used_after_mark(e0, 0);
            assert(e1[0].0 == s && e1[0].3);
            assert forall|t: u64| peer_has_seq(e1, t) implies s <= t by {
                let w = choose|w: int| 0 <= w < e1.len() && (#[trigger] e1[w]).0 == t;
                if w > 0 {
                    assert(e0[0].0 < e0[w].0);
                }
            }
        }
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-19.15
    //# An endpoint that is sending packets with a zero-length Destination
    //# Connection ID MUST treat receipt of a NEW_CONNECTION_ID frame as a
    //# connection error of type PROTOCOL_VIOLATION.
    //
    //= https://www.rfc-editor.org/rfc/rfc9000#section-19.15
    //# Receipt
    //# of the same frame multiple times MUST NOT be treated as a connection
    //# error.
    //
    //= https://www.rfc-editor.org/rfc/rfc9000#section-19.15
    //# A receiver
    //# MUST ignore any Retire Prior To fields that do not increase the
    //# largest received Retire Prior To value.
    //
    //= https://www.rfc-editor.org/rfc/rfc9000#section-19.15
    //# An endpoint that receives a NEW_CONNECTION_ID frame with a sequence
    //# number smaller than the Retire Prior To field of a previously
    //# received NEW_CONNECTION_ID frame MUST send a corresponding
    //# RETIRE_CONNECTION_ID frame that retires the newly received connection
    //# ID, unless it has already done so for that sequence number.
    //
    //= https://www.rfc-editor.org/rfc/rfc9000#section-5.1.1
    //# After processing a NEW_CONNECTION_ID frame and
    //# adding and retiring active connection IDs, if the number of active
    //# connection IDs exceeds the value advertised in its
    //# active_connection_id_limit transport parameter, an endpoint MUST
    //# close the connection with an error of type CONNECTION_ID_LIMIT_ERROR.
    //
    //= https://www.rfc-editor.org/rfc/rfc9000#section-5.1.2
    //# Upon receipt of an increased Retire Prior To field, the peer MUST
    //# stop using the corresponding connection IDs and retire them with
    //# RETIRE_CONNECTION_ID frames before adding the newly provided
    //# connection ID to the set of active connection IDs.
    //
    //= https://www.rfc-editor.org/rfc/rfc9000#section-5.1.2
    //# An endpoint MUST
    //# NOT forget a connection ID without retiring it, though it MAY choose
    //# to treat having connection IDs in need of retirement that exceed this
    //# limit as a connection error of type CONNECTION_ID_LIMIT_ERROR.
    /// Processes NEW_CONNECTION_ID{seq, rpt, cid, token} against our advertised
    /// `active_connection_id_limit` (`local_limit`). In order:
    /// 1. zero-length peer CIDs: PROTOCOL_VIOLATION (§19.15);
    /// 2. an exact repeat: Ok, nothing changes (§19.15), unless its `rpt` increases the
    ///    largest Retire Prior To: then the older CIDs are retired as in 5 (§5.1.2), and the
    ///    repeated CID stays;
    /// 3. the same seq with another CID or token, or the CID or token under another seq:
    ///    PROTOCOL_VIOLATION (§19.15 and §10.3.2 MAYs);
    /// 4. seq below the largest Retire Prior To (late, or a replay): Ok, nothing changes. Its
    ///    RETIRE_CONNECTION_ID was already queued when Retire Prior To passed it (§19.15
    ///    "unless it has already done so"), so a replay is never an error (§19.15);
    /// 5. otherwise retire every seq below an increased `rpt` (a smaller one is ignored),
    ///    received or not, add the CID, and if `current` was retired switch to the lowest
    ///    active one.
    /// Both limits (§5.1.1 active count after retiring; §5.1.2 MAY, at most
    /// `2 * local_limit` retirements outstanding, counting every seq the increase retires)
    /// are judged before anything changes, and an
    /// Err leaves the state unchanged (preflight I4), so `wf` holds on every path. Callers
    /// re-check every stored peer CID whenever `largest_rpt` increased; `current` can stay
    /// put while another used CID is retired.
    #[verifier::spinoff_prover]
    pub fn on_new_cid(
        &mut self,
        seq: u64,
        rpt: u64,
        cid: &[u8],
        token: [u8; 16],
        local_limit: u64,
    ) -> (r: Result<(), u64>)
        requires
            old(self).wf(),
            rpt <= seq,
            seq <= VARINT_MAX,
            1 <= cid@.len() <= MAX_CID_LEN,
            2 <= local_limit <= PEER_CID_CAP,
        ensures
            final(self).wf(),
            r is Err ==> *final(self) == *old(self),
            r is Err ==> r == Err::<(), u64>(PROTOCOL_VIOLATION) || r == Err::<(), u64>(
                CONNECTION_ID_LIMIT_ERROR,
            ),
            (r == Err::<(), u64>(PROTOCOL_VIOLATION)) <==> (old(self).zero_len_spec()
                || peer_clash(old(self).entries(), seq, cid@, token@)),
            (r == Err::<(), u64>(CONNECTION_ID_LIMIT_ERROR)) <==> (!old(self).zero_len_spec()
                && !peer_clash(old(self).entries(), seq, cid@, token@) && !peer_same(
                old(self).entries(),
                seq,
                cid@,
                token@,
            ) && old(self).cid_limit_hit(seq, rpt, local_limit) || !old(self).zero_len_spec()
                && peer_same(old(self).entries(), seq, cid@, token@) && old(
                self).repeat_limit_hit(rpt, local_limit)),
            !old(self).zero_len_spec() && peer_same(old(self).entries(), seq, cid@, token@) && rpt
                <= old(self).largest_rpt_spec() ==> *final(self) == *old(self),
            r is Ok && peer_same(old(self).entries(), seq, cid@, token@) && rpt > old(
                self).largest_rpt_spec() ==> {
                &&& final(self).largest_rpt_spec() == rpt
                &&& peer_same(final(self).entries(), seq, cid@, token@)
                &&& forall|s: u64| #[trigger]
                    peer_has_seq(final(self).entries(), s) <==> (peer_has_seq(old(self).entries(), s)
                        && s >= rpt)
                &&& forall|c: Seq<u8>| #[trigger]
                    peer_has_cid(final(self).entries(), c) ==> peer_has_cid(old(self).entries(), c)
                &&& final(self).entries().len() <= old(self).entries().len()
                &&& final(self).backlog() <= 2 * local_limit
                &&& final(self).retire_pending_spec() == old(self).retire_pending_spec() + seq_range(
                    old(self).largest_rpt_spec(),
                    rpt,
                )
                &&& final(self).retire_unacked_spec() == old(self).retire_unacked_spec()
                &&& peer_has_seq(final(self).entries(), old(self).current_spec()) ==> final(self).current_spec() == old(self).current_spec()
                &&& !peer_has_seq(final(self).entries(), old(self).current_spec()) ==> forall|
                    s: u64,
                |
                    peer_has_seq(final(self).entries(), s) ==> final(self).current_spec() <= s
                &&& forall|s: u64| #[trigger]
                    peer_used(final(self).entries(), s) ==> peer_used(old(self).entries(), s) || s
                        == final(self).current_spec()
                &&& forall|s: u64|
                    #![trigger peer_used(old(self).entries(), s)]
                    #![trigger peer_used(final(self).entries(), s)]
                    peer_used(old(self).entries(), s) && peer_has_seq(final(self).entries(), s)
                        ==> peer_used(final(self).entries(), s)
            },
            r is Ok && !peer_same(old(self).entries(), seq, cid@, token@) && seq >= old(
                self).largest_rpt_spec() ==> final(self).entries().len() <= local_limit && final(
                self).backlog() <= 2 * local_limit,
            r is Ok && !peer_same(old(self).entries(), seq, cid@, token@) && seq < old(
                self).largest_rpt_spec() ==> *final(self) == *old(self) && old(self).retired(seq),
            r is Ok && !peer_same(old(self).entries(), seq, cid@, token@) && seq >= old(self).largest_rpt_spec() ==> {
                &&& final(self).largest_rpt_spec() == if rpt > old(self).largest_rpt_spec() {
                    rpt
                } else {
                    old(self).largest_rpt_spec()
                }
                &&& peer_same(final(self).entries(), seq, cid@, token@)
                &&& forall|s: u64| #[trigger]
                    peer_has_seq(final(self).entries(), s) <==> (s == seq || (peer_has_seq(
                        old(self).entries(),
                        s,
                    ) && s >= rpt))
                &&& forall|c: Seq<u8>| #[trigger]
                    peer_has_cid(final(self).entries(), c) ==> c == cid@ || peer_has_cid(
                        old(self).entries(),
                        c,
                    )
                &&& final(self).largest_rpt_spec() == old(self).largest_rpt_spec() ==> forall|
                    c: Seq<u8>,
                | #[trigger]
                    peer_has_cid(old(self).entries(), c) ==> peer_has_cid(final(self).entries(), c)
                &&& final(self).retire_pending_spec() == old(self).retire_pending_spec() + seq_range(
                    old(self).largest_rpt_spec(),
                    rpt,
                )
                &&& final(self).retire_unacked_spec() == old(self).retire_unacked_spec()
                &&& peer_has_seq(final(self).entries(), old(self).current_spec()) ==> final(self).current_spec() == old(self).current_spec()
                &&& !peer_has_seq(final(self).entries(), old(self).current_spec()) ==> forall|
                    s: u64,
                |
                    peer_has_seq(final(self).entries(), s) ==> final(self).current_spec() <= s
                &&& forall|s: u64| #[trigger]
                    peer_used(final(self).entries(), s) ==> peer_used(old(self).entries(), s) || s
                        == final(self).current_spec()
                &&& forall|s: u64|
                    #![trigger peer_used(old(self).entries(), s)]
                    #![trigger peer_used(final(self).entries(), s)]
                    peer_used(old(self).entries(), s) && peer_has_seq(final(self).entries(), s)
                        ==> peer_used(final(self).entries(), s)
            },
    {
        if self.zero_len {
            return Err(PROTOCOL_VIOLATION);
        }
        let (same, clash) = match_scan(&self.active, seq, cid, &token);
        let k = count_prefix(&self.active, rpt);
        proof {
            lemma_same_not_clash(self.active@, seq, cid@, token@);
        }
        let backlog = self.retire_pending.len() as u64 + self.retire_unacked.len() as u64;
        if same {
            if rpt <= self.largest_rpt {
                return Ok(());
            }
            if backlog + (rpt - self.largest_rpt) > 2 * local_limit {
                return Err(CONNECTION_ID_LIMIT_ERROR);
            }
            self.repeat_raise(k, rpt, Ghost(seq), Ghost(cid@), Ghost(token@));
            return Ok(());
        }
        if clash {
            return Err(PROTOCOL_VIOLATION);
        }
        proof {
            if peer_has_seq(self.active@, seq) {
                let w = choose|w: int| 0 <= w < self.active@.len() && (#[trigger] self.active@[w]).0 == seq;
                assert(same_at(self.active@[w], seq, cid@, token@) || clash_at(self.active@[w], seq, cid@, token@));
            }
        }
        if seq < self.largest_rpt {
            assert(self.retired(seq));
            return Ok(());
        }
        proof {
            if k > 0 {
                assert(self.active@[0].0 >= self.largest_rpt);
            }
        }
        let n = if rpt > self.largest_rpt {
            rpt - self.largest_rpt
        } else {
            0
        };
        if self.active.len() as u64 + 1 - k as u64 > local_limit || backlog + n > 2
            * local_limit {
            return Err(CONNECTION_ID_LIMIT_ERROR);
        }
        let ghost e0 = self.active@;
        let ghost cur0 = self.current;
        self.retire_prefix(k, rpt);
        let ghost e1 = self.active@;
        proof {
            lemma_skip_membership(e0, k as int, rpt, seq, cid@, token@);
        }
        self.insert_entry(seq, cid, token);
        let ghost e2 = self.active@;
        self.fix_current();
        proof {
            let e3 = self.active@;
            let w = choose|w: int| 0 <= w < e2.len() && same_at(#[trigger] e2[w], seq, cid@, token@);
            assert(same_at(e3[w], seq, cid@, token@));
            assert(peer_has_seq(e3, cur0) <==> peer_has_seq(e1, cur0));
            if k == 0 {
                assert(e1 =~= e0);
            }
            assert forall|s: u64|
                peer_used(e0, s) && peer_has_seq(e3, s) implies peer_used(e3, s) by {
                assert(peer_has_seq(e0, s));
            }
        }
        Ok(())
    }

    /// An exact repeat whose Retire Prior To increases the largest one: retire every active
    /// seq below `rpt` and fix `current`; the repeated entry (seq >= rpt) stays (§5.1.2).
    fn repeat_raise(
        &mut self,
        k: usize,
        rpt: u64,
        Ghost(seq): Ghost<u64>,
        Ghost(c): Ghost<Seq<u8>>,
        Ghost(t): Ghost<Seq<u8>>,
    )
        requires
            old(self).wf(),
            rpt <= seq,
            rpt <= VARINT_MAX,
            peer_same(old(self).active@, seq, c, t),
            rpt > old(self).largest_rpt,
            k == count_below(old(self).active@, rpt),
            k <= old(self).active@.len(),
            forall|j: int| 0 <= j < k ==> (#[trigger] old(self).active@[j]).0 < rpt,
            forall|j: int|
                k <= j < old(self).active@.len() ==> (#[trigger] old(self).active@[j]).0 >= rpt,
            old(self).retire_pending@.len() + old(self).retire_unacked@.len() + (rpt - old(
                self).largest_rpt) <= 2 * PEER_CID_CAP,
        ensures
            final(self).wf(),
            final(self).largest_rpt == rpt,
            peer_same(final(self).active@, seq, c, t),
            forall|s: u64| #[trigger]
                peer_has_seq(final(self).active@, s) <==> (peer_has_seq(old(self).active@, s) && s
                    >= rpt),
            forall|x: Seq<u8>| #[trigger]
                peer_has_cid(final(self).active@, x) ==> peer_has_cid(old(self).active@, x),
            final(self).active@.len() <= old(self).active@.len(),
            final(self).retire_pending@ == old(self).retire_pending@ + seq_range(
                old(self).largest_rpt,
                rpt,
            ),
            final(self).retire_unacked == old(self).retire_unacked,
            final(self).zero_len == old(self).zero_len,
            peer_has_seq(final(self).active@, old(self).current) ==> final(self).current == old(
                self).current,
            !peer_has_seq(final(self).active@, old(self).current) ==> forall|s: u64|
                peer_has_seq(final(self).active@, s) ==> final(self).current <= s,
            forall|s: u64| #[trigger]
                peer_used(final(self).active@, s) ==> peer_used(old(self).active@, s) || s
                    == final(self).current,
            forall|s: u64|
                #![trigger peer_used(old(self).active@, s)]
                #![trigger peer_used(final(self).active@, s)]
                peer_used(old(self).active@, s) && peer_has_seq(final(self).active@, s) ==> peer_used(
                    final(self).active@,
                    s,
                ),
    {
        let ghost e0 = self.active@;
        let ghost cur0 = self.current;
        let ghost w = choose|w: int| 0 <= w < e0.len() && same_at(#[trigger] e0[w], seq, c, t);
        self.retire_prefix(k, rpt);
        let ghost e1 = self.active@;
        proof {
            lemma_skip_membership(e0, k as int, rpt, seq, c, t);
            assert(w >= k) by {
                if w < k {
                    assert(e0[w].0 < rpt);
                }
            }
            assert(e1[w - k] == e0[w]);
        }
        self.fix_current();
        proof {
            let e3 = self.active@;
            assert(same_at(e3[w - k], seq, c, t));
            assert(peer_has_seq(e3, cur0) <==> peer_has_seq(e1, cur0));
            assert forall|s: u64|
                peer_used(e0, s) && peer_has_seq(e3, s) implies peer_used(e3, s) by {
                assert(peer_has_seq(e0, s));
            }
        }
    }

    /// The index of the entry with sequence number `current`.
    fn current_idx(&self) -> (r: usize)
        requires
            self.wf(),
        ensures
            r < self.active@.len(),
            self.active@[r as int].0 == self.current,
            self.active@[r as int].3,
    {
        let mut i: usize = 0;
        while i < self.active.len()
            invariant
                i <= self.active@.len(),
                peer_used(self.active@, self.current),
                peer_sorted(self.active@),
                forall|j: int| 0 <= j < i ==> (#[trigger] self.active@[j]).0 != self.current,
            decreases self.active@.len() - i,
        {
            if self.active[i].0 == self.current {
                proof {
                    let w = choose|w: int|
                        0 <= w < self.active@.len() && (#[trigger] self.active@[w]).0
                            == self.current && self.active@[w].3;
                    if w < i {
                    } else if w > i {
                        assert(self.active@[i as int].0 < self.active@[w].0);
                    }
                }
                return i;
            }
            i = i + 1;
        }
        proof {
            let w = choose|w: int|
                0 <= w < self.active@.len() && (#[trigger] self.active@[w]).0 == self.current
                    && self.active@[w].3;
            assert(self.active@[w].0 != self.current);
        }
        0
    }

    /// The CID we send with on the handshake path.
    pub fn current(&self) -> (r: &[u8])
        requires
            self.wf(),
        ensures
            exists|i: int|
                0 <= i < self.entries().len() && (#[trigger] self.entries()[i]).0
                    == self.current_spec() && self.entries()[i].3 && r@ == self.entries()[i].1@,
            peer_has_cid(self.entries(), r@),
    {
        let i = self.current_idx();
        assert(self.entries()[i as int].0 == self.current_spec() && self.entries()[i as int].3);
        self.active[i].1.as_slice()
    }

    pub fn largest_rpt(&self) -> (r: u64)
        ensures
            r == self.largest_rpt_spec(),
    {
        self.largest_rpt
    }

    #[verifier::when_used_as_spec(is_active_spec)]
    /// Whether `cid` is one of the peer's active CIDs (3d2 rewrites any stored destination CID
    /// that is no longer active, §5.1.2 "MUST stop using").
    pub fn is_active(&self, cid: &[u8]) -> (r: bool)
        ensures
            r == self.is_active_spec(cid),
    {
        let mut i: usize = 0;
        while i < self.active.len()
            invariant
                i <= self.active@.len(),
                forall|j: int| 0 <= j < i ==> (#[trigger] self.active@[j]).1@ != cid@,
            decreases self.active@.len() - i,
        {
            if eq_bytes(self.active[i].1.as_slice(), cid) {
                return true;
            }
            i = i + 1;
        }
        false
    }

    /// The RETIRE_CONNECTION_ID frame owed first.
    pub fn pending_retire(&self) -> (r: Option<Frame>)
        requires
            self.wf(),
        ensures
            (r is None) == (self.retire_pending_spec().len() == 0),
            r matches Some(f) ==> frame_wf(f@) && f@ == SpecFrame::RetireConnectionId(
                self.retire_pending_spec()[0],
            ),
    {
        if self.retire_pending.len() == 0 {
            None
        } else {
            Some(Frame::RetireConnectionId(self.retire_pending[0]))
        }
    }

    /// The frame from `pending_retire` was put in a packet: it now awaits acknowledgment.
    pub fn commit_retire(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            old(self).retire_pending_spec().len() == 0 ==> *final(self) == *old(self),
            old(self).retire_pending_spec().len() > 0 ==> {
                &&& final(self).retire_pending_spec() == old(self).retire_pending_spec().drop_first()
                &&& final(self).retire_unacked_spec() == old(self).retire_unacked_spec().push(
                    old(self).retire_pending_spec()[0],
                )
            },
            final(self).entries() == old(self).entries(),
            final(self).current_spec() == old(self).current_spec(),
            final(self).largest_rpt_spec() == old(self).largest_rpt_spec(),
    {
        if self.retire_pending.len() == 0 {
            return;
        }
        let ghost rp0 = self.retire_pending@;
        let ghost ru0 = self.retire_unacked@;
        let s = self.retire_pending.remove(0);
        self.retire_unacked.push(s);
        proof {
            let rp = self.retire_pending@;
            let ru = self.retire_unacked@;
            assert(rp =~= rp0.drop_first());
            assert forall|x: u64|
                #![trigger rp.contains(x)]
                #![trigger ru.contains(x)]
                (rp.contains(x) || ru.contains(x)) <==> (rp0.contains(x) || ru0.contains(x)) by {
                if rp.contains(x) {
                    let m = choose|m: int| 0 <= m < rp.len() && rp[m] == x;
                    assert(rp0[m + 1] == x);
                }
                if ru.contains(x) {
                    let m = choose|m: int| 0 <= m < ru.len() && ru[m] == x;
                    if m < ru0.len() {
                        assert(ru0[m] == x);
                    } else {
                        assert(rp0[0] == x);
                    }
                }
                if rp0.contains(x) {
                    let m = choose|m: int| 0 <= m < rp0.len() && rp0[m] == x;
                    if m == 0 {
                        assert(ru[ru0.len() as int] == x);
                    } else {
                        assert(rp[m - 1] == x);
                    }
                }
                if ru0.contains(x) {
                    let m = choose|m: int| 0 <= m < ru0.len() && ru0[m] == x;
                    assert(ru[m] == x);
                }
            }
            assert forall|x: u64| x < self.largest_rpt implies rp0.contains(x) || ru0.contains(x)
                || self.acked@.contains(x) by {
                assert(old(self).retired(x));
            }
            self.lemma_lists_moved(rp0, ru0);
        }
    }

    /// A packet carrying RETIRE_CONNECTION_ID(`seq`) was lost: owe it again.
    pub fn retire_lost(&mut self, seq: u64)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            !old(self).retire_unacked_spec().contains(seq) ==> *final(self) == *old(self),
            old(self).retire_unacked_spec().contains(seq) ==> {
                &&& final(self).retire_pending_spec() == old(self).retire_pending_spec().push(seq)
                &&& exists|i: int|
                    0 <= i < old(self).retire_unacked_spec().len() && #[trigger] old(self).retire_unacked_spec()[i] == seq && final(self).retire_unacked_spec()
                        == old(self).retire_unacked_spec().remove(i)
            },
            final(self).entries() == old(self).entries(),
            final(self).current_spec() == old(self).current_spec(),
            final(self).largest_rpt_spec() == old(self).largest_rpt_spec(),
    {
        if let Some(i) = index_of_u64(&self.retire_unacked, seq) {
            let ghost rp0 = self.retire_pending@;
            let ghost ru0 = self.retire_unacked@;
            self.retire_unacked.remove(i);
            self.retire_pending.push(seq);
            proof {
                let rp = self.retire_pending@;
                let ru = self.retire_unacked@;
                assert(ru0[i as int] == seq);
                assert forall|x: u64|
                    #![trigger rp.contains(x)]
                    #![trigger ru.contains(x)]
                    (rp.contains(x) || ru.contains(x)) <==> (rp0.contains(x) || ru0.contains(x)) by {
                    if rp.contains(x) {
                        let m = choose|m: int| 0 <= m < rp.len() && rp[m] == x;
                        if m < rp0.len() {
                            assert(rp0[m] == x);
                        }
                    }
                    if ru.contains(x) {
                        let m = choose|m: int| 0 <= m < ru.len() && ru[m] == x;
                        let mo = if m < i { m } else { m + 1 };
                        assert(ru0[mo] == x);
                    }
                    if rp0.contains(x) {
                        let m = choose|m: int| 0 <= m < rp0.len() && rp0[m] == x;
                        assert(rp[m] == x);
                    }
                    if ru0.contains(x) {
                        let m = choose|m: int| 0 <= m < ru0.len() && ru0[m] == x;
                        if m == i {
                            assert(rp[rp0.len() as int] == x);
                        } else {
                            let mn = if m < i { m } else { m - 1 };
                            assert(ru[mn] == x);
                        }
                    }
                }
                assert forall|x: u64| x < self.largest_rpt implies rp0.contains(x) || ru0.contains(x)
                    || self.acked@.contains(x) by {
                    assert(old(self).retired(x));
                }
                self.lemma_lists_moved(rp0, ru0);
            }
        }
    }

    /// RETIRE_CONNECTION_ID(`seq`) was acknowledged: the peer has retired it.
    pub fn retire_acked(&mut self, seq: u64)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            !old(self).retire_unacked_spec().contains(seq) ==> *final(self) == *old(self),
            old(self).retire_unacked_spec().contains(seq) ==> {
                &&& final(self).acked() == old(self).acked().insert(seq)
                &&& exists|i: int|
                    0 <= i < old(self).retire_unacked_spec().len() && #[trigger] old(self).retire_unacked_spec()[i] == seq && final(self).retire_unacked_spec()
                        == old(self).retire_unacked_spec().remove(i)
            },
            final(self).retire_pending_spec() == old(self).retire_pending_spec(),
            final(self).entries() == old(self).entries(),
            final(self).current_spec() == old(self).current_spec(),
            final(self).largest_rpt_spec() == old(self).largest_rpt_spec(),
    {
        if let Some(i) = index_of_u64(&self.retire_unacked, seq) {
            let ghost ru0 = self.retire_unacked@;
            self.retire_unacked.remove(i);
            self.acked = Ghost(self.acked@.insert(seq));
            proof {
                let ru = self.retire_unacked@;
                assert forall|j: int| 0 <= j < ru.len() implies #[trigger] ru[j]
                    < self.largest_rpt by {
                    let jo = if j < i { j } else { j + 1 };
                    assert(ru[j] == ru0[jo]);
                }
                assert forall|s: u64| #[trigger] self.received@.dom().contains(s) implies peer_has_seq(
                    self.active@,
                    s,
                ) || self.retire_pending@.contains(s) || ru.contains(s) || self.acked@.contains(
                    s,
                ) by {
                    if s != seq && ru0.contains(s) {
                        let w = choose|w: int| 0 <= w < ru0.len() && ru0[w] == s;
                        assert(w != i);
                        let wn = if w < i { w } else { w - 1 };
                        assert(ru[wn] == s);
                    }
                }
                assert forall|x: u64| x < self.largest_rpt implies #[trigger] self.retired(x) by {
                    assert(old(self).retired(x));
                    if x != seq && ru0.contains(x) {
                        let w = choose|w: int| 0 <= w < ru0.len() && ru0[w] == x;
                        assert(w != i);
                        let wn = if w < i { w } else { w - 1 };
                        assert(ru[wn] == x);
                    }
                }
            }
        }
    }

    /// After moving one sequence number between the retire lists (same multiset of values),
    /// the list conjuncts of `wf` still hold.
    proof fn lemma_lists_moved(&self, rp0: Seq<u64>, ru0: Seq<u64>)
        requires
            self.active@.len() <= PEER_CID_CAP,
            1 <= self.active@.len(),
            peer_used(self.active@, self.current),
            peer_sorted(self.active@),
            peer_distinct(self.active@),
            peer_shape(self.active@, self.largest_rpt),
            self.largest_rpt <= VARINT_MAX,
            rp0.len() + ru0.len() <= 2 * PEER_CID_CAP,
            self.retire_pending@.len() + self.retire_unacked@.len() == rp0.len() + ru0.len(),
            forall|i: int| 0 <= i < rp0.len() ==> #[trigger] rp0[i] < self.largest_rpt,
            forall|i: int| 0 <= i < ru0.len() ==> #[trigger] ru0[i] < self.largest_rpt,
            forall|x: u64|
                #![trigger self.retire_pending@.contains(x)]
                #![trigger self.retire_unacked@.contains(x)]
                (self.retire_pending@.contains(x) || self.retire_unacked@.contains(x)) <==> (
                rp0.contains(x) || ru0.contains(x)),
            forall|i: int|
                0 <= i < self.active@.len() ==> self.received@.dom().contains(
                    (#[trigger] self.active@[i]).0,
                ) && self.received@[self.active@[i].0] == (
                    self.active@[i].1@,
                    self.active@[i].2,
                ),
            forall|s: u64| #[trigger]
                self.received@.dom().contains(s) ==> peer_has_seq(self.active@, s)
                    || rp0.contains(s) || ru0.contains(s) || self.acked@.contains(s),
            forall|s: u64|
                s < self.largest_rpt ==> rp0.contains(s) || ru0.contains(s) || self.acked@.contains(
                    s,
                ),
        ensures
            self.wf(),
    {
        assert forall|x: u64| x < self.largest_rpt implies #[trigger] self.retired(x) by {
            if rp0.contains(x) || ru0.contains(x) {
                assert(self.retire_pending@.contains(x) || self.retire_unacked@.contains(x));
            }
        }
        assert forall|i: int| 0 <= i < self.retire_pending@.len() implies #[trigger]
            self.retire_pending@[i] < self.largest_rpt by {
            let x = self.retire_pending@[i];
            assert(self.retire_pending@.contains(x));
            if rp0.contains(x) {
                let w = choose|w: int| 0 <= w < rp0.len() && rp0[w] == x;
                assert(rp0[w] < self.largest_rpt);
            } else {
                let w = choose|w: int| 0 <= w < ru0.len() && ru0[w] == x;
                assert(ru0[w] < self.largest_rpt);
            }
        }
        assert forall|i: int| 0 <= i < self.retire_unacked@.len() implies #[trigger]
            self.retire_unacked@[i] < self.largest_rpt by {
            let x = self.retire_unacked@[i];
            assert(self.retire_unacked@.contains(x));
            if rp0.contains(x) {
                let w = choose|w: int| 0 <= w < rp0.len() && rp0[w] == x;
                assert(rp0[w] < self.largest_rpt);
            } else {
                let w = choose|w: int| 0 <= w < ru0.len() && ru0[w] == x;
                assert(ru0[w] < self.largest_rpt);
            }
        }
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-10.3.1
    //# An endpoint MUST NOT check for any stateless reset tokens associated
    //# with connection IDs it has not used or for connection IDs that have
    //# been retired.
    /// Whether `tail` (a datagram's last 16 bytes) is the reset token of an active CID we
    /// have used. Constant-time style: all 16 bytes of every candidate are XOR-accumulated
    /// with no early exit (the timing itself is unverified; TRUSTED.md).
    pub fn matches_reset(&self, tail: &[u8; 16]) -> (r: bool)
        requires
            self.wf(),
        ensures
            r == reset_match(self.entries(), tail@),
    {
        let ghost e = self.active@;
        let mut hit = false;
        let mut i: usize = 0;
        while i < self.active.len()
            invariant
                e == self.active@,
                i <= e.len(),
                hit == exists|j: int| 0 <= j < i && (#[trigger] e[j]).3 && tok_is(e[j].2, tail@),
            decreases e.len() - i,
        {
            if let Some(t) = self.active[i].2 {
                let eq = ct_eq16(&t, tail);
                hit = hit | (eq & self.active[i].3);
            }
            i = i + 1;
        }
        hit
    }

    /// The reset tokens of every active CID we have used (registered with the shell).
    pub fn used_tokens(&self) -> (r: Vec<[u8; 16]>)
        requires
            self.wf(),
        ensures
            r@.len() <= self.entries().len(),
            forall|j: int| 0 <= j < r@.len() ==> reset_match(self.entries(), (#[trigger] r@[j])@),
            forall|i: int|
                0 <= i < self.entries().len() && (#[trigger] self.entries()[i]).3
                    && self.entries()[i].2 is Some ==> r@.contains(self.entries()[i].2->0),
    {
        let ghost e = self.active@;
        let mut out: Vec<[u8; 16]> = Vec::new();
        let mut i: usize = 0;
        while i < self.active.len()
            invariant
                e == self.active@,
                i <= e.len(),
                out@.len() <= i,
                forall|j: int| 0 <= j < out@.len() ==> reset_match(e, (#[trigger] out@[j])@),
                forall|m: int|
                    0 <= m < i && (#[trigger] e[m]).3 && e[m].2 is Some ==> out@.contains(
                        e[m].2->0,
                    ),
            decreases e.len() - i,
        {
            if self.active[i].3 {
                if let Some(t) = self.active[i].2 {
                    let ghost o0 = out@;
                    out.push(t);
                    proof {
                        assert(tok_is(e[i as int].2, t@));
                        assert(out@[o0.len() as int] == t);
                        assert forall|m: int|
                            0 <= m < i + 1 && (#[trigger] e[m]).3 && e[m].2 is Some implies out@.contains(
                            e[m].2->0,
                        ) by {
                            if m < i {
                                let w = choose|w: int| 0 <= w < o0.len() && o0[w] == e[m].2->0;
                                assert(out@[w] == o0[w]);
                            }
                        }
                    }
                }
            }
            i = i + 1;
        }
        out
    }

    /// Whether some active CID is still unused (a fresh one for a new destination, §9.5).
    pub fn has_unused(&self) -> (r: bool)
        ensures
            r == exists|i: int| 0 <= i < self.entries().len() && !(#[trigger] self.entries()[i]).3,
    {
        let mut i: usize = 0;
        while i < self.active.len()
            invariant
                i <= self.active@.len(),
                forall|j: int| 0 <= j < i ==> (#[trigger] self.active@[j]).3,
            decreases self.active@.len() - i,
        {
            if !self.active[i].3 {
                assert(!self.entries()[i as int].3);
                return true;
            }
            i = i + 1;
        }
        false
    }

    /// Marks the lowest unused active CID used and returns a copy (3d2 gives each new
    /// destination its own CID, §9.5).
    pub fn use_next(&mut self) -> (r: Option<Vec<u8>>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            (r is None) == (forall|i: int|
                0 <= i < old(self).entries().len() ==> (#[trigger] old(self).entries()[i]).3),
            r is None ==> *final(self) == *old(self),
            r matches Some(c) ==> exists|i: int|
                0 <= i < old(self).entries().len() && !(#[trigger] old(self).entries()[i]).3
                    && c@ == old(self).entries()[i].1@ && final(self).entries() == old(self).entries().update(
                    i,
                    (
                        old(self).entries()[i].0,
                        old(self).entries()[i].1,
                        old(self).entries()[i].2,
                        true,
                    ),
                ),
            r matches Some(c) ==> peer_has_cid(final(self).entries(), c@),
            final(self).current_spec() == old(self).current_spec(),
            final(self).largest_rpt_spec() == old(self).largest_rpt_spec(),
            final(self).retire_pending_spec() == old(self).retire_pending_spec(),
            final(self).retire_unacked_spec() == old(self).retire_unacked_spec(),
    {
        let ghost e0 = self.active@;
        let mut i: usize = 0;
        while i < self.active.len()
            invariant
                e0 == self.active@,
                *self == *old(self),
                old(self).wf(),
                i <= e0.len(),
                forall|j: int| 0 <= j < i ==> (#[trigger] e0[j]).3,
            decreases e0.len() - i,
        {
            if !self.active[i].3 {
                let e = self.active.remove(i);
                let c = slice_to_vec(e.1.as_slice());
                self.active.insert(i, (e.0, e.1, e.2, true));
                proof {
                    let e1 = self.active@;
                    assert(e1 =~= e0.update(i as int, (e.0, e.1, e.2, true)));
                    lemma_mark_parts(*old(self), *self, i as int);
                    lemma_update_used(e0, i as int, self.largest_rpt);
                    lemma_used_after_mark(e0, i as int);
                    assert(e1[i as int].1@ == c@);
                    assert(peer_has_cid(e1, c@));
                    assert(!old(self).entries()[i as int].3);
                    let w = choose|w: int| 0 <= w < e0.len() && (#[trigger] e0[w]).0 == self.current && e0[w].3;
                    assert(e1[w].0 == self.current && e1[w].3);
                }
                return Some(c);
            }
            i = i + 1;
        }
        assert forall|j: int| 0 <= j < old(self).entries().len() implies (#[trigger] old(self).entries()[j]).3 by {
            assert(e0[j].3);
        }
        None
    }
}

/// Whether NEW_CONNECTION_ID{seq, cid, token} repeats an entry, and whether it clashes with
/// one.
fn match_scan(v: &Vec<PeerEntry>, seq: u64, cid: &[u8], token: &[u8; 16]) -> (r: (bool, bool))
    ensures
        r.0 == peer_same(v@, seq, cid@, token@),
        r.1 == peer_clash(v@, seq, cid@, token@),
{
    let mut same = false;
    let mut clash = false;
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v@.len(),
            same == exists|j: int| 0 <= j < i && same_at(#[trigger] v@[j], seq, cid@, token@),
            clash == exists|j: int| 0 <= j < i && clash_at(#[trigger] v@[j], seq, cid@, token@),
        decreases v@.len() - i,
    {
        let c_eq = eq_bytes(v[i].1.as_slice(), cid);
        let t_eq = match v[i].2 {
            Some(t) => eq_bytes(t.as_slice(), token.as_slice()),
            None => false,
        };
        let hit_same = v[i].0 == seq && c_eq && t_eq;
        let hit_clash = if v[i].0 == seq {
            !(c_eq && t_eq)
        } else {
            c_eq || t_eq
        };
        proof {
            assert(t_eq == tok_is(v@[i as int].2, token@));
            assert(hit_same == same_at(v@[i as int], seq, cid@, token@));
            assert(hit_clash == clash_at(v@[i as int], seq, cid@, token@));
        }
        same = same || hit_same;
        clash = clash || hit_clash;
        i = i + 1;
    }
    (same, clash)
}

/// How many entries lie below `rpt`; sorted, they form a prefix.
fn count_prefix(v: &Vec<PeerEntry>, rpt: u64) -> (k: usize)
    requires
        peer_sorted(v@),
    ensures
        k == count_below(v@, rpt),
        k <= v@.len(),
        forall|j: int| 0 <= j < k ==> (#[trigger] v@[j]).0 < rpt,
        forall|j: int| k <= j < v@.len() ==> (#[trigger] v@[j]).0 >= rpt,
{
    let ghost e = v@;
    let mut k: usize = 0;
    let mut i: usize = 0;
    while i < v.len()
        invariant
            e == v@,
            peer_sorted(e),
            i <= e.len(),
            k <= i,
            k == count_below(e.take(i as int), rpt),
            forall|j: int| 0 <= j < k ==> (#[trigger] e[j]).0 < rpt,
            forall|j: int| k <= j < i ==> (#[trigger] e[j]).0 >= rpt,
        decreases e.len() - i,
    {
        let s = v[i].0;
        proof {
            assert(e.take(i + 1).drop_last() =~= e.take(i as int));
            assert(e.take(i + 1).last() == e[i as int]);
            if s < rpt && k < i {
                assert(e[k as int].0 < e[i as int].0);
            }
        }
        if s < rpt {
            k = k + 1;
        }
        i = i + 1;
    }
    assert(e.take(e.len() as int) =~= e);
    k
}

/// A repeat never clashes (sequence numbers and CIDs and tokens are distinct).
proof fn lemma_same_not_clash(e: Seq<PeerEntry>, s: u64, c: Seq<u8>, t: Seq<u8>)
    requires
        peer_sorted(e),
        peer_distinct(e),
    ensures
        peer_same(e, s, c, t) ==> !peer_clash(e, s, c, t),
{
    if peer_same(e, s, c, t) && peer_clash(e, s, c, t) {
        let i = choose|i: int| 0 <= i < e.len() && same_at(#[trigger] e[i], s, c, t);
        let j = choose|j: int| 0 <= j < e.len() && clash_at(#[trigger] e[j], s, c, t);
        if i < j {
            assert(e[i].0 < e[j].0);
        } else if j < i {
            assert(e[j].0 < e[i].0);
        }
    }
}

/// Dropping the prefix of entries below `rpt` keeps exactly the entries at or above it.
proof fn lemma_skip_membership(e: Seq<PeerEntry>, k: int, rpt: u64, seq: u64, c: Seq<u8>, t: Seq<u8>)
    requires
        0 <= k <= e.len(),
        forall|j: int| 0 <= j < k ==> (#[trigger] e[j]).0 < rpt,
        forall|j: int| k <= j < e.len() ==> (#[trigger] e[j]).0 >= rpt,
    ensures
        forall|s: u64| #[trigger]
            peer_has_seq(e.skip(k), s) <==> peer_has_seq(e, s) && s >= rpt,
        forall|x: Seq<u8>| #[trigger] peer_has_cid(e.skip(k), x) ==> peer_has_cid(e, x),
        forall|s: u64| #[trigger] peer_used(e.skip(k), s) <==> peer_used(e, s) && s >= rpt,
        !peer_clash(e, seq, c, t) ==> !peer_clash(e.skip(k), seq, c, t),
        !peer_has_seq(e, seq) ==> !peer_has_seq(e.skip(k), seq),
        k == 0 ==> e.skip(k) == e,
{
    let r = e.skip(k);
    assert forall|j: int| 0 <= j < r.len() implies #[trigger] r[j] == e[j + k] by {}
    assert forall|s: u64| #[trigger] peer_has_seq(r, s) <==> peer_has_seq(e, s) && s >= rpt by {
        if peer_has_seq(e, s) && s >= rpt {
            let w = choose|w: int| 0 <= w < e.len() && (#[trigger] e[w]).0 == s;
            assert(r[w - k] == e[w]);
        }
        if peer_has_seq(r, s) {
            let w = choose|w: int| 0 <= w < r.len() && (#[trigger] r[w]).0 == s;
            assert(r[w] == e[w + k]);
        }
    }
    assert forall|x: Seq<u8>| #[trigger] peer_has_cid(r, x) implies peer_has_cid(e, x) by {
        let w = choose|w: int| 0 <= w < r.len() && (#[trigger] r[w]).1@ == x;
        assert(r[w] == e[w + k]);
    }
    assert forall|s: u64| #[trigger] peer_used(r, s) <==> peer_used(e, s) && s >= rpt by {
        if peer_used(e, s) && s >= rpt {
            let w = choose|w: int| 0 <= w < e.len() && (#[trigger] e[w]).0 == s && e[w].3;
            assert(r[w - k] == e[w]);
        }
        if peer_used(r, s) {
            let w = choose|w: int| 0 <= w < r.len() && (#[trigger] r[w]).0 == s && r[w].3;
            assert(r[w] == e[w + k]);
        }
    }
    if peer_clash(r, seq, c, t) {
        let w = choose|w: int| 0 <= w < r.len() && clash_at(#[trigger] r[w], seq, c, t);
        assert(r[w] == e[w + k]);
    }
    if k == 0 {
        assert(r =~= e);
    }
}

/// The entries of `e.insert(pos, x)`, by index.
proof fn lemma_insert_index(e: Seq<PeerEntry>, pos: int, x: PeerEntry)
    requires
        0 <= pos <= e.len(),
    ensures
        e.insert(pos, x).len() == e.len() + 1,
        forall|j: int|
            0 <= j < e.insert(pos, x).len() ==> #[trigger] e.insert(pos, x)[j] == if j < pos {
                e[j]
            } else if j == pos {
                x
            } else {
                e[j - 1]
            },
{
}

/// Inserting `x` at its sorted position keeps the sequence numbers ascending.
proof fn lemma_insert_sorted(e: Seq<PeerEntry>, pos: int, x: PeerEntry)
    requires
        0 <= pos <= e.len(),
        peer_sorted(e),
        forall|j: int| 0 <= j < pos ==> (#[trigger] e[j]).0 < x.0,
        pos < e.len() ==> e[pos].0 > x.0,
    ensures
        peer_sorted(e.insert(pos, x)),
{
    let r = e.insert(pos, x);
    lemma_insert_index(e, pos, x);
    assert forall|i: int, j: int| 0 <= i < j < r.len() implies (#[trigger] r[i]).0 < (
    #[trigger] r[j]).0 by {
        if i < pos && j == pos {
        } else if i < pos && j > pos {
            assert(e[i].0 < x.0);
            if j - 1 > pos {
                assert(e[pos].0 < e[j - 1].0);
            }
        } else if i == pos {
            if j - 1 > pos {
                assert(e[pos].0 < e[j - 1].0);
            }
        } else if j < pos {
        } else {
            assert(e[i - 1].0 < e[j - 1].0);
        }
    }
}

/// Inserting an entry that clashes with none keeps CIDs and tokens distinct.
proof fn lemma_insert_distinct(e: Seq<PeerEntry>, pos: int, x: PeerEntry, c: Seq<u8>, t: Seq<u8>)
    requires
        0 <= pos <= e.len(),
        peer_distinct(e),
        !peer_has_seq(e, x.0),
        !peer_clash(e, x.0, c, t),
        x.1@ == c && tok_is(x.2, t),
    ensures
        peer_distinct(e.insert(pos, x)),
{
    let r = e.insert(pos, x);
    lemma_insert_index(e, pos, x);
    assert forall|i: int, j: int| 0 <= i < j < r.len() implies (#[trigger] r[i]).1@ != (
    #[trigger] r[j]).1@ && !(r[i].2 matches Some(z) && tok_is(r[j].2, z@)) by {
        if i == pos {
            assert(!clash_at(e[j - 1], x.0, c, t));
            assert(e[j - 1].0 != x.0);
        } else if j == pos {
            assert(!clash_at(e[i], x.0, c, t));
            assert(e[i].0 != x.0);
        } else {
            let io = if i < pos { i } else { i - 1 };
            let jo = if j < pos { j } else { j - 1 };
            assert(r[i] == e[io] && r[j] == e[jo]);
            assert(io < jo);
        }
    }
}

/// Inserting `x` adds exactly its sequence number and CID, and no used mark (`x` is unused).
proof fn lemma_insert_members(e: Seq<PeerEntry>, pos: int, x: PeerEntry)
    requires
        0 <= pos <= e.len(),
        !x.3,
        !peer_has_seq(e, x.0),
    ensures
        forall|s: u64| #[trigger] peer_has_seq(e.insert(pos, x), s) <==> peer_has_seq(e, s) || s == x.0,
        forall|y: Seq<u8>| #[trigger] peer_has_cid(e.insert(pos, x), y) <==> peer_has_cid(e, y) || y == x.1@,
        forall|s: u64| #[trigger] peer_used(e.insert(pos, x), s) <==> peer_used(e, s),
{
    let r = e.insert(pos, x);
    lemma_insert_index(e, pos, x);
    assert forall|s: u64| #[trigger] peer_has_seq(r, s) <==> peer_has_seq(e, s) || s == x.0 by {
        if peer_has_seq(e, s) {
            let w = choose|w: int| 0 <= w < e.len() && (#[trigger] e[w]).0 == s;
            let wn = if w < pos { w } else { w + 1 };
            assert(r[wn] == e[w]);
        }
        if s == x.0 {
            assert(r[pos].0 == s);
        }
        if peer_has_seq(r, s) {
            let w = choose|w: int| 0 <= w < r.len() && (#[trigger] r[w]).0 == s;
            if w != pos {
                let wo = if w < pos { w } else { w - 1 };
                assert(r[w] == e[wo]);
            }
        }
    }
    assert forall|y: Seq<u8>| #[trigger] peer_has_cid(r, y) <==> peer_has_cid(e, y) || y == x.1@ by {
        if peer_has_cid(e, y) {
            let w = choose|w: int| 0 <= w < e.len() && (#[trigger] e[w]).1@ == y;
            let wn = if w < pos { w } else { w + 1 };
            assert(r[wn] == e[w]);
        }
        if y == x.1@ {
            assert(r[pos].1@ == y);
        }
        if peer_has_cid(r, y) {
            let w = choose|w: int| 0 <= w < r.len() && (#[trigger] r[w]).1@ == y;
            if w != pos {
                let wo = if w < pos { w } else { w - 1 };
                assert(r[w] == e[wo]);
            }
        }
    }
    assert forall|s: u64| #[trigger] peer_used(r, s) <==> peer_used(e, s) by {
        if peer_used(e, s) {
            let w = choose|w: int| 0 <= w < e.len() && (#[trigger] e[w]).0 == s && e[w].3;
            let wn = if w < pos { w } else { w + 1 };
            assert(r[wn] == e[w]);
        }
        if peer_used(r, s) {
            let w = choose|w: int| 0 <= w < r.len() && (#[trigger] r[w]).0 == s && r[w].3;
            assert(w != pos);
            let wo = if w < pos { w } else { w - 1 };
            assert(r[w] == e[wo]);
        }
    }
}

/// Marking entry `i` of `a` used (`b`) keeps `wf_parts`.
proof fn lemma_mark_parts(a: PeerCids, b: PeerCids, i: int)
    requires
        a.wf_parts(),
        0 <= i < a.active@.len(),
        b.active@ == a.active@.update(i, (a.active@[i].0, a.active@[i].1, a.active@[i].2, true)),
        b.largest_rpt == a.largest_rpt,
        b.retire_pending == a.retire_pending,
        b.retire_unacked == a.retire_unacked,
        b.received == a.received,
        b.acked == a.acked,
    ensures
        b.wf_parts(),
{
    lemma_update_used(a.active@, i, a.largest_rpt);
    lemma_used_after_mark(a.active@, i);
    let e = b.active@;
    assert forall|x: u64| x < b.largest_rpt implies #[trigger] b.retired(x) by {
        assert(a.retired(x));
    }
    assert forall|j: int| 0 <= j < e.len() implies b.received@.dom().contains((#[trigger] e[j]).0)
        && b.received@[e[j].0] == (e[j].1@, e[j].2) by {
        assert(e[j].0 == a.active@[j].0 && e[j].1 == a.active@[j].1 && e[j].2 == a.active@[j].2);
    }
}

/// Marking entry `i` used keeps the sorted, distinct and shape invariants.
proof fn lemma_update_used(e: Seq<PeerEntry>, i: int, lrpt: u64)
    requires
        0 <= i < e.len(),
    ensures
        peer_sorted(e) ==> peer_sorted(e.update(i, (e[i].0, e[i].1, e[i].2, true))),
        peer_distinct(e) ==> peer_distinct(e.update(i, (e[i].0, e[i].1, e[i].2, true))),
        peer_shape(e, lrpt) ==> peer_shape(e.update(i, (e[i].0, e[i].1, e[i].2, true)), lrpt),
        forall|j: int|
            0 <= j < e.len() ==> (#[trigger] e.update(i, (e[i].0, e[i].1, e[i].2, true))[j]).0
                == e[j].0 && e.update(i, (e[i].0, e[i].1, e[i].2, true))[j].1 == e[j].1 && e.update(
                i,
                (e[i].0, e[i].1, e[i].2, true),
            )[j].2 == e[j].2,
{
    let r = e.update(i, (e[i].0, e[i].1, e[i].2, true));
    assert forall|j: int| 0 <= j < e.len() implies (#[trigger] r[j]).0 == e[j].0 && r[j].1
        == e[j].1 && r[j].2 == e[j].2 by {}
}

/// After marking entry `i` used: the same sequence numbers and CIDs, and exactly one more
/// used sequence number.
proof fn lemma_used_after_mark(e: Seq<PeerEntry>, i: int)
    requires
        0 <= i < e.len(),
    ensures
        forall|s: u64| #[trigger]
            peer_has_seq(e.update(i, (e[i].0, e[i].1, e[i].2, true)), s) <==> peer_has_seq(e, s),
        forall|c: Seq<u8>| #[trigger]
            peer_has_cid(e.update(i, (e[i].0, e[i].1, e[i].2, true)), c) <==> peer_has_cid(e, c),
        forall|s: u64| #[trigger]
            peer_used(e.update(i, (e[i].0, e[i].1, e[i].2, true)), s) <==> peer_used(e, s) || s
                == e[i].0,
{
    let r = e.update(i, (e[i].0, e[i].1, e[i].2, true));
    assert forall|s: u64| #[trigger] peer_has_seq(r, s) <==> peer_has_seq(e, s) by {
        if peer_has_seq(e, s) {
            let w = choose|w: int| 0 <= w < e.len() && (#[trigger] e[w]).0 == s;
            assert(r[w].0 == s);
        }
        if peer_has_seq(r, s) {
            let w = choose|w: int| 0 <= w < r.len() && (#[trigger] r[w]).0 == s;
            assert(e[w].0 == s);
        }
    }
    assert forall|c: Seq<u8>| #[trigger] peer_has_cid(r, c) <==> peer_has_cid(e, c) by {
        if peer_has_cid(e, c) {
            let w = choose|w: int| 0 <= w < e.len() && (#[trigger] e[w]).1@ == c;
            assert(r[w].1 == e[w].1);
        }
        if peer_has_cid(r, c) {
            let w = choose|w: int| 0 <= w < r.len() && (#[trigger] r[w]).1@ == c;
            assert(r[w].1 == e[w].1);
        }
    }
    assert forall|s: u64| #[trigger] peer_used(r, s) <==> peer_used(e, s) || s == e[i].0 by {
        if peer_used(e, s) {
            let w = choose|w: int| 0 <= w < e.len() && (#[trigger] e[w]).0 == s && e[w].3;
            assert(r[w].0 == s && r[w].3);
        }
        if s == e[i].0 {
            assert(r[i].0 == s && r[i].3);
        }
        if peer_used(r, s) && s != e[i].0 {
            let w = choose|w: int| 0 <= w < r.len() && (#[trigger] r[w]).0 == s && r[w].3;
            assert(w != i);
            assert(r[w] == e[w]);
        }
    }
}

// =============================================================================
// Byte helpers
// =============================================================================

fn eq_bytes(a: &[u8], b: &[u8]) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    if a.len() != b.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a@.len(),
            a@.len() == b@.len(),
            forall|k: int| 0 <= k < i ==> a@[k] == b@[k],
        decreases a@.len() - i,
    {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    assert(a@ =~= b@);
    true
}

proof fn lemma_or_xor(acc: u8, x: u8, y: u8)
    ensures
        ((acc | (x ^ y)) == 0) <==> (acc == 0 && x == y),
{
    assert(((acc | (x ^ y)) == 0) <==> (acc == 0 && x == y)) by (bit_vector);
}

/// Constant-time style: every byte is read, no early exit (TRUSTED.md: the timing is unproven).
fn ct_eq16(a: &[u8; 16], b: &[u8; 16]) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    let mut acc: u8 = 0;
    let mut i: usize = 0;
    while i < 16
        invariant
            i <= 16,
            a@.len() == 16,
            b@.len() == 16,
            (acc == 0) <==> (forall|j: int| 0 <= j < i ==> a@[j] == b@[j]),
        decreases 16 - i,
    {
        proof {
            lemma_or_xor(acc, a@[i as int], b@[i as int]);
        }
        acc = acc | (a[i] ^ b[i]);
        i += 1;
    }
    if acc == 0 {
        assert(a@ =~= b@);
    } else {
        let ghost j = choose|j: int| 0 <= j < 16 && a@[j] != b@[j];
        assert(a@[j] != b@[j]);
    }
    acc == 0
}

fn contains_u64(v: &Vec<u64>, x: u64) -> (r: bool)
    ensures
        r == v@.contains(x),
{
    index_of_u64(v, x).is_some()
}

fn index_of_u64(v: &Vec<u64>, x: u64) -> (r: Option<usize>)
    ensures
        r matches Some(i) ==> i < v@.len() && v@[i as int] == x,
        r is None ==> !v@.contains(x),
        (r is Some) == v@.contains(x),
{
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v@.len(),
            forall|j: int| 0 <= j < i ==> v@[j] != x,
        decreases v@.len() - i,
    {
        if v[i] == x {
            return Some(i);
        }
        i += 1;
    }
    None
}

} // verus!
const _: () = assert!(LOCAL_CID_LEN >= 1);

impl PeerCids {
    /// Test support: the retire lists' allocated capacity. Verus models `Vec` length, not
    /// capacity, so the allocation bound is checked by test only (TRUSTED.md).
    #[doc(hidden)]
    pub fn retire_capacity(&self) -> usize {
        self.retire_pending.capacity() + self.retire_unacked.capacity()
    }
}
