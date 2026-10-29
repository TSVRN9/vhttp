//! QUIC stream IDs (RFC 9000 §2.1, §4.6, §19.11): stream types, the peer's implicitly opened
//! streams against the limit we sent, and our own unidirectional streams against the peer's.
use vstd::prelude::*;
// Used only in ghost code, which a plain `cargo build` erases.
#[allow(unused_imports)]
use wire::varint::*;

use crate::codes::*;
use crate::flow::*;

verus! {

/// Stream types by the two low bits of the ID (RFC 9000 Table 1).
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum StreamKind {
    ClientBidi,
    ServerBidi,
    ClientUni,
    ServerUni,
}

pub open spec fn spec_stream_kind(id: u64) -> StreamKind {
    if id % 4 == 0 {
        StreamKind::ClientBidi
    } else if id % 4 == 1 {
        StreamKind::ServerBidi
    } else if id % 4 == 2 {
        StreamKind::ClientUni
    } else {
        StreamKind::ServerUni
    }
}

pub fn stream_kind(id: u64) -> (r: StreamKind)
    ensures
        r == spec_stream_kind(id),
{
    if id % 4 == 0 {
        StreamKind::ClientBidi
    } else if id % 4 == 1 {
        StreamKind::ServerBidi
    } else if id % 4 == 2 {
        StreamKind::ClientUni
    } else {
        StreamKind::ServerUni
    }
}

/// §4.6's "stream ID less than max_streams * 4 + first_stream_id_of_type", for an `id` of that
/// type, written without the multiplication.
pub open spec fn peer_id_allowed(id: u64, max_streams: u64) -> bool {
    id / 4 < max_streams
}

/// What a peer stream ID did: name a stream already open, or open `count` new streams of its
/// type, the lowest being `first`.
#[derive(Debug, PartialEq, Eq)]
pub enum Opened {
    Existing,
    New { first: u64, count: u64 },
}

/// Stream-ID accounting. Peer streams: `peer_*_next` counts those opened, and each credit's
/// `consumed` counts those closed (MAX_STREAMS). Ours: unidirectional only, `local_uni.used`
/// counts those opened.
pub struct StreamIds {
    peer_bidi_next: u64,
    peer_uni_next: u64,
    peer_bidi: RecvCredit,
    peer_uni: RecvCredit,
    local_uni: SendCredit,
}

impl StreamIds {
    pub closed spec fn wf(&self) -> bool {
        &&& self.peer_bidi.wf()
        &&& self.peer_uni.wf()
        &&& self.local_uni.wf()
        &&& self.peer_bidi.cap_spec() == MAX_STREAMS_LIMIT
        &&& self.peer_uni.cap_spec() == MAX_STREAMS_LIMIT
        &&& self.peer_bidi.consumed_spec() <= self.peer_bidi_next <= self.peer_bidi.limit_spec()
        &&& self.peer_uni.consumed_spec() <= self.peer_uni_next <= self.peer_uni.limit_spec()
        &&& self.local_uni.max_spec() <= MAX_STREAMS_LIMIT
    }

    /// The per-direction part of the invariant that `lemma_wf` exports.
    pub open spec fn peer_side_ok(&self, b: bool) -> bool {
        let c = self.peer_credit_spec(b);
        &&& c.wf()
        &&& c.cap_spec() == MAX_STREAMS_LIMIT
        &&& c.consumed_spec() <= self.peer_opened_spec(b) <= self.peer_limit_spec(b)
        &&& self.peer_limit_spec(b) == c.limit_spec()
        &&& self.peer_limit_spec(b) <= c.consumed_spec() + c.window_spec()
        &&& self.pending_max_streams_spec(b) == c.pending_spec()
        &&& self.peer_limit_spec(b) <= MAX_STREAMS_LIMIT
        &&& self.pending_max_streams_spec(b) matches Some(v) ==> self.peer_limit_spec(b) <= v
            <= MAX_STREAMS_LIMIT && v <= c.consumed_spec() + c.window_spec()
    }

    /// How many peer streams of this direction are open or were.
    pub closed spec fn peer_opened_spec(&self, bidi: bool) -> u64 {
        if bidi {
            self.peer_bidi_next
        } else {
            self.peer_uni_next
        }
    }

    /// The MAX_STREAMS credit for peer streams of this direction (`consumed` = closed).
    pub closed spec fn peer_credit_spec(&self, bidi: bool) -> RecvCredit {
        if bidi {
            self.peer_bidi
        } else {
            self.peer_uni
        }
    }

    /// The peer's limit on our unidirectional streams (`used` = opened).
    pub closed spec fn local_uni_spec(&self) -> SendCredit {
        self.local_uni
    }

    pub closed spec fn peer_created_spec(&self, id: u64) -> bool {
        if id % 4 == 0 {
            id / 4 < self.peer_bidi_next
        } else if id % 4 == 2 {
            id / 4 < self.peer_uni_next
        } else {
            false
        }
    }

    pub closed spec fn peer_limit_spec(&self, bidi: bool) -> u64 {
        self.peer_credit_spec(bidi).limit_spec()
    }

    pub closed spec fn pending_max_streams_spec(&self, bidi: bool) -> Option<u64> {
        self.peer_credit_spec(bidi).pending_spec()
    }

    pub closed spec fn local_uni_created_spec(&self, id: u64) -> bool {
        id % 4 == 3 && id / 4 < self.local_uni.used_spec()
    }

    pub closed spec fn local_uni_limit_spec(&self) -> u64 {
        self.local_uni.max_spec()
    }

    /// The invariant and the derived accessors, in terms of the primitive ones.
    pub proof fn lemma_wf(&self)
        requires
            self.wf(),
        ensures
            self.peer_side_ok(true),
            self.peer_side_ok(false),
            self.local_uni_spec().wf(),
            self.local_uni_limit_spec() == self.local_uni_spec().max_spec(),
            self.local_uni_limit_spec() <= MAX_STREAMS_LIMIT,
            self.local_uni_spec().used_spec() <= self.local_uni_limit_spec(),
            forall|id: u64| #[trigger]
                self.peer_created_spec(id) == (if id % 4 == 0 {
                    id / 4 < self.peer_opened_spec(true)
                } else if id % 4 == 2 {
                    id / 4 < self.peer_opened_spec(false)
                } else {
                    false
                }),
            forall|id: u64| #[trigger]
                self.local_uni_created_spec(id) == (id % 4 == 3 && id / 4
                    < self.local_uni_spec().used_spec()),
    {
        self.peer_bidi.lemma_wf();
        self.peer_uni.lemma_wf();
        self.local_uni.lemma_wf();
    }

    /// `local_max_*`: the stream limits we advertise in our transport parameters.
    /// `peer_max_uni`: the peer's `initial_max_streams_uni`.
    pub fn new(local_max_bidi: u64, local_max_uni: u64, peer_max_uni: u64) -> (r: StreamIds)
        requires
            local_max_bidi <= MAX_STREAMS_LIMIT,
            local_max_uni <= MAX_STREAMS_LIMIT,
            peer_max_uni <= MAX_STREAMS_LIMIT,
        ensures
            r.wf(),
            forall|b: bool| #[trigger] r.peer_opened_spec(b) == 0,
            r.peer_limit(true) == local_max_bidi,
            r.peer_limit(false) == local_max_uni,
            forall|b: bool|
                {
                    &&& #[trigger] r.peer_credit_spec(b).consumed_spec() == 0
                    &&& r.peer_credit_spec(b).pending_spec() is None
                    &&& r.peer_credit_spec(b).window_spec() == r.peer_limit(b)
                },
            r.local_uni_limit() == peer_max_uni,
            r.local_uni_spec().used_spec() == 0,
    {
        assert(MAX_STREAMS_LIMIT <= VARINT_MAX) by (compute_only);
        StreamIds {
            peer_bidi_next: 0,
            peer_uni_next: 0,
            peer_bidi: RecvCredit::new(local_max_bidi, MAX_STREAMS_LIMIT),
            peer_uni: RecvCredit::new(local_max_uni, MAX_STREAMS_LIMIT),
            local_uni: SendCredit::new(peer_max_uni),
        }
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-4.6
    //# An endpoint
    //# that receives a frame with a stream ID exceeding the limit it has
    //# sent MUST treat this as a connection error of type
    //# STREAM_LIMIT_ERROR; see Section 11 for details on error handling.
    //
    //= https://www.rfc-editor.org/rfc/rfc9000#section-19.11
    //# An endpoint MUST terminate a connection
    //# with an error of type STREAM_LIMIT_ERROR if a peer opens more streams
    //# than was permitted.
    /// A frame named peer stream `id`. Opening it opens every lower ID of its type (§3.2).
    pub fn on_peer_stream(&mut self, id: u64) -> (r: Result<Opened, u64>)
        requires
            old(self).wf(),
            id <= VARINT_MAX,
            spec_stream_kind(id) is ClientBidi || spec_stream_kind(id) is ClientUni,
        ensures
            final(self).wf(),
            r is Err <==> !peer_id_allowed(id, old(self).peer_limit(id % 4 == 0)),
            r matches Err(e) ==> e == STREAM_LIMIT_ERROR && *final(self) == *old(self),
            r matches Ok(Opened::Existing) ==> id / 4 < old(self).peer_opened_spec(id % 4 == 0)
                && *final(self) == *old(self),
            r matches Ok(Opened::New { first, count }) ==> {
                let b = id % 4 == 0;
                let n = old(self).peer_opened_spec(b);
                &&& n <= id / 4
                &&& first == 4 * n + id % 4
                &&& count == id / 4 + 1 - n
                &&& final(self).peer_opened_spec(b) == id / 4 + 1
                &&& final(self).peer_opened_spec(!b) == old(self).peer_opened_spec(!b)
                &&& forall|c: bool| #[trigger]
                    final(self).peer_credit_spec(c) == old(self).peer_credit_spec(c)
                &&& final(self).local_uni_spec() == old(self).local_uni_spec()
                &&& forall|x: u64|
                    x % 4 == id % 4 && first <= x <= id ==> #[trigger] final(self).peer_created(x)
            },
    {
        let bidi = id % 4 == 0;
        let q = id / 4;
        let (next, limit) = if bidi {
            (self.peer_bidi_next, self.peer_bidi.limit())
        } else {
            (self.peer_uni_next, self.peer_uni.limit())
        };
        if q >= limit {
            return Err(STREAM_LIMIT_ERROR);
        }
        if q < next {
            return Ok(Opened::Existing);
        }
        if bidi {
            self.peer_bidi_next = q + 1;
        } else {
            self.peer_uni_next = q + 1;
        }
        Ok(Opened::New { first: 4 * next + id % 4, count: q + 1 - next })
    }

    /// How many peer streams of this direction are open or were.
    pub fn peer_opened(&self, bidi: bool) -> (r: u64)
        ensures
            r == self.peer_opened_spec(bidi),
    {
        if bidi {
            self.peer_bidi_next
        } else {
            self.peer_uni_next
        }
    }

    #[verifier::when_used_as_spec(peer_created_spec)]
    pub fn peer_created(&self, id: u64) -> (r: bool)
        ensures
            r == self.peer_created_spec(id),
    {
        if id % 4 == 0 {
            id / 4 < self.peer_bidi_next
        } else if id % 4 == 2 {
            id / 4 < self.peer_uni_next
        } else {
            false
        }
    }

    /// The MAX_STREAMS value for this direction as sent: the limit enforced on the peer.
    #[verifier::when_used_as_spec(peer_limit_spec)]
    pub fn peer_limit(&self, bidi: bool) -> (r: u64)
        ensures
            r == self.peer_limit_spec(bidi),
    {
        if bidi {
            self.peer_bidi.limit()
        } else {
            self.peer_uni.limit()
        }
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-4.6
    //# An endpoint MUST NOT wait
    //# to receive this signal before advertising additional credit, since
    //# doing so will mean that the peer will be blocked for at least an
    //# entire round trip, and potentially indefinitely if the peer chooses
    //# not to send STREAMS_BLOCKED frames.
    /// A peer stream of this direction closed; the MAX_STREAMS update depends on closures alone.
    pub fn on_peer_closed(&mut self, bidi: bool)
        requires
            old(self).wf(),
            old(self).peer_credit_spec(bidi).consumed_spec() < old(self).peer_opened_spec(bidi),
        ensures
            final(self).wf(),
            forall|b: bool| #[trigger]
                final(self).peer_opened_spec(b) == old(self).peer_opened_spec(b),
            final(self).peer_credit_spec(!bidi) == old(self).peer_credit_spec(!bidi),
            final(self).local_uni_spec() == old(self).local_uni_spec(),
            ({
                let c0 = old(self).peer_credit_spec(bidi);
                let c1 = final(self).peer_credit_spec(bidi);
                &&& c1.consumed_spec() == c0.consumed_spec() + 1
                &&& c1.limit_spec() == c0.limit_spec()
                &&& c1.window_spec() == c0.window_spec()
                &&& c1.cap_spec() == c0.cap_spec()
                &&& c1.pending_spec() == credit_after(
                    c0.limit_spec(),
                    c1.consumed_spec(),
                    c0.window_spec(),
                    c0.cap_spec(),
                    c0.pending_spec(),
                )
            }),
    {
        if bidi {
            self.peer_bidi.on_consumed(1);
        } else {
            self.peer_uni.on_consumed(1);
        }
    }

    #[verifier::when_used_as_spec(pending_max_streams_spec)]
    pub fn pending_max_streams(&self, bidi: bool) -> (r: Option<u64>)
        ensures
            r == self.pending_max_streams_spec(bidi),
            self.wf() ==> (r matches Some(v) ==> v <= MAX_STREAMS_LIMIT),
    {
        proof {
            if self.wf() {
                self.lemma_wf();
            }
        }
        if bidi {
            self.peer_bidi.pending()
        } else {
            self.peer_uni.pending()
        }
    }

    /// The pending MAX_STREAMS was sent: it becomes the enforced limit.
    pub fn commit_max_streams(&mut self, bidi: bool)
        requires
            old(self).wf(),
            old(self).pending_max_streams(bidi) is Some,
        ensures
            final(self).wf(),
            final(self).peer_limit(bidi) == old(self).pending_max_streams(bidi)->0,
            final(self).pending_max_streams(bidi) is None,
            forall|b: bool| #[trigger]
                final(self).peer_opened_spec(b) == old(self).peer_opened_spec(b),
            final(self).peer_credit_spec(!bidi) == old(self).peer_credit_spec(!bidi),
            final(self).local_uni_spec() == old(self).local_uni_spec(),
            ({
                let c0 = old(self).peer_credit_spec(bidi);
                let c1 = final(self).peer_credit_spec(bidi);
                &&& c1.consumed_spec() == c0.consumed_spec()
                &&& c1.window_spec() == c0.window_spec()
                &&& c1.cap_spec() == c0.cap_spec()
            }),
    {
        proof {
            self.peer_bidi.lemma_wf();
            self.peer_uni.lemma_wf();
        }
        if bidi {
            self.peer_bidi.commit();
        } else {
            self.peer_uni.commit();
        }
    }

    /// The frame carrying this direction's MAX_STREAMS was lost: send the current value again.
    pub fn max_streams_lost(&mut self, bidi: bool)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).pending_max_streams(bidi) == Some(
                credit_resend(old(self).pending_max_streams(bidi), old(self).peer_limit(bidi)),
            ),
            forall|b: bool| #[trigger]
                final(self).peer_opened_spec(b) == old(self).peer_opened_spec(b),
            final(self).peer_credit_spec(!bidi) == old(self).peer_credit_spec(!bidi),
            final(self).local_uni_spec() == old(self).local_uni_spec(),
            ({
                let c0 = old(self).peer_credit_spec(bidi);
                let c1 = final(self).peer_credit_spec(bidi);
                &&& c1.limit_spec() == c0.limit_spec()
                &&& c1.consumed_spec() == c0.consumed_spec()
                &&& c1.window_spec() == c0.window_spec()
                &&& c1.cap_spec() == c0.cap_spec()
            }),
    {
        if bidi {
            self.peer_bidi.on_lost();
        } else {
            self.peer_uni.on_lost();
        }
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-2.1
    //# A QUIC
    //# endpoint MUST NOT reuse a stream ID within a connection.
    //
    //= https://www.rfc-editor.org/rfc/rfc9000#section-4.6
    //# Endpoints MUST NOT exceed the limit set by their peer.
    //
    //= https://www.rfc-editor.org/rfc/rfc9000#section-19.11
    //# An endpoint MUST NOT open more streams than permitted by the current
    //# stream limit set by its peer.
    /// Opens our next unidirectional stream, which must be `id`, if the peer's limit allows.
    pub fn open_local_uni(&mut self, id: u64) -> (ok: bool)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            ok == (id == 4 * old(self).local_uni_spec().used_spec() + 3
                && old(self).local_uni_spec().available_spec() > 0),
            ok ==> final(self).local_uni_spec().used_spec() == old(self).local_uni_spec().used_spec()
                + 1 && final(self).local_uni_limit() == old(self).local_uni_limit(),
            !ok ==> *final(self) == *old(self),
            ok ==> !old(self).local_uni_created(id) && final(self).local_uni_created(id),
            forall|x: u64| #[trigger]
                old(self).local_uni_created(x) ==> final(self).local_uni_created(x),
            forall|b: bool|
                {
                    &&& #[trigger] final(self).peer_opened_spec(b) == old(self).peer_opened_spec(b)
                    &&& final(self).peer_credit_spec(b) == old(self).peer_credit_spec(b)
                },
    {
        proof {
            self.local_uni.lemma_wf();
        }
        if id % 4 == 3 && id / 4 == self.local_uni.used() && self.local_uni.available() > 0 {
            self.local_uni.consume(1);
            true
        } else {
            false
        }
    }

    #[verifier::when_used_as_spec(local_uni_created_spec)]
    pub fn local_uni_created(&self, id: u64) -> (r: bool)
        ensures
            r == self.local_uni_created_spec(id),
    {
        id % 4 == 3 && id / 4 < self.local_uni.used()
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-4.6
    //# MAX_STREAMS frames
    //# that do not increase the stream limit MUST be ignored.
    //
    //= https://www.rfc-editor.org/rfc/rfc9000#section-19.11
    //# MAX_STREAMS frames that do not increase the stream limit MUST be
    //# ignored.
    /// The peer's MAX_STREAMS. We never open bidirectional streams, so that limit is ignored.
    pub fn on_max_streams(&mut self, bidi: bool, max: u64)
        requires
            old(self).wf(),
            !bidi ==> max <= MAX_STREAMS_LIMIT,
        ensures
            final(self).wf(),
            bidi ==> *final(self) == *old(self),
            !bidi ==> final(self).local_uni_limit() == if max > old(self).local_uni_limit() {
                max
            } else {
                old(self).local_uni_limit()
            },
            final(self).local_uni_spec().used_spec() == old(self).local_uni_spec().used_spec(),
            forall|b: bool|
                {
                    &&& #[trigger] final(self).peer_opened_spec(b) == old(self).peer_opened_spec(b)
                    &&& final(self).peer_credit_spec(b) == old(self).peer_credit_spec(b)
                },
    {
        if !bidi {
            self.local_uni.on_max(max);
        }
    }

    #[verifier::when_used_as_spec(local_uni_limit_spec)]
    pub fn local_uni_limit(&self) -> (r: u64)
        ensures
            r == self.local_uni_limit_spec(),
    {
        self.local_uni.max()
    }
}

} // verus!
