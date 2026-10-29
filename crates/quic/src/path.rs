//! The path table (RFC 9000 §8.2, §9): per-path amplification budgets, the PATH_CHALLENGE
//! we send on a path and the PATH_RESPONSEs we owe on it. Sans-IO: the shell supplies the
//! challenge data (randomness) and times; 3d2 builds and sends the frames.
use vstd::prelude::*;
use vstd::slice::slice_to_vec;

use crate::amp::*;
#[allow(unused_imports)]
use crate::codes::*;
use crate::datagram::PathId;
use crate::lifecycle::*;

verus! {

// ponytail: paths never evicted; datagrams from a 5th distinct path are dropped uncounted; evict a
// non-active unvalidated path when long-lived rebinding matters.
pub const MAX_PATHS: usize = 4;

/// Responses owed per path; further challenges are dropped until responses go out (the peer
/// retransmits, §8.2.1 MAY).
pub const MAX_RESPONSES: usize = 4;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum PathState {
    Unvalidated,
    Validating,
    Validated,
}

/// One network path.
pub struct Path {
    id: PathId,
    amp: AmpBudget,
    state: PathState,
    /// Our outstanding PATH_CHALLENGE: data, the time `start_challenge` ran, and whether the
    /// datagram carrying it reached 1200 bytes.
    challenge: Option<([u8; 8], u64, bool)>,
    /// Started but not yet sent.
    challenge_owed: bool,
    /// A challenge in a datagram of at least 1200 bytes was answered.
    mtu_ok: bool,
    /// PATH_RESPONSE data owed, oldest first.
    responses: Vec<[u8; 8]>,
    /// The peer CID we send with on this path; None: nothing may be sent there (§9.5).
    dcid: Option<Vec<u8>>,
    /// Our CID the peer last used on this path.
    peer_used: Option<Vec<u8>>,
    challenges_rcvd: Ghost<Seq<[u8; 8]>>,
    responses_taken: Ghost<Seq<[u8; 8]>>,
}

pub struct SpecPath {
    pub id: PathId,
    pub state: PathState,
    pub amp_trace: Seq<AmpEv>,
    pub budget: u64,
    pub challenge: Option<([u8; 8], u64, bool)>,
    pub owed: bool,
    pub mtu_ok: bool,
    pub responses: Seq<[u8; 8]>,
    pub dcid: Option<Seq<u8>>,
    pub peer_used: Option<Seq<u8>>,
    /// Every PATH_CHALLENGE data received on the path, in order.
    pub challenges_rcvd: Seq<[u8; 8]>,
    /// Every PATH_RESPONSE data handed out by `take_response`, in order.
    pub responses_taken: Seq<[u8; 8]>,
}

pub open spec fn opt_view(o: Option<Vec<u8>>) -> Option<Seq<u8>> {
    match o {
        Some(v) => Some(v@),
        None => None,
    }
}

pub open spec fn opt_slice_view(o: Option<&[u8]>) -> Option<Seq<u8>> {
    match o {
        Some(v) => Some(v@),
        None => None,
    }
}

impl View for Path {
    type V = SpecPath;

    closed spec fn view(&self) -> SpecPath {
        SpecPath {
            id: self.id,
            state: self.state,
            amp_trace: self.amp.trace(),
            budget: self.amp.budget_spec(),
            challenge: self.challenge,
            owed: self.challenge_owed,
            mtu_ok: self.mtu_ok,
            responses: self.responses@,
            dcid: opt_view(self.dcid),
            peer_used: opt_view(self.peer_used),
            challenges_rcvd: self.challenges_rcvd@,
            responses_taken: self.responses_taken@,
        }
    }
}

/// `a` is `b` with some elements left out, in order: `f` maps each element of `a` to its
/// position in `b`, strictly increasing.
pub open spec fn subseq_at<A>(a: Seq<A>, b: Seq<A>, f: Seq<int>) -> bool {
    &&& f.len() == a.len()
    &&& forall|k: int| 0 <= k < f.len() ==> 0 <= #[trigger] f[k] < b.len() && b[f[k]] == a[k]
    &&& forall|j: int, k: int| 0 <= j < k < f.len() ==> #[trigger] f[j] < #[trigger] f[k]
}

pub open spec fn is_subseq<A>(a: Seq<A>, b: Seq<A>) -> bool {
    exists|f: Seq<int>| #[trigger] subseq_at(a, b, f)
}

proof fn lemma_subseq_push_both<A>(a: Seq<A>, b: Seq<A>, x: A)
    requires
        is_subseq(a, b),
    ensures
        is_subseq(a.push(x), b.push(x)),
{
    let f = choose|f: Seq<int>| subseq_at(a, b, f);
    let g = f.push(b.len() as int);
    assert(subseq_at(a.push(x), b.push(x), g));
}

proof fn lemma_subseq_push_right<A>(a: Seq<A>, b: Seq<A>, x: A)
    requires
        is_subseq(a, b),
    ensures
        is_subseq(a, b.push(x)),
{
    let f = choose|f: Seq<int>| subseq_at(a, b, f);
    assert(subseq_at(a, b.push(x), f));
}

proof fn lemma_subseq_prefix<A>(a: Seq<A>, c: Seq<A>, b: Seq<A>)
    requires
        is_subseq(a + c, b),
    ensures
        is_subseq(a, b),
{
    let f = choose|f: Seq<int>| subseq_at(a + c, b, f);
    let g = f.take(a.len() as int);
    assert forall|k: int| 0 <= k < g.len() implies 0 <= #[trigger] g[k] < b.len() && b[g[k]]
        == a[k] by {
        assert(f[k] == g[k]);
        assert((a + c)[k] == a[k]);
    }
    assert forall|j: int, k: int| 0 <= j < k < g.len() implies #[trigger] g[j] < #[trigger] g[k] by {
        assert(f[j] < f[k]);
    }
    assert(subseq_at(a, b, g));
}

/// The path's state after a fresh `insert`.
pub open spec fn fresh_path(id: PathId) -> SpecPath {
    SpecPath {
        id,
        state: PathState::Unvalidated,
        amp_trace: Seq::empty(),
        budget: 0,
        challenge: None,
        owed: false,
        mtu_ok: false,
        responses: Seq::empty(),
        dcid: None,
        peer_used: None,
        challenges_rcvd: Seq::empty(),
        responses_taken: Seq::empty(),
    }
}

/// A sent challenge, waiting for its response or its timeout.
pub open spec fn timed(p: SpecPath) -> bool {
    p.challenge is Some && !p.owed
}

/// When a sent challenge is abandoned: `3·pto_us` after it started (§8.2.4), saturating.
pub open spec fn expiry(p: SpecPath, pto_us: u64) -> u64 {
    spec_sat_add(p.challenge.unwrap().1, spec_sat3(pto_us))
}

pub open spec fn expired(p: SpecPath, now: u64, pto_us: u64) -> bool {
    timed(p) && now >= expiry(p, pto_us)
}

/// `data` answers the path's sent challenge.
pub open spec fn answers(p: SpecPath, data: [u8; 8]) -> bool {
    p.challenge matches Some((d, _, _)) && d == data && !p.owed
}

pub open spec fn path_ok(p: SpecPath) -> bool {
    &&& amp_ok(p.amp_trace)
    &&& p.responses.len() <= MAX_RESPONSES
    &&& is_subseq(p.responses_taken + p.responses, p.challenges_rcvd)
    &&& (p.state is Validated) == validated_in(p.amp_trace)
    &&& p.owed ==> p.challenge is Some
    &&& p.state is Unvalidated ==> p.challenge is None
    &&& p.state is Validating ==> p.challenge is Some
    &&& p.dcid matches Some(c) ==> c.len() <= MAX_CID_LEN
    &&& p.peer_used matches Some(c) ==> c.len() <= MAX_CID_LEN
}

spec fn path_wf(p: Path) -> bool {
    p.amp.wf() && path_ok(p@)
}

spec fn tcount(s: Seq<Path>) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        tcount(s.drop_last()) + if timed(s.last()@) {
            1nat
        } else {
            0
        }
    }
}

proof fn lemma_tcount_update(s: Seq<Path>, i: int, p: Path)
    requires
        0 <= i < s.len(),
        timed(s[i]@),
        !timed(p@),
    ensures
        tcount(s.update(i, p)) + 1 == tcount(s),
    decreases s.len(),
{
    let u = s.update(i, p);
    if i == s.len() - 1 {
        assert(u.drop_last() =~= s.drop_last());
    } else {
        assert(u.drop_last() =~= s.drop_last().update(i, p));
        lemma_tcount_update(s.drop_last(), i, p);
    }
}

/// The paths of one connection. Paths are never removed.
pub struct Paths {
    paths: Vec<Path>,
    active: PathId,
    last_validated: Option<PathId>,
}

/// `b` differs from `a` at most on path `id` and `last_validated`.
pub open spec fn kept(a: Paths, b: Paths, id: PathId) -> bool {
    &&& b.ids() == a.ids()
    &&& b.active_spec() == a.active_spec()
    &&& forall|q: PathId| q != id ==> #[trigger] b.path(q) == a.path(q)
}

impl Paths {
    pub closed spec fn ids(&self) -> Seq<PathId> {
        self.paths@.map_values(|p: Path| p.id)
    }

    pub open spec fn has(&self, id: PathId) -> bool {
        self.ids().contains(id)
    }

    pub open spec fn index_spec(&self, id: PathId) -> Option<usize> {
        if self.has(id) {
            Some((choose|i: int| 0 <= i < self.ids().len() && self.ids()[i] == id) as usize)
        } else {
            None
        }
    }

    /// The path with this id (meaningful when `has(id)`).
    pub closed spec fn path(&self, id: PathId) -> SpecPath {
        match self.index_spec(id) {
            Some(i) => self.paths@[i as int]@,
            None => arbitrary(),
        }
    }

    pub open spec fn amp_trace(&self, id: PathId) -> Seq<AmpEv> {
        self.path(id).amp_trace
    }

    pub open spec fn budget_spec(&self, id: PathId) -> u64 {
        self.path(id).budget
    }

    pub open spec fn state_spec(&self, id: PathId) -> PathState {
        self.path(id).state
    }

    pub closed spec fn active_spec(&self) -> PathId {
        self.active
    }

    pub closed spec fn last_validated_spec(&self) -> Option<PathId> {
        self.last_validated
    }

    /// The number of sent challenges awaiting a response: `on_timeout` lowers it.
    pub closed spec fn timed_count(&self) -> nat {
        tcount(self.paths@)
    }

    pub closed spec fn wf(&self) -> bool {
        &&& self.paths@.len() <= MAX_PATHS
        &&& forall|i: int, j: int|
            0 <= i < self.paths@.len() && 0 <= j < self.paths@.len() && #[trigger] self.paths@[i].id
                == #[trigger] self.paths@[j].id ==> i == j
        &&& forall|i: int| 0 <= i < self.paths@.len() ==> path_wf(#[trigger] self.paths@[i])
        &&& self.has(self.active)
        &&& self.last_validated matches Some(p) ==> self.has(p) && self.path(p).state
            is Validated
    }

    proof fn lemma_index(&self, i: int)
        requires
            self.paths@.len() <= MAX_PATHS,
            forall|i: int, j: int|
                0 <= i < self.paths@.len() && 0 <= j < self.paths@.len() && #[trigger] self.paths@[i].id
                    == #[trigger] self.paths@[j].id ==> i == j,
            0 <= i < self.paths@.len(),
        ensures
            self.has(self.paths@[i].id),
            self.index_spec(self.paths@[i].id) == Some(i as usize),
            self.path(self.paths@[i].id) == self.paths@[i]@,
            self.ids()[i] == self.paths@[i].id,
    {
        let id = self.paths@[i].id;
        let s = self.ids();
        assert(s[i] == id);
        let c = choose|c: int| 0 <= c < s.len() && s[c] == id;
        assert(self.paths@[c].id == id);
    }

    /// Every path in the table is the view of some entry.
    proof fn lemma_has(&self, id: PathId) -> (i: int)
        requires
            self.paths@.len() <= MAX_PATHS,
            forall|i: int, j: int|
                0 <= i < self.paths@.len() && 0 <= j < self.paths@.len() && #[trigger] self.paths@[i].id
                    == #[trigger] self.paths@[j].id ==> i == j,
            self.has(id),
        ensures
            0 <= i < self.paths@.len(),
            self.paths@[i].id == id,
            self.index_spec(id) == Some(i as usize),
            self.path(id) == self.paths@[i]@,
    {
        let i = choose|i: int| 0 <= i < self.ids().len() && self.ids()[i] == id;
        self.lemma_index(i);
        i
    }

    /// The invariant, as the rest of the crate sees it.
    pub proof fn lemma_wf(&self)
        requires
            self.wf(),
        ensures
            self.ids().len() <= MAX_PATHS,
            self.has(self.active_spec()),
            self.last_validated_spec() matches Some(p) ==> self.has(p) && self.path(p).state
                is Validated,
            forall|q: PathId| #[trigger] self.has(q) ==> path_ok(self.path(q)),
            forall|q: PathId| #[trigger] self.has(q) ==> self.path(q).id == q,
            forall|q: PathId|
                #[trigger] self.has(q) ==> is_subseq(
                    self.path(q).responses_taken,
                    self.path(q).challenges_rcvd,
                ),
    {
        assert forall|q: PathId| #[trigger] self.has(q) implies path_ok(self.path(q))
            && self.path(q).id == q && is_subseq(
            self.path(q).responses_taken,
            self.path(q).challenges_rcvd,
        ) by {
            let i = self.lemma_has(q);
            assert(path_wf(self.paths@[i]));
            lemma_subseq_prefix(
                self.path(q).responses_taken,
                self.path(q).responses,
                self.path(q).challenges_rcvd,
            );
        }
    }

    /// Entry `i` of `a` was replaced, keeping its id; `b` keeps the invariant and every other
    /// path.
    proof fn lemma_set(a: Paths, b: Paths, i: int)
        requires
            a.wf(),
            0 <= i < a.paths@.len(),
            b.paths@.len() == a.paths@.len(),
            forall|k: int| 0 <= k < a.paths@.len() && k != i ==> b.paths@[k] == a.paths@[k],
            b.paths@[i].id == a.paths@[i].id,
            path_wf(b.paths@[i]),
            b.active == a.active,
            a.paths@[i].state is Validated ==> b.paths@[i].state is Validated,
            b.last_validated == a.last_validated || (b.last_validated == Some(a.paths@[i].id)
                && b.paths@[i].state is Validated),
        ensures
            b.wf(),
            kept(a, b, a.paths@[i].id),
            a.path(a.paths@[i].id) == a.paths@[i]@,
            b.path(a.paths@[i].id) == b.paths@[i]@,
    {
        let id = a.paths@[i].id;
        assert(b.paths@ =~= a.paths@.update(i, b.paths@[i]));
        assert(b.ids() =~= a.ids());
        a.lemma_index(i);
        b.lemma_index(i);
        assert forall|q: PathId| q != id implies #[trigger] b.path(q) == a.path(q) by {
            if a.has(q) {
                let j = a.lemma_has(q);
                b.lemma_index(j);
            }
        }
        assert forall|k: int| 0 <= k < b.paths@.len() implies path_wf(#[trigger] b.paths@[k]) by {
            if k != i {
                assert(b.paths@[k] == a.paths@[k]);
            }
        }
        if let Some(p) = b.last_validated {
            if p != id {
                assert(b.path(p) == a.path(p));
            }
        }
    }

    /// The entry index of a present path.
    fn find(&self, id: PathId) -> (i: usize)
        requires
            self.wf(),
            self.has(id),
        ensures
            i < self.paths@.len(),
            self.paths@[i as int].id == id,
            self.index_spec(id) == Some(i),
            self.path(id) == self.paths@[i as int]@,
    {
        proof {
            self.lemma_has(id);
        }
        let mut i: usize = 0;
        while i < self.paths.len()
            invariant
                self.wf(),
                self.has(id),
                i <= self.paths@.len(),
                forall|k: int| 0 <= k < i ==> (#[trigger] self.paths@[k]).id != id,
            decreases self.paths@.len() - i,
        {
            if self.paths[i].id == id {
                proof {
                    self.lemma_index(i as int);
                }
                return i;
            }
            i += 1;
        }
        proof {
            let j = self.lemma_has(id);
            assert(self.paths@[j].id == id);
        }
        0
    }

    fn fresh(id: PathId) -> (p: Path)
        ensures
            path_wf(p),
            p.id == id,
            p@ == fresh_path(id),
    {
        let p = Path {
            id,
            amp: AmpBudget::new(),
            state: PathState::Unvalidated,
            challenge: None,
            challenge_owed: false,
            mtu_ok: false,
            responses: Vec::new(),
            dcid: None,
            peer_used: None,
            challenges_rcvd: Ghost(Seq::empty()),
            responses_taken: Ghost(Seq::empty()),
        };
        proof {
            let f = Seq::<int>::empty();
            assert(subseq_at(Seq::<[u8; 8]>::empty() + Seq::<[u8; 8]>::empty(), Seq::empty(), f));
            assert(p@.amp_trace.len() == 0);
            assert(!validated_in(p@.amp_trace));
            assert(p@ =~= fresh_path(id));
        }
        p
    }

    pub fn new(first: PathId) -> (r: Paths)
        ensures
            r.wf(),
            r.ids() == seq![first],
            r.active_spec() == first,
            r.last_validated_spec() is None,
            r.path(first) == fresh_path(first),
    {
        let mut paths = Vec::new();
        paths.push(Paths::fresh(first));
        let r = Paths { paths, active: first, last_validated: None };
        proof {
            assert(r.ids() =~= seq![first]);
            r.lemma_index(0);
        }
        r
    }

    #[verifier::when_used_as_spec(index_spec)]
    pub fn index(&self, id: PathId) -> (r: Option<usize>)
        requires
            self.wf(),
        ensures
            r == self.index_spec(id),
            r is Some <==> self.has(id),
            r matches Some(i) ==> i < self.ids().len() && self.ids()[i as int] == id,
    {
        let mut i: usize = 0;
        while i < self.paths.len()
            invariant
                self.wf(),
                i <= self.paths@.len(),
                forall|k: int| 0 <= k < i ==> (#[trigger] self.paths@[k]).id != id,
            decreases self.paths@.len() - i,
        {
            if self.paths[i].id == id {
                proof {
                    self.lemma_index(i as int);
                }
                return Some(i);
            }
            i += 1;
        }
        proof {
            if self.has(id) {
                let j = self.lemma_has(id);
                assert(self.paths@[j].id == id);
            }
        }
        None
    }

    /// Add a path; false when the table is full.
    pub fn insert(&mut self, id: PathId) -> (ok: bool)
        requires
            old(self).wf(),
            !old(self).has(id),
        ensures
            final(self).wf(),
            ok == (old(self).ids().len() < MAX_PATHS),
            ok ==> {
                &&& final(self).ids() == old(self).ids().push(id)
                &&& final(self).active_spec() == old(self).active_spec()
                &&& final(self).last_validated_spec() == old(self).last_validated_spec()
                &&& final(self).path(id) == fresh_path(id)
                &&& forall|q: PathId| q != id ==> #[trigger] final(self).path(q) == old(self).path(
                    q,
                )
            },
            !ok ==> *final(self) == *old(self),
    {
        if self.paths.len() >= MAX_PATHS {
            return false;
        }
        let ghost a = *self;
        self.paths.push(Paths::fresh(id));
        proof {
            let n = a.paths@.len() as int;
            assert(self.ids() =~= a.ids().push(id));
            assert forall|i: int, j: int|
                0 <= i < self.paths@.len() && 0 <= j < self.paths@.len()
                    && #[trigger] self.paths@[i].id == #[trigger] self.paths@[j].id implies i
                == j by {
                if i < n && j == n {
                    assert(a.ids()[i] == id);
                }
                if j < n && i == n {
                    assert(a.ids()[j] == id);
                }
            }
            self.lemma_index(n);
            assert forall|q: PathId| q != id implies #[trigger] self.path(q) == a.path(q) by {
                if a.has(q) {
                    let j = a.lemma_has(q);
                    self.lemma_index(j);
                } else {
                    assert(!self.has(q));
                }
            }
            let j = a.lemma_has(a.active);
            self.lemma_index(j);
            if let Some(p) = self.last_validated {
                let j = a.lemma_has(p);
                self.lemma_index(j);
            }
            assert forall|k: int| 0 <= k < self.paths@.len() implies path_wf(
                #[trigger] self.paths@[k],
            ) by {
                if k < n {
                    assert(self.paths@[k] == a.paths@[k]);
                }
            }
        }
        true
    }

    /// A datagram of `n` bytes arrived on path `id` (§8.1, per path).
    pub fn on_recv(&mut self, id: PathId, n: u64)
        requires
            old(self).wf(),
            old(self).has(id),
        ensures
            final(self).wf(),
            kept(*old(self), *final(self), id),
            final(self).last_validated_spec() == old(self).last_validated_spec(),
            final(self).path(id) == (SpecPath {
                amp_trace: old(self).path(id).amp_trace.push(AmpEv::Recv(n as nat)),
                budget: final(self).path(id).budget,
                ..old(self).path(id)
            }),
    {
        let i = self.find(id);
        let ghost a = *self;
        self.paths[i].amp.on_recv(n);
        proof {
            let t = a.paths@[i as int].amp.trace();
            assert(t.push(AmpEv::Recv(n as nat)).drop_last() =~= t);
            Paths::lemma_set(a, *self, i as int);
        }
    }

    /// How many bytes may be sent on path `id` now.
    #[verifier::when_used_as_spec(budget_spec)]
    pub fn budget(&self, id: PathId) -> (b: u64)
        requires
            self.wf(),
            self.has(id),
        ensures
            b == self.budget_spec(id),
            !validated_in(self.amp_trace(id)) ==> sent_sum(self.amp_trace(id)) + b <= 3
                * recv_sum(self.amp_trace(id)),
    {
        let i = self.find(id);
        proof {
            assert(path_wf(self.paths@[i as int]));
        }
        self.paths[i].amp.budget()
    }

    /// `n` bytes were sent on path `id`, within its budget.
    pub fn on_sent(&mut self, id: PathId, n: u64)
        requires
            old(self).wf(),
            old(self).has(id),
            n <= old(self).budget_spec(id),
        ensures
            final(self).wf(),
            kept(*old(self), *final(self), id),
            final(self).last_validated_spec() == old(self).last_validated_spec(),
            final(self).path(id) == (SpecPath {
                amp_trace: old(self).path(id).amp_trace.push(AmpEv::Sent(n as nat)),
                budget: final(self).path(id).budget,
                ..old(self).path(id)
            }),
            amp_ok(final(self).amp_trace(id)),
    {
        let i = self.find(id);
        let ghost a = *self;
        proof {
            assert(path_wf(self.paths@[i as int]));
        }
        self.paths[i].amp.on_sent(n);
        proof {
            let t = a.paths@[i as int].amp.trace();
            assert(t.push(AmpEv::Sent(n as nat)).drop_last() =~= t);
            Paths::lemma_set(a, *self, i as int);
        }
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-14.1
    //# Sending UDP datagrams of this size ensures that the network path
    //# supports a reasonable Path Maximum Transmission Unit (PMTU), in both
    //# directions.
    /// The handshake validated path `id` (§8.1). Its MTU is validated too: the Initial
    /// datagrams on it were at least 1200 bytes each way (§14.1). PATH_RESPONSEs validate
    /// through `on_response`.
    pub fn set_validated(&mut self, id: PathId)
        requires
            old(self).wf(),
            old(self).has(id),
        ensures
            final(self).wf(),
            kept(*old(self), *final(self), id),
            final(self).last_validated_spec() == Some(id),
            final(self).path(id) == (SpecPath {
                state: PathState::Validated,
                amp_trace: old(self).path(id).amp_trace.push(AmpEv::Validated),
                budget: final(self).path(id).budget,
                mtu_ok: true,
                ..old(self).path(id)
            }),
    {
        let i = self.find(id);
        let ghost a = *self;
        proof {
            assert(path_wf(self.paths@[i as int]));
        }
        self.paths[i].amp.validate();
        self.paths[i].state = PathState::Validated;
        self.paths[i].mtu_ok = true;
        self.last_validated = Some(id);
        proof {
            let t = a.paths@[i as int].amp.trace();
            assert(t.push(AmpEv::Validated).drop_last() =~= t);
            Paths::lemma_set(a, *self, i as int);
        }
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-19.17
    //# The recipient of this frame MUST generate a PATH_RESPONSE frame
    //# (Section 19.18) containing the same Data value.
    /// A PATH_CHALLENGE with `data` arrived on path `id`: its response is owed, unless
    /// `MAX_RESPONSES` are already owed (then it is dropped; the peer retransmits).
    pub fn on_challenge(&mut self, id: PathId, data: [u8; 8])
        requires
            old(self).wf(),
            old(self).has(id),
        ensures
            final(self).wf(),
            kept(*old(self), *final(self), id),
            final(self).last_validated_spec() == old(self).last_validated_spec(),
            final(self).path(id) == (SpecPath {
                responses: if old(self).path(id).responses.len() < MAX_RESPONSES {
                    old(self).path(id).responses.push(data)
                } else {
                    old(self).path(id).responses
                },
                challenges_rcvd: old(self).path(id).challenges_rcvd.push(data),
                ..old(self).path(id)
            }),
    {
        let i = self.find(id);
        let ghost a = *self;
        proof {
            assert(path_wf(self.paths@[i as int]));
        }
        let ghost t = self.paths[i as int].responses_taken@;
        let ghost r = self.paths[i as int].responses@;
        let ghost c = self.paths[i as int].challenges_rcvd@;
        if self.paths[i].responses.len() < MAX_RESPONSES {
            self.paths[i].responses.push(data);
            proof {
                lemma_subseq_push_both(t + r, c, data);
                assert(t + r.push(data) =~= (t + r).push(data));
            }
        } else {
            proof {
                lemma_subseq_push_right(t + r, c, data);
            }
        }
        self.paths[i].challenges_rcvd = Ghost(c.push(data));
        proof {
            Paths::lemma_set(a, *self, i as int);
        }
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-19.17
    //# The recipient of this frame MUST generate a PATH_RESPONSE frame
    //# (Section 19.18) containing the same Data value.
    /// The oldest owed PATH_RESPONSE data on path `id`. Each one is handed out once, and the
    /// handed-out sequence stays a subsequence of the challenges received (`lemma_wf`).
    pub fn take_response(&mut self, id: PathId) -> (r: Option<[u8; 8]>)
        requires
            old(self).wf(),
            old(self).has(id),
        ensures
            final(self).wf(),
            r == if old(self).path(id).responses.len() > 0 {
                Some(old(self).path(id).responses[0])
            } else {
                None
            },
            r matches Some(x) ==> {
                &&& kept(*old(self), *final(self), id)
                &&& final(self).last_validated_spec() == old(self).last_validated_spec()
                &&& final(self).path(id) == (SpecPath {
                    responses: old(self).path(id).responses.drop_first(),
                    responses_taken: old(self).path(id).responses_taken.push(x),
                    ..old(self).path(id)
                })
            },
            r is None ==> *final(self) == *old(self),
    {
        let i = self.find(id);
        if self.paths[i].responses.len() == 0 {
            return None;
        }
        let ghost a = *self;
        proof {
            assert(path_wf(self.paths@[i as int]));
        }
        let ghost t = self.paths[i as int].responses_taken@;
        let ghost r0 = self.paths[i as int].responses@;
        // ponytail: shifts at most MAX_RESPONSES - 1 elements.
        let x = self.paths[i].responses.remove(0);
        self.paths[i].responses_taken = Ghost(t.push(x));
        proof {
            assert(t.push(x) + r0.drop_first() =~= t + r0);
            assert(self.paths@[i as int].responses@ =~= r0.drop_first());
            Paths::lemma_set(a, *self, i as int);
        }
        Some(x)
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-8.2.1
    //# The endpoint MUST use unpredictable data in every PATH_CHALLENGE
    //# frame so that it can associate the peer's response with the
    //# corresponding PATH_CHALLENGE.
    /// Start validating path `id` with `data`, drawn from the shell's randomness at `now`. An
    /// earlier challenge on the path is replaced; while Validating, the new one keeps the
    /// first one's start time, so the §8.2.4 3·PTO bound runs from the first challenge. A
    /// Validated path stays Validated (an MTU probe, §8.2.1).
    pub fn start_challenge(&mut self, id: PathId, data: [u8; 8], now: u64)
        requires
            old(self).wf(),
            old(self).has(id),
        ensures
            final(self).wf(),
            kept(*old(self), *final(self), id),
            final(self).last_validated_spec() == old(self).last_validated_spec(),
            final(self).path(id) == (SpecPath {
                challenge: Some(
                    (
                        data,
                        if old(self).path(id).state is Validating {
                            old(self).path(id).challenge.unwrap().1
                        } else {
                            now
                        },
                        false,
                    ),
                ),
                owed: true,
                state: if old(self).path(id).state is Unvalidated {
                    PathState::Validating
                } else {
                    old(self).path(id).state
                },
                ..old(self).path(id)
            }),
    {
        let i = self.find(id);
        let ghost a = *self;
        proof {
            assert(path_wf(self.paths@[i as int]));
        }
        let t = match (self.paths[i].state, self.paths[i].challenge) {
            (PathState::Validating, Some((_, t0, _))) => t0,
            _ => now,
        };
        self.paths[i].challenge = Some((data, t, false));
        self.paths[i].challenge_owed = true;
        if let PathState::Unvalidated = self.paths[i].state {
            self.paths[i].state = PathState::Validating;
        }
        proof {
            Paths::lemma_set(a, *self, i as int);
        }
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-8.2.1
    //# An endpoint MUST expand datagrams that contain a PATH_CHALLENGE frame
    //# to at least the smallest allowed maximum datagram size of 1200 bytes,
    //# unless the anti-amplification limit for the path does not permit
    //# sending a datagram of this size.
    /// The owed challenge's data on path `id`, now being sent; `padded` says whether its
    /// datagram reached 1200 bytes (3d2 pads it). The challenge's clock stays its start time.
    pub fn take_challenge(&mut self, id: PathId, padded: bool) -> (r: Option<[u8; 8]>)
        requires
            old(self).wf(),
            old(self).has(id),
        ensures
            final(self).wf(),
            r is Some <==> old(self).path(id).owed,
            old(self).path(id).owed ==> {
                &&& old(self).path(id).challenge matches Some((d, t, _))
                &&& r == Some(d)
                &&& kept(*old(self), *final(self), id)
                &&& final(self).last_validated_spec() == old(self).last_validated_spec()
                &&& final(self).path(id) == (SpecPath {
                    owed: false,
                    challenge: Some((d, t, padded)),
                    ..old(self).path(id)
                })
            },
            !old(self).path(id).owed ==> *final(self) == *old(self),
    {
        let i = self.find(id);
        if !self.paths[i].challenge_owed {
            return None;
        }
        let ghost a = *self;
        proof {
            assert(path_wf(self.paths@[i as int]));
        }
        match self.paths[i].challenge {
            Some((d, t, _)) => {
                self.paths[i].challenge = Some((d, t, padded));
                self.paths[i].challenge_owed = false;
                proof {
                    Paths::lemma_set(a, *self, i as int);
                }
                Some(d)
            },
            None => None,
        }
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-8.2.3
    //# Path validation succeeds when a PATH_RESPONSE frame is received that
    //# contains the data that was sent in a previous PATH_CHALLENGE frame.
    /// A PATH_RESPONSE with `data` arrived, on whatever path: it validates the path whose sent
    /// challenge it answers (the lowest such entry), and that path's MTU when the challenge's
    /// datagram reached 1200 bytes.
    pub fn on_response(&mut self, data: [u8; 8]) -> (r: Option<PathId>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            r matches Some(q) ==> {
                &&& old(self).has(q)
                &&& answers(old(self).path(q), data)
                &&& kept(*old(self), *final(self), q)
                &&& final(self).last_validated_spec() == Some(q)
                &&& final(self).path(q) == (SpecPath {
                    state: PathState::Validated,
                    amp_trace: old(self).path(q).amp_trace.push(AmpEv::Validated),
                    budget: final(self).path(q).budget,
                    challenge: None,
                    mtu_ok: old(self).path(q).mtu_ok || old(self).path(q).challenge.unwrap().2,
                    ..old(self).path(q)
                })
            },
            r is None ==> (forall|q: PathId| #[trigger] old(self).has(q) ==> !answers(
                old(self).path(q),
                data,
            )) && *final(self) == *old(self),
    {
        let mut i: usize = 0;
        while i < self.paths.len()
            invariant
                self.wf(),
                *self == *old(self),
                i <= self.paths@.len(),
                forall|k: int| 0 <= k < i ==> !answers(#[trigger] self.paths@[k]@, data),
            decreases self.paths@.len() - i,
        {
            if !self.paths[i].challenge_owed {
                if let Some((d, _, padded)) = self.paths[i].challenge {
                    if d == data {
                        let id = self.paths[i].id;
                        let ghost a = *self;
                        proof {
                            assert(path_wf(self.paths@[i as int]));
                            a.lemma_index(i as int);
                            assert(d =~= data);
                            assert(answers(a.paths@[i as int]@, data));
                        }
                        self.paths[i].amp.validate();
                        self.paths[i].state = PathState::Validated;
                        self.paths[i].challenge = None;
                        self.paths[i].mtu_ok = self.paths[i].mtu_ok || padded;
                        self.last_validated = Some(id);
                        proof {
                            let t = a.paths@[i as int].amp.trace();
                            assert(t.push(AmpEv::Validated).drop_last() =~= t);
                            Paths::lemma_set(a, *self, i as int);
                        }
                        return Some(id);
                    }
                }
            }
            i += 1;
        }
        proof {
            assert forall|q: PathId| #[trigger] self.has(q) implies !answers(self.path(q), data) by {
                let j = self.lemma_has(q);
                assert(!answers(self.paths@[j]@, data));
            }
        }
        None
    }

    //= https://www.rfc-editor.org/rfc/rfc9000#section-8.2.1
    //# To ensure that the path MTU is large enough, the endpoint
    //# MUST perform a second path validation by sending a PATH_CHALLENGE
    //# frame in a datagram of at least 1200 bytes.
    //= https://www.rfc-editor.org/rfc/rfc9000#section-8.2.3
    //# However, the endpoint MUST initiate
    //# another path validation with an expanded datagram to verify that the
    //# path supports the required MTU.
    /// Path `id` is validated but its MTU is not, and no challenge is underway: 3d2 starts a
    /// second validation, sent in a datagram of at least 1200 bytes.
    pub fn needs_mtu_probe(&self, id: PathId) -> (r: bool)
        requires
            self.wf(),
            self.has(id),
        ensures
            r == (self.path(id).state is Validated && !self.path(id).mtu_ok
                && self.path(id).challenge is None),
    {
        let i = self.find(id);
        match self.paths[i].state {
            PathState::Validated => !self.paths[i].mtu_ok && self.paths[i].challenge.is_none(),
            _ => false,
        }
    }

    /// Abandon at most one expired validation (§8.2.4: 3·PTO after the challenge started):
    /// the lowest entry whose sent challenge has expired. Its challenge is cleared and it is
    /// Unvalidated again, unless it was Validated (a failed MTU probe; `mtu_ok` stays false).
    pub fn on_timeout(&mut self, now: u64, pto_us: u64) -> (failed: Option<PathId>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            failed matches Some(q) ==> {
                &&& old(self).has(q)
                &&& expired(old(self).path(q), now, pto_us)
                &&& forall|q2: PathId|
                    #[trigger] old(self).has(q2) && old(self).index_spec(q2).unwrap()
                        < old(self).index_spec(q).unwrap() ==> !expired(
                        old(self).path(q2),
                        now,
                        pto_us,
                    )
                &&& kept(*old(self), *final(self), q)
                &&& final(self).last_validated_spec() == old(self).last_validated_spec()
                &&& final(self).path(q) == (SpecPath {
                    challenge: None,
                    state: if old(self).path(q).state is Validated {
                        PathState::Validated
                    } else {
                        PathState::Unvalidated
                    },
                    ..old(self).path(q)
                })
                &&& final(self).timed_count() < old(self).timed_count()
            },
            failed is None ==> (forall|q: PathId| #[trigger] old(self).has(q) ==> !expired(
                old(self).path(q),
                now,
                pto_us,
            )) && *final(self) == *old(self),
    {
        let w = sat3(pto_us);
        let mut i: usize = 0;
        while i < self.paths.len()
            invariant
                self.wf(),
                *self == *old(self),
                w == spec_sat3(pto_us),
                i <= self.paths@.len(),
                forall|k: int| 0 <= k < i ==> !expired(#[trigger] self.paths@[k]@, now, pto_us),
            decreases self.paths@.len() - i,
        {
            if !self.paths[i].challenge_owed {
                if let Some((_, t, _)) = self.paths[i].challenge {
                    if now >= sat_add(t, w) {
                        let id = self.paths[i].id;
                        let ghost a = *self;
                        proof {
                            assert(path_wf(self.paths@[i as int]));
                            a.lemma_index(i as int);
                        }
                        self.paths[i].challenge = None;
                        match self.paths[i].state {
                            PathState::Validated => {},
                            _ => {
                                self.paths[i].state = PathState::Unvalidated;
                            },
                        }
                        proof {
                            Paths::lemma_set(a, *self, i as int);
                            lemma_tcount_update(a.paths@, i as int, self.paths@[i as int]);
                            assert(self.paths@ == a.paths@.update(
                                i as int,
                                self.paths@[i as int],
                            ));
                            assert forall|q2: PathId|
                                #[trigger] a.has(q2) && a.index_spec(q2).unwrap()
                                    < a.index_spec(id).unwrap() implies !expired(
                                a.path(q2),
                                now,
                                pto_us,
                            ) by {
                                let j = a.lemma_has(q2);
                                assert(!expired(a.paths@[j]@, now, pto_us));
                            }
                        }
                        return Some(id);
                    }
                }
            }
            i += 1;
        }
        proof {
            assert forall|q: PathId| #[trigger] self.has(q) implies !expired(
                self.path(q),
                now,
                pto_us,
            ) by {
                let j = self.lemma_has(q);
                assert(!expired(self.paths@[j]@, now, pto_us));
            }
        }
        None
    }

    /// The earliest time `on_timeout` abandons a validation; None when no sent challenge is
    /// waiting.
    pub fn deadline(&self, pto_us: u64) -> (r: Option<u64>)
        requires
            self.wf(),
        ensures
            r is None <==> forall|q: PathId| #[trigger] self.has(q) ==> !timed(self.path(q)),
            r matches Some(d) ==> {
                &&& exists|q: PathId|
                    #[trigger] self.has(q) && timed(self.path(q)) && d == expiry(
                        self.path(q),
                        pto_us,
                    )
                &&& forall|q: PathId|
                    #[trigger] self.has(q) && timed(self.path(q)) ==> d <= expiry(
                        self.path(q),
                        pto_us,
                    )
            },
    {
        let w = sat3(pto_us);
        let mut best: Option<u64> = None;
        let mut i: usize = 0;
        while i < self.paths.len()
            invariant
                self.wf(),
                w == spec_sat3(pto_us),
                i <= self.paths@.len(),
                best is None <==> forall|k: int| 0 <= k < i ==> !timed(#[trigger] self.paths@[k]@),
                best matches Some(d) ==> {
                    &&& exists|k: int|
                        0 <= k < i && timed(#[trigger] self.paths@[k]@) && d == expiry(
                            self.paths@[k]@,
                            pto_us,
                        )
                    &&& forall|k: int|
                        0 <= k < i && timed(#[trigger] self.paths@[k]@) ==> d <= expiry(
                            self.paths@[k]@,
                            pto_us,
                        )
                },
            decreases self.paths@.len() - i,
        {
            if !self.paths[i].challenge_owed {
                if let Some((_, t, _)) = self.paths[i].challenge {
                    let e = sat_add(t, w);
                    best = match best {
                        Some(d) if d <= e => Some(d),
                        _ => Some(e),
                    };
                }
            }
            i += 1;
        }
        proof {
            assert forall|q: PathId| #[trigger] self.has(q) && timed(self.path(q)) implies best is Some
                && best.unwrap() <= expiry(self.path(q), pto_us) by {
                let j = self.lemma_has(q);
                assert(timed(self.paths@[j]@));
            }
            if let Some(d) = best {
                let k = choose|k: int|
                    0 <= k < self.paths@.len() && timed(#[trigger] self.paths@[k]@) && d == expiry(
                        self.paths@[k]@,
                        pto_us,
                    );
                self.lemma_index(k);
                assert(self.has(self.paths@[k].id));
            } else {
                assert forall|q: PathId| #[trigger] self.has(q) implies !timed(self.path(q)) by {
                    let j = self.lemma_has(q);
                }
            }
        }
        best
    }

    #[verifier::when_used_as_spec(active_spec)]
    pub fn active(&self) -> (r: PathId)
        ensures
            r == self.active_spec(),
    {
        self.active
    }

    /// Send on path `id` from now on.
    pub fn set_active(&mut self, id: PathId)
        requires
            old(self).wf(),
            old(self).has(id),
        ensures
            final(self).wf(),
            final(self).active_spec() == id,
            final(self).ids() == old(self).ids(),
            final(self).timed_count() == old(self).timed_count(),
            final(self).last_validated_spec() == old(self).last_validated_spec(),
            forall|q: PathId| #[trigger] final(self).path(q) == old(self).path(q),
    {
        self.active = id;
    }

    #[verifier::when_used_as_spec(last_validated_spec)]
    pub fn last_validated(&self) -> (r: Option<PathId>)
        ensures
            r == self.last_validated_spec(),
    {
        self.last_validated
    }

    #[verifier::when_used_as_spec(state_spec)]
    pub fn state(&self, id: PathId) -> (r: PathState)
        requires
            self.wf(),
            self.has(id),
        ensures
            r == self.state_spec(id),
    {
        let i = self.find(id);
        self.paths[i].state
    }

    pub fn dcid(&self, id: PathId) -> (r: Option<&[u8]>)
        requires
            self.wf(),
            self.has(id),
        ensures
            opt_slice_view(r) == self.path(id).dcid,
    {
        let i = self.find(id);
        match &self.paths[i].dcid {
            Some(v) => Some(v.as_slice()),
            None => None,
        }
    }

    /// Set (or, with None, clear) the peer CID used on path `id`.
    pub fn set_dcid(&mut self, id: PathId, d: Option<&[u8]>)
        requires
            old(self).wf(),
            old(self).has(id),
            d matches Some(c) ==> c@.len() <= MAX_CID_LEN,
        ensures
            final(self).wf(),
            kept(*old(self), *final(self), id),
            final(self).last_validated_spec() == old(self).last_validated_spec(),
            final(self).path(id) == (SpecPath { dcid: opt_slice_view(d), ..old(self).path(id) }),
    {
        let i = self.find(id);
        let ghost a = *self;
        proof {
            assert(path_wf(self.paths@[i as int]));
        }
        self.paths[i].dcid = match d {
            Some(c) => Some(slice_to_vec(c)),
            None => None,
        };
        proof {
            Paths::lemma_set(a, *self, i as int);
        }
    }

    pub fn peer_used(&self, id: PathId) -> (r: Option<&[u8]>)
        requires
            self.wf(),
            self.has(id),
        ensures
            opt_slice_view(r) == self.path(id).peer_used,
    {
        let i = self.find(id);
        match &self.paths[i].peer_used {
            Some(v) => Some(v.as_slice()),
            None => None,
        }
    }

    /// The peer used our CID `d` on path `id`.
    pub fn set_peer_used(&mut self, id: PathId, d: &[u8])
        requires
            old(self).wf(),
            old(self).has(id),
            d@.len() <= MAX_CID_LEN,
        ensures
            final(self).wf(),
            kept(*old(self), *final(self), id),
            final(self).last_validated_spec() == old(self).last_validated_spec(),
            final(self).path(id) == (SpecPath { peer_used: Some(d@), ..old(self).path(id) }),
    {
        let i = self.find(id);
        let ghost a = *self;
        proof {
            assert(path_wf(self.paths@[i as int]));
        }
        self.paths[i].peer_used = Some(slice_to_vec(d));
        proof {
            Paths::lemma_set(a, *self, i as int);
        }
    }

    pub open spec fn mtu_ok_spec(&self, id: PathId) -> bool {
        self.path(id).mtu_ok
    }

    /// Path `id`'s MTU is validated: by the handshake, or by an answered challenge whose
    /// datagram reached 1200 bytes.
    #[verifier::when_used_as_spec(mtu_ok_spec)]
    pub fn mtu_ok(&self, id: PathId) -> (r: bool)
        requires
            self.wf(),
            self.has(id),
        ensures
            r == self.mtu_ok_spec(id),
    {
        let i = self.find(id);
        self.paths[i].mtu_ok
    }

    /// A PATH_RESPONSE is owed on path `id` (`take_response` returns Some).
    pub fn has_response(&self, id: PathId) -> (r: bool)
        requires
            self.wf(),
            self.has(id),
        ensures
            r == (self.path(id).responses.len() > 0),
    {
        let i = self.find(id);
        self.paths[i].responses.len() > 0
    }

    /// A PATH_CHALLENGE is owed on path `id` (`take_challenge` returns Some).
    pub fn challenge_owed(&self, id: PathId) -> (r: bool)
        requires
            self.wf(),
            self.has(id),
        ensures
            r == self.path(id).owed,
    {
        let i = self.find(id);
        self.paths[i].challenge_owed
    }
}

} // verus!
impl Paths {
    /// Test support: the allocated capacities of the path list and of path `id`'s response
    /// list. Verus models `Vec` length, not capacity (TRUSTED.md).
    #[doc(hidden)]
    pub fn capacities(&self, id: PathId) -> (usize, usize) {
        let mut r = 0;
        for p in &self.paths {
            if p.id == id {
                r = p.responses.capacity();
            }
        }
        (self.paths.capacity(), r)
    }
}
