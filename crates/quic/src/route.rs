//! Datagram routing (RFC 9000 §5.2.2): the table from our connection IDs and the peers'
//! stateless reset tokens to connections, and the decision for an incoming datagram: an
//! existing connection, a new one, Version Negotiation, a Stateless Reset, or drop. Sans-IO.
use vstd::prelude::*;
use vstd::slice::{slice_subrange, slice_to_vec};

use crate::cid::*;
use crate::codes::*;
use crate::header::*;
use crate::stateless::*;

verus! {

pub type ConnId = u64;

// ponytail: linear-scan CID table, ~100 connections; a random-keyed SipHash index before production.
pub const MAX_TABLE: usize = 512;

/// The entries one connection may hold: `ISSUE_CAP_ACTIVE` active CIDs plus the client's
/// original DCID while its Initial space is live.
pub const PER_CONN: usize = ISSUE_CAP_ACTIVE as usize + 1;

/// The connections the table admits: `MAX_TABLE / PER_CONN`, so `MAX_CONNS * PER_CONN <=
/// MAX_TABLE`.
pub const MAX_CONNS: usize = 102;

/// The token list's cap. Each connection registers at most `PEER_CID_CAP` used tokens (3d2's
/// binding), and there are at most `MAX_CONNS` connections, so `AddToken` from well-formed
/// callers never hits it.
// ponytail: linear CT token scan, ~100 connections; a random-keyed SipHash index before production.
pub const MAX_TOKENS: usize = MAX_CONNS * PEER_CID_CAP as usize;

/// A change a connection asks of the table: our CIDs it issued or retired, and the peer's
/// reset tokens it learned or dropped.
#[derive(Debug, PartialEq, Eq)]
pub enum CidUpdate {
    Add(Vec<u8>),
    Remove(Vec<u8>),
    AddToken([u8; 16]),
    RemoveToken([u8; 16]),
}

/// Our connection IDs and the peers' reset tokens, each owned by one connection.
#[derive(Debug, PartialEq, Eq)]
pub struct CidTable {
    cids: Vec<(Vec<u8>, ConnId)>,
    tokens: Vec<([u8; 16], ConnId)>,
    /// The admitted connections: each one's first `Add` registers it, `remove_conn` drops it.
    conns: Vec<ConnId>,
}

pub struct SpecTable {
    pub cids: Seq<(Seq<u8>, ConnId)>,
    pub tokens: Seq<(Seq<u8>, ConnId)>,
    pub conns: Seq<ConnId>,
}

pub open spec fn cids_view(v: Seq<(Vec<u8>, ConnId)>) -> Seq<(Seq<u8>, ConnId)> {
    v.map_values(|e: (Vec<u8>, ConnId)| (e.0@, e.1))
}

pub open spec fn tokens_view(v: Seq<([u8; 16], ConnId)>) -> Seq<(Seq<u8>, ConnId)> {
    v.map_values(|e: ([u8; 16], ConnId)| (e.0@, e.1))
}

impl View for CidTable {
    type V = SpecTable;

    closed spec fn view(&self) -> SpecTable {
        SpecTable {
            cids: cids_view(self.cids@),
            tokens: tokens_view(self.tokens@),
            conns: self.conns@,
        }
    }
}

// =============================================================================
// Table specs
// =============================================================================

/// The owner of the first entry with key `k`.
pub open spec fn find_key(s: Seq<(Seq<u8>, ConnId)>, k: Seq<u8>) -> Option<ConnId>
    decreases s.len(),
{
    if s.len() == 0 {
        None
    } else if s[0].0 == k {
        Some(s[0].1)
    } else {
        find_key(s.skip(1), k)
    }
}

pub open spec fn keys_unique(s: Seq<(Seq<u8>, ConnId)>) -> bool
    decreases s.len(),
{
    s.len() == 0 || (find_key(s.skip(1), s[0].0) is None && keys_unique(s.skip(1)))
}

/// `s` without connection `c`'s entries.
pub open spec fn drop_conn(s: Seq<(Seq<u8>, ConnId)>, c: ConnId) -> Seq<(Seq<u8>, ConnId)>
    decreases s.len(),
{
    if s.len() == 0 {
        s
    } else if s[0].1 == c {
        drop_conn(s.skip(1), c)
    } else {
        seq![s[0]] + drop_conn(s.skip(1), c)
    }
}

/// The number of entries connection `c` owns.
pub open spec fn count_of(s: Seq<(Seq<u8>, ConnId)>, c: ConnId) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        (if s[0].1 == c {
            1nat
        } else {
            0nat
        }) + count_of(s.skip(1), c)
    }
}

pub open spec fn member(s: Seq<ConnId>, c: ConnId) -> bool
    decreases s.len(),
{
    s.len() > 0 && (s[0] == c || member(s.skip(1), c))
}

/// `s` without `c`.
pub open spec fn drop_id(s: Seq<ConnId>, c: ConnId) -> Seq<ConnId>
    decreases s.len(),
{
    if s.len() == 0 {
        s
    } else if s[0] == c {
        drop_id(s.skip(1), c)
    } else {
        seq![s[0]] + drop_id(s.skip(1), c)
    }
}

/// Every CID's owner is an admitted connection, each owns at most `PER_CONN` CIDs, and at
/// most `MAX_CONNS` are admitted; so `t.cids.len() <= MAX_CONNS * PER_CONN <= MAX_TABLE`
/// (`lemma_len_bound`), and an `Add` within its connection's cap never fails for room.
pub open spec fn table_wf(t: SpecTable) -> bool {
    &&& keys_unique(t.cids)
    &&& keys_unique(t.tokens)
    &&& t.cids.len() <= MAX_TABLE
    &&& t.tokens.len() <= MAX_TOKENS
    &&& t.conns.len() <= MAX_CONNS
    &&& forall|c: ConnId| #[trigger] count_of(t.cids, c) <= PER_CONN
    &&& forall|c: ConnId| #[trigger] count_of(t.cids, c) > 0 ==> member(t.conns, c)
}

/// Room for one more connection.
pub open spec fn table_room(t: SpecTable) -> bool {
    t.conns.len() < MAX_CONNS
}

/// What `apply(Add(k))` from connection `c` does: it fails only on a present key, at the
/// connection's `PER_CONN` cap, or for a connection not yet admitted when `MAX_CONNS` are;
/// never for lack of room in the list.
pub open spec fn add_cid(old: SpecTable, new: SpecTable, c: ConnId, k: Seq<u8>, ok: bool) -> bool {
    &&& ok == (find_key(old.cids, k) is None && count_of(old.cids, c) < PER_CONN && (member(
        old.conns,
        c,
    ) || old.conns.len() < MAX_CONNS))
    &&& new.tokens == old.tokens
    &&& new.cids == if ok {
        old.cids.push((k, c))
    } else {
        old.cids
    }
    &&& new.conns == if ok && !member(old.conns, c) {
        old.conns.push(c)
    } else {
        old.conns
    }
}

/// What `apply` does to one list of capacity `cap`: `Add` needs a new key and room, `Remove`
/// the owner.
pub open spec fn list_update(
    old: Seq<(Seq<u8>, ConnId)>,
    new: Seq<(Seq<u8>, ConnId)>,
    c: ConnId,
    k: Seq<u8>,
    add: bool,
    cap: nat,
    ok: bool,
) -> bool {
    if add {
        &&& ok == (find_key(old, k) is None && old.len() < cap)
        &&& new == if ok {
            old.push((k, c))
        } else {
            old
        }
    } else {
        &&& ok == (find_key(old, k) == Some(c))
        &&& ok ==> find_key(new, k) is None && new.len() + 1 == old.len() && forall|k2: Seq<u8>|
            k2 != k ==> #[trigger] find_key(new, k2) == find_key(old, k2)
        &&& !ok ==> new == old
    }
}

// =============================================================================
// Routing spec
// =============================================================================

#[derive(Debug, PartialEq, Eq)]
pub enum Route {
    Existing(ConnId),
    NewInitial,
    VersionNegotiation(Vec<u8>),
    Reset(ConnId),
    Drop,
}

pub enum SpecRoute {
    Existing(ConnId),
    NewInitial,
    VersionNegotiation(Seq<u8>),
    Reset(ConnId),
    Drop,
}

impl View for Route {
    type V = SpecRoute;

    open spec fn view(&self) -> SpecRoute {
        match self {
            Route::Existing(c) => SpecRoute::Existing(*c),
            Route::NewInitial => SpecRoute::NewInitial,
            Route::VersionNegotiation(v) => SpecRoute::VersionNegotiation(v@),
            Route::Reset(c) => SpecRoute::Reset(*c),
            Route::Drop => SpecRoute::Drop,
        }
    }
}

/// The connection a version 1 header's DCID maps to.
pub open spec fn header_owner(h: Option<SpecHeader>, t: SpecTable) -> Option<ConnId> {
    match h {
        Some(SpecHeader::Long { dcid, .. }) => find_key(t.cids, dcid),
        Some(SpecHeader::Short { dcid, .. }) => find_key(t.cids, dcid),
        _ => None,
    }
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-14.1
//# A server MUST discard an Initial packet that is carried in a UDP
//# datagram with a payload that is smaller than the smallest allowed
//# maximum datagram size of 1200 bytes.
/// Rule 3: an Initial that may open a connection: in a datagram of at least 1200 bytes, with a DCID
/// of at least 8 bytes (§7.2), and with room in the table.
pub open spec fn opens_connection(d: Seq<u8>, h: Option<SpecHeader>, t: SpecTable) -> bool {
    match h {
        Some(SpecHeader::Long { ty: LongType::Initial, dcid, .. }) => d.len()
            >= MIN_INITIAL_DATAGRAM && 8 <= dcid.len() && table_room(t),
        _ => false,
    }
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-10.3
//# However, endpoints MUST treat any packet ending in a
//# valid stateless reset token as a Stateless Reset, as other QUIC
//# versions might allow the use of a long header.
/// Rule 2: the connection whose reset token ends `d`, for a datagram that matched no
/// connection.
pub open spec fn reset_of(d: Seq<u8>, t: SpecTable) -> Option<ConnId> {
    if d.len() >= MIN_SHORT_PACKET {
        find_key(t.tokens, d.subrange(d.len() - RESET_TOKEN_LEN, d.len() as int))
    } else {
        None
    }
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-5.2.2
//# Servers MUST drop smaller packets that specify unsupported versions.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-5.2.2
//# Servers MUST drop incoming packets under all other circumstances.
/// Where a datagram goes; the first rule that applies:
/// 1. a version 1 header whose DCID is ours: that connection;
/// 2. a datagram of at least 21 bytes ending in a known reset token: a Stateless Reset of its
///    connection (§10.3: any packet, long headers and other versions included; §10.3.1: no
///    connection matched). It precedes rules 3 and 4, so every datagram not matched by CID
///    gets the comparison;
/// 3. an Initial that `opens_connection` (§14.1, §7.2): a new connection;
/// 4. an unsupported version in a datagram of at least 1200 bytes: Version Negotiation
///    (§6, §5.2.2);
/// 5. anything else is dropped: sub-1200 unsupported versions and Initials, unknown
///    Handshake and 0-RTT packets, unmatched short headers, and Initials when the table is
///    full (we do not send §5.2.2's CONNECTION_REFUSED, a SHOULD).
pub open spec fn rfc_route(d: Seq<u8>, t: SpecTable) -> SpecRoute {
    let h = rfc_header(d, LOCAL_CID_LEN as nat);
    if header_owner(h, t) is Some {
        SpecRoute::Existing(header_owner(h, t)->0)
    } else if reset_of(d, t) is Some {
        SpecRoute::Reset(reset_of(d, t)->0)
    } else if opens_connection(d, h, t) {
        SpecRoute::NewInitial
    } else if h matches Some(SpecHeader::UnsupportedVersion { .. })
        && rfc_version_negotiation(d) is Some {
        SpecRoute::VersionNegotiation(rfc_version_negotiation(d)->0)
    } else {
        SpecRoute::Drop
    }
}

// We never send a Stateless Reset (stateless.rs), so neither a load balancer nor a shared
// static key can turn this server into a reset oracle.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-5.2.3
//= type=exception
//= reason=We never send a Stateless Reset.
//# Server deployments that use this simple form of load balancing MUST
//# avoid the creation of a stateless reset oracle; see Section 21.11.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-21.11
//= type=exception
//= reason=No static key: our reset tokens are random per CID (cid.rs issue), and we never send a Stateless Reset.
//# To defend
//# against this style of denial of service, endpoints that share a
//# static key for stateless resets (see Section 10.3.2) MUST be arranged
//# so that packets with a given connection ID always arrive at an
//# instance that has connection state, unless that connection is no
//# longer active.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-21.11
//= type=exception
//= reason=We never send a Stateless Reset.
//# More generally, servers MUST NOT generate a stateless reset if a
//# connection with the corresponding connection ID could be active on
//# any endpoint using the same static key.

// =============================================================================
// Table proofs
// =============================================================================

/// Skipping entries whose key is not `k` keeps the lookup.
proof fn lemma_find_scan(s: Seq<(Seq<u8>, ConnId)>, k: Seq<u8>, i: int)
    requires
        0 <= i <= s.len(),
        forall|j: int| 0 <= j < i ==> (#[trigger] s[j]).0 != k,
    ensures
        find_key(s, k) == find_key(s.skip(i), k),
    decreases i,
{
    if i == 0 {
        assert(s.skip(0) =~= s);
    } else {
        assert(s[0].0 != k);
        let t = s.skip(1);
        assert forall|j: int| 0 <= j < i - 1 implies (#[trigger] t[j]).0 != k by {
            assert(t[j] == s[j + 1]);
        }
        lemma_find_scan(t, k, i - 1);
        assert(t.skip(i - 1) =~= s.skip(i));
    }
}

proof fn lemma_find_push(s: Seq<(Seq<u8>, ConnId)>, e: (Seq<u8>, ConnId), k: Seq<u8>)
    ensures
        find_key(s.push(e), k) == if find_key(s, k) is Some {
            find_key(s, k)
        } else if e.0 == k {
            Some(e.1)
        } else {
            None
        },
    decreases s.len(),
{
    let u = s.push(e);
    if s.len() == 0 {
        assert(u[0] == e);
        assert(u.skip(1) =~= Seq::<(Seq<u8>, ConnId)>::empty());
        assert(find_key(u.skip(1), k) is None);
    } else {
        assert(u[0] == s[0]);
        assert(u.skip(1) =~= s.skip(1).push(e));
        lemma_find_push(s.skip(1), e, k);
    }
}

proof fn lemma_unique_push(s: Seq<(Seq<u8>, ConnId)>, e: (Seq<u8>, ConnId))
    requires
        keys_unique(s),
        find_key(s, e.0) is None,
    ensures
        keys_unique(s.push(e)),
    decreases s.len(),
{
    let u = s.push(e);
    if s.len() == 0 {
        let z = u.skip(1);
        assert(z =~= Seq::<(Seq<u8>, ConnId)>::empty());
        assert(find_key(z, u[0].0) is None);
        assert(keys_unique(z));
    } else {
        assert(u[0] == s[0]);
        assert(s[0].0 != e.0);
        assert(find_key(s.skip(1), e.0) is None);
        assert(u.skip(1) =~= s.skip(1).push(e));
        lemma_find_push(s.skip(1), e, s[0].0);
        lemma_unique_push(s.skip(1), e);
    }
}

/// Removing the first entry with key `k` from a table with unique keys removes `k` and
/// nothing else.
proof fn lemma_remove_first(s: Seq<(Seq<u8>, ConnId)>, k: Seq<u8>, idx: int)
    requires
        keys_unique(s),
        0 <= idx < s.len(),
        s[idx].0 == k,
        forall|j: int| 0 <= j < idx ==> (#[trigger] s[j]).0 != k,
    ensures
        keys_unique(s.remove(idx)),
        find_key(s.remove(idx), k) is None,
        forall|k2: Seq<u8>| k2 != k ==> #[trigger] find_key(s.remove(idx), k2) == find_key(s, k2),
    decreases idx,
{
    let r = s.remove(idx);
    if idx == 0 {
        assert(r =~= s.skip(1));
        assert forall|k2: Seq<u8>| k2 != k implies #[trigger] find_key(r, k2) == find_key(s, k2) by {
            assert(s[0].0 != k2);
        }
    } else {
        let t = s.skip(1);
        assert forall|j: int| 0 <= j < idx - 1 implies (#[trigger] t[j]).0 != k by {
            assert(t[j] == s[j + 1]);
        }
        assert(t[idx - 1] == s[idx]);
        lemma_remove_first(t, k, idx - 1);
        assert(r[0] == s[0]);
        assert(r.skip(1) =~= t.remove(idx - 1));
        assert(s[0].0 != k);
        assert forall|k2: Seq<u8>| k2 != k implies #[trigger] find_key(r, k2) == find_key(s, k2) by {
            if s[0].0 != k2 {
                assert(find_key(t.remove(idx - 1), k2) == find_key(t, k2));
            }
        }
    }
}

/// With unique keys, dropping connection `c` unmaps exactly the keys `c` owned.
pub proof fn lemma_drop_find(s: Seq<(Seq<u8>, ConnId)>, c: ConnId, k: Seq<u8>)
    requires
        keys_unique(s),
    ensures
        find_key(drop_conn(s, c), k) == if find_key(s, k) == Some(c) {
            None
        } else {
            find_key(s, k)
        },
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_drop_find(s.skip(1), c, k);
        if s[0].1 != c {
            let d = seq![s[0]] + drop_conn(s.skip(1), c);
            assert(d[0] == s[0]);
            assert(d.skip(1) =~= drop_conn(s.skip(1), c));
        }
    }
}

proof fn lemma_drop_unique(s: Seq<(Seq<u8>, ConnId)>, c: ConnId)
    requires
        keys_unique(s),
    ensures
        keys_unique(drop_conn(s, c)),
        drop_conn(s, c).len() <= s.len(),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_drop_unique(s.skip(1), c);
        if s[0].1 != c {
            let d = seq![s[0]] + drop_conn(s.skip(1), c);
            assert(d[0] == s[0]);
            assert(d.skip(1) =~= drop_conn(s.skip(1), c));
            lemma_drop_find(s.skip(1), c, s[0].0);
        }
    }
}

proof fn lemma_count_push(s: Seq<(Seq<u8>, ConnId)>, e: (Seq<u8>, ConnId), c: ConnId)
    ensures
        count_of(s.push(e), c) == count_of(s, c) + if e.1 == c {
            1nat
        } else {
            0nat
        },
    decreases s.len(),
{
    let u = s.push(e);
    if s.len() == 0 {
        assert(u[0] == e);
        assert(u.skip(1) =~= Seq::<(Seq<u8>, ConnId)>::empty());
        assert(count_of(u.skip(1), c) == 0);
    } else {
        assert(u[0] == s[0]);
        assert(u.skip(1) =~= s.skip(1).push(e));
        lemma_count_push(s.skip(1), e, c);
    }
}

proof fn lemma_count_remove(s: Seq<(Seq<u8>, ConnId)>, i: int, c: ConnId)
    requires
        0 <= i < s.len(),
    ensures
        count_of(s.remove(i), c) + (if s[i].1 == c {
            1nat
        } else {
            0nat
        }) == count_of(s, c),
    decreases i,
{
    let r = s.remove(i);
    if i == 0 {
        assert(r =~= s.skip(1));
    } else {
        lemma_count_remove(s.skip(1), i - 1, c);
        assert(r[0] == s[0]);
        assert(r.skip(1) =~= s.skip(1).remove(i - 1));
        assert(s.skip(1)[i - 1] == s[i]);
    }
}

/// Dropping connection `c` removes exactly its `count_of` entries.
proof fn lemma_count_drop(s: Seq<(Seq<u8>, ConnId)>, c: ConnId, c2: ConnId)
    ensures
        count_of(drop_conn(s, c), c2) == if c2 == c {
            0
        } else {
            count_of(s, c2)
        },
        drop_conn(s, c).len() + count_of(s, c) == s.len(),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_count_drop(s.skip(1), c, c2);
        if s[0].1 != c {
            let d = seq![s[0]] + drop_conn(s.skip(1), c);
            assert(d[0] == s[0]);
            assert(d.skip(1) =~= drop_conn(s.skip(1), c));
        }
    }
}

proof fn lemma_member_push(s: Seq<ConnId>, e: ConnId, c: ConnId)
    ensures
        member(s.push(e), c) == (member(s, c) || e == c),
    decreases s.len(),
{
    let u = s.push(e);
    if s.len() == 0 {
        assert(u[0] == e);
        assert(u.skip(1) =~= Seq::<ConnId>::empty());
        assert(!member(u.skip(1), c));
    } else {
        assert(u[0] == s[0]);
        assert(u.skip(1) =~= s.skip(1).push(e));
        lemma_member_push(s.skip(1), e, c);
    }
}

proof fn lemma_member_drop(s: Seq<ConnId>, c: ConnId, x: ConnId)
    ensures
        member(drop_id(s, c), x) == (member(s, x) && x != c),
        drop_id(s, c).len() <= s.len(),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_member_drop(s.skip(1), c, x);
        if s[0] != c {
            let d = seq![s[0]] + drop_id(s.skip(1), c);
            assert(d[0] == s[0]);
            assert(d.skip(1) =~= drop_id(s.skip(1), c));
        }
    }
}

/// Owners drawn from `conns`, each with at most `PER_CONN` entries, fill at most
/// `conns.len() * PER_CONN` entries.
proof fn lemma_len_bound(s: Seq<(Seq<u8>, ConnId)>, conns: Seq<ConnId>)
    requires
        forall|c: ConnId| #[trigger] count_of(s, c) <= PER_CONN,
        forall|c: ConnId| #[trigger] count_of(s, c) > 0 ==> member(conns, c),
    ensures
        s.len() <= conns.len() * PER_CONN,
    decreases conns.len(),
{
    if conns.len() == 0 {
        if s.len() > 0 {
            assert(count_of(s, s[0].1) > 0);
        }
    } else {
        let c0 = conns[0];
        let d = drop_conn(s, c0);
        lemma_count_drop(s, c0, c0);
        assert forall|c: ConnId| #[trigger] count_of(d, c) <= PER_CONN by {
            lemma_count_drop(s, c0, c);
        }
        assert forall|c: ConnId| #[trigger] count_of(d, c) > 0 implies member(conns.skip(1), c) by {
            lemma_count_drop(s, c0, c);
        }
        lemma_len_bound(d, conns.skip(1));
        assert(count_of(s, c0) <= PER_CONN);
        let n = conns.len();
        assert(s.len() <= n * PER_CONN) by (nonlinear_arith)
            requires
                s.len() <= d.len() + PER_CONN,
                d.len() <= (n - 1) * PER_CONN,
                n >= 1,
        ;
    }
}

// =============================================================================
// Executable code
// =============================================================================

/// Constant-time style comparison of a stored token with 16 bytes of a datagram: every byte
/// is read, no early exit (TRUSTED.md: the timing is unproven).
fn ct_eq_token(a: &[u8; 16], b: &[u8]) -> (r: bool)
    requires
        b@.len() == 16,
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

/// The first index of key `k` in the CID list.
fn cid_index(v: &Vec<(Vec<u8>, ConnId)>, k: &[u8]) -> (r: Option<usize>)
    ensures
        match r {
            Some(i) => i < v@.len() && cids_view(v@)[i as int].0 == k@ && (forall|j: int|
                0 <= j < i ==> (#[trigger] cids_view(v@)[j]).0 != k@) && find_key(
                cids_view(v@),
                k@,
            ) == Some(v@[i as int].1),
            None => find_key(cids_view(v@), k@) is None,
        },
{
    let ghost s = cids_view(v@);
    let mut i: usize = 0;
    while i < v.len()
        invariant
            s == cids_view(v@),
            i <= v@.len(),
            forall|j: int| 0 <= j < i ==> (#[trigger] s[j]).0 != k@,
        decreases v@.len() - i,
    {
        if eq_bytes(v[i].0.as_slice(), k) {
            proof {
                lemma_find_scan(s, k@, i as int);
                assert(s.skip(i as int)[0] == s[i as int]);
            }
            return Some(i);
        }
        i += 1;
    }
    proof {
        lemma_find_scan(s, k@, i as int);
    }
    None
}

/// The first index of token `k` (16 bytes) in the token list.
fn token_index(v: &Vec<([u8; 16], ConnId)>, k: &[u8]) -> (r: Option<usize>)
    requires
        k@.len() == 16,
    ensures
        match r {
            Some(i) => i < v@.len() && tokens_view(v@)[i as int].0 == k@ && (forall|j: int|
                0 <= j < i ==> (#[trigger] tokens_view(v@)[j]).0 != k@) && find_key(
                tokens_view(v@),
                k@,
            ) == Some(v@[i as int].1),
            None => find_key(tokens_view(v@), k@) is None,
        },
{
    let ghost s = tokens_view(v@);
    let mut i: usize = 0;
    while i < v.len()
        invariant
            s == tokens_view(v@),
            i <= v@.len(),
            k@.len() == 16,
            forall|j: int| 0 <= j < i ==> (#[trigger] s[j]).0 != k@,
        decreases v@.len() - i,
    {
        if ct_eq_token(&v[i].0, k) {
            proof {
                lemma_find_scan(s, k@, i as int);
                assert(s.skip(i as int)[0] == s[i as int]);
            }
            return Some(i);
        }
        i += 1;
    }
    proof {
        lemma_find_scan(s, k@, i as int);
    }
    None
}

/// The CID list without connection `c`, in a fresh `Vec`.
fn keep_cids(v: &Vec<(Vec<u8>, ConnId)>, c: ConnId) -> (r: Vec<(Vec<u8>, ConnId)>)
    ensures
        cids_view(r@) == drop_conn(cids_view(v@), c),
{
    let ghost s = cids_view(v@);
    let mut r: Vec<(Vec<u8>, ConnId)> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(s.skip(0) =~= s);
        assert(cids_view(r@) =~= Seq::<(Seq<u8>, ConnId)>::empty());
    }
    while i < v.len()
        invariant
            s == cids_view(v@),
            i <= v@.len(),
            cids_view(r@) + drop_conn(s.skip(i as int), c) == drop_conn(s, c),
        decreases v@.len() - i,
    {
        let ghost r0 = cids_view(r@);
        proof {
            assert(s.skip(i as int)[0] == s[i as int]);
            assert(s.skip(i as int).skip(1) =~= s.skip(i as int + 1));
        }
        if v[i].1 != c {
            r.push((slice_to_vec(v[i].0.as_slice()), v[i].1));
            proof {
                assert(cids_view(r@) =~= r0.push(s[i as int]));
                assert(r0.push(s[i as int]) + drop_conn(s.skip(i as int + 1), c) =~= r0 + (seq![
                    s[i as int],
                ] + drop_conn(s.skip(i as int + 1), c)));
            }
        }
        i += 1;
    }
    proof {
        assert(s.skip(i as int) =~= Seq::<(Seq<u8>, ConnId)>::empty());
        assert(cids_view(r@) + Seq::<(Seq<u8>, ConnId)>::empty() =~= cids_view(r@));
    }
    r
}

/// The token list without connection `c`, in a fresh `Vec`.
fn keep_tokens(v: &Vec<([u8; 16], ConnId)>, c: ConnId) -> (r: Vec<([u8; 16], ConnId)>)
    ensures
        tokens_view(r@) == drop_conn(tokens_view(v@), c),
{
    let ghost s = tokens_view(v@);
    let mut r: Vec<([u8; 16], ConnId)> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(s.skip(0) =~= s);
        assert(tokens_view(r@) =~= Seq::<(Seq<u8>, ConnId)>::empty());
    }
    while i < v.len()
        invariant
            s == tokens_view(v@),
            i <= v@.len(),
            tokens_view(r@) + drop_conn(s.skip(i as int), c) == drop_conn(s, c),
        decreases v@.len() - i,
    {
        let ghost r0 = tokens_view(r@);
        proof {
            assert(s.skip(i as int)[0] == s[i as int]);
            assert(s.skip(i as int).skip(1) =~= s.skip(i as int + 1));
        }
        if v[i].1 != c {
            r.push(v[i]);
            proof {
                assert(tokens_view(r@) =~= r0.push(s[i as int]));
                assert(r0.push(s[i as int]) + drop_conn(s.skip(i as int + 1), c) =~= r0 + (seq![
                    s[i as int],
                ] + drop_conn(s.skip(i as int + 1), c)));
            }
        }
        i += 1;
    }
    proof {
        assert(s.skip(i as int) =~= Seq::<(Seq<u8>, ConnId)>::empty());
        assert(tokens_view(r@) + Seq::<(Seq<u8>, ConnId)>::empty() =~= tokens_view(r@));
    }
    r
}

/// The number of CIDs connection `c` owns.
fn conn_count(v: &Vec<(Vec<u8>, ConnId)>, c: ConnId) -> (n: usize)
    ensures
        n == count_of(cids_view(v@), c),
{
    let ghost s = cids_view(v@);
    let mut n: usize = 0;
    let mut i: usize = 0;
    proof {
        assert(s.skip(0) =~= s);
    }
    while i < v.len()
        invariant
            s == cids_view(v@),
            i <= v@.len(),
            n <= i,
            n + count_of(s.skip(i as int), c) == count_of(s, c),
        decreases v@.len() - i,
    {
        proof {
            assert(s.skip(i as int)[0] == s[i as int]);
            assert(s.skip(i as int).skip(1) =~= s.skip(i as int + 1));
        }
        if v[i].1 == c {
            n += 1;
        }
        i += 1;
    }
    proof {
        assert(s.skip(i as int) =~= Seq::<(Seq<u8>, ConnId)>::empty());
    }
    n
}

fn conn_member(v: &Vec<ConnId>, c: ConnId) -> (r: bool)
    ensures
        r == member(v@, c),
{
    let mut i: usize = 0;
    proof {
        assert(v@.skip(0) =~= v@);
    }
    while i < v.len()
        invariant
            i <= v@.len(),
            member(v@, c) == member(v@.skip(i as int), c),
        decreases v@.len() - i,
    {
        proof {
            assert(v@.skip(i as int)[0] == v@[i as int]);
            assert(v@.skip(i as int).skip(1) =~= v@.skip(i as int + 1));
        }
        if v[i] == c {
            return true;
        }
        i += 1;
    }
    false
}

/// The connection list without `c`, in a fresh `Vec`.
fn keep_conns(v: &Vec<ConnId>, c: ConnId) -> (r: Vec<ConnId>)
    ensures
        r@ == drop_id(v@, c),
{
    let ghost s = v@;
    let mut r: Vec<ConnId> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(s.skip(0) =~= s);
        assert(r@ + drop_id(s, c) =~= drop_id(s, c));
    }
    while i < v.len()
        invariant
            s == v@,
            i <= v@.len(),
            r@ + drop_id(s.skip(i as int), c) == drop_id(s, c),
        decreases v@.len() - i,
    {
        let ghost r0 = r@;
        proof {
            assert(s.skip(i as int)[0] == s[i as int]);
            assert(s.skip(i as int).skip(1) =~= s.skip(i as int + 1));
        }
        if v[i] != c {
            r.push(v[i]);
            proof {
                assert(r0.push(s[i as int]) + drop_id(s.skip(i as int + 1), c) =~= r0 + (seq![
                    s[i as int],
                ] + drop_id(s.skip(i as int + 1), c)));
            }
        }
        i += 1;
    }
    proof {
        assert(s.skip(i as int) =~= Seq::<ConnId>::empty());
        assert(r@ + Seq::<ConnId>::empty() =~= r@);
    }
    r
}

impl CidTable {
    pub open spec fn wf(&self) -> bool {
        table_wf(self@)
    }

    pub fn new() -> (r: CidTable)
        ensures
            r.wf(),
            r@.cids.len() == 0,
            r@.tokens.len() == 0,
            r@.conns.len() == 0,
    {
        let r = CidTable { cids: Vec::new(), tokens: Vec::new(), conns: Vec::new() };
        assert(r@.cids =~= Seq::<(Seq<u8>, ConnId)>::empty());
        assert(r@.tokens =~= Seq::<(Seq<u8>, ConnId)>::empty());
        r
    }

    /// Applies connection `c`'s update; `false` (table unchanged) when an added key is
    /// already present for any connection, `c` is at its cap (`add_cid`) or a token list is
    /// full, or a removed key is not `c`'s.
    pub fn apply(&mut self, c: ConnId, u: &CidUpdate) -> (ok: bool)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            match u {
                CidUpdate::Add(k) => add_cid(old(self)@, final(self)@, c, k@, ok),
                CidUpdate::Remove(k) => final(self)@.conns == old(self)@.conns && final(self)@.tokens == old(self)@.tokens && list_update(
                    old(self)@.cids,
                    final(self)@.cids,
                    c,
                    k@,
                    false,
                    MAX_TABLE as nat,
                    ok,
                ),
                CidUpdate::AddToken(t) => final(self)@.conns == old(self)@.conns && final(self)@.cids == old(self)@.cids && list_update(
                    old(self)@.tokens,
                    final(self)@.tokens,
                    c,
                    t@,
                    true,
                    MAX_TOKENS as nat,
                    ok,
                ),
                CidUpdate::RemoveToken(t) => final(self)@.conns == old(self)@.conns && final(self)@.cids == old(self)@.cids && list_update(
                    old(self)@.tokens,
                    final(self)@.tokens,
                    c,
                    t@,
                    false,
                    MAX_TOKENS as nat,
                    ok,
                ),
            },
    {
        let ghost s = old(self)@;
        match u {
            CidUpdate::Add(k) => {
                if cid_index(&self.cids, k.as_slice()).is_some() || conn_count(&self.cids, c)
                    >= PER_CONN {
                    return false;
                }
                if !conn_member(&self.conns, c) {
                    if self.conns.len() >= MAX_CONNS {
                        return false;
                    }
                    self.conns.push(c);
                }
                self.cids.push((slice_to_vec(k.as_slice()), c));
                proof {
                    assert(self@.cids =~= s.cids.push((k@, c)));
                    lemma_unique_push(s.cids, (k@, c));
                    assert forall|c2: ConnId| #[trigger] count_of(self@.cids, c2) <= PER_CONN && (
                    count_of(self@.cids, c2) > 0 ==> member(self@.conns, c2)) by {
                        lemma_count_push(s.cids, (k@, c), c2);
                        lemma_member_push(s.conns, c, c2);
                    }
                    lemma_len_bound(self@.cids, self@.conns);
                    assert(self@.conns.len() * PER_CONN <= MAX_TABLE) by (nonlinear_arith)
                        requires
                            self@.conns.len() <= MAX_CONNS,
                    ;
                }
                true
            },
            CidUpdate::Remove(k) => {
                match cid_index(&self.cids, k.as_slice()) {
                    Some(i) => {
                        if self.cids[i].1 != c {
                            return false;
                        }
                        let _ = self.cids.remove(i);
                        proof {
                            assert(self@.cids =~= s.cids.remove(i as int));
                            lemma_remove_first(s.cids, k@, i as int);
                            assert forall|c2: ConnId| #[trigger] count_of(self@.cids, c2) <= count_of(
                                s.cids,
                                c2,
                            ) by {
                                lemma_count_remove(s.cids, i as int, c2);
                            }
                        }
                        true
                    },
                    None => false,
                }
            },
            CidUpdate::AddToken(t) => {
                if self.tokens.len() >= MAX_TOKENS || token_index(&self.tokens, t.as_slice()).is_some() {
                    return false;
                }
                self.tokens.push((*t, c));
                proof {
                    assert(self@.tokens =~= s.tokens.push((t@, c)));
                    lemma_unique_push(s.tokens, (t@, c));
                }
                true
            },
            CidUpdate::RemoveToken(t) => {
                match token_index(&self.tokens, t.as_slice()) {
                    Some(i) => {
                        if self.tokens[i].1 != c {
                            return false;
                        }
                        let _ = self.tokens.remove(i);
                        proof {
                            assert(self@.tokens =~= s.tokens.remove(i as int));
                            lemma_remove_first(s.tokens, t@, i as int);
                        }
                        true
                    },
                    None => false,
                }
            },
        }
    }

    /// Drops connection `c` and every entry it owns, rebuilding each list once.
    pub fn remove_conn(&mut self, c: ConnId)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self)@.cids == drop_conn(old(self)@.cids, c),
            final(self)@.tokens == drop_conn(old(self)@.tokens, c),
            final(self)@.conns == drop_id(old(self)@.conns, c),
    {
        let ghost s = old(self)@;
        self.cids = keep_cids(&self.cids, c);
        self.tokens = keep_tokens(&self.tokens, c);
        self.conns = keep_conns(&self.conns, c);
        proof {
            lemma_drop_unique(s.cids, c);
            lemma_drop_unique(s.tokens, c);
            lemma_member_drop(s.conns, c, c);
            assert forall|c2: ConnId| #[trigger] count_of(self@.cids, c2) <= PER_CONN && (count_of(
                self@.cids,
                c2,
            ) > 0 ==> member(self@.conns, c2)) by {
                lemma_count_drop(s.cids, c, c2);
                lemma_member_drop(s.conns, c, c2);
            }
        }
    }

    pub fn lookup(&self, cid: &[u8]) -> (r: Option<ConnId>)
        ensures
            r == find_key(self@.cids, cid@),
    {
        match cid_index(&self.cids, cid) {
            Some(i) => Some(self.cids[i].1),
            None => None,
        }
    }

    /// The connection whose peer reset token is `tail`.
    pub fn reset_owner(&self, tail: &[u8]) -> (r: Option<ConnId>)
        ensures
            r == find_key(self@.tokens, tail@),
    {
        if tail.len() != RESET_TOKEN_LEN {
            proof {
                assert forall|j: int| 0 <= j < self@.tokens.len() implies (
                #[trigger] self@.tokens[j]).0.len() == 16 by {
                    assert(self@.tokens[j].0 == self.tokens@[j].0@);
                }
                lemma_find_none_len(self@.tokens, tail@);
            }
            return None;
        }
        match token_index(&self.tokens, tail) {
            Some(i) => Some(self.tokens[i].1),
            None => None,
        }
    }

    #[verifier::when_used_as_spec(has_room_spec)]
    pub fn has_room(&self) -> (r: bool)
        ensures
            r == table_room(self@),
    {
        self.conns.len() < MAX_CONNS
    }

    pub open spec fn has_room_spec(&self) -> bool {
        table_room(self@)
    }
}

/// Every key in the token list is 16 bytes, so a key of another length is absent.
proof fn lemma_find_none_len(s: Seq<(Seq<u8>, ConnId)>, k: Seq<u8>)
    requires
        k.len() != 16,
        forall|j: int| 0 <= j < s.len() ==> (#[trigger] s[j]).0.len() == 16,
    ensures
        find_key(s, k) is None,
    decreases s.len(),
{
    if s.len() > 0 {
        let t = s.skip(1);
        assert forall|j: int| 0 <= j < t.len() implies (#[trigger] t[j]).0.len() == 16 by {
            assert(t[j] == s[j + 1]);
        }
        lemma_find_none_len(t, k);
    }
}

/// Where `datagram` goes. 3e calls `version_negotiation` only through here, so at most one
/// Version Negotiation packet answers a datagram (§17.2.1).
pub fn route(datagram: &[u8], table: &CidTable) -> (r: Route)
    ensures
        r@ == rfc_route(datagram@, table@),
{
    let h = parse_header(datagram, LOCAL_CID_LEN);
    let owner = match &h {
        Some(Header::Long { dcid, .. }) => table.lookup(dcid.as_slice()),
        Some(Header::Short { dcid, .. }) => table.lookup(dcid.as_slice()),
        _ => None,
    };
    if let Some(c) = owner {
        return Route::Existing(c);
    }
    if datagram.len() >= MIN_SHORT_PACKET {
        let tail = slice_subrange(datagram, datagram.len() - RESET_TOKEN_LEN, datagram.len());
        if let Some(c) = table.reset_owner(tail) {
            return Route::Reset(c);
        }
    }
    let opens = match &h {
        Some(Header::Long { ty: LongType::Initial, dcid, .. }) => datagram.len()
            >= MIN_INITIAL_DATAGRAM && 8 <= dcid.len() && table.has_room(),
        _ => false,
    };
    if opens {
        return Route::NewInitial;
    }
    if let Some(Header::UnsupportedVersion { .. }) = &h {
        if let Some(v) = version_negotiation(datagram) {
            return Route::VersionNegotiation(v);
        }
    }
    Route::Drop
}

} // verus!
const _: () = assert!(MAX_CONNS == MAX_TABLE / PER_CONN);

impl CidTable {
    /// Test support: the three lists' allocated capacities. Verus models `Vec` length, not
    /// capacity, so the release on `remove_conn` is checked by test only (TRUSTED.md).
    #[doc(hidden)]
    pub fn capacities(&self) -> (usize, usize, usize) {
        (self.cids.capacity(), self.tokens.capacity(), self.conns.capacity())
    }
}
