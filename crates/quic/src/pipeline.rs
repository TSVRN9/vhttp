//! The receive and send pipelines between the wire and `Connection` (3e): `accept_datagram`
//! and `receive` open a datagram (`open_datagram`) and hand its packets to the connection,
//! closing it on a connection error; `transmit` protects what `poll_transmit` returns
//! (`protect_datagram`). Verified glue, so `plain_wf`, `close`'s code bound and `protect`'s
//! precondition are discharged here and the shell calls only fns whose `requires` is `wf()`.
//! The 1-RTT keys are masked until the handshake completes (RFC 9001 §5.7).
use vstd::prelude::*;

use crate::aead::*;
use crate::conn::*;
use crate::datagram::*;
use crate::header::*;
use crate::payload::PacketKind;
use crate::protect::*;
use crate::route::CidUpdate;
use crate::tp::TransportParams;
#[allow(unused_imports)]
use wire::varint::*;

verus! {

/// The receive keys `open_datagram` gets: no 1-RTT keys before the handshake completes.
pub open spec fn rx_keys(keys: Seq<Option<SpecKeyPair>>, complete: bool) -> Seq<Option<SpecKeyPair>> {
    if complete {
        keys
    } else {
        keys.update(2, None)
    }
}

//= https://www.rfc-editor.org/rfc/rfc9001#section-5.7
//# Endpoints in either role MUST NOT decrypt 1-RTT packets from
//# their peer prior to completing the handshake.
/// `keys` with the 1-RTT slot emptied unless `complete`, whatever keys the caller holds.
fn gate_keys(keys: &[Option<KeyPair>; 3], complete: bool) -> (r: [Option<KeyPair>; 3])
    ensures
        r.deep_view() == rx_keys(keys.deep_view(), complete),
{
    let r = if complete {
        [keys[0], keys[1], keys[2]]
    } else {
        [keys[0], keys[1], None]
    };
    assert(r.deep_view() =~= rx_keys(keys.deep_view(), complete));
    r
}

/// The datagram opened for `c`: its receive keys gated on `c`'s handshake, packet numbers
/// decoded against `c`'s largest in each space.
#[verifier::spinoff_prover]
fn open_for(c: &Connection, d: &[u8], keys: &[Option<KeyPair>; 3]) -> (rx: Rx)
    ensures
        rx@ == rfc_open_datagram(
            d@,
            rx_keys(keys.deep_view(), c.live(PacketKind::OneRtt)),
            seq![
                c.recv(PacketKind::Initial).largest_spec(),
                c.recv(PacketKind::Handshake).largest_spec(),
                c.recv(PacketKind::OneRtt).largest_spec(),
            ],
        ),
        forall|i: int| 0 <= i < rx.packets.len() ==> plain_wf(#[trigger] rx.packets@[i]@),
        rx.error matches Some((e, h)) ==> e <= VARINT_MAX && plain_wf(h@),
{
    hide(rfc_open_datagram);
    let largest = [
        c.largest_pn(PacketKind::Initial),
        c.largest_pn(PacketKind::Handshake),
        c.largest_pn(PacketKind::OneRtt),
    ];
    let gk = gate_keys(keys, c.handshake_complete());
    let rx = open_datagram(d, &gk, &largest);
    assert(largest@ =~= seq![
        c.recv(PacketKind::Initial).largest_spec(),
        c.recv(PacketKind::Handshake).largest_spec(),
        c.recv(PacketKind::OneRtt).largest_spec(),
    ]);
    rx
}

/// The datagram that may create a connection, opened with no 1-RTT keys and no largest packet
/// number in any space.
#[verifier::spinoff_prover]
fn open_first(d: &[u8], keys: &[Option<KeyPair>; 3]) -> (rx: Rx)
    ensures
        rx@ == rfc_open_datagram(d@, rx_keys(keys.deep_view(), false), seq![None, None, None]),
        forall|i: int| 0 <= i < rx.packets.len() ==> plain_wf(#[trigger] rx.packets@[i]@),
        rx.error matches Some((e, h)) ==> e <= VARINT_MAX && plain_wf(h@),
{
    hide(rfc_open_datagram);
    let none = [None, None, None];
    let gk = gate_keys(keys, false);
    let rx = open_datagram(d, &gk, &none);
    assert(none@ =~= seq![None::<u64>, None, None]);
    rx
}

/// The Destination Connection ID of a client Initial: what the shell looks keys up by for
/// `Route::NewInitial`.
pub fn initial_dcid(d: &[u8]) -> (r: Option<Vec<u8>>)
    ensures
        match r {
            Some(c) => rfc_long_header(d@) matches Some(SpecHeader::Long { ty: LongType::Initial, dcid, .. })
                && dcid == c@,
            None => !(rfc_long_header(d@) matches Some(SpecHeader::Long { ty: LongType::Initial, .. })),
        },
{
    match parse_long_header(d) {
        Some(Header::Long { ty: LongType::Initial, dcid, .. }) => Some(dcid),
        _ => None,
    }
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-14
//# Therefore, an endpoint MUST NOT close a connection
//# when it receives a datagram that does not meet size constraints; the
//# endpoint MAY discard such datagrams.
/// A connection for the client Initial `d`, or None when nothing in `d` decrypted (no state is
/// kept) or `Connection::accept` refuses it (§14.1: under 1200 bytes). The whole datagram is
/// counted before a connection error on its first packet closes it (Decision 5); `on_datagram`
/// closes only for an error whose header passes the gate a packet would, so sizes only drop
/// packets.
#[verifier::spinoff_prover]
pub fn accept_datagram(
    d: &[u8],
    path: PathId,
    now: u64,
    rand: &[u8; RAND_LEN],
    local_tp: &TransportParams,
    keys: &[Option<KeyPair>; 3],
) -> (r: Option<Connection>)
    ensures
        r matches Some(c) ==> c.wf(),
{
    let rx = open_first(d, keys);
    let first = if rx.packets.len() > 0 {
        Connection::accept(&rx.packets[0], d.len(), path, now, rand, local_tp)
    } else {
        match &rx.error {
            Some((_, h)) => Connection::accept(h, d.len(), path, now, rand, local_tp),
            None => None,
        }
    };
    let mut c = match first {
        Some(c) => c,
        None => return None,
    };
    c.on_datagram(path, d.len(), rx.packets, rx.error, now, rand);
    Some(c)
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-14
//# Therefore, an endpoint MUST NOT close a connection
//# when it receives a datagram that does not meet size constraints; the
//# endpoint MAY discard such datagrams.
/// A datagram for `c`: always counted by `on_datagram`, even with no packet in it (§8.1); a
/// connection error closes `c` if its header passes the gate a packet would; a first packet that did not decrypt makes the last 16 bytes a
/// stateless reset candidate (§10.3.1).
#[verifier::spinoff_prover]
pub fn receive(
    c: &mut Connection,
    d: &[u8],
    path: PathId,
    now: u64,
    rand: &[u8; RAND_LEN],
    keys: &[Option<KeyPair>; 3],
)
    requires
        old(c).wf(),
    ensures
        final(c).wf(),
        final(c).out_log() == old(c).out_log(),
{
    let rx = open_for(c, d, keys);
    c.on_datagram(path, d.len(), rx.packets, rx.error, now, rand);
    if let Some(tail) = rx.reset_tail {
        c.on_reset_candidate(&tail, now);
    }
}

/// Clears `out`, then protects the next datagram `poll_transmit` gives into it and returns its
/// path. A `Some` with an empty `out` means no packet had keys: send nothing, poll again.
#[verifier::spinoff_prover]
pub fn transmit(c: &mut Connection, now: u64, keys: &[Option<KeyPair>; 3], out: &mut Vec<u8>) -> (r:
    Option<PathId>)
    requires
        old(c).wf(),
    ensures
        final(c).wf(),
        r matches Some(q) ==> {
            let l = final(c).out_log().last();
            &&& final(c).out_log() == old(c).out_log().push(l)
            &&& l.path == q
            &&& final(out)@ == rfc_protect_datagram(l, keys.deep_view())
            &&& final(out)@.len() <= out_datagram_len(l) <= MAX_DATAGRAM
            &&& transmit_ok(*old(c), *final(c), l)
        },
        r is None ==> final(out)@ == Seq::<u8>::empty() && final(c).out_log() == old(c).out_log()
            && final(c).acks_later(now),
        now < u64::MAX && old(c).timers_later(now) ==> final(c).timers_later(now),
{
    out.clear();
    let d = match c.poll_transmit(now) {
        Some(d) => d,
        None => return None,
    };
    proof {
        assert forall|i: int| 0 <= i < d@.packets.len() implies protect_ok(#[trigger] d@.packets[i]) by {
            lemma_wf_protect_ok(d@.packets[i], c.sent(d@.packets[i].kind).largest_acked_spec());
        }
    }
    protect_datagram(&d, keys, out);
    assert(out@ =~= rfc_protect_datagram(d@, keys.deep_view()));
    Some(d.path)
}

/// The shell's wake sequence for one connection: `on_timeout(now)`, `poll_cid_updates`, then
/// `transmit` until None; every timer is then later than `now`, so sleeping until
/// `next_timeout` cannot spin. Never called: its contract is the proof. That the loop ends is
/// not proved, so it stops at `cap` as the shell does, and says nothing then.
#[verifier::spinoff_prover]
#[allow(dead_code)]
fn settled_later(
    c: &mut Connection,
    now: u64,
    rand: &[u8; RAND_LEN],
    keys: &[Option<KeyPair>; 3],
    out: &mut Vec<u8>,
    cap: usize,
) -> (r: Option<Option<u64>>)
    requires
        old(c).wf(),
        now < u64::MAX,
    ensures
        r matches Some(t) ==> later(t, now),
{
    c.on_timeout(now, rand);
    let ghost c1 = *c;
    let mut v: Vec<CidUpdate> = Vec::new();
    c.poll_cid_updates(&mut v);
    proof {
        c.lemma_keeps_elim(c1, now);
    }
    let mut i: usize = 0;
    while i < cap
        invariant
            c.wf(),
            now < u64::MAX,
            c.timers_later(now),
        decreases cap - i,
    {
        if transmit(c, now, keys, out).is_none() {
            return Some(c.next_timeout());
        }
        i += 1;
    }
    None
}

} // verus!
