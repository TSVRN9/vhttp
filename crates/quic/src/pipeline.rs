//! The receive and send pipelines between the wire and `Connection` (3e): `accept_datagram`
//! and `receive` open a datagram (`open_datagram`) and hand its packets to the connection,
//! closing it on a connection error; `transmit` protects what `poll_transmit` returns
//! (`protect_datagram`). Verified glue, so `plain_wf`, `close`'s code bound and `protect`'s
//! precondition are discharged here and the shell calls only fns whose `requires` is `wf()`.
//! The 1-RTT keys are masked until the handshake completes (RFC 9001 §5.7); `refeed_one_rtt`
//! then opens the 1-RTT packet of the datagram that completed it.
use vstd::prelude::*;

use crate::aead::*;
use crate::cid::{eq_bytes, LOCAL_CID_LEN};
use crate::conn::*;
use crate::datagram::*;
use crate::header::*;
use crate::lifecycle::Phase;
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
/// packets. The accepting packet's DCID must be the first header's, `initial_dcid(d)`, which the
/// caller's Initial keys come from: then the odcid is the keys' DCID.
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
        r is Some ==> rfc_long_header(d@) matches Some(SpecHeader::Long { ty: LongType::Initial, .. }),
        r matches Some(c) ==> !c.peer_tp_known_spec(),
        r matches Some(c) ==> (c.phase_spec() is Open && c.live(PacketKind::Initial) ==> c.crypto_base_spec(PacketKind::Initial) == 0),
        r matches Some(c) ==> (c.phase_spec() is Open && c.live(PacketKind::Handshake) ==> c.crypto_base_spec(PacketKind::Handshake) == 0),
{
    hide(rfc_open_datagram);
    let dcid = match initial_dcid(d) {
        Some(x) => x,
        None => return None,
    };
    let rx = open_first(d, keys);
    let p = if rx.packets.len() > 0 {
        &rx.packets[0]
    } else {
        match &rx.error {
            Some((_, h)) => h,
            None => return None,
        }
    };
    if !eq_bytes(p.dcid.as_slice(), dcid.as_slice()) {
        return None;
    }
    let mut c = match Connection::accept(p, d.len(), path, now, rand, local_tp) {
        Some(c) => c,
        None => return None,
    };
    proof {
        assert(c.odcid_spec() == dcid@);
    }
    let ghost c0 = c;
    c.on_datagram(path, d.len(), rx.packets, rx.error, now, rand);
    proof {
        Connection::lemma_crypto_kept_elim(c, c0);
    }
    Some(c)
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-14
//# Therefore, an endpoint MUST NOT close a connection
//# when it receives a datagram that does not meet size constraints; the
//# endpoint MAY discard such datagrams.
/// A datagram for `c`: always counted by `on_datagram`, even with no packet in it (§8.1); a
/// connection error closes `c` if its header passes the gate a packet would; a first packet
/// that did not decrypt makes the last 16 bytes a stateless reset candidate (§10.3.1).
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
        // §8.1: counted on a known path, whatever decrypted.
        old(c).has_path(path) && !(old(c).phase_spec() is Draining) && !(old(c).phase_spec() is Closed)
            ==> recv_counted(old(c).amp_trace(path), final(c).amp_trace(path), d.len() as nat),
        final(c).crypto_kept(*old(c)),
{
    hide(rfc_open_datagram);
    let rx = open_for(c, d, keys);
    c.on_datagram(path, d.len(), rx.packets, rx.error, now, rand);
    if let Some(tail) = rx.reset_tail {
        let ghost c1 = *c;
        c.on_reset_candidate(&tail, now);
        proof {
            Connection::lemma_crypto_kept_trans(*old(c), c1, *c);
        }
    }
}

/// Whether every packet of `rx`, and its error's header, has Destination Connection ID `dcid`.
fn all_to(rx: &Rx, dcid: &[u8]) -> bool {
    let mut i: usize = 0;
    while i < rx.packets.len()
        decreases rx.packets.len() - i,
    {
        if !eq_bytes(rx.packets[i].dcid.as_slice(), dcid) {
            return false;
        }
        i += 1;
    }
    match &rx.error {
        Some((_, h)) => eq_bytes(h.dcid.as_slice(), dcid),
        None => true,
    }
}

//= https://www.rfc-editor.org/rfc/rfc9001#section-5.7
//# Received
//# packets protected with 1-RTT keys MAY be stored and later decrypted
//# and used once the handshake is complete.
//
//= https://www.rfc-editor.org/rfc/rfc9000#section-12.2
//# Receivers
//# SHOULD ignore any subsequent packets with a different Destination
//# Connection ID than the first packet in the datagram.
//
//= https://www.rfc-editor.org/rfc/rfc9001#section-5.7
//= type=exception
//= reason=Binds clients; the server's half is gate_keys (3e) and conn.rs's 1-RTT gate.
//# Even if it has 1-RTT secrets, a client MUST NOT
//# process incoming 1-RTT protected packets before the TLS handshake is
//# complete.
/// The datagram `d` again, once the handshake is complete: `receive` dropped its 1-RTT packet
/// unopened, and TLS has since completed on the Finished in front of it. Only the 1-RTT packet
/// can open, and it is processed only if it, and any error, has the first header's DCID. The
/// datagram was already counted (§8.1), so it counts 0 bytes; its reset tail was the first
/// pass's to handle. Only an open connection is refed.
#[verifier::spinoff_prover]
pub fn refeed_one_rtt(
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
        !old(c).live(PacketKind::OneRtt) ==> *final(c) == *old(c),
        !(old(c).phase_spec() is Open) ==> *final(c) == *old(c),
        final(c).crypto_kept(*old(c)),
{
    hide(rfc_open_datagram);
    proof {
        Connection::lemma_crypto_kept_refl(*c);
    }
    if !c.handshake_complete() {
        return;
    }
    // In Closing, `on_datagram` would count the datagram again as a closing-state arrival and
    // owe one more CONNECTION_CLOSE.
    if !matches!(c.phase(), Phase::Open) {
        return;
    }
    let first = match parse_header(d, LOCAL_CID_LEN) {
        Some(Header::Long { dcid, .. }) => dcid,
        Some(Header::Short { dcid, .. }) => dcid,
        Some(Header::UnsupportedVersion { dcid, .. }) => dcid,
        None => return,
    };
    let rx = open_for(c, d, &[None, None, keys[2]]);
    if all_to(&rx, first.as_slice()) {
        c.on_datagram(path, 0, rx.packets, rx.error, now, rand);
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
        final(c).crypto_kept(*old(c)),
        drained_kept(*final(c), *old(c)),
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
