mod common;

use common::*;
use crypto::p256::p256_ecdh;
use crypto::sha256::sha256;
use tls::config::*;
use tls::flight::*;
use tls::schedule::*;
use tls::server::*;
use tls::server_msgs::*;

type Exts = Vec<(u16, Vec<u8>)>;

const R: [u8; 96] = [7u8; 96];
const TP: [u8; 2] = [1, 0];
const HRR: &str = "020000340303cf21ad74e59a6111be1d8c021e65b891c2a211167abb8c5e079e09e2c8a8339c00130100000c003300020017002b00020304";

fn p256() -> (u16, Vec<u8>) {
    (0x17, P256_SHARE.to_vec())
}

fn x25519() -> (u16, Vec<u8>) {
    (0x1d, X25519_SHARE.to_vec())
}

fn direct_ch() -> Vec<u8> {
    h3_ch(&[p256()], |_| {})
}

fn hrr_ch() -> Vec<u8> {
    h3_ch(&[x25519()], |_| {})
}

fn set(e: &mut Exts, ty: u16, d: Vec<u8>) {
    e.iter_mut().find(|(t, _)| *t == ty).expect("extension present").1 = d;
}

fn u16_list(xs: &[u16]) -> Vec<u8> {
    let n = 2 * xs.len();
    let mut v = vec![(n >> 8) as u8, n as u8];
    v.extend(xs.iter().flat_map(|x| x.to_be_bytes()));
    v
}

fn a2_tp() -> Vec<u8> {
    split_ch(A2_CH).1.into_iter().find(|(t, _)| *t == 0x39).unwrap().1
}

fn feed(hs: &mut ServerHandshake, level: Level, data: &[u8]) -> (Result<(), u64>, Vec<TlsEvent>) {
    let mut ev = Vec::new();
    let r = hs.on_crypto(level, data, &R, &mut ev);
    (r, ev)
}

fn kind(e: &TlsEvent) -> &'static str {
    match e {
        TlsEvent::PeerParams(_) => "PeerParams",
        TlsEvent::Send { level: Level::Initial, .. } => "Send(Initial)",
        TlsEvent::Send { level: Level::Handshake, .. } => "Send(Handshake)",
        TlsEvent::Send { level: Level::OneRtt, .. } => "Send(OneRtt)",
        TlsEvent::Secrets { level: Level::Handshake, .. } => "Secrets(Handshake)",
        TlsEvent::Secrets { level: Level::OneRtt, .. } => "Secrets(OneRtt)",
        TlsEvent::Secrets { level: Level::Initial, .. } => "Secrets(Initial)",
        TlsEvent::Complete => "Complete",
    }
}

fn check_flight(evs: &[TlsEvent]) {
    let kinds: Vec<_> = evs.iter().map(kind).collect();
    assert_eq!(
        kinds,
        ["PeerParams", "Send(Initial)", "Secrets(Handshake)", "Send(Handshake)", "Secrets(OneRtt)"]
    );
}

fn send(e: &TlsEvent) -> Vec<u8> {
    match e {
        TlsEvent::Send { data, .. } => data.clone(),
        other => panic!("not Send: {other:?}"),
    }
}

/// The client Finished for a flight `evs`, where `t0` is the transcript up to the ClientHello.
fn fin_for(evs: &[TlsEvent], t0: &[u8]) -> Vec<u8> {
    let client = match &evs[2] {
        TlsEvent::Secrets { level: Level::Handshake, client, .. } => *client,
        other => panic!("not Secrets(Handshake): {other:?}"),
    };
    let th = sha256(&[t0, &send(&evs[1]), &send(&evs[3])].concat());
    let mut m = Vec::new();
    serialize_finished(&verify_data(&client, &th), &mut m);
    m
}

/// A handshake after `direct_ch`'s flight, with the client Finished to send.
fn waiting(cfg: &ServerConfig) -> (ServerHandshake<'_>, Vec<TlsEvent>, Vec<u8>) {
    let mut hs = ServerHandshake::new(cfg, TP.to_vec());
    let (r, ev) = feed(&mut hs, Level::Initial, &direct_ch());
    assert_eq!(r, Ok(()));
    check_flight(&ev);
    let fin = fin_for(&ev, &direct_ch());
    (hs, ev, fin)
}

fn complete(cfg: &ServerConfig) -> ServerHandshake<'_> {
    let (mut hs, _, fin) = waiting(cfg);
    assert_eq!(feed(&mut hs, Level::Handshake, &fin), (Ok(()), vec![TlsEvent::Complete]));
    assert!(hs.is_complete());
    hs
}

/// A handshake that has answered `hrr_ch` with the HelloRetryRequest.
fn after_hrr(cfg: &ServerConfig) -> ServerHandshake<'_> {
    let mut hs = ServerHandshake::new(cfg, TP.to_vec());
    let (r, ev) = feed(&mut hs, Level::Initial, &hrr_ch());
    assert_eq!(r, Ok(()));
    assert_eq!(ev, vec![TlsEvent::Send { level: Level::Initial, data: hex(HRR) }]);
    hs
}

#[test]
fn a2_ch_0x178() {
    let cfg = ecdsa_cfg();
    let mut hs = ServerHandshake::new(&cfg, TP.to_vec());
    assert_eq!(feed(&mut hs, Level::Initial, A2_CH), (Err(0x178), vec![]));
    for level in [Level::Initial, Level::Handshake, Level::OneRtt] {
        assert_eq!(feed(&mut hs, level, &[1]), (Err(0x178), vec![]));
    }
}

#[test]
fn curl_ch_hrr() {
    let cfg = ecdsa_cfg();
    let mut hs = ServerHandshake::new(&cfg, TP.to_vec());
    assert_eq!(feed(&mut hs, Level::Initial, &CURL_CH[..1200]), (Ok(()), vec![]));
    let (r, ev) = feed(&mut hs, Level::Initial, &CURL_CH[1200..]);
    assert_eq!(r, Ok(()));
    assert_eq!(ev, vec![TlsEvent::Send { level: Level::Initial, data: hex(HRR) }]);
    assert_eq!(send(&ev[0]).len(), 56);
    assert!(!hs.pending(Level::Initial));
}

#[test]
fn direct_p256() {
    let cfg = ecdsa_cfg();
    let (mut hs, ev, fin) = waiting(&cfg);
    assert_eq!(ev[0], TlsEvent::PeerParams(a2_tp()));
    assert_eq!(a2_tp().len(), 50);
    assert_eq!(&send(&ev[1])[6..38], &R[..32]);
    assert!(!hs.is_complete());
    assert_eq!(feed(&mut hs, Level::Handshake, &fin), (Ok(()), vec![TlsEvent::Complete]));
    assert!(hs.is_complete());
    assert!(!hs.pending(Level::Initial) && !hs.pending(Level::Handshake));
}

#[test]
fn hrr_then_ch2() {
    let cfg = ecdsa_cfg();
    let mut hs = after_hrr(&cfg);
    let ch2 = direct_ch();
    let (r, ev) = feed(&mut hs, Level::Initial, &ch2);
    assert_eq!(r, Ok(()));
    check_flight(&ev);
    let t0 = [&message_hash(&hrr_ch())[..], &hex(HRR), &ch2].concat();
    let z = p256_ecdh(&R[32..64], P256_SHARE).unwrap();
    let want = handshake_secrets(&z, &sha256(&[&t0[..], &send(&ev[1])].concat()));
    assert_eq!(
        ev[2],
        TlsEvent::Secrets { level: Level::Handshake, client: want.client, server: want.server }
    );
    let fin = fin_for(&ev, &t0);
    assert_eq!(feed(&mut hs, Level::Handshake, &fin), (Ok(()), vec![TlsEvent::Complete]));
    assert!(hs.is_complete());
}

fn bad_ch2s() -> Vec<Vec<u8>> {
    let (_, exts) = split_ch(&direct_ch());
    let mut random = direct_ch();
    random[6] ^= 1;
    vec![
        h3_ch(&[p256(), p256()], |_| {}),
        join_ch(&head(0x0303, &[], &[0x1302], &[0]), &exts),
        h3_ch(&[p256()], |e| set(e, 0x10, vec![0, 9, 2, b'h', b'3', 5, b'h', b'3', b'-', b'2', b'9'])),
        random,
        hrr_ch(),
        h3_ch(&[], |_| {}),
        h3_ch(&[p256()], |e| set(e, 0x39, vec![1, 1, 7])),
    ]
}

#[test]
fn ch2_rules() {
    let cfg = ecdsa_cfg();
    for (i, ch2) in bad_ch2s().iter().enumerate() {
        let mut hs = after_hrr(&cfg);
        assert_eq!(feed(&mut hs, Level::Initial, ch2), (Err(0x12f), vec![]), "case {i}");
    }
}

#[test]
fn ch_at_wrong_time() {
    let cfg = ecdsa_cfg();
    let (mut hs, _, _) = waiting(&cfg);
    assert_eq!(feed(&mut hs, Level::Initial, &direct_ch()), (Err(0x10a), vec![]));
    let mut hs = complete(&cfg);
    assert_eq!(feed(&mut hs, Level::Initial, &direct_ch()), (Err(0x10a), vec![]));
}

#[test]
fn finished_checks() {
    let cfg = ecdsa_cfg();
    let (mut hs, _, mut fin) = waiting(&cfg);
    fin[10] ^= 0x80;
    assert_eq!(feed(&mut hs, Level::Handshake, &fin), (Err(0x133), vec![]));
    assert!(!hs.is_complete());
    let (mut hs, _, fin) = waiting(&cfg);
    let short = [&[0x14, 0, 0, 0x1f][..], &fin[4..35]].concat();
    assert_eq!(feed(&mut hs, Level::Handshake, &short), (Err(0x132), vec![]));
    let (mut hs, _, _) = waiting(&cfg);
    assert_eq!(feed(&mut hs, Level::Handshake, &[0x02, 0, 0, 0]), (Err(0x10a), vec![]));
}

#[test]
fn key_update() {
    let cfg = ecdsa_cfg();
    let ku = [0x18, 0, 0, 1, 0];
    let (mut hs, _, _) = waiting(&cfg);
    assert_eq!(feed(&mut hs, Level::Handshake, &ku), (Err(0x10a), vec![]));
    let mut hs = complete(&cfg);
    assert_eq!(feed(&mut hs, Level::OneRtt, &[]), (Ok(()), vec![]));
    assert_eq!(feed(&mut hs, Level::OneRtt, &ku), (Err(0x10a), vec![]));
}

#[test]
fn finished_coalesced() {
    let cfg = ecdsa_cfg();
    let (mut hs, _, fin) = waiting(&cfg);
    let both = [&fin[..], &[0x14]].concat();
    assert_eq!(feed(&mut hs, Level::Handshake, &both), (Ok(()), vec![TlsEvent::Complete]));
    assert!(hs.is_complete());
    assert!(hs.pending(Level::Handshake));
    let mut hs = complete(&cfg);
    assert_eq!(feed(&mut hs, Level::Handshake, &[0x14]), (Err(0x10a), vec![]));
}

#[test]
fn leftover_initial() {
    let cfg = ecdsa_cfg();
    let mut hs = ServerHandshake::new(&cfg, TP.to_vec());
    let (r, ev) = feed(&mut hs, Level::Initial, &[&direct_ch()[..], &[0x01]].concat());
    assert_eq!(r, Ok(()));
    check_flight(&ev);
    assert!(hs.pending(Level::Initial));
    assert!(!hs.pending(Level::Handshake));
    assert!(!hs.pending(Level::OneRtt));
}

#[test]
fn failed_absorbs() {
    let cfg = ecdsa_cfg();
    let mut hs = after_hrr(&cfg);
    let mut ev = vec![TlsEvent::Complete];
    assert_eq!(hs.on_crypto(Level::Initial, &bad_ch2s()[0], &R, &mut ev), Err(0x12f));
    assert_eq!(hs.on_crypto(Level::Initial, &direct_ch(), &R, &mut ev), Err(0x12f));
    assert_eq!(ev, vec![TlsEvent::Complete]);
    assert!(!hs.is_complete());
}

#[test]
fn doomed_ch1() {
    let ecdsa = ecdsa_cfg();
    let rsa = rsa_cfg();
    let cases: [(&ServerConfig, Vec<u8>, u64); 4] = [
        (&rsa, h3_ch(&[x25519()], |e| set(e, 0x0d, u16_list(&[0x0403]))), 0x128),
        (&ecdsa, h3_ch(&[x25519()], |e| set(e, 0x10, vec![0, 6, 5, b'h', b'3', b'-', b'2', b'9'])), 0x178),
        (&ecdsa, join_ch(&head(0x0303, &[], &[0x1302], &[0]), &split_ch(&hrr_ch()).1), 0x128),
        (&ecdsa, h3_ch(&[p256()], |e| set(e, 0x0a, u16_list(&[0x1d]))), 0x128),
    ];
    for (i, (cfg, ch, want)) in cases.iter().enumerate() {
        let mut hs = ServerHandshake::new(cfg, TP.to_vec());
        assert_eq!(feed(&mut hs, Level::Initial, ch), (Err(*want), vec![]), "case {i}");
    }
}

#[test]
fn reader_bound() {
    let cfg = ecdsa_cfg();
    let mut hs = ServerHandshake::new(&cfg, TP.to_vec());
    assert_eq!(feed(&mut hs, Level::Initial, &[1, 0x01, 0x00, 0x01]), (Err(0x0d), vec![]));
    assert_eq!(feed(&mut hs, Level::Initial, &[0; 8]), (Err(0x0d), vec![]));
    let (mut hs, _, _) = waiting(&cfg);
    assert!(!hs.pending(Level::Initial));
    assert_eq!(feed(&mut hs, Level::Initial, &[0x01]), (Err(0x10a), vec![]));
    assert!(!hs.pending(Level::Initial));
}
