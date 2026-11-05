//! Phase 4c Task 4: the QUIC-TLS glue against rustls 0.23.45 (ring) as a real QUIC client, in
//! memory (RFC 9001 §4.1.2, §4.1.3, §4.6.2, §4.8, §4.9.1, §4.9.2, §8.3).
#![allow(dead_code, non_snake_case)]
#[path = "../../quic/tests/common/mod.rs"]
mod qc;
#[path = "../../tls/tests/common/mod.rs"]
mod tc;

use quic::aead::{open_packet, KeyPair};
use quic::datagram::OutPacket;
use quic::frame::{parse_frame_body, parse_frame_type, Frame};
use quic::header::{parse_header, Header, LongType};
use quic::hp::remove_hp;
use quic::lifecycle::Phase;
use quic::payload::PacketKind;
use quic::pn::decode_pn;
use quic::protect::protect;
use quictls::keys::{initial_keys, packet_keys};
use quictls::server::*;
use rustls::client::danger::{HandshakeSignatureValid, ServerCertVerified, ServerCertVerifier};
use rustls::crypto::ring::{default_provider, kx_group};
use rustls::crypto::WebPkiSupportedAlgorithms;
use rustls::pki_types::{CertificateDer, ServerName, UnixTime};
use rustls::quic::{ClientConnection, KeyChange, Version};
use rustls::{DigitallySignedStruct, SignatureScheme};
use std::sync::{Arc, Mutex, OnceLock};
use tls::config::ServerConfig;
use tls::flight::Level;

const NOW: u64 = 10;

fn cfg() -> &'static ServerConfig {
    static C: OnceLock<ServerConfig> = OnceLock::new();
    C.get_or_init(tc::ecdsa_cfg)
}

fn R(n: u8) -> Rand {
    Rand { conn: qc::rnd(n), refeed: qc::rnd(n + 50), complete: qc::rnd(n + 100), tls: [n; 96] }
}

// ---------------------------------------------------------------------------------------------
// rustls as a client (copied from crates/tls/tests/rustls_e2e.rs)
// ---------------------------------------------------------------------------------------------

#[derive(Debug, Default)]
struct Log(Mutex<Vec<(String, Vec<u8>)>>);

impl rustls::KeyLog for Log {
    fn log(&self, label: &str, _client_random: &[u8], secret: &[u8]) {
        self.0.lock().unwrap().push((label.to_string(), secret.to_vec()));
    }
}

impl Log {
    fn get(&self, label: &str) -> [u8; 32] {
        let v = self.0.lock().unwrap();
        let hits: Vec<_> = v.iter().filter(|(l, _)| l == label).collect();
        assert_eq!(hits.len(), 1, "{label}");
        hits[0].1.clone().try_into().unwrap()
    }
}

/// Test-only: no path validation (the chain is opaque DER), but the CertificateVerify signature
/// really is checked, with ring.
#[derive(Debug)]
struct Verifier {
    schemes: Vec<SignatureScheme>,
    algs: WebPkiSupportedAlgorithms,
}

impl ServerCertVerifier for Verifier {
    fn verify_server_cert(
        &self,
        _end_entity: &CertificateDer<'_>,
        _intermediates: &[CertificateDer<'_>],
        _server_name: &ServerName<'_>,
        _ocsp: &[u8],
        _now: UnixTime,
    ) -> Result<ServerCertVerified, rustls::Error> {
        Ok(ServerCertVerified::assertion())
    }

    fn verify_tls12_signature(
        &self,
        _msg: &[u8],
        _cert: &CertificateDer<'_>,
        _dss: &DigitallySignedStruct,
    ) -> Result<HandshakeSignatureValid, rustls::Error> {
        Err(rustls::Error::General("TLS 1.2".into()))
    }

    fn verify_tls13_signature(
        &self,
        msg: &[u8],
        cert: &CertificateDer<'_>,
        dss: &DigitallySignedStruct,
    ) -> Result<HandshakeSignatureValid, rustls::Error> {
        rustls::crypto::verify_tls13_signature(msg, cert, dss, &self.algs)
    }

    fn supported_verify_schemes(&self) -> Vec<SignatureScheme> {
        self.schemes.clone()
    }
}

/// The client's transport parameters (preflight C2): `initial_source_connection_id` C1,
/// `active_connection_id_limit` 4, `initial_max_streams_uni` 3, `initial_max_data` 65536,
/// `initial_max_stream_data_uni` 16384.
fn client_tp() -> Vec<u8> {
    qc::hex("0f08c1c1c1c1c1c1c1c1 0e0104 090103 040480010000 070480004000")
}

fn rustls_client() -> (ClientConnection, Arc<Log>) {
    let mut provider = default_provider();
    provider.kx_groups = vec![kx_group::X25519, kx_group::SECP256R1];
    let algs = provider.signature_verification_algorithms;
    let mut c = rustls::ClientConfig::builder_with_provider(Arc::new(provider))
        .with_protocol_versions(&[&rustls::version::TLS13])
        .unwrap()
        .dangerous()
        .with_custom_certificate_verifier(Arc::new(Verifier {
            schemes: vec![SignatureScheme::ECDSA_NISTP256_SHA256],
            algs,
        }))
        .with_no_client_auth();
    let log = Arc::new(Log::default());
    c.key_log = log.clone();
    c.alpn_protocols = vec![b"h3".to_vec()];
    let name = "localhost".try_into().unwrap();
    (ClientConnection::new(Arc::new(c), Version::V1, name, client_tp()).unwrap(), log)
}

// ---------------------------------------------------------------------------------------------
// The test client: rustls plus QUIC packet protection (client view of the keys)
// ---------------------------------------------------------------------------------------------

/// In-order CRYPTO delivery of one level.
#[derive(Default)]
struct Reader {
    next: u64,
    held: Vec<(u64, Vec<u8>)>,
}

impl Reader {
    fn feed(&mut self, off: u64, data: &[u8]) -> Vec<u8> {
        self.held.push((off, data.to_vec()));
        let mut out = Vec::new();
        loop {
            let mut moved = false;
            for (o, d) in &self.held {
                if *o <= self.next && *o + d.len() as u64 > self.next {
                    out.extend_from_slice(&d[(self.next - *o) as usize..]);
                    self.next = *o + d.len() as u64;
                    moved = true;
                }
            }
            if !moved {
                return out;
            }
        }
    }
}

fn idx(l: Level) -> usize {
    match l {
        Level::Initial => 0,
        Level::Handshake => 1,
        Level::OneRtt => 2,
    }
}

fn kind(l: Level) -> PacketKind {
    match l {
        Level::Initial => PacketKind::Initial,
        Level::Handshake => PacketKind::Handshake,
        Level::OneRtt => PacketKind::OneRtt,
    }
}

struct Client {
    tls: ClientConnection,
    log: Arc<Log>,
    odcid: [u8; 8],
    scid: [u8; 8],
    dcid: Vec<u8>,
    /// The client view: `rx` is the server's key, `tx` the client's.
    keys: [Option<KeyPair>; 3],
    pn: [u64; 3],
    rx: [Reader; 3],
    tx_off: [u64; 3],
    largest: [Option<u64>; 3],
    /// TLS output not yet put in a packet, by write level.
    out: Vec<(Level, Vec<u8>)>,
    level: Level,
}

/// The frames a test client sends are PING and CRYPTO.
fn dup(fs: &[Frame]) -> Vec<Frame> {
    fs.iter()
        .map(|f| match f {
            Frame::Ping => Frame::Ping,
            Frame::Crypto { offset, data } => Frame::Crypto { offset: *offset, data: data.clone() },
            _ => panic!("dup"),
        })
        .collect()
}

fn swapped(k: KeyPair) -> KeyPair {
    KeyPair { rx: k.tx, tx: k.rx }
}

impl Client {
    fn new() -> Client {
        let (tls, log) = rustls_client();
        let odcid = qc::S1;
        let mut c = Client {
            tls,
            log,
            odcid,
            scid: qc::C1,
            dcid: odcid.to_vec(),
            keys: [Some(swapped(initial_keys(&odcid))), None, None],
            pn: [0; 3],
            rx: Default::default(),
            tx_off: [0; 3],
            largest: [None; 3],
            out: Vec::new(),
            level: Level::Initial,
        };
        c.pull();
        c
    }

    /// Everything rustls has to send, with the keys of each `KeyChange`.
    fn pull(&mut self) {
        loop {
            let mut buf = Vec::new();
            let kc = self.tls.write_hs(&mut buf);
            if !buf.is_empty() {
                self.out.push((self.level, buf));
            }
            match kc {
                Some(KeyChange::Handshake { .. }) => {
                    self.level = Level::Handshake;
                    self.keys[1] = Some(KeyPair {
                        rx: packet_keys(&self.log.get("SERVER_HANDSHAKE_TRAFFIC_SECRET")),
                        tx: packet_keys(&self.log.get("CLIENT_HANDSHAKE_TRAFFIC_SECRET")),
                    });
                },
                Some(KeyChange::OneRtt { .. }) => {
                    self.level = Level::OneRtt;
                    self.keys[2] = Some(KeyPair {
                        rx: packet_keys(&self.log.get("SERVER_TRAFFIC_SECRET_0")),
                        tx: packet_keys(&self.log.get("CLIENT_TRAFFIC_SECRET_0")),
                    });
                },
                None => return,
            }
        }
    }

    /// The pending TLS output as CRYPTO frames at each level's next offset.
    fn crypto_parts(&mut self) -> Vec<(Level, Vec<Frame>)> {
        let mut parts: Vec<(Level, Vec<Frame>)> = Vec::new();
        for (l, d) in std::mem::take(&mut self.out) {
            let off = self.tx_off[idx(l)];
            self.tx_off[idx(l)] += d.len() as u64;
            parts.push((l, vec![Frame::Crypto { offset: off, data: d }]));
        }
        parts
    }

    fn packet(&mut self, l: Level, frames: Vec<Frame>, padding: usize) -> Vec<u8> {
        let i = idx(l);
        let pn = self.pn[i];
        self.pn[i] += 1;
        let p = OutPacket {
            kind: kind(l),
            dcid: self.dcid.clone(),
            scid: self.scid.to_vec(),
            pn,
            pn_len: 4,
            frames,
            padding,
            spin: false,
        };
        let mut v = Vec::new();
        protect(&p, &self.keys[i].as_ref().unwrap().tx, &mut v);
        v
    }

    /// One datagram of coalesced packets, Initial then Handshake then 1-RTT (RFC 9000 §12.2). An
    /// Initial packet is padded so that the datagram is 1200 bytes.
    fn dgram(&mut self, parts: Vec<(Level, Vec<Frame>)>) -> Vec<u8> {
        let mut parts = parts;
        parts.sort_by_key(|(l, _)| idx(*l));
        let mut rest = Vec::new();
        for (l, f) in parts.iter().filter(|(l, _)| *l != Level::Initial) {
            let p = self.packet(*l, dup(f), 0);
            rest.extend(p);
        }
        let mut out = Vec::new();
        if let Some((_, f)) = parts.iter().find(|(l, _)| *l == Level::Initial) {
            let pn = self.pn[0];
            let want = 1200 - rest.len();
            let mut padding = 0;
            loop {
                self.pn[0] = pn;
                let p = self.packet(Level::Initial, dup(f), padding);
                if p.len() == want {
                    out = p;
                    break;
                }
                // The Length varint can grow a byte with the padding.
                if p.len() > want {
                    padding -= p.len() - want;
                } else {
                    padding += want - p.len();
                }
            }
        }
        out.extend(rest);
        out
    }

    /// Everything pending, as one datagram (none when nothing is pending), with `extra_one_rtt`
    /// last.
    fn datagrams(&mut self, extra_one_rtt: Option<Vec<Frame>>) -> Vec<Vec<u8>> {
        let mut parts = self.crypto_parts();
        if let Some(f) = extra_one_rtt {
            parts.push((Level::OneRtt, f));
        }
        if parts.is_empty() {
            return vec![];
        }
        vec![self.dgram(parts)]
    }

    /// A client-side opener (preflight C3): `open_datagram` parses frames as a server does and
    /// rejects HANDSHAKE_DONE. CRYPTO goes in order to rustls.
    fn absorb(&mut self, d: &[u8]) -> Vec<(PacketKind, Vec<Frame>)> {
        let mut res = Vec::new();
        let mut i = 0;
        while i < d.len() {
            let (l, o, end) = match parse_header(&d[i..], self.scid.len()).expect("header") {
                Header::Long { ty: LongType::Initial, scid, pn_offset, packet_end, .. } => {
                    if self.dcid == self.odcid.to_vec() {
                        self.dcid = scid;
                    }
                    (Level::Initial, pn_offset, packet_end)
                },
                Header::Long { ty: LongType::Handshake, pn_offset, packet_end, .. } => {
                    (Level::Handshake, pn_offset, packet_end)
                },
                Header::Short { pn_offset, .. } => (Level::OneRtt, pn_offset, d.len() - i),
                h => panic!("unexpected {:?}", h),
            };
            let pkt = &d[i..i + end];
            i += end;
            let k = match &self.keys[idx(l)] {
                Some(k) => k.rx,
                None => panic!("server sent a {:?} packet to a client without keys", l),
            };
            let u = remove_hp(pkt, o, &k.hp);
            let n = (u[0] & 3) as usize + 1;
            let mut t = 0u64;
            for b in &u[o..o + n] {
                t = t << 8 | *b as u64;
            }
            let pn = decode_pn(self.largest[idx(l)], t, n as u8);
            let pt = open_packet(&k, pn, &u[..o + n], &u[o + n..]).expect("server packet opens");
            self.largest[idx(l)] = Some(self.largest[idx(l)].map_or(pn, |x| x.max(pn)));
            let mut frames = Vec::new();
            let mut p = 0;
            while p < pt.len() {
                let (ty, m) = parse_frame_type(&pt[p..]).unwrap();
                if ty == 0x1e {
                    frames.push(Frame::HandshakeDone);
                    p += m;
                    continue;
                }
                let (f, q) = parse_frame_body(ty, &pt[p + m..]).unwrap();
                p += m + q;
                frames.push(f);
            }
            for f in &frames {
                if let Frame::Crypto { offset, data } = f {
                    let bytes = self.rx[idx(l)].feed(*offset, data);
                    if !bytes.is_empty() {
                        self.tls.read_hs(&bytes).expect("rustls accepts the server's bytes");
                        self.pull();
                    }
                }
            }
            res.push((kind(l), frames));
        }
        res
    }
}

type Pkts = Vec<(PacketKind, Vec<Frame>)>;

/// Server datagrams until `None`, each opened by the client; every `Some` is non-empty (3e: no
/// keyless ack-eliciting packet).
fn pull_server(s: &mut QuicServer, c: &mut Client, log: &mut Vec<(bool, Pkts)>) {
    for _ in 0..32 {
        let complete = s.conn().handshake_complete();
        let mut out = Vec::new();
        match s.transmit(NOW, &mut out) {
            Some(_) => {
                assert!(!out.is_empty(), "a Some with an empty datagram");
                log.push((complete, c.absorb(&out)));
            },
            None => return,
        }
    }
    panic!("transmit never returned None");
}

fn accept(c: &mut Client) -> (QuicServer<'static>, Vec<(bool, Pkts)>) {
    let ds = c.datagrams(None);
    assert_eq!(ds.len(), 1);
    assert_eq!(ds[0].len(), 1200);
    let mut app = Vec::new();
    let mut s = QuicServer::accept(cfg(), &ds[0], 0, 0, &R(1), &qc::ltp(), &mut app).expect("accepted");
    let mut log = Vec::new();
    pull_server(&mut s, c, &mut log);
    (s, log)
}

fn send(s: &mut QuicServer, d: &[u8], n: u8) {
    let mut app = Vec::new();
    s.receive(d, 0, NOW, &R(n), &mut app);
}

/// Shuttles both ways until the client's handshake and the server's are complete.
fn run(s: &mut QuicServer, c: &mut Client, max_rounds: usize) -> Vec<(bool, Pkts)> {
    let mut log = Vec::new();
    for round in 0..max_rounds {
        if !c.tls.is_handshaking() && s.conn().handshake_complete() && round > 0 {
            return log;
        }
        for (j, d) in c.datagrams(None).into_iter().enumerate() {
            send(s, &d, 2 + (round * 4 + j) as u8);
        }
        pull_server(s, c, &mut log);
    }
    assert!(!c.tls.is_handshaking() && s.conn().handshake_complete(), "not complete in {max_rounds} rounds");
    log
}

/// A completed handshake: the server, the client, the datagrams the server sent.
fn established() -> (QuicServer<'static>, Client, Vec<(bool, Pkts)>) {
    let mut c = Client::new();
    let (mut s, mut log) = accept(&mut c);
    log.extend(run(&mut s, &mut c, 6));
    (s, c, log)
}

fn has(pkts: &Pkts, k: PacketKind, f: impl Fn(&Frame) -> bool) -> bool {
    pkts.iter().any(|(pk, fs)| *pk == k && fs.iter().any(&f))
}

fn close_in(log: &[(bool, Pkts)], k: PacketKind, code: u64) -> bool {
    log.iter().any(|(_, p)| {
        has(p, k, |f| matches!(f, Frame::ConnectionClose { app: false, error_code, .. } if *error_code == code))
    })
}

fn done(log: &[(bool, Pkts)]) -> bool {
    log.iter().any(|(_, p)| has(p, PacketKind::OneRtt, |f| matches!(f, Frame::HandshakeDone)))
}

/// The server up to the point where the client holds the whole server flight: the HRR round and
/// the flight round are done; the client's Finished is pending.
fn flight() -> (QuicServer<'static>, Client, Vec<(bool, Pkts)>) {
    let mut c = Client::new();
    let (mut s, mut log) = accept(&mut c);
    let d = c.datagrams(None);
    assert_eq!(d.len(), 1);
    send(&mut s, &d[0], 2);
    pull_server(&mut s, &mut c, &mut log);
    assert!(!c.tls.is_handshaking());
    assert!(!c.out.is_empty(), "no Finished pending");
    assert_eq!(s.key_slots(), [true, true, true]);
    (s, c, log)
}

// ---------------------------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------------------------

#[test]
fn rustls_quic_handshake() {
    let mut c = Client::new();
    let (mut s, mut log) = accept(&mut c);
    log.extend(run(&mut s, &mut c, 6));
    assert!(!c.tls.is_handshaking());
    assert_eq!(c.tls.alpn_protocol(), Some(&b"h3"[..]));
    assert!(s.conn().handshake_complete());
    // §4.1.2: the first datagram after completion holds HANDSHAKE_DONE.
    let after: Vec<_> = log.iter().filter(|(c, _)| *c).collect();
    assert!(!after.is_empty());
    assert!(
        has(&after[0].1, PacketKind::OneRtt, |f| matches!(f, Frame::HandshakeDone)),
        "first datagram after completion: {:?}",
        after[0].1
    );
    // §4.9.2: the Handshake keys are discarded at completion.
    assert_eq!(s.key_slots(), [false, false, true]);
    for (_, p) in &after {
        assert!(p.iter().all(|(k, _)| *k == PacketKind::OneRtt), "{:?}", p);
    }
}

#[test]
fn initial_keys_dropped_on_first_handshake_packet() {
    let (mut s, mut c, mut log) = flight();
    // Before its Finished, the client sends a lone Handshake PING.
    let d = c.dgram(vec![(Level::Handshake, vec![Frame::Ping])]);
    let before = log.len();
    send(&mut s, &d, 3);
    assert_eq!(s.key_slots(), [false, true, true]);
    pull_server(&mut s, &mut c, &mut log);
    let fin = c.datagrams(None);
    send(&mut s, &fin[0], 4);
    pull_server(&mut s, &mut c, &mut log);
    for (_, p) in &log[before..] {
        assert!(!p.iter().any(|(k, _)| *k == PacketKind::Initial), "{:?}", p);
    }
    assert!(s.conn().handshake_complete());
}

#[test]
fn finished_coalesced_with_one_rtt() {
    let (mut s, mut c, _) = flight();
    let d = c.datagrams(Some(vec![Frame::Ping]));
    send(&mut s, &d[0], 3);
    assert!(s.conn().handshake_complete());
    assert_eq!(s.conn().largest_pn(PacketKind::OneRtt), Some(0));
}

#[test]
fn finished_trailing_bytes_pv() {
    let (mut s, mut c, mut log) = flight();
    let mut parts = c.crypto_parts();
    match &mut parts[0].1[0] {
        Frame::Crypto { data, .. } => data.push(0x14),
        _ => unreachable!(),
    }
    let d = c.dgram(parts);
    send(&mut s, &d, 3);
    pull_server(&mut s, &mut c, &mut log);
    assert!(close_in(&log, PacketKind::Handshake, 0x0a), "{:?}", log);
    assert!(!done(&log));
}

#[test]
fn tampered_finished_0x133() {
    let (mut s, mut c, mut log) = flight();
    let mut parts = c.crypto_parts();
    match &mut parts[0].1[0] {
        Frame::Crypto { data, .. } => *data.last_mut().unwrap() ^= 1,
        _ => unreachable!(),
    }
    let d = c.dgram(parts);
    send(&mut s, &d, 3);
    pull_server(&mut s, &mut c, &mut log);
    assert!(close_in(&log, PacketKind::Handshake, 0x133), "{:?}", log);
    assert!(!done(&log));
    assert!(!s.key_slots()[2]);
}

/// A 0-RTT long header (type 0xd0) to `dcid`, whose Length covers 30 bytes of `[0x06; 30]`.
fn zero_rtt(dcid: &[u8]) -> Vec<u8> {
    let mut v = vec![0xd0, 0, 0, 0, 1, dcid.len() as u8];
    v.extend_from_slice(dcid);
    v.push(8);
    v.extend_from_slice(&qc::C1);
    v.push(30);
    v.extend_from_slice(&[0x06; 30]);
    v
}

#[test]
fn zero_rtt_dropped() {
    // Behind the first Initial.
    let mut c = Client::new();
    let mut d = c.datagrams(None).remove(0);
    d.extend(zero_rtt(&qc::S1));
    let mut app = Vec::new();
    let mut s = QuicServer::accept(cfg(), &d, 0, 0, &R(1), &qc::ltp(), &mut app).expect("accepted");
    let mut log = Vec::new();
    pull_server(&mut s, &mut c, &mut log);
    log.extend(run(&mut s, &mut c, 6));
    assert!(s.conn().handshake_complete());
    assert_eq!(s.conn().phase(), Phase::Open);
    assert!(done(&log));

    // In front of CH2: the first packet is a drop, so `receive` takes CH2's last 16 bytes as a
    // reset candidate.
    let mut c = Client::new();
    let (mut s, mut log) = accept(&mut c);
    let ch2 = c.datagrams(None).remove(0);
    let mut d = zero_rtt(&c.dcid);
    d.extend(ch2);
    send(&mut s, &d, 2);
    assert_eq!(s.conn().phase(), Phase::Open);
    pull_server(&mut s, &mut c, &mut log);
    log.extend(run(&mut s, &mut c, 6));
    assert!(s.conn().handshake_complete());
    assert_eq!(s.conn().phase(), Phase::Open);
    assert!(done(&log));
}

#[test]
fn post_handshake_error_closes_under_one_rtt() {
    let (mut s, mut c, _) = established();
    assert_eq!(s.key_slots(), [false, false, true]);
    let d = c.dgram(vec![(Level::OneRtt, vec![Frame::Crypto { offset: 0, data: vec![0x18, 0, 0, 1, 0] }])]);
    send(&mut s, &d, 3);
    let mut log = Vec::new();
    pull_server(&mut s, &mut c, &mut log);
    assert!(close_in(&log, PacketKind::OneRtt, 0x10a), "{:?}", log);
    assert_eq!(s.key_slots(), [false, false, true]);
}

/// RFC 9001 §4.1.3 (M2): Initial CRYPTO data past the consumed end, then the client's first
/// Handshake packet in the same datagram, whose processing discards Initial before the glue runs
/// TLS.
#[test]
fn initial_data_past_end_with_handshake_pv() {
    let (mut s, mut c, mut log) = flight();
    let mut parts = c.crypto_parts();
    parts.push((Level::Initial, vec![Frame::Crypto { offset: c.tx_off[0], data: vec![7; 5] }]));
    let d = c.dgram(parts);
    assert_eq!(d.len(), 1200);
    send(&mut s, &d, 3);
    pull_server(&mut s, &mut c, &mut log);
    assert!(close_in(&log, PacketKind::Handshake, 0x0a), "{:?}", log);
    assert!(!close_in(&log, PacketKind::Initial, 0x0a), "{:?}", log);
    assert!(!done(&log));
}

/// RFC 9001 §4.1.3 (M1, Handshake to 1-RTT): Handshake CRYPTO bytes buffered past a gap when the
/// 1-RTT keys install.
#[test]
fn gapped_handshake_at_one_rtt_pv() {
    let (mut s, mut c, mut log) = flight();
    let mut parts = c.crypto_parts();
    let fin_end = c.tx_off[1];
    parts[0].1.push(Frame::Crypto { offset: fin_end + 10, data: vec![9; 4] });
    let d = c.dgram(parts);
    send(&mut s, &d, 3);
    pull_server(&mut s, &mut c, &mut log);
    assert!(close_in(&log, PacketKind::Handshake, 0x0a), "{:?}", log);
    assert!(!done(&log));
}
