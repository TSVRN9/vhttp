//! Phase 4c Task 3: the QUIC-TLS glue over A.2, curl's ClientHello and A.2-based h3 ClientHellos
//! (RFC 9001 §4, §4.1.3, §4.8, §4.9).
#![allow(dead_code, non_snake_case)]
#[path = "../../quic/tests/common/mod.rs"]
mod qc;
#[path = "../../tls/tests/common/mod.rs"]
mod tc;

use quic::ack::AckFrame;
use quic::aead::KeyPair;
use quic::datagram::{OutPacket, PlainPacket};
use quic::frame::Frame;
use quic::header::{parse_long_header, Header, LongType};
use quic::lifecycle::Phase;
use quic::payload::PacketKind;
use quic::protect::{open_datagram, protect};
use quic::tp::parse_transport_params;
use quictls::keys::initial_keys;
use quictls::server::*;
use std::sync::OnceLock;
use tls::codes::HRR_RANDOM;
use tls::config::ServerConfig;

fn cfg() -> &'static ServerConfig {
    static C: OnceLock<ServerConfig> = OnceLock::new();
    C.get_or_init(tc::ecdsa_cfg)
}

fn R(n: u8) -> Rand {
    Rand { conn: qc::rnd(n), refeed: qc::rnd(n + 50), complete: qc::rnd(n + 100), tls: [n; 96] }
}

fn CC(code: u64) -> Frame {
    Frame::ConnectionClose { app: false, error_code: code, frame_type: 0, reason: vec![] }
}

fn cr(offset: usize, data: &[u8]) -> Frame {
    Frame::Crypto { offset: offset as u64, data: data.to_vec() }
}

/// A client Initial to `dcid` from `scid`, pn length 4, padded to exactly `len` bytes, under the
/// Initial keys of `dcid`.
fn pkt(dcid: &[u8], scid: &[u8], pn: u64, frames: impl Fn() -> Vec<Frame>, len: usize) -> Vec<u8> {
    let k = initial_keys(dcid).rx;
    let mut padding = 0;
    loop {
        let p = OutPacket {
            kind: PacketKind::Initial,
            dcid: dcid.to_vec(),
            scid: scid.to_vec(),
            pn,
            pn_len: 4,
            frames: frames(),
            padding,
            spin: false,
        };
        let mut v = Vec::new();
        protect(&p, &k, &mut v);
        if v.len() == len {
            return v;
        }
        if v.len() > len {
            // The Length varint grew a byte with the padding.
            assert!(padding >= v.len() - len, "frames too long for {len} bytes");
            padding -= v.len() - len;
        } else {
            padding += len - v.len();
        }
    }
}

/// `pkt` from C1, 1200 bytes.
fn ini(dcid: &[u8], pn: u64, frames: impl Fn() -> Vec<Frame>) -> Vec<u8> {
    pkt(dcid, &qc::C1, pn, frames, 1200)
}

/// The client's transport parameters: initial_source_connection_id C1, active_connection_id_limit 4.
fn ctp() -> Vec<u8> {
    qc::hex("0f08c1c1c1c1c1c1c1c1 0e0104")
}

/// A.2's ClientHello with ALPN `h3`, one P-256 share and `ctp()`, then `edit`.
fn h3ch(edit: impl FnOnce(&mut Vec<(u16, Vec<u8>)>)) -> Vec<u8> {
    tc::h3_ch(&[(0x17, tc::P256_SHARE.to_vec())], |e| {
        for (t, d) in e.iter_mut() {
            if *t == 0x39 {
                *d = ctp();
            }
        }
        edit(e)
    })
}

fn id(_: &mut Vec<(u16, Vec<u8>)>) {}

/// The server's Initial packets in `out`, under S1's Initial keys (a Handshake packet is dropped
/// for lack of keys).
fn open_pkts(out: &[u8]) -> Vec<PlainPacket> {
    let ik = initial_keys(&qc::S1);
    let rx = open_datagram(out, &[Some(KeyPair { rx: ik.tx, tx: ik.rx }), None, None], &[None; 3]);
    assert!(rx.error.is_none(), "error {:?}", rx.error);
    for p in &rx.packets {
        assert_eq!(p.kind, PacketKind::Initial);
    }
    rx.packets
}

fn open(out: &[u8]) -> Vec<Frame> {
    open_pkts(out).into_iter().flat_map(|p| p.frames).collect()
}

/// Every datagram `transmit` returns until None.
fn drain(s: &mut QuicServer, now: u64) -> Vec<Vec<u8>> {
    let mut v = Vec::new();
    for _ in 0..32 {
        let mut out = Vec::new();
        match s.transmit(now, &mut out) {
            Some(_) => v.push(out),
            None => return v,
        }
    }
    panic!("transmit never returned None");
}

fn crypto_data(fs: &[Frame]) -> Vec<(u64, Vec<u8>)> {
    fs.iter()
        .filter_map(|f| match f {
            Frame::Crypto { offset, data } => Some((*offset, data.clone())),
            _ => None,
        })
        .collect()
}

fn is_server_hello(d: &[u8]) -> bool {
    d[0] == 2 && d[6..38] != HRR_RANDOM
}

fn accept(d: &[u8]) -> QuicServer<'static> {
    let mut app = Vec::new();
    QuicServer::accept(cfg(), d, 0, 0, &R(1), &qc::ltp(), &mut app).expect("accepted")
}

fn receive(s: &mut QuicServer, d: &[u8], n: u8) {
    let mut app = Vec::new();
    s.receive(d, 0, 10, &R(n), &mut app);
}

/// The close code of the server's next datagram, which must hold only CONNECTION_CLOSE.
fn close_code(s: &mut QuicServer) -> u64 {
    let mut out = Vec::new();
    assert!(s.transmit(20, &mut out).is_some());
    match open(&out).as_slice() {
        [Frame::ConnectionClose { app: false, error_code, .. }] => *error_code,
        f => panic!("not a close: {:?}", f),
    }
}

#[test]
fn a2_closes_0x178() {
    let mut app = Vec::new();
    let mut s = QuicServer::accept(cfg(), &qc::A2, 0, 0, &R(1), &qc::ltp(), &mut app).expect("accepted");
    let mut out = Vec::new();
    assert_eq!(s.transmit(0, &mut out), Some(0));
    let ps = open_pkts(&out);
    assert_eq!(ps.len(), 1);
    assert_eq!(ps[0].frames, vec![CC(0x178)]);
    assert_eq!(s.key_slots(), [true, false, false]);
}

/// The `initial_source_connection_id` of curl's ClientHello.
fn curl_scid() -> Vec<u8> {
    let (_, e) = tc::split_ch(tc::CURL_CH);
    let tp = &e.iter().find(|(t, _)| *t == 0x39).unwrap().1;
    parse_transport_params(tp, true).unwrap().initial_source_connection_id.unwrap()
}

/// CURL_CH's 192-byte CRYPTO frames (the last 188), by index.
fn curl_frames(idx: &[usize]) -> Vec<Frame> {
    let c = tc::CURL_CH;
    assert_eq!(c.len(), 1532);
    idx.iter()
        .map(|&i| {
            let a = 192 * i;
            cr(a, &c[a..(a + 192).min(c.len())])
        })
        .collect()
}

const HRR: &str = "020000340303cf21ad74e59a6111be1d8c021e65b891c2a211167abb8c5e079e09e2c8a8339c00130100000c003300020017002b00020304";

/// curl's ClientHello in two shuffled, overlapping datagrams; returns the server after the HRR.
fn curl_hrr() -> QuicServer<'static> {
    let scid = curl_scid();
    let d1 = pkt(&qc::S1, &scid, 0, || curl_frames(&[5, 0, 7, 2]), 1200);
    let mut s = accept(&d1);
    for out in drain(&mut s, 0) {
        assert!(crypto_data(&open(&out)).is_empty());
    }
    let d2 = pkt(
        &qc::S1,
        &scid,
        1,
        || {
            let mut f = curl_frames(&[1, 3, 4, 6]);
            f.push(cr(64, &tc::CURL_CH[64..256]));
            f
        },
        1200,
    );
    receive(&mut s, &d2, 2);
    let mut out = Vec::new();
    assert!(s.transmit(10, &mut out).is_some());
    let ps = open_pkts(&out);
    assert_eq!(ps.len(), 1);
    assert_eq!(crypto_data(&ps[0].frames), vec![(0, qc::hex(HRR))]);
    assert_eq!(s.key_slots(), [true, false, false]);
    assert_eq!(s.conn().phase(), Phase::Open);
    s
}

#[test]
fn curl_ch_two_datagrams_hrr() {
    curl_hrr();
}

/// curl's ClientHello with its key_share replaced by one P-256 share.
fn curl_ch2() -> Vec<u8> {
    let (h, mut e) = tc::split_ch(tc::CURL_CH);
    let n = tc::P256_SHARE.len();
    let mut ks = vec![0, (4 + n) as u8, 0, 0x17, 0, n as u8];
    ks.extend_from_slice(tc::P256_SHARE);
    for (t, d) in e.iter_mut() {
        if *t == 0x33 {
            *d = ks.clone();
        }
    }
    tc::join_ch(&h, &e)
}

#[test]
fn ch2_under_1200_dropped() {
    let scid = curl_scid();
    let mut s = curl_hrr();
    let ch2 = curl_ch2();
    let short = pkt(&qc::S1, &scid, 2, || vec![cr(1532, &ch2)], 1199);
    receive(&mut s, &short, 3);
    for out in drain(&mut s, 10) {
        for f in open(&out) {
            assert!(matches!(f, Frame::Ack(_)), "not ACK-only: {:?}", f);
        }
    }
    let full = pkt(&qc::S1, &scid, 3, || vec![cr(1532, &ch2)], 1200);
    receive(&mut s, &full, 4);
    let outs = drain(&mut s, 10);
    let sh = outs.iter().flat_map(|o| crypto_data(&open(o))).any(|(_, d)| is_server_hello(&d));
    assert!(sh, "no ServerHello");
    assert_eq!(s.key_slots(), [true, true, true]);
}

/// `direct_flight`'s server, with its first `transmit` loop drained.
fn flight() -> QuicServer<'static> {
    let ch = h3ch(id);
    let mut s = accept(&ini(&qc::S1, 0, || vec![cr(0, &ch)]));
    let outs = drain(&mut s, 0);
    let mut sh = false;
    let mut hs = false;
    for o in &outs {
        sh |= crypto_data(&open(o)).iter().any(|(off, d)| *off == 0 && is_server_hello(d));
        let mut i = 0;
        while i < o.len() {
            match parse_long_header(&o[i..]) {
                Some(Header::Long { ty, dcid, packet_end, .. }) => {
                    hs |= ty == LongType::Handshake && dcid == qc::C1;
                    i += packet_end;
                },
                _ => break,
            }
        }
    }
    assert!(sh, "no ServerHello");
    assert!(hs, "no Handshake packet");
    assert_eq!(s.key_slots(), [true, true, true]);
    assert_eq!(s.conn().phase(), Phase::Open);
    s
}

#[test]
fn direct_flight() {
    flight();
}

#[test]
fn trailing_initial_bytes_pv() {
    let mut ch = h3ch(id);
    ch.push(0x01);
    let mut s = accept(&ini(&qc::S1, 0, || vec![cr(0, &ch)]));
    assert_eq!(close_code(&mut s), 0x0a);
    assert!(!s.key_slots()[1]);
}

#[test]
fn initial_retransmit_after_switch_ok() {
    let ch = h3ch(id);
    let mut s = flight();
    receive(&mut s, &ini(&qc::S1, 1, || vec![cr(0, &ch)]), 2);
    assert_eq!(s.conn().phase(), Phase::Open);
    let ack = || vec![Frame::Ack(AckFrame { largest: 0, delay: 0, first_range: 0, ranges: vec![], ecn: None })];
    receive(&mut s, &ini(&qc::S1, 2, ack), 3);
    assert_eq!(s.conn().phase(), Phase::Open);
}

#[test]
fn initial_data_after_switch_pv() {
    let l = h3ch(id).len();
    let mut s = flight();
    receive(&mut s, &ini(&qc::S1, 1, || vec![cr(l + 100, &[7; 10])]), 2);
    assert_eq!(close_code(&mut s), 0x0a);
    // Closed before completion: the 1-RTT keys are gone (RFC 8446 §6).
    assert_eq!(s.key_slots(), [true, true, false]);
    let mut s = flight();
    receive(&mut s, &ini(&qc::S1, 1, || vec![cr(l, &[7; 10])]), 2);
    assert_eq!(close_code(&mut s), 0x0a);
}

/// The ClientHello and, in the same datagram, an out-of-order Initial CRYPTO frame past it: at the
/// key change TLS has not consumed it (RFC 9001 §4.1.3).
#[test]
fn gapped_initial_at_key_change_pv() {
    let ch = h3ch(id);
    let l = ch.len();
    let mut s = accept(&ini(&qc::S1, 0, || vec![cr(0, &ch), cr(l + 100, &[7; 10])]));
    assert_eq!(close_code(&mut s), 0x0a);
    assert_eq!(s.key_slots(), [true, false, false]);
}

#[test]
fn error_ranges() {
    let code = |ch: &[u8]| {
        let mut s = accept(&ini(&qc::S1, 0, || vec![cr(0, ch)]));
        close_code(&mut s)
    };
    let mut big = vec![1, 1, 0, 1];
    big.extend([0u8; 1000]);
    assert_eq!(code(&big), 0x0d);
    let sid = tc::join_ch(&tc::head(0x0303, &[7], &[0x1301], &[0]), &tc::split_ch(&h3ch(id)).1);
    assert_eq!(code(&sid), 0x0a);
    let h329 = h3ch(|e| {
        for (t, d) in e.iter_mut() {
            if *t == 0x10 {
                *d = qc::hex("0006 05 68332d3239");
            }
        }
    });
    assert_eq!(code(&h329), 0x178);
    let dup = h3ch(|e| {
        for (t, d) in e.iter_mut() {
            if *t == 0x39 {
                *d = qc::hex("010105 010105");
            }
        }
    });
    assert_eq!(code(&dup), 0x08);
}

#[test]
fn peer_tp_mismatch_no_keys() {
    let ch = h3ch(id);
    let mut s = accept(&pkt(&qc::S1, &[0xc2; 8], 0, || vec![cr(0, &ch)], 1200));
    assert_eq!(close_code(&mut s), 0x08);
    assert_eq!(s.key_slots(), [true, false, false]);
}
