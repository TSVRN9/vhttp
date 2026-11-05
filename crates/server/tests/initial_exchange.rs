#[path = "../../quic/tests/common/mod.rs"]
mod common;
use common::*;
use quic::aead::KeyPair;
use quic::datagram::OutPacket;
use quic::payload::PacketKind;
use quic::frame::Frame;
use quic::protect::{protect, unprotect};
use server::{bind, load_config, run};
use std::net::{SocketAddr, UdpSocket};
use std::thread;
use std::time::Duration;

fn start() -> SocketAddr {
    let s = bind("127.0.0.1:0".parse().unwrap()).unwrap();
    let a = s.local_addr().unwrap();
    let cfg: &'static _ = Box::leak(Box::new(
        load_config(include_bytes!("data/cert.pem"), include_bytes!("data/key.pem"), vec![]).unwrap(),
    ));
    thread::spawn(move || run(s, cfg));
    a
}

fn client(server: SocketAddr) -> UdpSocket {
    let s = UdpSocket::bind("127.0.0.1:0").unwrap();
    s.set_read_timeout(Some(Duration::from_millis(500))).unwrap();
    s.connect(server).unwrap();
    s
}

fn assert_silent(s: &UdpSocket) {
    let mut buf = [0u8; 3600];
    let e = s.recv(&mut buf).unwrap_err();
    assert!(matches!(e.kind(), std::io::ErrorKind::WouldBlock | std::io::ErrorKind::TimedOut), "{e}");
}

fn assert_a2_reply(s: &UdpSocket) {
    let kc = [Some(KeyPair { rx: SERVER, tx: CLIENT }), None, None];
    let mut buf = [0u8; 3600];
    let n = s.recv(&mut buf).unwrap();
    let (p, used) = unprotect(&buf[..n], &kc, &[None; 3]).ok().unwrap();
    assert_eq!(used, n);
    let p = p.unwrap();
    assert!(matches!(p.kind, PacketKind::Initial));
    assert!(p.dcid.is_empty());
    assert_eq!(p.scid.len(), 8);
    assert_eq!(p.pn, 0);
    assert_eq!(p.frames, [Frame::ConnectionClose { app: false, error_code: 0x178, frame_type: 0, reason: vec![] }]);
    assert_silent(s);
}

#[test]
fn a2_gets_close_0x178() {
    let c = client(start());
    c.send(&A2).unwrap();
    assert_a2_reply(&c);
}

#[test]
fn initial_1199_ignored() {
    let c = client(start());
    let p = OutPacket {
        kind: PacketKind::Initial,
        dcid: S1.to_vec(),
        scid: vec![],
        pn: 2,
        pn_len: 4,
        frames: vec![Frame::Crypto { offset: 0, data: A2_CRYPTO.to_vec() }],
        padding: 916,
        spin: false,
    };
    let mut d = Vec::new();
    protect(&p, &CLIENT, &mut d);
    assert_eq!(d.len(), 1199);
    c.send(&d).unwrap();
    assert_silent(&c);
    c.send(&A2).unwrap();
    assert_a2_reply(&c);
}

fn unknown_version(len: usize) -> Vec<u8> {
    let mut d = vec![0xc0, 0x1a, 0x2a, 0x3a, 0x4a, 0x08];
    d.extend_from_slice(&S1);
    d.push(0);
    d.resize(len, 0);
    d
}

#[test]
fn unknown_version_gets_vn() {
    let c = client(start());
    c.send(&unknown_version(1200)).unwrap();
    let mut buf = [0u8; 3600];
    let n = c.recv(&mut buf).unwrap();
    let mut exp = vec![0xc0, 0, 0, 0, 0, 0x00, 0x08];
    exp.extend_from_slice(&S1);
    exp.extend_from_slice(&[0, 0, 0, 1]);
    assert_eq!(&buf[..n], &exp[..]);
    assert_silent(&c);
}

#[test]
fn small_unknown_version_dropped() {
    let c = client(start());
    c.send(&unknown_version(1199)).unwrap();
    assert_silent(&c);
}
