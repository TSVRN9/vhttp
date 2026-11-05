//! Phase 3e Task 6: the shell's socket options, keys, timeout floor and routing order.
#[path = "../../quic/tests/common/mod.rs"]
mod common;
use common::*;
use quic::aead::KeyPair;
use quic::frame::Frame;
use quic::protect::unprotect;
use quictls::server::{QuicServer, Rand};
use server::*;
use std::io;
use std::net::SocketAddr;

fn rng(b: &mut [u8]) -> io::Result<()> {
    for (i, x) in b.iter_mut().enumerate() {
        *x = (i as u8).wrapping_mul(7).wrapping_add(1);
    }
    Ok(())
}

const CERT: &[u8] = include_bytes!("data/cert.pem");
const KEY: &[u8] = include_bytes!("data/key.pem");
const CA: &[u8] = include_bytes!("data/ca.pem");
const LEAF: &[u8] = include_bytes!("data/leaf.pem");
const LEAF_KEY: &[u8] = include_bytes!("data/leaf-key.pem");
const RSA_KEY: &[u8] = include_bytes!("data/rsa-key.pem");

fn cfg() -> &'static tls::config::ServerConfig {
    Box::leak(Box::new(load_config(CERT, KEY, vec![]).unwrap()))
}

fn cat(a: &[u8], b: &[u8]) -> Vec<u8> {
    [a, b].concat()
}

#[test]
fn loads_p256_pem() {
    assert!(load_config(CERT, KEY, vec![]).is_ok());
}

#[test]
fn rejects_mismatched_key() {
    assert!(load_config(CERT, LEAF_KEY, vec![]).is_err());
}

#[test]
fn rejects_rsa_key() {
    assert!(load_config(CERT, RSA_KEY, vec![]).err().unwrap().contains("Phase 7"));
}

#[test]
fn chain_needs_schemes() {
    let chain = cat(LEAF, CA);
    assert!(load_config(&chain, LEAF_KEY, vec![]).is_err());
    assert!(load_config(&chain, LEAF_KEY, vec![0x0403]).is_ok());
    let rev = cat(CA, LEAF);
    assert!(load_config(&rev, LEAF_KEY, vec![]).is_err());
    assert!(load_config(&rev, LEAF_KEY, vec![0x0403]).is_err());
}

#[test]
fn loader_fails_closed() {
    let key = String::from_utf8(KEY.to_vec()).unwrap();
    // Two keys, a key in the certificate file, junk outside blocks, a damaged body.
    assert!(load_config(CERT, &cat(KEY, LEAF_KEY), vec![]).is_err());
    assert!(load_config(&cat(CERT, KEY), KEY, vec![]).is_err());
    assert!(load_config(CERT, &cat(b"junk\n", KEY), vec![]).is_err());
    assert!(load_config(CERT, key.replace("MIG", "MIH").as_bytes(), vec![]).is_err());
    assert!(load_config(CERT, key.replace("-----END PRIVATE KEY-----", "-----END KEY-----").as_bytes(), vec![]).is_err());
    assert!(load_config(b"", KEY, vec![]).is_err());
    assert!(load_config(CERT, b"", vec![]).is_err());
    // Errors never echo key text.
    for k in [&b"-----BEGIN PRIVATE KEY-----\nAAAA\n-----END PRIVATE KEY-----\n"[..], RSA_KEY, LEAF_KEY] {
        let e = load_config(CERT, k, vec![]).err().unwrap();
        assert!(e.len() < 100 && !e.contains("MIG"), "{e}");
    }
}

#[test]
fn local_params_accepted() {
    let r = Rand { conn: [1; 129], refeed: [2; 129], complete: [3; 129], tls: [4; 96] };
    let mut app = Vec::new();
    assert!(QuicServer::accept(cfg(), &A2, 0, 0, &r, &local_params(), &mut app).is_some());
}

#[test]
fn fill_random_fills() {
    let (mut a, mut b) = ([0u8; 96], [0u8; 96]);
    fill_random(&mut a).unwrap();
    fill_random(&mut b).unwrap();
    assert_ne!(a, b);
    assert_ne!(a, [0u8; 96]);
}

fn addr(p: u16) -> SocketAddr {
    format!("127.0.0.1:{p}").parse().unwrap()
}

fn getopt(s: &std::net::UdpSocket, level: i32, name: i32) -> i32 {
    use std::os::fd::AsRawFd;
    let mut v: i32 = -1;
    let mut l = std::mem::size_of::<i32>() as libc::socklen_t;
    let r = unsafe { libc::getsockopt(s.as_raw_fd(), level, name, &mut v as *mut i32 as *mut libc::c_void, &mut l) };
    assert_eq!(r, 0);
    v
}

#[test]
fn df_set_v4() {
    let s = bind("127.0.0.1:0".parse().unwrap()).unwrap();
    assert_eq!(getopt(&s, libc::IPPROTO_IP, libc::IP_MTU_DISCOVER), libc::IP_PMTUDISC_PROBE);
}

#[test]
fn df_set_v6() {
    let s = match bind("[::1]:0".parse().unwrap()) {
        Ok(s) => s,
        Err(e) if e.kind() == io::ErrorKind::AddrNotAvailable => return,
        Err(e) => panic!("{e}"),
    };
    assert_eq!(getopt(&s, libc::IPPROTO_IPV6, libc::IPV6_MTU_DISCOVER), libc::IPV6_PMTUDISC_PROBE);
    assert_eq!(getopt(&s, libc::IPPROTO_IPV6, libc::IPV6_DONTFRAG), 1);
    assert_eq!(getopt(&s, libc::IPPROTO_IPV6, libc::IPV6_V6ONLY), 1);
}

#[test]
fn read_timeout_floor() {
    use std::time::Duration;
    let ms = Some(Duration::from_millis(1));
    assert_eq!(read_timeout(10, Some(5)), ms);
    assert_eq!(read_timeout(10, Some(10)), ms);
    assert_eq!(read_timeout(0, Some(2500)), Some(Duration::from_micros(2500)));
    assert_eq!(read_timeout(0, None), None);
}

#[test]
fn a2_registered_before_next() {
    let mut s = Server::new(cfg(), rng);
    let mut send = Vec::new();
    s.on_datagram(&A2, addr(1), 0, &mut send).unwrap();
    assert_eq!(send.len(), 1);
    assert_eq!(send[0].1, addr(1));
    let kc = [Some(KeyPair { rx: SERVER, tx: CLIENT }), None, None];
    let (p, used) = unprotect(&send[0].0, &kc, &[None; 3]).ok().unwrap();
    assert_eq!(used, send[0].0.len());
    assert_eq!(p.unwrap().frames, [Frame::ConnectionClose { app: false, error_code: 0x178, frame_type: 0, reason: vec![] }]);
    s.on_datagram(&A2, addr(1), 1, &mut send).unwrap();
    assert_eq!(s.conn_count(), 1);
}

#[test]
fn spoofed_addresses_take_no_slot() {
    let mut s = Server::new(cfg(), rng);
    let mut send = Vec::new();
    s.on_datagram(&A2, addr(1), 0, &mut send).unwrap();
    let mut bad = A2;
    bad[1199] ^= 1;
    for p in 2..6 {
        s.on_datagram(&bad, addr(p), 1, &mut send).unwrap();
    }
    assert_eq!(s.addr_count(0), 1);
}

#[test]
fn timeout_close_frees_slot() {
    let mut s = Server::new(cfg(), rng);
    let mut send = Vec::new();
    s.on_datagram(&A2, addr(1), 0, &mut send).unwrap();
    s.on_wake(60_000_000, &mut send).unwrap();
    assert_eq!(s.conn_count(), 0);
    s.on_datagram(&A2, addr(1), 60_000_001, &mut send).unwrap();
    assert_eq!(s.conn_count(), 1);
}
