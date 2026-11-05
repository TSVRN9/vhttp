//! Phase 3e Task 6: the shell's socket options, keys, timeout floor and routing order.
#[path = "../../quic/tests/common/mod.rs"]
mod common;
use common::*;
use server::*;
use std::io;
use std::net::SocketAddr;

fn rng() -> io::Result<[u8; 129]> {
    Ok(rnd(1))
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
    let mut s = Server::new(rng);
    let mut send = Vec::new();
    s.on_datagram(&A2, addr(1), 0, &mut send).unwrap();
    assert_eq!(send.len(), 1);
    assert_eq!(send[0].0.len(), 39);
    assert_eq!(send[0].1, addr(1));
    s.on_datagram(&A2, addr(1), 1, &mut send).unwrap();
    assert_eq!(s.conn_count(), 1);
}

#[test]
fn spoofed_addresses_take_no_slot() {
    let mut s = Server::new(rng);
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
fn idle_close_frees_slot() {
    let mut s = Server::new(rng);
    let mut send = Vec::new();
    s.on_datagram(&A2, addr(1), 0, &mut send).unwrap();
    s.on_wake(60_000_000, &mut send).unwrap();
    assert_eq!(s.conn_count(), 0);
    s.on_datagram(&A2, addr(1), 60_000_001, &mut send).unwrap();
    assert_eq!(s.conn_count(), 1);
}

#[test]
fn local_params_are_ltp() {
    assert_eq!(local_params(), ltp());
}
