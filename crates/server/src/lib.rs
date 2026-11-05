//! The unverified IO shell (Phase 3e): the UDP socket, the clock and the RNG around the
//! verified sans-IO pipelines in `quic`. Every `quic` function it calls requires at most the
//! receiver's `wf()`, which Verus does not check at an unverified call site; every `Connection`
//! constructor and method ensures `wf()` over private fields.
use quic::aead::{KeyPair, PacketKeys, MAX_UDP_PAYLOAD};
use quic::conn::{Connection, RAND_LEN};
use quic::pipeline::{accept_datagram, initial_dcid, receive, transmit};
use quic::route::{route, CidTable, ConnId, Route};
use quic::tp::{default_transport_params, TransportParams};
use std::io;
use std::net::{SocketAddr, UdpSocket};
use std::os::fd::{AsRawFd, FromRawFd};
use std::time::{Duration, Instant};

pub const MAX_POLLS: usize = 1024;

fn setopt(fd: i32, level: i32, name: i32, val: i32) -> io::Result<()> {
    let p = &val as *const i32 as *const libc::c_void;
    let r = unsafe { libc::setsockopt(fd, level, name, p, std::mem::size_of::<i32>() as libc::socklen_t) };
    if r < 0 {
        Err(io::Error::last_os_error())
    } else {
        Ok(())
    }
}

//= https://www.rfc-editor.org/rfc/rfc9000#section-14
//# UDP datagrams MUST NOT be fragmented at the IP layer.  In IPv4
//# [IPv4], the Don't Fragment (DF) bit MUST be set if possible, to
//# prevent fragmentation on the path.

//= https://www.rfc-editor.org/rfc/rfc9000#section-14
//= type=exception
//= reason=Every datagram is at most MAX_DATAGRAM, and a path that fails the 1200-byte probe gets only probes and CONNECTION_CLOSE (3d2's P17 gate, Paths::mtu_failed in conn.rs).
//# QUIC MUST NOT be used if the network path cannot support a
//# maximum datagram size of at least 1200 bytes.

//= https://www.rfc-editor.org/rfc/rfc9000#section-9.7
//= type=exception
//= reason=The shell never sets a flow label; any label is the kernel's (the OS UDP stack, trusted base).
//# The flow label generation MUST be designed to minimize the chances of
//# linkability with a previously used flow label, as a stable flow label
//# would enable correlating activity on multiple paths; see Section 9.5.

//= https://www.rfc-editor.org/rfc/rfc9000#section-14.2.1
//= type=exception
//= reason=No ICMP is read (no IP_RECVERR), and PMTUDISC_PROBE makes the kernel ignore ICMP PMTU for our sends.
//# An endpoint MUST ignore an ICMP message that claims the PMTU has
//# decreased below QUIC's smallest allowed maximum datagram size.

//= https://www.rfc-editor.org/rfc/rfc9000#section-14.2.1
//= type=exception
//= reason=No ICMP is read (no IP_RECVERR), and PMTUDISC_PROBE makes the kernel ignore ICMP PMTU for our sends.
//# ICMP message validation MUST include matching IP addresses and UDP
//# ports [RFC8085] and, when possible, connection IDs to an active QUIC
//# session.

//= https://www.rfc-editor.org/rfc/rfc9000#section-14.2.1
//= type=exception
//= reason=No ICMP is read (no IP_RECVERR), and PMTUDISC_PROBE makes the kernel ignore ICMP PMTU for our sends.
//# An endpoint MUST NOT increase the PMTU based on ICMP messages; see
//# Item 6 in Section 3 of [DPLPMTUD].
/// A UDP socket on `addr` with the Don't Fragment bit set (IPv4 `IP_PMTUDISC_PROBE`; IPv6
/// `IPV6_PMTUDISC_PROBE`, `IPV6_DONTFRAG` and `IPV6_V6ONLY`, so no v4-mapped traffic escapes DF); a failed `setsockopt` is an error.
pub fn bind(addr: SocketAddr) -> io::Result<UdpSocket> {
    let SocketAddr::V6(a) = addr else {
        let s = UdpSocket::bind(addr)?;
        setopt(s.as_raw_fd(), libc::IPPROTO_IP, libc::IP_MTU_DISCOVER, libc::IP_PMTUDISC_PROBE)?;
        return Ok(s);
    };
    // IPV6_V6ONLY must precede bind, so the socket is made by hand; the fd is owned from here.
    let fd = unsafe { libc::socket(libc::AF_INET6, libc::SOCK_DGRAM | libc::SOCK_CLOEXEC, 0) };
    if fd < 0 {
        return Err(io::Error::last_os_error());
    }
    let s = unsafe { UdpSocket::from_raw_fd(fd) };
    setopt(fd, libc::IPPROTO_IPV6, libc::IPV6_V6ONLY, 1)?;
    setopt(fd, libc::IPPROTO_IPV6, libc::IPV6_MTU_DISCOVER, libc::IPV6_PMTUDISC_PROBE)?;
    setopt(fd, libc::IPPROTO_IPV6, libc::IPV6_DONTFRAG, 1)?;
    let mut sa: libc::sockaddr_in6 = unsafe { std::mem::zeroed() };
    sa.sin6_family = libc::AF_INET6 as libc::sa_family_t;
    sa.sin6_port = a.port().to_be();
    sa.sin6_addr.s6_addr = a.ip().octets();
    sa.sin6_flowinfo = a.flowinfo();
    sa.sin6_scope_id = a.scope_id();
    let p = &sa as *const libc::sockaddr_in6 as *const libc::sockaddr;
    if unsafe { libc::bind(fd, p, std::mem::size_of::<libc::sockaddr_in6>() as libc::socklen_t) } < 0 {
        return Err(io::Error::last_os_error());
    }
    Ok(s)
}

const A1_DCID: [u8; 8] = [0x83, 0x94, 0xc8, 0xf0, 0x3e, 0x51, 0x57, 0x08];
const A1_CLIENT: PacketKeys = PacketKeys {
    key: [0x1f, 0x36, 0x96, 0x13, 0xdd, 0x76, 0xd5, 0x46, 0x77, 0x30, 0xef, 0xcb, 0xe3, 0xb1, 0xa2, 0x2d],
    iv: [0xfa, 0x04, 0x4b, 0x2f, 0x42, 0xa3, 0xfd, 0x3b, 0x46, 0xfb, 0x25, 0x5c],
    hp: [0x9f, 0x50, 0x44, 0x9e, 0x04, 0xa0, 0xe8, 0x10, 0x28, 0x3a, 0x1e, 0x99, 0x33, 0xad, 0xed, 0xd2],
};
const A1_SERVER: PacketKeys = PacketKeys {
    key: [0xcf, 0x3a, 0x53, 0x31, 0x65, 0x3c, 0x36, 0x4c, 0x88, 0xf0, 0xf3, 0x79, 0xb6, 0x06, 0x7e, 0x37],
    iv: [0x0a, 0xc1, 0x49, 0x3c, 0xa1, 0x90, 0x58, 0x53, 0xb0, 0xbb, 0xa0, 0x3e],
    hp: [0xc2, 0x06, 0xb8, 0xd9, 0xb9, 0xf0, 0xf3, 0x76, 0x44, 0x43, 0x0b, 0x49, 0x0e, 0xea, 0xa3, 0x14],
};

/// The Initial keys for `dcid`: RFC 9001 A.1's, for its DCID only.
// ponytail: RFC constants stand in for Initial secret derivation (RFC 9001 §5.2); Phase 4 derives the keys for any DCID.
pub fn initial_keys(dcid: &[u8]) -> Option<KeyPair> {
    (dcid == A1_DCID).then_some(KeyPair { rx: A1_CLIENT, tx: A1_SERVER })
}

/// Our transport parameters.
pub fn local_params() -> TransportParams {
    let mut t = default_transport_params();
    t.max_idle_timeout = 30000;
    t.initial_max_data = 1000;
    t.initial_max_stream_data_bidi_remote = 100;
    t.initial_max_stream_data_uni = 100;
    t.initial_max_streams_bidi = 10;
    t.initial_max_streams_uni = 3;
    t.active_connection_id_limit = 2;
    t.disable_active_migration = true;
    t
}

/// How long to block in `recv_from`: until `deadline`, at least 1 ms. The floor is defence in
/// depth only; `pipeline::settled_later` guarantees the deadline is later than `now`.
pub fn read_timeout(now: u64, deadline: Option<u64>) -> Option<Duration> {
    deadline.map(|t| Duration::from_micros(t.saturating_sub(now).max(1000)))
}

/// Fresh randomness from the kernel; partial reads and EINTR are retried.
pub fn fresh_rand() -> io::Result<[u8; RAND_LEN]> {
    let mut b = [0u8; RAND_LEN];
    let mut got = 0;
    while got < RAND_LEN {
        let r = unsafe { libc::getrandom(b[got..].as_mut_ptr() as *mut libc::c_void, RAND_LEN - got, 0) };
        if r < 0 {
            let e = io::Error::last_os_error();
            if e.kind() != io::ErrorKind::Interrupted {
                return Err(e);
            }
        } else {
            got += r as usize;
        }
    }
    Ok(b)
}

struct Conn {
    id: ConnId,
    conn: Connection,
    keys: [Option<KeyPair>; 3],
    /// `PathId` is an index here; an address is kept only once `conn` accepts its path.
    addrs: Vec<SocketAddr>,
}

type Outbox = Vec<(Vec<u8>, SocketAddr)>;

/// The socket-free server: datagrams and wake-ups in, datagrams out.
// ponytail: linear scans over conns and route's CID/token lists (<= MAX_CONNS = 102 connections; route costs <= 512 CID and 816 CT token comparisons per datagram); a random-keyed SipHash index before production, never a sorted Vec (it leaks token order, §10.3.1). Connections are capped by route's has_room (MAX_CONNS), counted at the first applied Add, which service applies before the next datagram; nothing is evicted, and RFC 9000 §10.1's 3*PTO floor lets a peer hold a slot up to 55.6 min (3d2 note), which admission must plan for. A.1-only keys allow one connection in 3e.
pub struct Server {
    table: CidTable,
    conns: Vec<Conn>,
    next_id: ConnId,
    rng: fn() -> io::Result<[u8; RAND_LEN]>,
    out: Vec<u8>,
}

impl Server {
    pub fn new(rng: fn() -> io::Result<[u8; RAND_LEN]>) -> Server {
        Server { table: CidTable::new(), conns: Vec::new(), next_id: 0, rng, out: Vec::new() }
    }

    #[doc(hidden)]
    pub fn conn_count(&self) -> usize {
        self.conns.len()
    }

    #[doc(hidden)]
    pub fn addr_count(&self, i: usize) -> usize {
        self.conns[i].addrs.len()
    }

    /// The earliest `next_timeout` over the connections, read fresh on every call.
    pub fn deadline(&self) -> Option<u64> {
        self.conns.iter().filter_map(|c| c.conn.next_timeout()).min()
    }

    pub fn on_datagram(&mut self, d: &[u8], from: SocketAddr, now: u64, send: &mut Outbox) -> io::Result<()> {
        // The sole version_negotiation call site (RFC 9000 §17.2.1) is route.
        match route(d, &self.table) {
            Route::VersionNegotiation(v) => send.push((v, from)),
            Route::Reset(id) => {
                if let (Some(i), Some(t)) = (self.index(id), d.last_chunk::<16>()) {
                    self.conns[i].conn.on_reset_candidate(t, now);
                    self.service(i, now, send);
                }
            }
            Route::Existing(id) => {
                if let Some(i) = self.index(id) {
                    let r = (self.rng)()?;
                    let c = &mut self.conns[i];
                    let (p, new) = match c.addrs.iter().position(|a| *a == from) {
                        Some(p) => (p, false),
                        None => {
                            c.addrs.push(from);
                            (c.addrs.len() - 1, true)
                        }
                    };
                    receive(&mut c.conn, d, p as u64, now, &r, &c.keys);
                    if new && c.conn.path_state(p as u64).is_none() {
                        c.addrs.truncate(p); // no slot for an unaccepted path
                    }
                    self.service(i, now, send);
                }
            }
            Route::NewInitial => {
                if let Some(kp) = initial_dcid(d).and_then(|x| initial_keys(&x)) {
                    let keys = [Some(kp), None, None];
                    let r = (self.rng)()?;
                    if let Some(conn) = accept_datagram(d, 0, now, &r, &local_params(), &keys) {
                        self.conns.push(Conn { id: self.next_id, conn, keys, addrs: vec![from] });
                        self.next_id += 1;
                        self.service(self.conns.len() - 1, now, send);
                    }
                }
            }
            Route::Drop => {}
        }
        Ok(())
    }

    /// Fires the due timers, then services every connection.
    pub fn on_wake(&mut self, now: u64, send: &mut Outbox) -> io::Result<()> {
        let mut i = 0;
        while i < self.conns.len() {
            if matches!(self.conns[i].conn.next_timeout(), Some(t) if t <= now) {
                let r = (self.rng)()?;
                self.conns[i].conn.on_timeout(now, &r);
            }
            if !self.service(i, now, send) {
                i += 1;
            }
        }
        Ok(())
    }

    fn index(&self, id: ConnId) -> Option<usize> {
        self.conns.iter().position(|c| c.id == id)
    }

    /// In `settled_later`'s order: the CID updates, then the datagrams, then the removal of a
    /// closed connection. Returns whether the connection at `i` was removed.
    fn service(&mut self, i: usize, now: u64, send: &mut Outbox) -> bool {
        let c = &mut self.conns[i];
        let mut ups = Vec::new();
        c.conn.poll_cid_updates(&mut ups);
        for u in &ups {
            self.table.apply(c.id, u); // false: a key collision, issue_cids' ponytail
        }
        let mut drained = false;
        for _ in 0..MAX_POLLS {
            match transmit(&mut c.conn, now, &c.keys, &mut self.out) {
                None => {
                    drained = true;
                    break;
                }
                Some(p) => {
                    if !self.out.is_empty() && (p as usize) < c.addrs.len() {
                        send.push((self.out.clone(), c.addrs[p as usize]));
                    }
                }
            }
        }
        if !drained {
            eprintln!("server: transmit gave {MAX_POLLS} datagrams without stopping");
        }
        if c.conn.is_closed() {
            self.table.remove_conn(c.id);
            self.conns.remove(i);
            return true;
        }
        false
    }
}

fn send_all(sock: &UdpSocket, send: &mut Outbox) {
    for (b, to) in send.drain(..) {
        let _ = sock.send_to(&b, to); // UDP: a lost datagram is the protocol's business
    }
}

/// Serves `sock` until a fatal socket or RNG error.
pub fn run(sock: UdpSocket) -> io::Result<()> {
    let start = Instant::now();
    let us = || start.elapsed().as_micros() as u64;
    let mut srv = Server::new(fresh_rand);
    let mut buf = vec![0; MAX_UDP_PAYLOAD];
    let mut send = Vec::new();
    loop {
        let now = us();
        srv.on_wake(now, &mut send)?;
        send_all(&sock, &mut send);
        sock.set_read_timeout(read_timeout(now, srv.deadline()))?;
        match sock.recv_from(&mut buf) {
            Ok((n, from)) => {
                srv.on_datagram(&buf[..n], from, us(), &mut send)?;
                send_all(&sock, &mut send);
            }
            Err(e) if matches!(e.kind(), io::ErrorKind::WouldBlock | io::ErrorKind::TimedOut | io::ErrorKind::Interrupted) => {}
            Err(e) => return Err(e),
        }
    }
}
