//! The unverified IO shell (Phases 3e and 4c): the UDP socket, the clock, the RNG, the PEM
//! chain and key loader and a static response around the verified sans-IO `QuicServer`. Every
//! `quic`, `tls` and `quictls` function it calls requires at most the receiver's `wf()`, which
//! Verus does not check at an unverified call site (TRUSTED.md); `QuicServer::accept` requires
//! `cfg.wf()`, which `load_config` establishes through `build_config` and `p256_signing_key`.
use h3::conn::Output;
use h3::message::Response;
use h3::qpack::field_section::FieldLine;
use quic::aead::MAX_UDP_PAYLOAD;
use quic::conn::RAND_LEN;
use quic::h3_server::{AppEvent, SendError};
use quic::route::{route, CidTable, ConnId, Route};
use quic::tp::{default_transport_params, TransportParams};
use quictls::server::{QuicServer, Rand};
use std::io;
use std::net::{SocketAddr, UdpSocket};
use std::os::fd::{AsRawFd, FromRawFd};
use std::time::{Duration, Instant};
use tls::codes::TLS_RAND_LEN;
use tls::config::{build_config, p256_signing_key, CertChain, ServerConfig};

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

/// Our transport parameters (the interop values: 64 KiB in total, 16 KiB per request stream, 4 KiB per uni stream), at most about 1 MiB per connection and MAX_CONNS = 102 connections.
pub fn local_params() -> TransportParams {
    let mut t = default_transport_params();
    t.max_idle_timeout = 30000;
    t.initial_max_data = 65536;
    t.initial_max_stream_data_bidi_remote = 16384;
    t.initial_max_stream_data_uni = 4096;
    t.initial_max_streams_bidi = 100;
    t.initial_max_streams_uni = 8;
    t.active_connection_id_limit = 2;
    t.disable_active_migration = true;
    t
}

pub const RESPONSE_BODY: &[u8] = b"hello from a verified HTTP/3 server\n";

// ponytail: one static response; a handler API when there is a second page.
pub fn response() -> Response {
    Response {
        status: 200,
        headers: vec![FieldLine { name: b"content-type".to_vec(), value: b"text/plain".to_vec() }],
        body: RESPONSE_BODY.to_vec(),
    }
}

/// How long to block in `recv_from`: until `deadline`, at least 1 ms. The floor is defence in
/// depth only; `pipeline::settled_later` guarantees the deadline is later than `now`.
pub fn read_timeout(now: u64, deadline: Option<u64>) -> Option<Duration> {
    deadline.map(|t| Duration::from_micros(t.saturating_sub(now).max(1000)))
}

/// Fills `b` from the kernel (`getrandom`); partial reads and EINTR are retried, and any other
/// error is returned: there is no fallback.
pub fn fill_random(b: &mut [u8]) -> io::Result<()> {
    let mut got = 0;
    while got < b.len() {
        let r = unsafe { libc::getrandom(b[got..].as_mut_ptr() as *mut libc::c_void, b.len() - got, 0) };
        if r < 0 {
            let e = io::Error::last_os_error();
            if e.kind() != io::ErrorKind::Interrupted {
                return Err(e);
            }
        } else {
            got += r as usize;
        }
    }
    Ok(())
}

type Rng = fn(&mut [u8]) -> io::Result<()>;

/// One fresh `Rand`; each array is filled by its own call.
fn rand(rng: Rng) -> io::Result<Rand> {
    let mut r = Rand { conn: [0; RAND_LEN], refeed: [0; RAND_LEN], complete: [0; RAND_LEN], tls: [0; TLS_RAND_LEN] };
    rng(&mut r.conn)?;
    rng(&mut r.refeed)?;
    rng(&mut r.complete)?;
    rng(&mut r.tls)?;
    Ok(r)
}

struct Conn<'a> {
    id: ConnId,
    q: QuicServer<'a>,
    /// `PathId` is an index here; an address is kept only once `q` accepts its path.
    addrs: Vec<SocketAddr>,
    /// Request streams not yet answered.
    owed: Vec<u64>,
}

impl Conn<'_> {
    /// Takes the requests out of `app`; every other event is dropped.
    fn take_requests(&mut self, app: &mut Vec<AppEvent>) {
        for e in app.drain(..) {
            if let AppEvent::H3(Output::Request { stream_id, .. }) = e {
                self.owed.push(stream_id);
            }
        }
    }

    /// Answers the owed requests in order, stopping at the first `Busy`.
    fn respond(&mut self) {
        let resp = response();
        let mut app = Vec::new();
        while let Some(&id) = self.owed.first() {
            let r = self.q.send_response(id, &resp, &mut app);
            self.take_requests(&mut app);
            if r == Err(SendError::Busy) {
                break;
            }
            self.owed.remove(0);
        }
    }
}

type Outbox = Vec<(Vec<u8>, SocketAddr)>;

/// The socket-free server: datagrams and wake-ups in, datagrams out.
// ponytail: linear scans over conns and route's CID/token lists (<= MAX_CONNS = 102 connections; route costs <= 512 CID and 816 CT token comparisons per datagram); a random-keyed SipHash index before production, never a sorted Vec (it leaks token order, §10.3.1). Connections are capped by route's has_room (MAX_CONNS), counted at the first applied Add, which service applies before the next datagram; nothing is evicted, and RFC 9000 §10.1's 3*PTO floor lets a peer hold a slot up to 55.6 min (3d2 note), which admission must plan for. every DCID is keyed, so MAX_CONNS (102) and route's linear scan are reachable, and each unauthenticated Initial costs a P-256 signature (~15 ms); Retry or a per-source handshake limit before deployment.
pub struct Server<'a> {
    cfg: &'a ServerConfig,
    table: CidTable,
    conns: Vec<Conn<'a>>,
    next_id: ConnId,
    rng: Rng,
    out: Vec<u8>,
}

impl<'a> Server<'a> {
    pub fn new(cfg: &'a ServerConfig, rng: Rng) -> Server<'a> {
        Server { cfg, table: CidTable::new(), conns: Vec::new(), next_id: 0, rng, out: Vec::new() }
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
        self.conns.iter().filter_map(|c| c.q.conn().next_timeout()).min()
    }

    pub fn on_datagram(&mut self, d: &[u8], from: SocketAddr, now: u64, send: &mut Outbox) -> io::Result<()> {
        let mut app = Vec::new();
        // The sole version_negotiation call site (RFC 9000 §17.2.1) is route.
        match route(d, &self.table) {
            Route::VersionNegotiation(v) => send.push((v, from)),
            Route::Reset(id) => {
                if let (Some(i), Some(t)) = (self.index(id), d.last_chunk::<16>()) {
                    let c = &mut self.conns[i];
                    c.q.on_reset_candidate(t, now, &mut app);
                    c.take_requests(&mut app);
                    self.service(i, now, send);
                }
            }
            Route::Existing(id) => {
                if let Some(i) = self.index(id) {
                    let r = rand(self.rng)?;
                    let c = &mut self.conns[i];
                    let (p, new) = match c.addrs.iter().position(|a| *a == from) {
                        Some(p) => (p, false),
                        None => {
                            c.addrs.push(from);
                            (c.addrs.len() - 1, true)
                        }
                    };
                    c.q.receive(d, p as u64, now, &r, &mut app);
                    c.take_requests(&mut app);
                    if new && c.q.conn().path_state(p as u64).is_none() {
                        c.addrs.truncate(p); // no slot for an unaccepted path
                    }
                    self.service(i, now, send);
                }
            }
            Route::NewInitial => {
                let r = rand(self.rng)?;
                if let Some(q) = QuicServer::accept(self.cfg, d, 0, now, &r, &local_params(), &mut app) {
                    let mut c = Conn { id: self.next_id, q, addrs: vec![from], owed: Vec::new() };
                    c.take_requests(&mut app);
                    self.conns.push(c);
                    self.next_id += 1;
                    self.service(self.conns.len() - 1, now, send);
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
            if matches!(self.conns[i].q.conn().next_timeout(), Some(t) if t <= now) {
                let mut r = [0u8; RAND_LEN];
                (self.rng)(&mut r)?;
                let mut app = Vec::new();
                let c = &mut self.conns[i];
                c.q.on_timeout(now, &r, &mut app);
                c.take_requests(&mut app);
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

    /// In `settled_later`'s order: the CID updates, the responses, then the datagrams, then the
    /// removal of a closed connection. Returns whether the connection at `i` was removed.
    fn service(&mut self, i: usize, now: u64, send: &mut Outbox) -> bool {
        let c = &mut self.conns[i];
        let mut ups = Vec::new();
        c.q.poll_cid_updates(&mut ups);
        for u in &ups {
            self.table.apply(c.id, u); // false: a key collision, issue_cids' ponytail
        }
        c.respond();
        let mut drained = false;
        for _ in 0..MAX_POLLS {
            match c.q.transmit(now, &mut self.out) {
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
        if c.q.conn().is_closed() {
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
pub fn run(sock: UdpSocket, cfg: &ServerConfig) -> io::Result<()> {
    let start = Instant::now();
    let us = || start.elapsed().as_micros() as u64;
    let mut srv = Server::new(cfg, fill_random);
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

// ponytail: std has no base64; this is the strict standard-alphabet decoder (padding only at the end, no stray characters, zero trailing bits).
fn base64(s: &[u8]) -> Option<Vec<u8>> {
    if s.len() % 4 != 0 {
        return None;
    }
    let mut out = Vec::with_capacity(s.len() / 4 * 3);
    for (n, q) in s.chunks(4).enumerate() {
        let last = (n + 1) * 4 == s.len();
        let pad = q.iter().rev().take_while(|c| **c == b'=').count();
        if pad > 2 || (pad > 0 && !last) {
            return None;
        }
        let mut acc = 0u32;
        for c in &q[..4 - pad] {
            let v = match c {
                b'A'..=b'Z' => c - b'A',
                b'a'..=b'z' => c - b'a' + 26,
                b'0'..=b'9' => c - b'0' + 52,
                b'+' => 62,
                b'/' => 63,
                _ => return None,
            };
            acc = acc << 6 | v as u32;
        }
        acc <<= 6 * pad as u32;
        if acc & ((1 << (8 * pad)) - 1) != 0 {
            return None; // non-zero trailing bits
        }
        out.extend_from_slice(&acc.to_be_bytes()[1..4 - pad]);
    }
    Some(out)
}

/// The PEM blocks of `pem` as (label, DER); anything but whitespace outside a block is an error.
fn pem_blocks(pem: &[u8]) -> Result<Vec<(String, Vec<u8>)>, String> {
    let bad = || "malformed PEM".to_string();
    let text = std::str::from_utf8(pem).map_err(|_| bad())?;
    let mut blocks = Vec::new();
    let mut open: Option<(String, Vec<u8>)> = None;
    for line in text.lines() {
        let line = line.trim();
        match (&mut open, line.strip_prefix("-----BEGIN ").and_then(|l| l.strip_suffix("-----")), line.strip_prefix("-----END ").and_then(|l| l.strip_suffix("-----"))) {
            (None, Some(label), _) => open = Some((label.to_string(), Vec::new())),
            (Some((label, body)), _, Some(end)) if end == label => {
                let der = base64(body).ok_or_else(bad)?;
                blocks.push((std::mem::take(label), der));
                open = None;
            }
            (Some((_, body)), None, None) => body.extend_from_slice(line.as_bytes()),
            (None, None, None) if line.is_empty() => {}
            _ => return Err(bad()),
        }
    }
    if open.is_some() {
        return Err(bad());
    }
    Ok(blocks)
}

/// One DER element of `tag` at the front of `b`: (content, rest). Definite, minimal lengths only.
fn der<'a>(b: &'a [u8], tag: u8) -> Option<(&'a [u8], &'a [u8])> {
    let (&t, b) = b.split_first()?;
    let (&l, b) = b.split_first()?;
    let (len, b) = match l {
        0..=0x7f => (l as usize, b),
        0x81..=0x83 => {
            let n = (l & 0x7f) as usize;
            let (lb, b) = b.split_at_checked(n)?;
            let len = lb.iter().fold(0usize, |a, x| a << 8 | *x as usize);
            if lb[0] == 0 || len < 0x80 {
                return None;
            }
            (len, b)
        }
        _ => return None,
    };
    if t != tag || len > b.len() {
        return None;
    }
    Some(b.split_at(len))
}

const OID_EC_PUBLIC_KEY: &[u8] = &[0x2a, 0x86, 0x48, 0xce, 0x3d, 0x02, 0x01];
const OID_PRIME256V1: &[u8] = &[0x2a, 0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07];
const OID_RSA: &[u8] = &[0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x01];

/// The P-256 scalar of a PKCS#8 `PrivateKeyInfo` (RFC 5208) holding an RFC 5915 `ECPrivateKey`.
/// Every error is a fixed string; nothing of the key is echoed.
fn pkcs8_p256_scalar(k: &[u8]) -> Result<[u8; 32], String> {
    let bad = || "malformed PKCS#8 key".to_string();
    let (info, rest) = der(k, 0x30).ok_or_else(bad)?;
    if !rest.is_empty() {
        return Err(bad());
    }
    let (ver, info) = der(info, 0x02).ok_or_else(bad)?;
    let (alg, info) = der(info, 0x30).ok_or_else(bad)?;
    let (key, tail) = der(info, 0x04).ok_or_else(bad)?;
    if ver != [0] || !tail.is_empty() {
        return Err(bad());
    }
    let (oid, params) = der(alg, 0x06).ok_or_else(bad)?;
    if oid == OID_RSA {
        return Err("RSA keys are not loaded before Phase 7: rsa_key_wf needs a primality check".into());
    }
    if oid != OID_EC_PUBLIC_KEY {
        return Err("unsupported key algorithm".into());
    }
    match der(params, 0x06) {
        Some((c, [])) if c == OID_PRIME256V1 => {}
        _ => return Err("the key is not on prime256v1".into()),
    }
    let (ec, rest) = der(key, 0x30).ok_or_else(bad)?;
    if !rest.is_empty() {
        return Err(bad());
    }
    let (ver, ec) = der(ec, 0x02).ok_or_else(bad)?;
    let (d, mut ec) = der(ec, 0x04).ok_or_else(bad)?;
    if ver != [1] {
        return Err(bad());
    }
    // Optional [0] parameters (the same curve) and [1] publicKey; nothing else may follow.
    if ec.first() == Some(&0xa0) {
        let (p, r) = der(ec, 0xa0).ok_or_else(bad)?;
        if der(p, 0x06) != Some((OID_PRIME256V1, &[][..])) {
            return Err("the key is not on prime256v1".into());
        }
        ec = r;
    }
    if ec.first() == Some(&0xa1) {
        let (p, r) = der(ec, 0xa1).ok_or_else(bad)?;
        if der(p, 0x03).is_none() || !r.is_empty() {
            return Err(bad());
        }
        ec = r;
    }
    if !ec.is_empty() {
        return Err(bad());
    }
    d.try_into().map_err(|_| "the key scalar is not 32 bytes".to_string())
}

/// The server configuration for a PEM certificate chain (leaf first) and a PKCS#8 P-256 key.
/// What it establishes: the scalar is in [1, n-1] and the chain fits (`ServerConfig::wf`), and
/// the key's public point occurs in the leaf. That the chain is X.509v3, permits
/// digitalSignature and matches `chain_schemes` is the operator's (TRUSTED.md).
pub fn load_config(cert_pem: &[u8], key_pem: &[u8], chain_schemes: Vec<u16>) -> Result<ServerConfig, String> {
    let mut chain = Vec::new();
    for (label, d) in pem_blocks(cert_pem)? {
        if label != "CERTIFICATE" {
            return Err("the certificate file holds a block that is not a CERTIFICATE".into());
        }
        chain.push(d);
    }
    if chain.is_empty() {
        return Err("no certificate".into());
    }
    let mut keys = pem_blocks(key_pem)?;
    if keys.len() != 1 || keys[0].0 != "PRIVATE KEY" {
        return Err("the key file needs exactly one PRIVATE KEY block".into());
    }
    let (_, k) = keys.remove(0);
    let (key, point) = p256_signing_key(pkcs8_p256_scalar(&k)?).ok_or("scalar out of range")?;
    if !chain[0].windows(point.len()).any(|w| w == point) {
        return Err("key does not match the certificate".into());
    }
    if chain.len() >= 2 && chain_schemes.is_empty() {
        return Err("a chain needs --chain-schemes".into());
    }
    build_config(vec![CertChain { der: chain, chain_schemes, key }]).ok_or_else(|| "chain too large".into())
}
