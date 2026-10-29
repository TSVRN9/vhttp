//! Phase 3d datagram routing (RFC 9000 §5.2.2, §6, §10.3, §14.1).
use quic::route::*;

const C7: [u8; 8] = [0x83, 0x94, 0xc8, 0xf0, 0x3e, 0x51, 0x57, 0x08];

fn hex(s: &str) -> Vec<u8> {
    let s: String = s.split_whitespace().collect();
    (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap()).collect()
}

fn padded(mut b: Vec<u8>, n: usize) -> Vec<u8> {
    b.resize(n, 0);
    b
}

/// RFC 9001 §A.2's Initial header up to the packet number.
const A2H: &str = "c000000001088394c8f03e5157080000449e";

fn table() -> CidTable {
    let mut t = CidTable::new();
    assert!(t.apply(7, &CidUpdate::Add(C7.to_vec())));
    assert!(t.apply(7, &CidUpdate::Add(vec![0x11; 8])));
    assert!(t.apply(7, &CidUpdate::AddToken([0x77; 16])));
    t
}

fn short(dcid: &[u8], rest: &[u8]) -> Vec<u8> {
    [&[0x40][..], dcid, rest].concat()
}

#[test]
fn route_existing() {
    let t = table();
    assert_eq!(route(&padded(hex(A2H), 1200), &t), Route::Existing(7));
    assert_eq!(route(&short(&[0x11; 8], &[0; 20]), &t), Route::Existing(7));
    assert_eq!(t.lookup(&C7), Some(7));
}

#[test]
fn route_new_initial() {
    let empty = CidTable::new();
    assert_eq!(route(&padded(hex(A2H), 1200), &empty), Route::NewInitial);
    // A 7-byte DCID.
    assert_eq!(route(&padded(hex("c00000000107 8394c8f03e5157 00 00 449e"), 1200), &empty), Route::Drop);
    // 1199 bytes, Length 0x449d so the header still parses.
    assert_eq!(route(&padded(hex("c000000001088394c8f03e5157080000449d"), 1199), &empty), Route::Drop);
}

#[test]
fn route_vn() {
    let mut b = vec![0xc0, 0x1a, 0x2a, 0x3a, 0x4a, 8];
    b.extend(hex("0001020304050607"));
    b.push(4);
    b.extend(hex("0a0b0c0d"));
    let t = table();
    assert_eq!(
        route(&padded(b.clone(), 1200), &t),
        Route::VersionNegotiation(hex("c000000000040a0b0c0d08000102030405060700000001"))
    );
    assert_eq!(route(&padded(b, 1199), &t), Route::Drop);
}

#[test]
fn route_reset() {
    let t = table();
    let r = short(&[0x22; 8], &[[0x33; 5].as_slice(), &[0x77; 16]].concat());
    assert_eq!(r.len(), 30);
    assert_eq!(route(&r, &t), Route::Reset(7));
    let r2 = short(&[0x22; 8], &[[0x33; 5].as_slice(), &[0x78; 16]].concat());
    assert_eq!(route(&r2, &t), Route::Drop);
    // A Handshake long header with an unknown DCID.
    let hs = padded(hex("e00000000108 2222222222222222 00 4040"), 1200);
    assert_eq!(route(&hs, &t), Route::Drop);
}

/// §10.3: the reset check precedes NewInitial, so a long header ending in a token is a reset.
#[test]
fn route_reset_before_new_initial() {
    let t = table();
    assert!(t.has_room());
    let mut b = padded(hex("c000000001082222222222222222 0000449e"), 1200);
    b[1184..].copy_from_slice(&[0x77; 16]);
    assert_eq!(route(&b, &t), Route::Reset(7));
    b[1199] = 0x78;
    assert_eq!(route(&b, &t), Route::NewInitial);
}

#[test]
fn table_rules() {
    let mut t = table();
    assert!(!t.apply(8, &CidUpdate::Add(vec![0x11; 8])));
    assert_eq!(t.lookup(&[0x11; 8]), Some(7));
    assert!(!t.apply(8, &CidUpdate::Remove(vec![0x11; 8])));
    assert!(t.apply(7, &CidUpdate::Remove(vec![0x11; 8])));
    assert_eq!(t.lookup(&[0x11; 8]), None);
    assert!(!t.apply(8, &CidUpdate::AddToken([0x77; 16])));
    assert!(!t.apply(8, &CidUpdate::RemoveToken([0x77; 16])));
    assert_eq!(t.reset_owner(&[0x77; 16]), Some(7));
    assert!(t.apply(9, &CidUpdate::AddToken([0x99; 16])));
    t.remove_conn(7);
    assert_eq!(t.lookup(&C7), None);
    assert_eq!(t.reset_owner(&[0x77; 16]), None);
    assert_eq!(t.reset_owner(&[0x99; 16]), Some(9));
    assert!(t.apply(9, &CidUpdate::RemoveToken([0x99; 16])));
    assert_eq!(t.reset_owner(&[0x99; 16]), None);
}

fn cid(c: u64, i: u64) -> Vec<u8> {
    [(c as u32).to_be_bytes(), (i as u32).to_be_bytes()].concat()
}

/// Admission counts connections: `MAX_CONNS` of them, each with `PER_CONN` CIDs, all fit.
#[test]
fn table_full() {
    assert_eq!((PER_CONN, MAX_CONNS, MAX_TABLE), (5, 102, 512));
    let mut t = CidTable::new();
    for c in 0..MAX_CONNS as u64 {
        assert!(t.has_room());
        for i in 0..PER_CONN as u64 {
            assert!(t.apply(c, &CidUpdate::Add(cid(c, i))));
        }
    }
    assert!(!t.has_room());
    let mut unknown = hex(A2H);
    unknown[6] = 0x00;
    assert_eq!(route(&padded(unknown, 1200), &t), Route::Drop);
    let mut known = hex(A2H);
    known[6..14].copy_from_slice(&cid(9, 4));
    assert_eq!(route(&padded(known, 1200), &t), Route::Existing(9));
    // A new connection is refused, and so is a 6th entry.
    assert!(!t.apply(500, &CidUpdate::Add(vec![0xbb; 8])));
    assert!(!t.apply(3, &CidUpdate::Add(vec![0xbc; 8])));
    assert_eq!(t.lookup(&[0xbb; 8]), None);
    // A Remove frees a slot of that connection only.
    assert!(t.apply(3, &CidUpdate::Remove(cid(3, 0))));
    assert!(t.apply(3, &CidUpdate::Add(vec![0xbc; 8])));
    assert!(!t.apply(500, &CidUpdate::Add(vec![0xbb; 8])));
    t.remove_conn(7);
    assert!(t.has_room());
    assert!(t.apply(500, &CidUpdate::Add(vec![0xbb; 8])));
    assert!(!t.has_room());
}

/// A connection stays admitted with no CIDs, until `remove_conn`.
#[test]
fn admitted_until_removed() {
    let mut t = CidTable::new();
    for c in 0..MAX_CONNS as u64 {
        assert!(t.apply(c, &CidUpdate::Add(cid(c, 0))));
    }
    assert!(t.apply(1, &CidUpdate::Remove(cid(1, 0))));
    assert!(!t.has_room());
    assert!(t.apply(1, &CidUpdate::Add(cid(1, 1))));
    t.remove_conn(1);
    assert!(t.has_room());
}

#[test]
fn remove_conn_frees() {
    let mut t = CidTable::new();
    for c in 1..=100u64 {
        for i in 0..5 {
            assert!(t.apply(c, &CidUpdate::Add(cid(c, i))));
        }
    }
    assert!(t.apply(1, &CidUpdate::AddToken([1; 16])));
    assert!(t.apply(200, &CidUpdate::Add(vec![5; 8])));
    for c in 1..=100u64 {
        t.remove_conn(c);
    }
    assert_eq!(t.lookup(&[5; 8]), Some(200));
    let (c, k, n) = t.capacities();
    assert!(c < 500 && n < 100, "{c} {n}");
    assert_eq!(k, 0);
}
