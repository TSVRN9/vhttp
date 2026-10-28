mod common;

use common::*;
use tls::ch_ext::KeyShareEntry;
use tls::client_hello::*;

type Exts = Vec<(u16, Vec<u8>)>;

fn p(msg: &[u8]) -> Result<ClientHello, u64> {
    parse_client_hello(&msg[4..])
}

/// `msg` with `f` applied to its extension list.
fn with(msg: &[u8], f: impl FnOnce(&mut Exts)) -> Vec<u8> {
    let (h, mut e) = split_ch(msg);
    f(&mut e);
    join_ch(&h, &e)
}

/// `msg`'s extensions after the head `h`.
fn with_head(msg: &[u8], h: Vec<u8>) -> Vec<u8> {
    join_ch(&h, &split_ch(msg).1)
}

/// A handshake message of type client_hello around `body` (no extension block added).
fn hs(body: &[u8]) -> Vec<u8> {
    let mut m = vec![1, 0, (body.len() >> 8) as u8, body.len() as u8];
    m.extend_from_slice(body);
    m
}

fn vec1(c: &[u8]) -> Vec<u8> {
    let mut v = vec![c.len() as u8];
    v.extend_from_slice(c);
    v
}

fn vec2(c: &[u8]) -> Vec<u8> {
    let mut v = vec![(c.len() >> 8) as u8, c.len() as u8];
    v.extend_from_slice(c);
    v
}

fn u16s(xs: &[u16]) -> Vec<u8> {
    xs.iter().flat_map(|x| x.to_be_bytes()).collect()
}

fn ks(group: u16, kx: &[u8]) -> Vec<u8> {
    let mut v = group.to_be_bytes().to_vec();
    v.extend(vec2(kx));
    v
}

fn body_of(e: &Exts, ty: u16) -> Vec<u8> {
    e.iter().find(|(t, _)| *t == ty).expect("extension present").1.clone()
}

fn set(e: &mut Exts, ty: u16, d: Vec<u8>) {
    e.iter_mut().find(|(t, _)| *t == ty).expect("extension present").1 = d;
}

fn remove(e: &mut Exts, ty: u16) {
    let n = e.len();
    e.retain(|(t, _)| *t != ty);
    assert_eq!(e.len(), n - 1, "removed exactly one {ty:#x}");
}

fn qtp() -> (u16, Vec<u8>) {
    (0x39, vec![0x01, 0x00])
}

/// RFC 8448 §4's (valid) pre_shared_key body.
fn psk() -> Vec<u8> {
    body_of(&split_ch(R4_CH).1, 0x29)
}

fn a2_head() -> Vec<u8> {
    head(0x0303, &[], &[0x1301, 0x1302], &[0])
}

#[test]
fn helpers_rebuild() {
    for m in [A2_CH, CURL_CH, R3_CH, R4_CH, R5_CH1, R5_CH2] {
        assert_eq!(with(m, |_| {}), m);
    }
    assert_eq!(with_head(A2_CH, a2_head()), A2_CH);
}

#[test]
fn a2_ch() {
    let c = p(A2_CH).unwrap();
    assert_eq!(c.random.to_vec(), hex("ebf8fa56f12939b9584a3896472ec40bb863cfd3e86804fe3a47f06a2b69484c"));
    assert_eq!(c.legacy_session_id, Vec::<u8>::new());
    assert_eq!(c.cipher_suites, vec![0x1301, 0x1302]);
    assert_eq!(c.versions, vec![0x0304]);
    assert_eq!(c.groups, Some(vec![0x1d, 0x17, 0x18]));
    let x = hex("9370b2c9caa47fbabaf4559fedba753de171fa71f50f1ce15d43e994ec74d748");
    assert_eq!(c.key_shares, Some(vec![KeyShareEntry { group: 0x1d, key_exchange: x }]));
    assert_eq!(c.sig_algs, vec![0x0403, 0x0503, 0x0603, 0x0203, 0x0804, 0x0805, 0x0806]);
    assert_eq!(c.sig_algs_cert, None);
    assert_eq!(c.alpn, Some(vec![b"alpn".to_vec()]));
    assert_eq!(c.server_name, Some(b"example.com".to_vec()));
    let tp = hex(
        "0408ffffffffffffffff05048000ffff07048000ffff0801100104800075300901100f088394c8f03e51570806048000ffff",
    );
    assert_eq!(tp.len(), 50);
    assert_eq!(c.transport_params, tp);
}

#[test]
fn curl_ch() {
    let c = p(CURL_CH).unwrap();
    assert_eq!(c.cipher_suites, vec![0x1302, 0x1303, 0x1301, 0x1304]);
    assert_eq!(c.versions, vec![0x0304]);
    assert!(c.groups.as_ref().unwrap().contains(&0x0017));
    let k = c.key_shares.as_ref().unwrap();
    assert_eq!(k.iter().map(|e| e.group).collect::<Vec<_>>(), vec![0x11ec, 0x001d]);
    assert_eq!(k.iter().map(|e| e.key_exchange.len()).collect::<Vec<_>>(), vec![1216, 32]);
    assert_eq!(c.alpn, Some(vec![b"h3".to_vec(), b"h3-29".to_vec()]));
    assert_eq!(c.server_name, Some(b"localhost".to_vec()));
    assert_eq!(c.transport_params.len(), 68);
    assert!(c.sig_algs.contains(&0x0403) && c.sig_algs.contains(&0x0804));
}

#[test]
fn rfc8448_needs_qtp() {
    for m in [R3_CH, R5_CH1, R4_CH] {
        assert_eq!(p(m), Err(0x16d));
    }
    let c = p(&with(R3_CH, |e| e.push(qtp()))).unwrap();
    assert_eq!(c.groups, Some(vec![0x1d, 0x17, 0x18, 0x19, 0x100, 0x101, 0x102, 0x103, 0x104]));
    assert_eq!(c.alpn, None);
    assert_eq!(c.transport_params, vec![0x01, 0x00]);
    assert!(split_ch(R3_CH).1.iter().any(|(t, _)| *t == 0x23), "session_ticket is in R3_CH");
}

#[test]
fn rfc8448_s5_ch2_cookie() {
    assert_eq!(p(R5_CH2), Err(0x12f));
    assert_eq!(p(&with(R5_CH2, |e| e.push(qtp()))), Err(0x12f));
}

#[test]
fn rfc8448_s4_psk_not_last() {
    assert_eq!(p(&with(R4_CH, |e| e.push(qtp()))), Err(0x12f));
    let m = with(R4_CH, |e| {
        let i = e.iter().position(|(t, _)| *t == 0x29).unwrap();
        e.insert(i, qtp());
    });
    let c = p(&m).unwrap();
    assert_eq!(c.transport_params, vec![0x01, 0x00]);
    assert_eq!(c.groups, Some(vec![0x1d, 0x17, 0x18, 0x19, 0x100, 0x101, 0x102, 0x103, 0x104]));
    let x = hex("e4ffb68ac05f8d96c99da26698346c6be16482badddafe051a66b4f18d668f0b");
    assert_eq!(c.key_shares, Some(vec![KeyShareEntry { group: 0x1d, key_exchange: x }]));
    assert_eq!(c.server_name, Some(b"server".to_vec()));
}

#[test]
fn grease_ignored() {
    let m = with(&with_head(A2_CH, head(0x0303, &[], &[0x6a6a, 0x1301], &[0])), |e| {
        e.insert(0, (0x0a0a, vec![]));
        set(e, 0x2b, vec1(&u16s(&[0x3a3a, 0x0304])));
        set(e, 0x0a, vec2(&u16s(&[0x4a4a, 0x1d, 0x17, 0x18])));
        let mut sa = vec![0x4a, 0x4a];
        sa.extend_from_slice(&body_of(e, 0x0d)[2..]);
        set(e, 0x0d, vec2(&sa));
        let mut k = ks(0x5a5a, &[0x00]);
        k.extend_from_slice(&body_of(e, 0x33)[2..]);
        set(e, 0x33, vec2(&k));
        let mut a = vec1(b"\x7a\x7a");
        a.extend_from_slice(&body_of(e, 0x10)[2..]);
        set(e, 0x10, vec2(&a));
        e.push((0xfafa, vec![0]));
    });
    let c = p(&m).unwrap();
    assert_eq!(c.cipher_suites, vec![0x6a6a, 0x1301]);
    assert_eq!(c.versions, vec![0x3a3a, 0x0304]);
    assert_eq!(c.groups, Some(vec![0x4a4a, 0x1d, 0x17, 0x18]));
    assert_eq!(c.sig_algs[0], 0x4a4a);
    assert_eq!(c.sig_algs.len(), 8);
    let k = c.key_shares.unwrap();
    assert_eq!(k[0], KeyShareEntry { group: 0x5a5a, key_exchange: vec![0x00] });
    assert_eq!(k[1].group, 0x1d);
    assert_eq!(c.alpn, Some(vec![b"\x7a\x7a".to_vec(), b"alpn".to_vec()]));
}

#[test]
fn ch_errors() {
    let (h, _) = split_ch(A2_CH);
    let mut odd_suites = h[..35].to_vec();
    odd_suites.extend([0x00, 0x03, 0x13, 0x01, 0x13, 0x01, 0x00]);
    let mut trailing = A2_CH.to_vec();
    trailing.push(0);
    let rows: Vec<(&str, Vec<u8>, u64)> = vec![
        ("truncated", A2_CH[..A2_CH.len() - 1].to_vec(), 0x132),
        ("session id 33", with_head(A2_CH, head(0x0303, &[7; 33], &[0x1301], &[0])), 0x132),
        ("suites odd length", with_head(A2_CH, odd_suites), 0x132),
        ("suites empty", with_head(A2_CH, head(0x0303, &[], &[], &[0])), 0x132),
        ("compression empty", with_head(A2_CH, head(0x0303, &[], &[0x1301], &[])), 0x132),
        ("block of 4, no versions", join_ch(&h, &[(0x1234, vec![])]), 0x146),
        ("empty block, no versions", join_ch(&h, &[]), 0x146),
        ("trailing byte", trailing, 0x132),
        ("key_share 00", with(A2_CH, |e| set(e, 0x33, vec![0])), 0x132),
        ("early_data [0]", with(A2_CH, |e| e.push((0x2a, vec![0]))), 0x132),
        ("alpn empty name", with(A2_CH, |e| set(e, 0x10, hex("0003000141"))), 0x132),
        ("no extension block", hs(&h), 0x146),
        ("legacy_version 0x0300", with_head(A2_CH, head(0x0300, &[], &[0x1301], &[0])), 0x146),
        ("versions [0x0303]", with(A2_CH, |e| set(e, 0x2b, hex("020303"))), 0x146),
        ("versions absent", with(A2_CH, |e| remove(e, 0x2b)), 0x146),
        ("compression [0, 1]", with_head(A2_CH, head(0x0303, &[], &[0x1301], &[0, 1])), 0x12f),
        ("compression [1]", with_head(A2_CH, head(0x0303, &[], &[0x1301], &[1])), 0x12f),
        ("session id 32", with_head(A2_CH, head(0x0303, &[7; 32], &[0x1301], &[0])), 0x0a),
        ("cookie", with(A2_CH, |e| e.push((0x2c, hex("0001aa")))), 0x12f),
        ("no signature_algorithms", with(A2_CH, |e| remove(e, 0x0d)), 0x16d),
        (
            "no groups, no key_share, no psk",
            with(A2_CH, |e| {
                remove(e, 0x0a);
                remove(e, 0x33);
            }),
            0x16d,
        ),
        ("no key_share", with(A2_CH, |e| remove(e, 0x33)), 0x16d),
        ("no supported_groups", with(A2_CH, |e| remove(e, 0x0a)), 0x16d),
        (
            "psk without modes",
            with(A2_CH, |e| {
                remove(e, 0x2d);
                e.push((0x29, psk()));
            }),
            0x16d,
        ),
        ("no qtp", with(A2_CH, |e| remove(e, 0x39)), 0x16d),
        (
            "order: compression before missing_extension",
            with(&with_head(A2_CH, head(0x0303, &[], &[0x1301], &[1])), |e| remove(e, 0x39)),
            0x12f,
        ),
        (
            "order: duplicate before version",
            with(A2_CH, |e| {
                set(e, 0x2b, hex("020303"));
                e.insert(0, (0x2b, hex("020303")));
            }),
            0x12f,
        ),
        (
            "order: bodies before legacy_version",
            with(&with_head(A2_CH, head(0x0300, &[], &[0x1301], &[0])), |e| set(e, 0x33, vec![0])),
            0x132,
        ),
        (
            "order: legacy_version before compression",
            with_head(A2_CH, head(0x0300, &[], &[0x1301], &[1])),
            0x146,
        ),
        (
            "order: versions before compression",
            with(&with_head(A2_CH, head(0x0303, &[], &[0x1301], &[1])), |e| remove(e, 0x2b)),
            0x146,
        ),
        (
            "order: compression before session id",
            with_head(A2_CH, head(0x0303, &[7; 32], &[0x1301], &[1])),
            0x12f,
        ),
        (
            "order: session id before cookie",
            with(&with_head(A2_CH, head(0x0303, &[7; 32], &[0x1301], &[0])), |e| {
                e.push((0x2c, hex("0001aa")))
            }),
            0x0a,
        ),
        (
            "order: duplicate before bodies",
            with(A2_CH, |e| {
                set(e, 0x33, vec![0]);
                e.insert(0, (0x0a0a, vec![]));
                e.insert(1, (0x0a0a, vec![]));
            }),
            0x12f,
        ),
    ];
    for (name, m, want) in rows {
        assert_eq!(p(&m).err(), Some(want), "{name}");
    }
}

#[test]
fn ch_oks() {
    let c = p(&with(A2_CH, |e| remove(e, 0x10))).unwrap();
    assert_eq!(c.alpn, None);
    let c = p(&with(A2_CH, |e| {
        remove(e, 0x0a);
        remove(e, 0x33);
        e.push((0x29, psk()));
    }))
    .unwrap();
    assert_eq!(c.groups, None);
    assert_eq!(c.key_shares, None);
    let c = p(&with(A2_CH, |e| e.push((0x32, hex("00020403"))))).unwrap();
    assert_eq!(c.sig_algs_cert, Some(vec![0x0403]));
}
