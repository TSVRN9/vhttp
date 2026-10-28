mod common;

use common::*;
use tls::ch_ext::*;
use tls::codes::*;
use tls::ext::parse_ext_list;

/// The extension bodies of a ClientHello message (header, version, random, session id,
/// suites and compression skipped).
fn bodies(ch: &[u8]) -> Vec<(u16, Vec<u8>)> {
    let mut i = 4 + 2 + 32;
    i += 1 + ch[i] as usize;
    i += 2 + (((ch[i] as usize) << 8) | ch[i + 1] as usize);
    i += 1 + ch[i] as usize;
    let n = ((ch[i] as usize) << 8) | ch[i + 1] as usize;
    assert_eq!(i + 2 + n, ch.len());
    parse_ext_list(&ch[i + 2..]).unwrap().into_iter().map(|e| (e.ty, e.data)).collect()
}

fn body(ch: &[u8], ty: u16) -> Vec<u8> {
    bodies(ch).into_iter().find(|(t, _)| *t == ty).expect("extension present").1
}

/// `len` as a `<_..ceiling>` length prefix of `ceiling`'s width, then `c`.
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

/// A length prefix that lies: `claimed` over `c`.
fn vec2_claim(claimed: usize, c: &[u8]) -> Vec<u8> {
    let mut v = vec![(claimed >> 8) as u8, claimed as u8];
    v.extend_from_slice(c);
    v
}

fn pairs(n: usize) -> Vec<u8> {
    (0..n).flat_map(|i| [(i >> 8) as u8, i as u8]).collect()
}

fn ks(group: u16, kx: &[u8]) -> Vec<u8> {
    let mut v = vec![(group >> 8) as u8, group as u8];
    v.extend(vec2(kx));
    v
}

fn ks_entry(group: u16, kx: &[u8]) -> KeyShareEntry {
    KeyShareEntry { group, key_exchange: kx.to_vec() }
}

#[test]
fn a2_bodies() {
    let b = |ty| body(A2_CH, ty);
    assert_eq!(parse_versions(&b(EXT_SUPPORTED_VERSIONS)), Some(vec![0x0304]));
    assert_eq!(parse_groups(&b(EXT_SUPPORTED_GROUPS)), Some(vec![0x1d, 0x17, 0x18]));
    assert_eq!(
        parse_sig_schemes(&b(EXT_SIGNATURE_ALGORITHMS)),
        Some(vec![0x0403, 0x0503, 0x0603, 0x0203, 0x0804, 0x0805, 0x0806])
    );
    assert_eq!(parse_alpn(&b(EXT_ALPN)), Some(vec![b"alpn".to_vec()]));
    assert_eq!(parse_server_name(&b(EXT_SERVER_NAME)), Some(Some(b"example.com".to_vec())));
    let x = hex("9370b2c9caa47fbabaf4559fedba753de171fa71f50f1ce15d43e994ec74d748");
    assert_eq!(b(EXT_KEY_SHARE).len(), 38);
    assert_eq!(parse_key_shares(&b(EXT_KEY_SHARE)), Some(vec![ks_entry(0x1d, &x)]));
    assert_eq!(parse_psk_modes(&b(EXT_PSK_KEY_EXCHANGE_MODES)), Some(vec![1]));
    assert_eq!(hex("020304"), b(EXT_SUPPORTED_VERSIONS));
    assert_eq!(hex("000504616c706e"), b(EXT_ALPN));
}

#[test]
fn curl_bodies() {
    let b = |ty| body(CURL_CH, ty);
    assert_eq!(parse_versions(&b(EXT_SUPPORTED_VERSIONS)), Some(vec![0x0304]));
    assert_eq!(
        parse_groups(&b(EXT_SUPPORTED_GROUPS)),
        Some(vec![
            0x11ec, 0x11eb, 0x11ed, 0x1d, 0x17, 0x1e, 0x19, 0x18, 0x100, 0x101, 0x102, 0x103,
            0x104
        ])
    );
    assert_eq!(
        parse_sig_schemes(&b(EXT_SIGNATURE_ALGORITHMS)),
        Some(vec![
            0x0904, 0x0905, 0x0906, 0x0403, 0x0503, 0x0603, 0x0807, 0x0808, 0x0809, 0x080a,
            0x080b, 0x0804, 0x0805, 0x0806, 0x0401, 0x0501, 0x0601
        ])
    );
    assert_eq!(
        parse_alpn(&b(EXT_ALPN)),
        Some(vec![b"h3".to_vec(), b"h3-29".to_vec()])
    );
    assert_eq!(parse_server_name(&b(EXT_SERVER_NAME)), Some(Some(b"localhost".to_vec())));
    assert_eq!(parse_psk_modes(&b(EXT_PSK_KEY_EXCHANGE_MODES)), Some(vec![1]));
    let k = parse_key_shares(&b(EXT_KEY_SHARE)).unwrap();
    let shape: Vec<(u16, usize)> = k.iter().map(|e| (e.group, e.key_exchange.len())).collect();
    assert_eq!(shape, [(0x11ec, 1216), (0x001d, 32)]);
}

#[test]
fn versions_bounds() {
    assert_eq!(parse_versions(&hex("020304")), Some(vec![0x0304]));
    for b in ["00", "0102", "03030400", "020304ff", "04030400", ""] {
        assert_eq!(parse_versions(&hex(b)), None, "{b}");
    }
    let max = vec1(&pairs(127));
    assert_eq!(max.len(), 255);
    assert_eq!(parse_versions(&max).unwrap().len(), 127);
    assert_eq!(parse_versions(&vec1(&pairs(126))).unwrap().len(), 126);
    let mut over = vec![0xff];
    over.extend(vec![0u8; 255]);
    assert_eq!(parse_versions(&over), None);
    let mut trailing = max.clone();
    trailing.push(0);
    assert_eq!(parse_versions(&trailing), None);
}

fn u16_list_bounds(parse: fn(&[u8]) -> Option<Vec<u16>>, max_content: usize) {
    assert_eq!(parse(&hex("00020017")), Some(vec![0x17]));
    for b in ["", "00", "0000", "0001aa", "00030017aa", "0004001d", "00020017aa"] {
        assert_eq!(parse(&hex(b)), None, "{b}");
    }
    let max = vec2(&pairs(max_content / 2));
    assert_eq!(parse(&max).unwrap().len(), max_content / 2);
    let under = vec2(&pairs(max_content / 2 - 1));
    assert_eq!(parse(&under).unwrap().len(), max_content / 2 - 1);
    let mut over = vec2_claim(max_content + 1, &pairs(max_content / 2));
    over.push(0);
    assert_eq!(parse(&over), None);
    let mut trailing = max.clone();
    trailing.push(0);
    assert_eq!(parse(&trailing), None);
}

#[test]
fn groups_bounds() {
    u16_list_bounds(parse_groups, 65534);
    let mut odd_max = vec![0xff, 0xff];
    odd_max.extend(vec![0u8; 65535]);
    assert_eq!(parse_groups(&odd_max), None);
}

#[test]
fn sig_schemes_bounds() {
    u16_list_bounds(parse_sig_schemes, 65534);
    let mut odd_max = vec![0xff, 0xff];
    odd_max.extend(vec![0u8; 65535]);
    assert_eq!(parse_sig_schemes(&odd_max), None);
    assert_eq!(parse_sig_schemes(&vec2(&pairs(32766))).unwrap().len(), 32766);
}

#[test]
fn key_shares_bounds() {
    assert_eq!(parse_key_shares(&hex("0000")), Some(vec![]));
    assert_eq!(parse_key_shares(&hex("000500170001aa")), Some(vec![ks_entry(0x17, &[0xaa])]));
    for b in [
        "",
        "00",
        "000500170001aa00", // trailing byte
        "000400170000",     // empty key_exchange
        "00040017",         // entry cut off after the group
        "00030017aa",       // entry cut off inside its length
        "000500170002aa",   // inner vector overruns the outer one
        "0004001700ff",
        "000700170001aa0017", // second entry has no key_exchange
    ] {
        assert_eq!(parse_key_shares(&hex(b)), None, "{b}");
    }
    // the largest single entry: 2 + 2 + 65531 = 65535
    let big = vec![7u8; 65531];
    let max = vec2(&ks(0x1234, &big));
    assert_eq!(max.len(), 65537);
    assert_eq!(parse_key_shares(&max), Some(vec![ks_entry(0x1234, &big)]));
    // one more byte of key_exchange: the inner vector overruns the outer
    let over = vec2_claim(65535, &ks(0x1234, &vec![7u8; 65532]));
    assert_eq!(parse_key_shares(&over), None);
    let mut two = ks(0x1d, &[1, 2]);
    two.extend(ks(0x17, &[3]));
    assert_eq!(
        parse_key_shares(&vec2(&two)),
        Some(vec![ks_entry(0x1d, &[1, 2]), ks_entry(0x17, &[3])])
    );
}

#[test]
fn alpn_bounds() {
    assert_eq!(parse_alpn(&hex("00020161")), Some(vec![b"a".to_vec()]));
    for b in [
        "",
        "0000",         // below the list floor of 2
        "000100",       // floor not met
        "00020061",     // zero-length ProtocolName
        "0003000141",   // first ProtocolName of length 0
        "00040161 00 00", // trailing zero-length name
        "0003036161",   // ProtocolName overruns the list
        "00020161aa",   // trailing byte
        "0004 0161 0261", // second name overruns the list
    ] {
        assert_eq!(parse_alpn(&hex(b)), None, "{b}");
    }
    let n255 = vec![b'x'; 255];
    let mut list = vec![];
    for _ in 0..255 {
        list.extend(vec1(&n255));
    }
    list.extend(vec1(&vec![b'y'; 254]));
    assert_eq!(list.len(), 65535);
    let got = parse_alpn(&vec2(&list)).unwrap();
    assert_eq!(got.len(), 256);
    assert_eq!(got[255].len(), 254);
    list.push(0);
    assert_eq!(parse_alpn(&vec2_claim(65536 - 1, &list)), None);
    let one = vec1(&n255);
    assert_eq!(parse_alpn(&vec2(&one)), Some(vec![n255.clone()]));
}

#[test]
fn server_name_bounds() {
    let sn = |c: &[u8]| parse_server_name(&vec2(c));
    assert_eq!(parse_server_name(&hex("0005 01 0002 abcd")), Some(None));
    assert_eq!(parse_server_name(&hex("0003 01 0000")), Some(None));
    assert_eq!(sn(&hex("00 0001 61")), Some(Some(b"a".to_vec())));
    for b in [
        "",
        "0000",
        "0001 00",              // entry has no length
        "0003 00 0000",         // empty HostName
        "0004 00 0002 61",      // HostName overruns the list
        "0004 01 0002 61",      // unknown-type body overruns the list
        "0005 00 0001 61 aa", // entry cut off after the first
        "0006 00 0001 61 00 00", // second entry cut off
        "0003 00 0001 61",      // outer length shorter than entry
    ] {
        assert_eq!(parse_server_name(&hex(b)), None, "{b}");
    }
    // trailing byte after the list
    assert_eq!(parse_server_name(&hex("0004 00 0001 61 aa")), None);
    let mut t = vec2(&hex("00 0001 61"));
    t.push(0);
    assert_eq!(parse_server_name(&t), None);
    // maximum: 1 + 2 + 65532 = 65535
    let big = vec![b'h'; 65532];
    let mut e = vec![0u8];
    e.extend(vec2(&big));
    assert_eq!(e.len(), 65535);
    assert_eq!(sn(&e), Some(Some(big.clone())));
    // one more byte: inner overruns outer
    let mut e = vec![0u8];
    e.extend(vec2_claim(65533, &big));
    assert_eq!(parse_server_name(&vec2_claim(65535, &e)), None);
    // a second host_name is rejected; unknown types are skipped; validation covers the whole list
    assert_eq!(
        sn(&hex("07 0001 aa 00 0001 61")),
        Some(Some(b"a".to_vec()))
    );
    assert_eq!(sn(&hex("00 0001 61 00 0001 62")), None);
    assert_eq!(sn(&hex("00 0001 61 00 0002 62")), None);
    assert_eq!(sn(&hex("00 0001 61 07")), None);
    // unknown type, empty body, then a host_name
    assert_eq!(sn(&hex("07 0000 00 0001 61")), Some(Some(b"a".to_vec())));
}

#[test]
fn cookie_bounds() {
    assert!(cookie_ok(&hex("0001aa")));
    for b in ["", "00", "0000", "0002aa", "0001aaaa", "0001"] {
        assert!(!cookie_ok(&hex(b)), "{b}");
    }
    let max = vec2(&vec![1u8; 65535]);
    assert!(cookie_ok(&max));
    assert!(cookie_ok(&vec2(&vec![1u8; 65534])));
    assert!(!cookie_ok(&vec2_claim(65535, &vec![1u8; 65534])));
    let mut over = max.clone();
    over.push(0);
    assert!(!cookie_ok(&over));
}

#[test]
fn psk_modes_bounds() {
    assert_eq!(parse_psk_modes(&hex("0101")), Some(vec![1]));
    assert_eq!(parse_psk_modes(&hex("020001")), Some(vec![0, 1]));
    for b in ["", "00", "0201", "010101", "01"] {
        assert_eq!(parse_psk_modes(&hex(b)), None, "{b}");
    }
    let m = vec1(&vec![1u8; 255]);
    assert_eq!(parse_psk_modes(&m).unwrap().len(), 255);
    assert_eq!(parse_psk_modes(&vec1(&vec![1u8; 254])).unwrap().len(), 254);
    let mut over = m.clone();
    over.push(1);
    assert_eq!(parse_psk_modes(&over), None);
}

#[test]
fn early_data_bounds() {
    assert!(early_data_ok(&[]));
    assert!(!early_data_ok(&[0]));
    assert!(!early_data_ok(&[0, 0, 0, 0]));
}

/// `PskIdentity`: `opaque identity<1..2^16-1>; uint32 obfuscated_ticket_age`.
fn identity(id: &[u8]) -> Vec<u8> {
    let mut v = vec2(id);
    v.extend([0xde, 0xad, 0xbe, 0xef]);
    v
}

fn binder(n: usize) -> Vec<u8> {
    vec1(&vec![0x5a; n])
}

fn psk_body(ids: &[u8], binders: &[u8]) -> Vec<u8> {
    let mut v = vec2(ids);
    v.extend(vec2(binders));
    v
}

#[test]
fn offered_psks_bounds() {
    let min = psk_body(&identity(&[1]), &binder(32));
    assert_eq!(min.len(), 2 + 7 + 2 + 33);
    assert!(offered_psks_ok(&min));
    // identities one under the floor of 7: an empty identity makes 6 bytes
    let six = [0, 0, 1, 2, 3, 4];
    assert!(!offered_psks_ok(&psk_body(&six, &binder(32))));
    assert!(!offered_psks_ok(&psk_body(&[], &binder(32))));
    assert!(!offered_psks_ok(&psk_body(&[0, 1, 1, 1, 2, 3], &binder(32))));
    // binders one under the floor of 33
    assert!(!offered_psks_ok(&psk_body(&identity(&[1]), &[])));
    assert!(!offered_psks_ok(&psk_body(&identity(&[1]), &binder(31))));
    assert!(!offered_psks_ok(&psk_body(&identity(&[1]), &vec![0u8; 32])));
    // binder length bounds 32..255
    assert!(offered_psks_ok(&psk_body(&identity(&[1]), &binder(255))));
    assert!(offered_psks_ok(&psk_body(&identity(&[1]), &binder(33))));
    let mut b = binder(32);
    b.extend(binder(32));
    assert!(offered_psks_ok(&psk_body(&identity(&[1]), &b)));
    // trailing bytes
    let mut t = min.clone();
    t.push(0);
    assert!(!offered_psks_ok(&t));
    // identity overruns the identities vector; identity cut off before its age
    assert!(!offered_psks_ok(&psk_body(&[0, 4, 1, 2, 3, 4, 5, 6, 7], &binder(32))));
    assert!(!offered_psks_ok(&psk_body(&[0, 1, 1, 2, 3, 4, 0, 1], &binder(32))));
    assert!(!offered_psks_ok(&psk_body(&[0, 2, 1, 2, 3, 4, 5], &binder(32))));
    // a binder overruns the binders vector
    assert!(!offered_psks_ok(&psk_body(&identity(&[1]), &[40, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32])));
    // identities vector larger than the body
    let mut o = vec2_claim(8, &identity(&[1]));
    o.extend(vec2(&binder(32)));
    assert!(!offered_psks_ok(&o));
    // maximum identities: one identity of 65535 - 6 bytes
    let ids = identity(&vec![9u8; 65535 - 6]);
    assert_eq!(ids.len(), 65535);
    assert!(offered_psks_ok(&psk_body(&ids, &binder(32))));
    // many binders: 1985 of 32 bytes; a 28-byte one is too short
    let mut bs = vec![];
    for _ in 0..1985 {
        bs.extend(binder(32));
    }
    assert_eq!(bs.len(), 65505);
    assert!(offered_psks_ok(&psk_body(&identity(&[1]), &bs)));
    let mut short = bs.clone();
    short.extend(binder(28));
    assert!(!offered_psks_ok(&psk_body(&identity(&[1]), &short)));
    // the largest binders vector: 255 binders of 255 bytes, then one of 254
    let mut full = vec![];
    for _ in 0..255 {
        full.extend(binder(255));
    }
    full.extend(binder(254));
    assert_eq!(full.len(), 65535);
    assert!(offered_psks_ok(&psk_body(&identity(&[1]), &full)));
    let mut stray = bs.clone();
    stray.push(0);
    assert!(!offered_psks_ok(&psk_body(&identity(&[1]), &stray)));
}

#[test]
fn offered_psks_hand_built_ticket() {
    // a 32-byte identity with a ticket age, and one 32-byte binder (RFC 8446 §4.2.11 shape)
    let b = psk_body(&identity(&[7u8; 32]), &binder(32));
    assert!(offered_psks_ok(&b));
}

#[test]
fn r4_bodies() {
    assert_eq!(R4_CH.len(), 512);
    let psk = body(R4_CH, EXT_PRE_SHARED_KEY);
    assert_eq!(psk.len(), 221);
    assert!(offered_psks_ok(&psk));
    assert!(early_data_ok(&body(R4_CH, EXT_EARLY_DATA)));
    assert_eq!(parse_server_name(&body(R4_CH, EXT_SERVER_NAME)), Some(Some(b"server".to_vec())));
    assert_eq!(bodies(R4_CH).last().unwrap().0, EXT_PRE_SHARED_KEY);
}
