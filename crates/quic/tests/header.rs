use quic::header::*;

fn hex(s: &str) -> Vec<u8> {
    (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap()).collect()
}

#[test]
fn a2_client_initial_header() {
    let dcid = hex("8394c8f03e515708");
    let mut out = Vec::new();
    let off = serialize_long_header(LongType::Initial, &dcid, &[], 2, 4, 1178, &mut out);
    assert_eq!(out, hex("c300000001088394c8f03e5157080000449e00000002"));
    assert_eq!(off, 18);

    let mut pkt = hex("c000000001088394c8f03e5157080000449e");
    pkt.resize(1200, 0);
    assert_eq!(
        parse_header(&pkt, 8),
        Some(Header::Long {
            ty: LongType::Initial,
            dcid,
            scid: vec![],
            token: vec![],
            pn_offset: 18,
            packet_end: 1200,
        })
    );
}

#[test]
fn a3_server_initial_header() {
    let scid = hex("f067a5502a4262b5");
    let mut out = Vec::new();
    let off = serialize_long_header(LongType::Initial, &[], &scid, 1, 2, 115, &mut out);
    assert_eq!(out, hex("c1000000010008f067a5502a4262b50040750001"));
    assert_eq!(off, 18);

    // The real protected header: reserved and pn-length bits are not interpreted.
    let mut pkt = hex("cf000000010008f067a5502a4262b5004075");
    pkt.resize(135, 0);
    assert_eq!(
        parse_header(&pkt, 8),
        Some(Header::Long {
            ty: LongType::Initial,
            dcid: vec![],
            scid,
            token: vec![],
            pn_offset: 18,
            packet_end: 135,
        })
    );
}

#[test]
fn a5_short_header() {
    let mut out = Vec::new();
    let off = serialize_short_header(&[], false, false, 654360564, 3, &mut out);
    assert_eq!(out, hex("4200bff4"));
    assert_eq!(off, 1);
    assert_eq!(first_byte_pn_len(0x42), 3);
    assert!(!first_byte_key_phase(0x42));
}

#[test]
fn header_drops() {
    let v1 = [0, 0, 0, 1];
    let long = |b0: u8, rest: &[u8]| [&[b0][..], &v1, rest].concat();
    // Sanity: the base Initial (empty CIDs, empty token, Length 1, one byte) parses.
    assert!(parse_long_header(&long(0xc0, &[0, 0, 0, 1, 0])).is_some());
    // Fixed bit 0.
    assert_eq!(parse_long_header(&long(0x80, &[0, 0, 0, 1, 0])), None);
    // DCID length 21.
    let mut b = long(0xc0, &[21]);
    b.extend([0u8; 21]);
    b.extend([0, 0, 1, 0]);
    assert_eq!(parse_long_header(&b), None);
    // Retry.
    assert_eq!(parse_long_header(&long(0xf0, &[0, 0, 0, 1, 0, 0, 0, 0])), None);
    // Version 0.
    assert_eq!(parse_long_header(&[0x80, 0, 0, 0, 0, 0, 0, 0, 1, 0]), None);
    // Length one more than remains.
    assert_eq!(parse_long_header(&long(0xc0, &[0, 0, 0, 2, 0])), None);
    // Token length 5 with 2 bytes left.
    assert_eq!(parse_long_header(&long(0xc0, &[0, 0, 5, 0xaa, 0xbb])), None);
    // SCID length 21.
    let mut b = long(0xc0, &[0, 21]);
    b.extend([0u8; 21]);
    b.extend([0, 1, 0]);
    assert_eq!(parse_long_header(&b), None);
    // Short header: 20 bytes is too small, 21 is enough.
    assert_eq!(parse_header(&[0x40; 20], 8), None);
    assert!(parse_header(&[0x40; 21], 8).is_some());
    // Short header with fixed bit 0.
    assert_eq!(parse_header(&[0x00; 30], 8), None);
    assert_eq!(parse_header(&[], 8), None);
    assert_eq!(parse_long_header(&[]), None);
}

#[test]
fn unsupported_version() {
    let mut b = vec![0x80, 0x1a, 0x2a, 0x3a, 0x4a, 21];
    b.extend(1u8..=21);
    b.push(0);
    assert_eq!(
        parse_header(&b, 8),
        Some(Header::UnsupportedVersion {
            version: 0x1a2a3a4a,
            dcid: (1u8..=21).collect(),
            scid: vec![],
        })
    );
}

#[test]
fn reserved_bits() {
    assert!(reserved_bits_zero(0xc3, true));
    assert!(reserved_bits_zero(0x44, false));
    assert!(!reserved_bits_zero(0xcb, true));
    assert!(!reserved_bits_zero(0x48, false));
    assert!(first_byte_key_phase(0x44));
}

#[test]
fn header_roundtrip() {
    let dcid: Vec<u8> = (0..20).collect();
    let scid: Vec<u8> = (100..120).collect();
    let mut b = Vec::new();
    let off = serialize_long_header(LongType::Handshake, &dcid, &scid, 7, 1, 30, &mut b);
    b.extend([0xee; 30]);
    assert_eq!(first_byte_pn_len(b[0]), 1);
    assert_eq!(off, 48);
    assert_eq!(
        parse_header(&b, 8),
        Some(Header::Long {
            ty: LongType::Handshake,
            dcid,
            scid,
            token: vec![],
            pn_offset: 48,
            packet_end: b.len(),
        })
    );

    let dcid: Vec<u8> = (1..=8).collect();
    let mut b = Vec::new();
    let off = serialize_short_header(&dcid, true, true, 0x1234, 2, &mut b);
    b.resize(40, 0);
    assert_eq!(off, 9);
    assert_eq!(b[0], 0x65);
    assert!(first_byte_key_phase(b[0]));
    assert_eq!(first_byte_pn_len(b[0]), 2);
    assert!(reserved_bits_zero(b[0], false));
    assert_eq!(parse_header(&b, 8), Some(Header::Short { dcid, pn_offset: 9 }));
}
