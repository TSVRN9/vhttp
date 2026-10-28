use h3::qpack::int::*;

fn enc(n: u8, flags: u8, v: u64) -> Vec<u8> {
    let mut out = Vec::new();
    serialize_prefix_int(n, flags, v, &mut out);
    out
}

#[test]
fn rfc7541_c1() {
    for (n, v, bytes) in [
        (5u8, 10u64, vec![0x0au8]),
        (5, 1337, vec![0x1f, 0x9a, 0x0a]),
        (8, 42, vec![0x2a]),
    ] {
        assert_eq!(enc(n, 0, v), bytes);
        assert_eq!(
            parse_prefix_int(n, &bytes),
            PrefixInt::Value { value: v, consumed: bytes.len() }
        );
    }
}

#[test]
fn prefix_int_62bit_all_widths() {
    for n in 1..=8u8 {
        let b = enc(n, 0, PREFIX_INT_MAX);
        assert_eq!(
            parse_prefix_int(n, &b),
            PrefixInt::Value { value: PREFIX_INT_MAX, consumed: b.len() }
        );
    }
    // 2^62 with N=8: 255 + (2^62 - 255) as 7-bit groups.
    let mut b = vec![0xff];
    let mut r = (1u64 << 62) - 255;
    while r >= 128 {
        b.push((r & 127) as u8 | 128);
        r >>= 7;
    }
    b.push(r as u8);
    assert_eq!(parse_prefix_int(8, &b), PrefixInt::TooLarge);
}

#[test]
fn prefix_int_incomplete() {
    assert_eq!(parse_prefix_int(5, &[0x1f]), PrefixInt::Incomplete);
    assert_eq!(parse_prefix_int(5, &[0x1f, 0x9a]), PrefixInt::Incomplete);
    assert_eq!(parse_prefix_int(5, &[]), PrefixInt::Incomplete);
}

#[test]
fn prefix_int_flags_ignored() {
    assert_eq!(parse_prefix_int(5, &[0xea]), PrefixInt::Value { value: 10, consumed: 1 });
    assert_eq!(enc(5, 0xe0, 10), vec![0xea]);
}

#[test]
fn prefix_int_too_many_cont() {
    let mut b = vec![0x1f];
    b.extend([0x80; 11]);
    b.push(0x00);
    assert_eq!(parse_prefix_int(5, &b), PrefixInt::TooLarge);
}

#[test]
fn prefix_int_cont_cap_boundary() {
    // 10 continuation bytes (PREFIX_INT_MAX_CONT) decode; the 11th is TooLarge.
    let mut b = vec![0x1f];
    b.extend([0x80; 9]);
    b.push(0x00);
    assert_eq!(parse_prefix_int(5, &b), PrefixInt::Value { value: 31, consumed: 11 });
    let mut b = vec![0x1f];
    b.extend([0x80; 10]);
    b.push(0x00);
    assert_eq!(parse_prefix_int(5, &b), PrefixInt::TooLarge);
}
