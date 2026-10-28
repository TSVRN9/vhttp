mod common;

use tls::codes::*;
use tls::pl::*;

#[test]
fn vec_widths() {
    assert_eq!(read_vec(&[0x02, 0xaa, 0xbb, 0xcc], 0, 0, 255), Some((1, 3)));
    assert_eq!(read_vec(&[0x00, 0x02, 0xaa, 0xbb], 0, 0, 0xffff), Some((2, 4)));
    assert_eq!(read_vec(&[0, 0, 1, 0xaa], 0, 1, 0xff_ffff), Some((3, 4)));
}

#[test]
fn vec_bounds() {
    assert_eq!(read_vec(&[0x00], 0, 1, 255), None);
    assert_eq!(read_vec(&[0x03, 1, 2, 3], 0, 0, 2), None);
    assert_eq!(read_vec(&[0x05, 1, 2], 0, 0, 255), None);
    assert_eq!(read_vec(&[], 0, 0, 255), None);
    assert_eq!(read_vec(&[0x00], 0, 0, 0xffff), None);
}

#[test]
fn vec_offset() {
    assert_eq!(read_vec(&[9, 9, 0x01, 0x7f], 2, 1, 255), Some((3, 4)));
}

#[test]
fn u16_list() {
    assert_eq!(parse_u16_list(&[0x13, 0x01, 0x13, 0x02]), Some(vec![0x1301, 0x1302]));
    assert_eq!(parse_u16_list(&[0x13]), None);
    assert_eq!(parse_u16_list(&[]), Some(vec![]));
}

#[test]
fn put_vec_widths() {
    for (ceiling, want) in [
        (255, &[0xaa, 2, 0x68, 0x33][..]),
        (0xffff, &[0xaa, 0, 2, 0x68, 0x33][..]),
        (0xff_ffff, &[0xaa, 0, 0, 2, 0x68, 0x33][..]),
    ] {
        let mut out = vec![0xaa];
        put_vec(&mut out, ceiling, b"h3");
        assert_eq!(out, want);
    }
}

#[test]
fn alert_sums() {
    assert_eq!(ALERT_UNEXPECTED_MESSAGE, CRYPTO_ERROR_BASE + 10);
    assert_eq!(ALERT_ILLEGAL_PARAMETER, CRYPTO_ERROR_BASE + 47);
    assert_eq!(ALERT_DECODE_ERROR, CRYPTO_ERROR_BASE + 50);
    assert_eq!(ALERT_PROTOCOL_VERSION, CRYPTO_ERROR_BASE + 70);
    assert_eq!(ALERT_MISSING_EXTENSION, CRYPTO_ERROR_BASE + 109);
}

#[test]
fn vec_multibyte_lengths() {
    let mut b = vec![0x01, 0x02];
    b.resize(2 + 0x0102, 0xaa);
    assert_eq!(read_vec(&b, 0, 0, 0xffff), Some((2, 2 + 0x0102)));
    let mut b = vec![0x01, 0x02, 0x03];
    b.resize(3 + 0x01_0203, 0xaa);
    assert_eq!(read_vec(&b, 0, 0, 0xff_ffff), Some((3, 3 + 0x01_0203)));
}

#[test]
fn put_vec_multibyte_lengths() {
    for (ceiling, n, hdr) in [
        (0xffff, 0x0102, &[0x01, 0x02][..]),
        (0xff_ffff, 0x0102, &[0x00, 0x01, 0x02][..]),
        (0xff_ffff, 0x01_0203, &[0x01, 0x02, 0x03][..]),
    ] {
        let c = vec![0x55; n];
        let mut out = vec![0xaa];
        put_vec(&mut out, ceiling, &c);
        assert_eq!(out.len(), 1 + hdr.len() + n);
        assert_eq!(out[0], 0xaa);
        assert_eq!(&out[1..1 + hdr.len()], hdr);
        assert_eq!(&out[1 + hdr.len()..], &c[..]);
    }
}

#[test]
fn u16_read_put() {
    assert_eq!(read_u16(&[0x12, 0x34, 0x56], 0), Some(0x1234));
    assert_eq!(read_u16(&[0x12, 0x34, 0x56], 1), Some(0x3456));
    assert_eq!(read_u16(&[0x12, 0x34, 0x56], 2), None);
    assert_eq!(read_u16(&[0x12, 0x34], 5), None);
    assert_eq!(read_u16(&[], 0), None);
    let mut out = vec![0xaa];
    put_u16(&mut out, 0x1301);
    put_u16(&mut out, 0xff00);
    assert_eq!(out, [0xaa, 0x13, 0x01, 0xff, 0x00]);
}

#[test]
fn codepoints() {
    assert_eq!(
        HRR_RANDOM[..],
        common::hex("cf21ad74e59a6111be1d8c021e65b891c2a211167abb8c5e079e09e2c8a8339c")[..]
    );
    assert_eq!(H3_ALPN, *b"h3");
    assert_eq!(
        [HT_CLIENT_HELLO, HT_SERVER_HELLO, HT_ENCRYPTED_EXTENSIONS, HT_CERTIFICATE],
        [1, 2, 8, 11]
    );
    assert_eq!([HT_CERTIFICATE_VERIFY, HT_FINISHED], [15, 20]);
    assert_eq!(
        [EXT_SERVER_NAME, EXT_SUPPORTED_GROUPS, EXT_SIGNATURE_ALGORITHMS, EXT_ALPN],
        [0, 10, 13, 16]
    );
    assert_eq!(
        [EXT_PRE_SHARED_KEY, EXT_EARLY_DATA, EXT_SUPPORTED_VERSIONS, EXT_COOKIE],
        [41, 42, 43, 44]
    );
    assert_eq!(
        [EXT_PSK_KEY_EXCHANGE_MODES, EXT_OID_FILTERS, EXT_SIGNATURE_ALGORITHMS_CERT, EXT_KEY_SHARE],
        [45, 48, 50, 51]
    );
    assert_eq!(EXT_QUIC_TRANSPORT_PARAMETERS, 0x39);
    assert_eq!([LEGACY_VERSION, TLS13, SSL30, TLS_AES_128_GCM_SHA256], [0x0303, 0x0304, 0x0300, 0x1301]);
    assert_eq!([CRYPTO_ERROR_BASE, PROTOCOL_VIOLATION, CRYPTO_BUFFER_EXCEEDED], [0x100, 0x0a, 0x0d]);
    assert_eq!(MAX_HS_BODY, 65536);
}
