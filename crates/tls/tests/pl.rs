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
