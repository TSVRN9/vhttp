use quic::codes::PN_MAX;
use quic::pn::*;

#[test]
fn a2_encode() {
    assert_eq!(pn_encode_len(0xac5c02, Some(0xabe8b3)), Some(2));
    assert_eq!(pn_encode_len(0xace8fe, Some(0xabe8b3)), Some(3));
}

#[test]
fn a3_decode() {
    assert_eq!(decode_pn(Some(0xa82f30ea), 0x9b32, 2), 0xa82f9b32);
}

#[test]
fn rfc9001_a5_decode() {
    assert_eq!(decode_pn(Some(654360563), 0x00bff4, 3), 654360564);
}

#[test]
fn pn_len_boundary() {
    assert_eq!(pn_encode_len(0x8000, Some(0)), Some(3));
    assert_eq!(pn_encode_len(0x7fff, Some(0)), Some(2));
    assert_eq!(pn_encode_len((1 << 31) - 1, Some(0)), Some(4));
    assert_eq!(pn_encode_len(1 << 31, Some(0)), None);
    assert_eq!(pn_encode_len(255, None), Some(1));
    assert_eq!(pn_encode_len(256, None), Some(2));
}

#[test]
fn decode_pn_edges() {
    assert_eq!(decode_pn(None, 0, 1), 0);
    assert_eq!(decode_pn(Some(0xff), 0x00, 1), 0x100);
    // candidate 0x100 <= expected 0x1ff - 0x80: the +win branch.
    assert_eq!(decode_pn(Some(0x1fe), 0x00, 1), 0x200);
    assert_eq!(decode_pn(Some(0x100), 0xff, 1), 0xff);
    assert_eq!(decode_pn(Some(PN_MAX - 1), 0xff, 1), PN_MAX);
    assert_eq!(decode_pn(Some(0x3fff_ffff_ffff_ff7f), 0x00, 1), 0x3fff_ffff_ffff_ff00);
}

#[test]
fn pn_bytes() {
    let mut v = Vec::new();
    put_pn(0x2700bff4, 3, &mut v);
    assert_eq!(v, [0x00, 0xbf, 0xf4]);
    assert_eq!(read_pn(&v), 0x00bff4);
    let w = [0x00, 0xbf, 0xf4, 0x99];
    assert_eq!([1, 2, 3, 4].map(|n| read_pn_masked(&w, n)), [0x00, 0x00bf, 0x00bff4, 0x00bff499]);
}
