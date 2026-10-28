use vest_lib::core::exec::{Parser, Prepare, SerializerExt};
use wire::varint::*;

// RFC 9000 Appendix A.1. A trailing 0xAA byte checks that it isn't consumed.
#[test]
fn rfc_a1_samples() {
    let cases: &[(&[u8], u64, usize)] = &[
        (&[0xc2, 0x19, 0x7c, 0x5e, 0xff, 0x14, 0xe8, 0x8c, 0xAA], 151_288_809_941_952_652, 8),
        (&[0x9d, 0x7f, 0x3e, 0x7d, 0xAA], 494_878_333, 4),
        (&[0x7b, 0xbd, 0xAA], 15_293, 2),
        (&[0x25, 0xAA], 37, 1),
        (&[0x40, 0x25, 0xAA], 37, 2), // non-minimal, accepted by the lenient parser
    ];
    for (bytes, v, n) in cases {
        assert_eq!(QuicVarInt::<false>.parse(bytes).unwrap(), (*n, *v));
    }
}

#[test]
fn minimal_rejects_overlong() {
    assert!(QuicVarInt::<true>.parse(&&[0x40u8, 0x25][..]).is_err());
}

#[test]
fn rejects_truncated() {
    for b in [&[][..], &[0x40][..], &[0x80, 0, 0][..], &[0xc0, 0, 0, 0, 0, 0, 0][..]] {
        assert!(QuicVarInt::<false>.parse(&b).is_err());
    }
}

#[test]
fn boundaries_roundtrip() {
    for (v, len) in [
        (0, 1),
        (63, 1),
        (64, 2),
        (16383, 2),
        (16384, 4),
        ((1u64 << 30) - 1, 4),
        (1u64 << 30, 8),
        (VARINT_MAX, 8),
    ] {
        let mut out = Vec::new();
        QuicVarInt::<true>.serialize_with_vec(&v, &mut out);
        assert_eq!(out.len(), len);
        assert_eq!(QuicVarInt::<true>.parse(&out.as_slice()).unwrap(), (len, v));
    }
}

#[test]
fn prepare_rejects_out_of_range() {
    assert!(QuicVarInt::<true>.prepare(&(VARINT_MAX + 1)).is_err());
    assert_eq!(QuicVarInt::<true>.prepare(&VARINT_MAX).unwrap(), 8);
}
