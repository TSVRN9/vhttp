use h3::codes::QPACK_DECOMPRESSION_FAILED;
use h3::qpack::field_section::{decode_field_section, encode_field_section, FieldLine};

type Pairs = Vec<(Vec<u8>, Vec<u8>)>;

fn hex(h: &str) -> Vec<u8> {
    let h: String = h.split_whitespace().collect();
    (0..h.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&h[i..i + 2], 16).unwrap())
        .collect()
}

fn dec(h: &str) -> Result<Pairs, u64> {
    decode_field_section(&hex(h)).map(|v| v.into_iter().map(|f| (f.name, f.value)).collect())
}

fn pair(n: &str, v: &str) -> (Vec<u8>, Vec<u8>) {
    (n.as_bytes().to_vec(), v.as_bytes().to_vec())
}

#[test]
fn rfc9204_b1() {
    assert_eq!(
        dec("0000 510b 2f69 6e64 6578 2e68 746d 6c"),
        Ok(vec![pair(":path", "/index.html")])
    );
}

#[test]
fn b2_rejected() {
    assert_eq!(dec("0381 10 11"), Err(QPACK_DECOMPRESSION_FAILED));
}

#[test]
fn string_length_overflow() {
    assert_eq!(
        dec("0000 27 ff ff ff ff 0f"),
        Err(QPACK_DECOMPRESSION_FAILED)
    );
}

#[test]
fn invalid_static_index() {
    assert_eq!(dec("0000 ff 24"), Err(QPACK_DECOMPRESSION_FAILED));
    // Index 98 is the last valid entry.
    assert_eq!(
        dec("0000 ff 23"),
        Ok(vec![pair("x-frame-options", "sameorigin")])
    );
}

#[test]
fn huffman_literal() {
    // Literal name "foo", value H=1 with RFC 7541 C.4.1's www.example.com.
    assert_eq!(
        dec("0000 23 666f6f 8c f1e3 c2e5 f23a 6ba0 ab90 f4ff"),
        Ok(vec![pair("foo", "www.example.com")])
    );
    // Name H=1 (3-bit length 7 + 1 = 8): RFC 7541 C.4.3's custom-key; empty value.
    assert_eq!(
        dec("0000 2f 01 25a8 49e9 5ba9 7d7f 00"),
        Ok(vec![pair("custom-key", "")])
    );
    // Invalid Huffman (8 one-bits of padding).
    assert_eq!(dec("0000 23 666f6f 81 ff"), Err(QPACK_DECOMPRESSION_FAILED));
}

#[test]
fn encode_roundtrip() {
    let fields: Vec<FieldLine> = [
        (":status", "200"),
        ("content-type", "text/plain"),
        ("x-custom", "v"),
    ]
    .iter()
    .map(|(n, v)| FieldLine {
        name: n.as_bytes().to_vec(),
        value: v.as_bytes().to_vec(),
    })
    .collect();
    let mut out = vec![0xaa];
    encode_field_section(&fields, &mut out);
    assert_eq!(out[0], 0xaa);
    assert_eq!(&out[1..4], &[0x00, 0x00, 0xd9]);
    let got = decode_field_section(&out[1..])
        .map(|v| v.into_iter().map(|f| (f.name, f.value)).collect::<Pairs>());
    assert_eq!(
        got,
        Ok(vec![
            pair(":status", "200"),
            pair("content-type", "text/plain"),
            pair("x-custom", "v")
        ])
    );
}

#[test]
fn encode_name_reference() {
    // Name-only static match: literal with static name ref 44 (0x5f 0x1d), H=0 value.
    let f = FieldLine {
        name: b"content-type".to_vec(),
        value: b"text/x".to_vec(),
    };
    let mut out = Vec::new();
    encode_field_section(&[f], &mut out);
    assert_eq!(out, hex("0000 5f1d 06 746578742f78"));
}

#[test]
fn negative_vectors() {
    let e = Err(QPACK_DECOMPRESSION_FAILED);
    assert_eq!(dec("0000 80"), e); // indexed, T=0 (dynamic)
    assert_eq!(dec("0000 10"), e); // indexed post-Base
    assert_eq!(dec("0000 00 00"), e); // literal, post-Base name reference
    assert_eq!(dec("0000 40 00"), e); // literal, dynamic name reference (T=0)
    assert_eq!(dec("00 80"), e); // Sign=1: negative Base
    assert_eq!(dec("0000 51 05 2f 61"), e); // value length 5, 2 bytes present
    assert_eq!(dec("0000 d9 ff"), e); // 0xff: indexed static whose 6-bit index needs a missing continuation byte
}

#[test]
fn n_bit_ignored() {
    // 0x71: literal with name reference, N=1, T=1, index 1 (:path); value "/".
    assert_eq!(dec("0000 71 01 2f"), Ok(vec![pair(":path", "/")]));
}
