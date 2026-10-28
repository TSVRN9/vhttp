mod common;

use common::*;
use tls::codes::*;
use tls::handshake::*;

/// `ty`, uint24 length, `body`.
fn hs(ty: u8, body: &[u8]) -> Vec<u8> {
    let n = body.len();
    let mut v = vec![ty, (n >> 16) as u8, (n >> 8) as u8, n as u8];
    v.extend_from_slice(body);
    v
}

#[test]
fn a2_byte_by_byte() {
    let mut r = HsReader::new();
    for (i, b) in A2_CH.iter().enumerate() {
        r.push(&[*b]);
        let got = r.next_message(HT_CLIENT_HELLO);
        if i + 1 < A2_CH.len() {
            assert_eq!(got, Ok(None), "push {}", i + 1);
        } else {
            assert_eq!(got, Ok(Some(A2_CH.to_vec())));
        }
    }
    assert!(r.is_empty());
}

#[test]
fn curl_ch_any_chunking() {
    let sevens: Vec<&[u8]> = CURL_CH.chunks(7).collect();
    assert_eq!(sevens.len(), 219);
    let splits: Vec<Vec<&[u8]>> = vec![
        vec![CURL_CH],
        vec![&CURL_CH[..1200], &CURL_CH[1200..]],
        sevens,
        vec![&CURL_CH[..1531], &CURL_CH[1531..]],
    ];
    for chunks in splits {
        let mut r = HsReader::new();
        let last = chunks.len() - 1;
        for (i, c) in chunks.iter().enumerate() {
            r.push(c);
            let got = r.next_message(HT_CLIENT_HELLO);
            if i < last {
                assert_eq!(got, Ok(None));
            } else {
                assert_eq!(got, Ok(Some(CURL_CH.to_vec())));
            }
        }
        assert!(r.is_empty());
    }
}

#[test]
fn two_coalesced() {
    let mut r = HsReader::new();
    let a = hs(1, &[0xaa; 3]);
    r.push(&[a.clone(), hs(1, &[])].concat());
    assert_eq!(r.next_message(1), Ok(Some(a)));
    assert_eq!(r.next_message(1), Ok(Some(vec![1, 0, 0, 0])));
    assert_eq!(r.next_message(1), Ok(None));
    assert!(r.is_empty());
}

#[test]
fn wrong_type_first_byte() {
    let mut r = HsReader::new();
    r.push(&[0x02]);
    assert_eq!(r.next_message(1), Err(0x10a));
    assert!(!r.is_empty());
    let mut r = HsReader::new();
    r.push(&[0x18]);
    assert_eq!(r.next_message(20), Err(0x10a));
}

#[test]
fn length_cap() {
    for (hdr, want) in [
        ([1, 0x01, 0x00, 0x00], Ok(None)),
        ([1, 0x01, 0x00, 0x01], Err(0x0d)),
        ([1, 0xff, 0xff, 0xff], Err(0x0d)),
    ] {
        let mut r = HsReader::new();
        r.push(&hdr);
        assert_eq!(r.next_message(1), want, "{:02x?}", hdr);
    }
}

#[test]
fn empty_body() {
    let mut r = HsReader::new();
    r.push(&[20, 0, 0, 0]);
    assert_eq!(r.next_message(20), Ok(Some(vec![20, 0, 0, 0])));
    assert!(r.is_empty());
}
