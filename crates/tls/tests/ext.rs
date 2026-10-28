mod common;

use common::*;
use tls::ext::*;

/// `spec_ext_bytes`: u16 type, then `extension_data<0..2^16-1>`.
fn ext_bytes(ty: u16, data: &[u8]) -> Vec<u8> {
    let n = data.len();
    let mut v = vec![(ty >> 8) as u8, ty as u8, (n >> 8) as u8, n as u8];
    v.extend_from_slice(data);
    v
}

/// `spec_ext_list_bytes`.
fn list_bytes(exts: &[(u16, &[u8])]) -> Vec<u8> {
    exts.iter().flat_map(|(t, d)| ext_bytes(*t, d)).collect()
}

fn exts(e: &[(u16, &[u8])]) -> Vec<Ext> {
    let got = parse_ext_list(&list_bytes(e)).expect("well-formed block");
    assert_eq!(got.len(), e.len());
    got
}

fn a2_list() -> Vec<Ext> {
    assert_eq!(&A2_CH[47..49], &[0x00, 0xc0]);
    parse_ext_list(&A2_CH[49..241]).expect("A.2 extensions parse")
}

#[test]
fn a2_ext_list() {
    let l = a2_list();
    let tys: Vec<u16> = l.iter().map(|e| e.ty).collect();
    let lens: Vec<usize> = l.iter().map(|e| e.data.len()).collect();
    assert_eq!(
        tys,
        [0x0000, 0xff01, 0x000a, 0x0010, 0x0005, 0x0033, 0x002b, 0x000d, 0x002d, 0x001c, 0x0039]
    );
    assert_eq!(lens, [16, 1, 8, 7, 5, 38, 3, 16, 2, 2, 50]);
    let back: Vec<(u16, &[u8])> = l.iter().map(|e| (e.ty, &e.data[..])).collect();
    assert_eq!(list_bytes(&back), &A2_CH[49..241]);
    assert_eq!(check_ch_exts(&l), Ok(()));
}

#[test]
fn ext_list_empty() {
    assert_eq!(parse_ext_list(&[]), Some(vec![]));
    assert_eq!(check_ch_exts(&vec![]), Ok(()));
}

#[test]
fn ext_list_malformed() {
    for b in [&[0x00][..], &[0x00, 0x2b, 0x00], &[0x00, 0x2b, 0x00, 0x03, 0x02, 0x03]] {
        assert_eq!(parse_ext_list(b), None, "{:02x?}", b);
    }
}

#[test]
fn dup_known() {
    assert_eq!(check_ch_exts(&exts(&[(0x2b, &[2, 3, 4]), (0x2b, &[2, 3, 4])])), Err(0x12f));
}

#[test]
fn dup_unknown() {
    let groups = hex("0006001d00170018");
    let l = exts(&[(0xff01, &[0]), (0x000a, &groups), (0xff01, &[0])]);
    assert_eq!(check_ch_exts(&l), Err(0x12f));
}

#[test]
fn dup_grease() {
    assert_eq!(check_ch_exts(&exts(&[(0x0a0a, &[]), (0x0a0a, &[])])), Err(0x12f));
}

#[test]
fn psk_last() {
    let sv: &[u8] = &[2, 3, 4];
    let psk: &[u8] = &[0, 1, 2, 3];
    assert_eq!(check_ch_exts(&exts(&[(0x2b, sv), (0x29, psk)])), Ok(()));
    assert_eq!(check_ch_exts(&exts(&[(0x29, psk), (0x2b, sv)])), Err(0x12f));
}

#[test]
fn oid_filters_in_ch() {
    assert_eq!(check_ch_exts(&exts(&[(0x30, &[0, 0])])), Err(0x12f));
}

#[test]
fn oid_filters_among_others() {
    let sv: &[u8] = &[2, 3, 4];
    let psk: &[u8] = &[0, 1, 2, 3];
    let oid: &[u8] = &[0, 0];
    let mid = exts(&[(0x2b, sv), (0x30, oid), (0x2d, &[1, 1])]);
    assert_eq!(check_ch_exts(&mid), Err(0x12f));
    let last = exts(&[(0x2b, sv), (0x2d, &[1, 1]), (0x30, oid)]);
    assert_eq!(check_ch_exts(&last), Err(0x12f));
    let psk_last = exts(&[(0x2b, sv), (0x30, oid), (0x29, psk)]);
    assert_eq!(check_ch_exts(&psk_last), Err(0x12f));
}

#[test]
fn max_ext_count() {
    let mut tys: Vec<u16> = (0x1000..0x4fff).collect();
    assert_eq!(tys.len(), 16383);
    let block = |tys: &[u16]| -> Vec<u8> {
        tys.iter().flat_map(|t| ext_bytes(*t, &[])).collect()
    };
    let b = block(&tys);
    assert_eq!(b.len(), 65532);
    let l = parse_ext_list(&b).expect("parses");
    assert_eq!(l.len(), 16383);
    assert_eq!(check_ch_exts(&l), Ok(()));
    *tys.last_mut().unwrap() = 0x1000;
    let l = parse_ext_list(&block(&tys)).expect("parses");
    assert_eq!(check_ch_exts(&l), Err(0x12f));
}

#[test]
fn find_first() {
    let l = a2_list();
    assert_eq!(find_ext(&l, 0x39), Some(10));
    assert_eq!(find_ext(&l, 0x2c), None);
    let d = exts(&[(7, &[1]), (7, &[2])]);
    assert_eq!(find_ext(&d, 7), Some(0));
}

#[test]
fn seen_word_edges() {
    let l = exts(&[(0, &[]), (63, &[]), (64, &[]), (0xffbf, &[]), (0xffc0, &[]), (0xffff, &[])]);
    assert_eq!(check_ch_exts(&l), Ok(()));
    assert_eq!(check_ch_exts(&exts(&[(0xffff, &[]), (0xffc0, &[]), (0xffff, &[])])), Err(0x12f));
    assert_eq!(check_ch_exts(&exts(&[(63, &[]), (0, &[]), (63, &[])])), Err(0x12f));
}

/// Smoke check (debug build): the per-ClientHello seen table on curl's extension list.
#[test]
fn curl_check_repeated() {
    let l: Vec<Ext> = split_ch(CURL_CH).1.into_iter().map(|(ty, data)| Ext { ty, data }).collect();
    assert!(l.len() > 1);
    for _ in 0..1000 {
        assert_eq!(check_ch_exts(&l), Ok(()));
    }
}
