mod common;

use common::*;
use tls::client_hello::*;
use tls::config::*;
use tls::negotiate::*;

type Exts = Vec<(u16, Vec<u8>)>;

fn p(msg: &[u8]) -> ClientHello {
    parse_client_hello(&msg[4..]).expect("test ClientHello parses")
}

fn u16_list(xs: &[u16]) -> Vec<u8> {
    let n = 2 * xs.len();
    let mut v = vec![(n >> 8) as u8, n as u8];
    v.extend(xs.iter().flat_map(|x| x.to_be_bytes()));
    v
}

fn set(e: &mut Exts, ty: u16, d: Vec<u8>) {
    match e.iter_mut().find(|(t, _)| *t == ty) {
        Some(x) => x.1 = d,
        None => e.push((ty, d)),
    }
}

fn x25519() -> (u16, Vec<u8>) {
    (0x1d, X25519_SHARE.to_vec())
}

fn p256() -> (u16, Vec<u8>) {
    (0x17, P256_SHARE.to_vec())
}

fn ecdsa_cfg() -> ServerConfig {
    dummy_cfg(vec![(ecdsa(), vec![])])
}

fn proceed(chain: usize, scheme: u16, share: usize) -> Result<Choice, u64> {
    Ok(Choice::Proceed { chain, scheme, share })
}

#[test]
fn a2_alpn() {
    assert_eq!(negotiate(&p(A2_CH), &ecdsa_cfg(), false), Err(0x178));
    let ch = h3_ch(&[p256()], |e| e.retain(|(t, _)| *t != 0x10));
    assert_eq!(negotiate(&p(&ch), &ecdsa_cfg(), false), Err(0x178));
}

#[test]
fn order() {
    let (_, e) = split_ch(A2_CH);
    let ch = join_ch(&head(0x0303, &[], &[0x1302], &[0]), &e);
    assert_eq!(negotiate(&p(&ch), &ecdsa_cfg(), false), Err(0x128));
    let ch = h3_ch(&[x25519()], |e| set(e, 0x10, vec![0, 6, 5, b'h', b'3', b'-', b'2', b'9']));
    assert_eq!(negotiate(&p(&ch), &ecdsa_cfg(), false), Err(0x178));
    let ch = h3_ch(&[x25519()], |e| set(e, 0x0d, u16_list(&[0x0804])));
    assert_eq!(negotiate(&p(&ch), &ecdsa_cfg(), false), Err(0x128));
}

#[test]
fn groups() {
    let n = |shares: &[(u16, Vec<u8>)], groups: Option<&[u16]>| {
        let ch = h3_ch(shares, |e| {
            if let Some(g) = groups {
                set(e, 0x0a, u16_list(g))
            }
        });
        negotiate(&p(&ch), &ecdsa_cfg(), false)
    };
    assert_eq!(n(&[x25519()], None), Ok(Choice::Retry));
    assert_eq!(n(&[x25519(), p256()], None), proceed(0, 0x0403, 1));
    assert_eq!(n(&[p256()], Some(&[0x1d])), Err(0x128));
    assert_eq!(n(&[x25519()], Some(&[0x1d])), Err(0x128));
    assert_eq!(n(&[], None), Ok(Choice::Retry));
}

#[test]
fn after_hrr() {
    let n = |shares: &[(u16, Vec<u8>)]| negotiate(&p(&h3_ch(shares, |_| {})), &ecdsa_cfg(), true);
    assert_eq!(n(&[p256()]), proceed(0, 0x0403, 0));
    assert_eq!(n(&[p256(), p256()]), Err(0x12f));
    assert_eq!(n(&[x25519()]), Err(0x12f));
    assert_eq!(n(&[]), Err(0x12f));
}

#[test]
fn chain_selection() {
    let n = |cfg: ServerConfig, sig_algs: &[u16], cert: Option<&[u16]>| {
        let ch = h3_ch(&[p256()], |e| {
            set(e, 0x0d, u16_list(sig_algs));
            if let Some(c) = cert {
                set(e, 0x32, u16_list(c));
            }
        });
        negotiate(&p(&ch), &cfg, false)
    };
    let two = || dummy_cfg(vec![(ecdsa(), vec![0x0401]), (rsa(), vec![])]);
    assert_eq!(n(two(), &[0x0403, 0x0804], None), proceed(1, 0x0804, 0));
    assert_eq!(n(two(), &[0x0403, 0x0804], Some(&[0x0401])), proceed(0, 0x0403, 0));
    // §4.2.3: a SHA-1-free chain that fits beats an earlier one signed with an offered SHA-1.
    let sha1_first = || dummy_cfg(vec![(ecdsa(), vec![0x0201]), (ecdsa(), vec![0x0401])]);
    assert_eq!(n(sha1_first(), &[0x0403], Some(&[0x0201, 0x0401])), proceed(1, 0x0403, 0));
    assert_eq!(n(dummy_cfg(vec![(ecdsa(), vec![0x0202])]), &[0x0403], None), Err(0x128));
    assert_eq!(n(dummy_cfg(vec![(ecdsa(), vec![0x0501])]), &[0x0403], None), proceed(0, 0x0403, 0));
    assert_eq!(n(dummy_cfg(vec![(ecdsa(), vec![0x0203])]), &[0x0403], None), Err(0x128));
    assert_eq!(n(dummy_cfg(vec![(rsa(), vec![])]), &[0x0403], None), Err(0x128));
}

#[test]
fn curl_ch() {
    assert_eq!(negotiate(&p(CURL_CH), &ecdsa_cfg(), false), Ok(Choice::Retry));
}

#[test]
fn build_config_checks() {
    let chain = |der: Vec<Vec<u8>>| CertChain { der, chain_schemes: vec![], key: ecdsa() };
    assert!(build_config(vec![]).is_none());
    assert!(build_config(vec![chain(vec![])]).is_none());
    assert!(build_config(vec![chain(vec![vec![]])]).is_none());
    assert!(build_config(vec![chain(vec![vec![0x30; 10]])]).is_some());
}
