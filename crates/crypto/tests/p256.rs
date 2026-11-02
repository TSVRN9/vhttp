use crypto::p256::{p256_ecdh, p256_public_key, P256_B, P256_GX, P256_GY, P256_N, P256_P};
use p256::elliptic_curve::sec1::ToSec1Point;

fn h(s: &str) -> Vec<u8> {
    let s: String = s.chars().filter(|c| !c.is_whitespace()).collect();
    (0..s.len() / 2).map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap()).collect()
}

const I: &str = "c88f01f510d9ac3f70a292daa2316de544e9aab8afe84049c62a9c57862d1433";
const R: &str = "c6ef9c5d78ae012a011164acb397ce2088685d8f06bf9be0b283ab46476bee53";
const GI: &str = "04 dad0b65394221cf9b051e1feca5787d098dfe637fc90b9ef945d0c3772581180 5271a0461cdb8252d61f1c456fa3e59ab1f45b33accf5f58389e0577b8990bb3";
const GR: &str = "04 d12dfb5289c8d4f81208b70270398c342296970a0bccb74c736fc7554494bf63 56fbf3ca366cc23e8157854c13c58d6aac23f046ada30f8353e74f33039872ab";

#[test]
fn rfc6979_a25_public_key() {
    let d = h("c9afa9d845ba75166b5c215767b1d6934e50c3db36e89b127b8a622b120f6721");
    assert_eq!(
        p256_public_key(&d).unwrap().to_vec(),
        h("04 60fed4ba255a9d31c961eb74c6356d68c049b8923b61fa6ce669622e60f29fb6 7903fe1008b8bc99a41ae9e95628bc64f2f1b20c2d7e9f5177a3c294d4462299")
    );
}

#[test]
fn rfc5903_ecdh() {
    let (i, r, gi, gr) = (h(I), h(R), h(GI), h(GR));
    assert_eq!(p256_public_key(&i).unwrap().to_vec(), gi);
    assert_eq!(p256_public_key(&r).unwrap().to_vec(), gr);
    let z = h("d6840f6b42f6edafd13116e0e12565202fef8e9ece7dce03812464d04b9442de");
    assert_eq!(p256_ecdh(&i, &gr).unwrap().to_vec(), z);
    assert_eq!(p256_ecdh(&r, &gi).unwrap().to_vec(), z);
}

#[test]
fn ecdh_rejects_invalid() {
    let (i, gr) = (h(I), h(GR));
    let mut off = gr.clone();
    off[64] ^= 1;
    assert!(p256_ecdh(&i, &off).is_none());
    assert!(p256_ecdh(&i, &gr[..64]).is_none());
    assert!(p256_ecdh(&i, &gr[1..]).is_none());
    let mut comp = gr[..33].to_vec();
    comp[0] = 0x03;
    assert!(p256_ecdh(&i, &comp).is_none());
    comp[0] = 0x02;
    assert!(p256_ecdh(&i, &comp).is_none());
    assert!(p256_ecdh(&i, &[&gr[..], &[0x00]].concat()).is_none());
    assert!(p256_ecdh(&i, &[0x00]).is_none());
    let y0 = "66485c780e2f83d72433bd5d84a06bb6541c2af31dae871728bf856a174f93f4";
    let xp = h(&format!("04 ffffffff00000001000000000000000000000000ffffffffffffffffffffffff {y0}"));
    assert!(p256_ecdh(&i, &xp).is_none());
    let x0 = h(&format!("04 {} {y0}", "00".repeat(32)));
    assert!(p256_ecdh(&i, &x0).is_some());
    let x1 = "09e78d4ef60d05f750f6636209092bc43cbdd6b47e11a9de20a9feb2a50bb96c";
    let yp1 = h(&format!("04 {x1} ffffffff00000001000000000000000000000001000000000000000000000000"));
    assert!(p256_ecdh(&i, &yp1).is_none());
    let y1 = h(&format!("04 {x1} {}01", "00".repeat(31)));
    assert!(p256_ecdh(&i, &y1).is_some());
    assert!(p256_ecdh(&[0u8; 32], &gr).is_none());
    assert!(p256_ecdh(&P256_N, &gr).is_none());
    assert!(p256_ecdh(&[0xff; 32], &gr).is_none());
}

#[test]
fn scalar_range() {
    assert!(p256_public_key(&[0u8; 32]).is_none());
    assert!(p256_public_key(&h("ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551")).is_none());
    assert!(p256_public_key(&[0xff; 32]).is_none());
    assert!(p256_public_key(&h("ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632550")).is_some());
}

#[test]
fn p256_constants_match_rustcrypto() {
    use p256::elliptic_curve::Curve;
    use primeorder::PrimeCurveParams;
    assert_eq!(P256_N.to_vec(), p256::NistP256::ORDER.to_be_bytes().as_ref().to_vec());
    assert_eq!(P256_B.to_vec(), p256::NistP256::EQUATION_B.to_bytes().to_vec());
    // p = 2^256 - 2^224 + 2^192 + 2^96 - 1, as 8 big-endian u32 words.
    let words: [u32; 8] = [0xffffffff, 0x00000001, 0, 0, 0, 0xffffffff, 0xffffffff, 0xffffffff];
    let p: Vec<u8> = words.iter().flat_map(|w| w.to_be_bytes()).collect();
    assert_eq!(P256_P.to_vec(), p);
    let mut one = [0u8; 32];
    one[31] = 1;
    let g = [&[0x04u8][..], &P256_GX, &P256_GY].concat();
    assert_eq!(p256_public_key(&one).unwrap().to_vec(), g);
}

// RustCrypto reference, called directly.
fn rc_public_key(d: &[u8]) -> Option<Vec<u8>> {
    let d: [u8; 32] = d.try_into().unwrap();
    let sk = p256::SecretKey::from_bytes((&d).into()).ok()?;
    Some(sk.public_key().to_sec1_point(false).as_bytes().to_vec())
}

// RustCrypto reference; every peer here is 65 octets starting 0x04.
fn rc_ecdh(d: &[u8], peer: &[u8]) -> Option<Vec<u8>> {
    let d: [u8; 32] = d.try_into().unwrap();
    let sk = p256::SecretKey::from_bytes((&d).into()).ok()?;
    let pk = p256::PublicKey::from_sec1_bytes(peer).ok()?;
    Some(p256::ecdh::diffie_hellman(sk.to_nonzero_scalar(), pk.as_affine()).raw_secret_bytes().to_vec())
}

fn pattern(i: usize) -> [u8; 32] {
    core::array::from_fn(|j| (i * 37 + j * 11 + 1) as u8)
}

// The big-endian 32-octet a - b, for a >= b.
fn sub_be(a: &[u8], b: &[u8]) -> Vec<u8> {
    let mut r = vec![0u8; 32];
    let mut borrow = 0i16;
    for j in (0..32).rev() {
        let v = a[j] as i16 - b[j] as i16 - borrow;
        borrow = (v < 0) as i16;
        r[j] = v.rem_euclid(256) as u8;
    }
    assert_eq!(borrow, 0);
    r
}

fn small(k: u8) -> Vec<u8> {
    let mut d = vec![0u8; 32];
    d[31] = k;
    d
}

fn g_sec1() -> Vec<u8> {
    [&[0x04u8][..], &P256_GX, &P256_GY].concat()
}

#[test]
fn public_key_matches_rustcrypto() {
    let mut ds: Vec<Vec<u8>> = (0..64).map(|i| pattern(i).to_vec()).collect();
    let mut top = vec![0u8; 32];
    top[0] = 0x80;
    ds.extend([small(1), small(2), sub_be(&P256_N, &small(1)), sub_be(&P256_N, &small(2)), top]);
    for d in &ds {
        let want = rc_public_key(d);
        assert!(want.is_some(), "{d:02x?}");
        assert_eq!(p256_public_key(d).map(|q| q.to_vec()), want, "{d:02x?}");
    }
}

#[test]
fn ecdh_matches_rustcrypto() {
    // Peers whose x starts with a zero octet, found among the pattern scalars.
    let zx: Vec<Vec<u8>> = (0..4096)
        .filter_map(|i| rc_public_key(&pattern(i)))
        .filter(|q| q[1] == 0)
        .take(2)
        .collect();
    assert_eq!(zx.len(), 2);
    let mut pairs: Vec<(Vec<u8>, Vec<u8>)> =
        (0..30).map(|i| (pattern(i).to_vec(), rc_public_key(&pattern(i + 1)).unwrap())).collect();
    pairs.extend(zx.into_iter().enumerate().map(|(i, q)| (pattern(40 + i).to_vec(), q)));
    assert_eq!(pairs.len(), 32);
    for (d, q) in &pairs {
        let want = rc_ecdh(d, q);
        assert!(want.is_some());
        assert_eq!(p256_ecdh(d, q).map(|z| z.to_vec()), want, "{d:02x?} {q:02x?}");
    }
}

#[test]
fn ecdh_peer_edge_cases() {
    let i = h(I);
    let g = g_sec1();
    let neg_g = [&[0x04u8][..], &P256_GX, &sub_be(&P256_P, &P256_GY)].concat();
    let y0 = "66485c780e2f83d72433bd5d84a06bb6541c2af31dae871728bf856a174f93f4";
    let x0 = h(&format!("04 {} {y0}", "00".repeat(32)));
    let x1 = "09e78d4ef60d05f750f6636209092bc43cbdd6b47e11a9de20a9feb2a50bb96c";
    let y1 = h(&format!("04 {x1} {}01", "00".repeat(31)));
    for peer in [&g, &neg_g, &x0, &y1] {
        let want = rc_ecdh(&i, peer);
        assert!(want.is_some(), "{peer:02x?}");
        assert_eq!(p256_ecdh(&i, peer).map(|z| z.to_vec()), want, "{peer:02x?}");
    }
    // dG's x is the public key's x; (n - 1)G = -G has x = Gx.
    assert_eq!(p256_ecdh(&i, &g).unwrap().to_vec(), h(GI)[1..33].to_vec());
    let nm1 = sub_be(&P256_N, &small(1));
    assert_eq!(p256_ecdh(&nm1, &g).map(|z| z.to_vec()), rc_ecdh(&nm1, &g));
    assert_eq!(p256_ecdh(&nm1, &g).unwrap(), P256_GX);
}

#[test]
#[ignore] // timing only; run with --release -- --ignored --nocapture
fn p256_speed() {
    let (i, gr) = (h(I), h(GR));
    let t = std::time::Instant::now();
    std::hint::black_box(p256_public_key(std::hint::black_box(&i)));
    let pk = t.elapsed();
    let t = std::time::Instant::now();
    std::hint::black_box(p256_ecdh(std::hint::black_box(&i), &gr));
    let dh = t.elapsed();
    println!("p256_public_key {pk:?}, p256_ecdh {dh:?}");
}
