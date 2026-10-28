mod common;

use common::*;
use crypto::hkdf::hkdf_extract;
use crypto::p256::{p256_ecdh, p256_public_key};
use crypto::sha256::sha256;
use tls::hkdf_label::derive_secret;
use tls::schedule::*;

fn h(parts: &[&[u8]]) -> [u8; 32] {
    sha256(&parts.concat())
}

fn s32(s: &str) -> [u8; 32] {
    hex(s).try_into().unwrap()
}

#[test]
fn rfc8448_s3() {
    let ikm = s32("8bd4054fb55b9d63fdfbacf9f04b9f0d35e6d63f537563efd46272900f89492d");
    let th = h(&[R3_CH, R3_SH]);
    assert_eq!(th, s32("860c06edc07858ee8e78f0e7428c58edd6b43f2ca3e6e95f02ed063cf0e1cad8"));
    let s = handshake_secrets(&ikm, &th);
    assert_eq!(s.hs, s32("1dc826e93606aa6fdc0aadc12f741b01046aa6b99f691ed221a9f0ca043fbeac"));
    assert_eq!(s.client, s32("b3eddb126e067f35a780b3abf45e2d8f3b1a950738f52e9600746a0e27a55a21"));
    assert_eq!(s.server, s32("b67b7d690cc16c4e75e54213cb2d37b4e9c912bcded9105d42befd59d391ad38"));
    let master = master_secret(&s.hs);
    assert_eq!(master, s32("18df06843d13a08bf2a449844c5f8a478001bc4d4c627984d5a41da8d0402919"));
    assert_eq!(finished_key(&s.server), s32("008d3b66f816ea559f96b537e885c31fc068bf492c652f01f288a1d8cdc19fc8"));
    assert_eq!(finished_key(&s.client), s32("b80ad01015fb2f0bd65ff7d4da5d6bf83f84821d1f87fdc7d3c75b5a7b42d9c4"));
    let th_cv = h(&[R3_CH, R3_SH, R3_EE, R5_CERT, R3_CV]);
    assert_eq!(&verify_data(&s.server, &th_cv)[..], &R3_SFIN[4..]);
    let th_sf = h(&[R3_CH, R3_SH, R3_EE, R5_CERT, R3_CV, R3_SFIN]);
    assert_eq!(th_sf, s32("9608102a0f1ccc6db6250b7b7e417b1a000eaada3daae4777a7686c9ff83df13"));
    let (c_ap, s_ap) = app_secrets(&master, &th_sf);
    assert_eq!(c_ap, s32("9e40646ce79a7f9dc05af8889bce6552875afa0b06df0087f792ebb7c17504a5"));
    assert_eq!(s_ap, s32("a11af9f05531f856ad47116b45a950328204b4f44bfb6b3a4b4f1f3fcb631643"));
    assert_eq!(&verify_data(&s.client, &th_sf)[..], &R3_CFIN[4..]);
}

#[test]
fn rfc8448_s5_hrr() {
    let d = hex("8c510601f9765bfb8ed693449a48989859b5cfa879cb9f5443c41c5ff10634ed");
    assert_eq!(&p256_public_key(&d).unwrap()[..], &R5_SH[52..117]);
    let (_, exts) = split_ch(R5_CH2);
    let ks = &exts.iter().find(|e| e.0 == 0x33).unwrap().1;
    assert_eq!(&ks[2..4], &[0x00, 0x17]);
    let n = u16::from_be_bytes([ks[4], ks[5]]) as usize;
    let z = p256_ecdh(&d, &ks[6..6 + n]).unwrap();
    assert_eq!(z, s32("c142ce13ca11b5c2233652e63ad3d97844f1621fbfb9de69d547dc8fedeabeb4"));
    let mh = message_hash(R5_CH1);
    assert_eq!(mh, hex("fe000020de7420cc7426d2f6b221edcc9c4bdc9bb0ab048b3ddd2411da7e3a01baea6c7e"));
    let th = h(&[&mh, R5_HRR, R5_CH2, R5_SH]);
    assert_eq!(th, s32("8aa8e828ec2f8a884fec95a3139de01c15a3daa7ff5bfc3f4bfcc21b438d7bf8"));
    let s = handshake_secrets(&z, &th);
    assert_eq!(s.hs, s32("ce022e5e6e81e50736d773f2d3adfce8220d049bf510f0dbfac927ef4243b148"));
    assert_eq!(s.client, s32("158aa7ab8855073582b41d674b4055cabcc534728f659314861b4e08e2011566"));
    assert_eq!(s.server, s32("3403e781e2af7b6508da28574f6e95a1abf162de83a97927c37672a4a0cef8a1"));
    let master = master_secret(&s.hs);
    assert_eq!(master, s32("1131545d0baf79ddce9b87f06945781a57dd18ef378dcd2060f8f9a569027ed8"));
    assert_eq!(finished_key(&s.server), s32("e7f8bb3ea4b6c30c4710b3d09c3313658117e70b097e850368e2510ca5631f74"));
    assert_eq!(finished_key(&s.client), s32("81be4131fbb9b6f4471450846f74fd1e68c5224ba7c2a8677f5c53ad226fdc13"));
    let th_cv = h(&[&mh, R5_HRR, R5_CH2, R5_SH, R5_EE, R5_CERT, R5_CV]);
    assert_eq!(&verify_data(&s.server, &th_cv)[..], &R5_SFIN[4..]);
    let th_sf = h(&[&mh, R5_HRR, R5_CH2, R5_SH, R5_EE, R5_CERT, R5_CV, R5_SFIN]);
    assert_eq!(th_sf, s32("50f63cbf36b0dd049e7a0ba27d6455745ea2aaac54bb167f9950b2b7ce9509da"));
    let (c_ap, s_ap) = app_secrets(&master, &th_sf);
    assert_eq!(c_ap, s32("75ecf4b972525aa0dcd057c9944d4cd5d82671d8843141d7dc2a4ff15a21dc51"));
    assert_eq!(s_ap, s32("5c74f87df04225db0f8209c9de6429e49435fdefa7cad61864874d12f31cfc8d"));
    assert_eq!(&verify_data(&s.client, &th_sf)[..], &R5_CFIN[4..]);
}

#[test]
fn early_secret_constant() {
    let early = s32("33ad0a1c607ec03b09e6cd9893680ce210adf300aa1f2660e1b22e10f170f92a");
    assert_eq!(hkdf_extract(&[0; 32], &[0; 32]), early);
    let derived = derive_secret(&early, b"derived", &sha256(b""));
    assert_eq!(derived, s32("6f2615a108c702c5678f54fc9dbab69716c076189c48250cebeac3576c3611ba"));
    let s = handshake_secrets(&[0; 32], &[0; 32]);
    assert_eq!(s.hs, hkdf_extract(&derived, &[0; 32]));
}
