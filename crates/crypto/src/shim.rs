//! Trusted shim: every RustCrypto call lives here. Plain Rust outside `verus!`; removed in phase 5.
use sha2::{Digest, Sha256};

pub(crate) fn sha256(m: &[u8]) -> [u8; 32] {
    Sha256::digest(m).into()
}

pub(crate) fn hmac_sha256(key: &[u8], msg: &[u8]) -> [u8; 32] {
    use hmac::{Hmac, KeyInit, Mac};
    // unreachable: HMAC accepts any key length
    let mut m = <Hmac<Sha256> as KeyInit>::new_from_slice(key).unwrap();
    m.update(msg);
    m.finalize().into_bytes().into()
}

pub(crate) fn hkdf_extract(salt: &[u8], ikm: &[u8]) -> [u8; 32] {
    hkdf::Hkdf::<Sha256>::extract(Some(salt), ikm).0.into()
}

pub(crate) fn hkdf_expand(prk: &[u8], info: &[u8], len: usize) -> Vec<u8> {
    // unreachable: requires prk@.len() == 32
    let k = hkdf::Hkdf::<Sha256>::from_prk(prk).unwrap();
    let mut out = vec![0u8; len];
    // unreachable: requires len <= 8160
    k.expand(info, &mut out).unwrap();
    out
}

pub(crate) fn aes128_encrypt_block(key: &[u8], block: &[u8]) -> [u8; 16] {
    use aes::cipher::{BlockCipherEncrypt, KeyInit};
    // unreachable: requires key@.len() == 16
    let k: [u8; 16] = key.try_into().unwrap();
    // unreachable: requires block@.len() == 16
    let mut b: [u8; 16] = block.try_into().unwrap();
    aes::Aes128::new(&k.into()).encrypt_block((&mut b).into());
    b
}

pub(crate) fn aes128_gcm_seal(key: &[u8], nonce: &[u8], aad: &[u8], pt: &[u8]) -> Vec<u8> {
    use aes_gcm::aead::{Aead, KeyInit, Payload};
    // unreachable: requires key@.len() == 16
    let k: [u8; 16] = key.try_into().unwrap();
    // unreachable: requires nonce@.len() == 12
    let n: [u8; 12] = nonce.try_into().unwrap();
    // unreachable: requires pt@.len() <= GCM_MAX_PT_LEN (= P_MAX) and aad@.len() <= MAX_INPUT_LEN (< A_MAX)
    aes_gcm::Aes128Gcm::new(&k.into()).encrypt(&n.into(), Payload { msg: pt, aad }).unwrap()
}

pub(crate) fn aes128_gcm_open(key: &[u8], nonce: &[u8], aad: &[u8], ct: &[u8]) -> Option<Vec<u8>> {
    use aes_gcm::aead::{Aead, KeyInit, Payload};
    // unreachable: requires key@.len() == 16
    let k: [u8; 16] = key.try_into().unwrap();
    // unreachable: requires nonce@.len() == 12
    let n: [u8; 12] = nonce.try_into().unwrap();
    aes_gcm::Aes128Gcm::new(&k.into()).decrypt(&n.into(), Payload { msg: ct, aad }).ok()
}

pub(crate) fn p256_public_key(d: &[u8]) -> Option<[u8; 65]> {
    use p256::elliptic_curve::sec1::ToSec1Point;
    // unreachable: requires d@.len() == 32
    let d: [u8; 32] = d.try_into().unwrap();
    let sk = p256::SecretKey::from_bytes((&d).into()).ok()?;
    sk.public_key().to_sec1_point(false).as_bytes().try_into().ok()
}

pub(crate) fn p256_ecdh(d: &[u8], peer: &[u8]) -> Option<[u8; 32]> {
    // from_sec1_bytes also accepts the compressed form, which the spec rejects.
    if peer.len() != 65 || peer.first() != Some(&4) {
        return None;
    }
    // unreachable: requires d@.len() == 32
    let d: [u8; 32] = d.try_into().unwrap();
    let sk = p256::SecretKey::from_bytes((&d).into()).ok()?;
    let pk = p256::PublicKey::from_sec1_bytes(peer).ok()?;
    Some((*p256::ecdh::diffie_hellman(sk.to_nonzero_scalar(), pk.as_affine()).raw_secret_bytes()).into())
}

pub(crate) fn p256_ecdsa_sign(d: &[u8], msg: &[u8]) -> Option<[u8; 64]> {
    use p256::ecdsa::signature::Signer;
    // unreachable: requires d@.len() == 32
    let d: [u8; 32] = d.try_into().unwrap();
    let sk = p256::ecdsa::SigningKey::from_bytes((&d).into()).ok()?;
    // unreachable: sign's internal expect needs try_sign to fail, and it cannot: from_bytes
    // accepted d (1 <= d < n, requires d@.len() == 32), requires msg@.len() <= MAX_INPUT_LEN keeps
    // the SHA-256 input under its length limit, and sign_prehash loops until a k is suitable.
    let sig: p256::ecdsa::Signature = sk.sign(msg);
    Some(sig.to_bytes().into())
}
