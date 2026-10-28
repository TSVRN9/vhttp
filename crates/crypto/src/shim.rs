//! Trusted shim: every RustCrypto call lives here. Plain Rust outside `verus!`; removed in phase 5.
use sha2::{Digest, Sha256};

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
    // unreachable: a valid scalar never gives the identity, and the uncompressed encoding is 65 bytes
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

struct SaltRng<'a>(&'a [u8], bool); // yields the caller's salt exactly once

impl rsa::rand_core::TryRng for SaltRng<'_> {
    type Error = core::convert::Infallible;
    fn try_next_u32(&mut self) -> Result<u32, Self::Error> {
        // unreachable: unblinded PSS draws only the salt, through try_fill_bytes
        unreachable!("PSS draws only the salt")
    }
    fn try_next_u64(&mut self) -> Result<u64, Self::Error> {
        // unreachable: unblinded PSS draws only the salt, through try_fill_bytes
        unreachable!("PSS draws only the salt")
    }
    fn try_fill_bytes(&mut self, dst: &mut [u8]) -> Result<(), Self::Error> {
        // unreachable: requires salt@.len() == 32; Pss::new_with_salt(32) is unblinded and fills
        // exactly one 32-byte salt
        assert!(!self.1 && dst.len() == 32, "unblinded PSS draws exactly one 32-byte salt");
        dst.copy_from_slice(self.0);
        self.1 = true;
        Ok(())
    }
}

impl rsa::rand_core::TryCryptoRng for SaltRng<'_> {}

// ponytail: rebuilds and re-validates the RustCrypto key on every signature; the whole shim goes in Phase 5.
pub(crate) fn rsa_pss_sign(n: &[u8], e: &[u8], d: &[u8], p: &[u8], q: &[u8], msg: &[u8], salt: &[u8]) -> Option<Vec<u8>> {
    let u = |b: &[u8]| rsa::BoxedUint::from_be_slice_vartime(b);
    // d is built at n's precision: RustCrypto's rsa_decrypt does c.try_resize(d.bits_precision())
    // and fails with Error::Internal when d's precision is below n's (c has n's precision). With
    // minimal bytes that happens whenever d needs fewer limbs than n, e.g. every 2052-bit key.
    let n = u(n);
    let d = &d[d.iter().take_while(|&&b| b == 0).count()..];
    // unreachable: requires rsa_key_wf, so d < n, so the stripped d fits in n's precision
    let d = rsa::BoxedUint::from_be_slice(d, n.bits_precision()).unwrap();
    let key = rsa::RsaPrivateKey::from_components(n, u(e), d, vec![u(p), u(q)]).ok()?;
    // Not pss::SigningKey + Signature::to_vec: that pads to limb width (264 bytes for a 2049-bit n).
    key.sign_with_rng(&mut SaltRng(salt, false), rsa::Pss::<Sha256>::new_with_salt(32), &Sha256::digest(msg)).ok()
}
