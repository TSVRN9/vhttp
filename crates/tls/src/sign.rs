//! The server CertificateVerify content and signature (RFC 8446 §4.4.3).
use crate::codes::*;
use crate::config::*;
use crypto::ecdsa::*;
use crypto::rsa::*;
use vstd::prelude::*;

verus! {

//= https://www.rfc-editor.org/rfc/rfc8446#section-4.4.3
//# The digital signature is then computed over the concatenation of:
//#
//# -  A string that consists of octet 32 (0x20) repeated 64 times
//#
//# -  The context string
//#
//# -  A single 0 byte which serves as the separator
//#
//# -  The content to be signed
pub open spec fn spec_cv_content(th: Seq<u8>) -> Seq<u8> {
    Seq::new(64, |_i| 0x20u8) + CV_SERVER_CONTEXT@ + seq![0x00u8] + th
}

pub open spec fn spec_cv_raw(key: SpecSigningKey, m: Seq<u8>, salt: Seq<u8>) -> Option<Seq<u8>> {
    match key {
        SpecSigningKey::EcdsaP256(d) => match spec_ecdsa_p256_sha256_sign(d, m) {
            Some(rs) => Some(spec_ecdsa_der(rs)),
            None => None,
        },
        SpecSigningKey::Rsa(k) => Some(spec_rsassa_pss_sign(k, m, salt)),
    }
}

/// `None` for an invalid ECDSA scalar, or a signature over 0xffff octets.
pub open spec fn spec_cv_signature(key: SpecSigningKey, th: Seq<u8>, salt: Seq<u8>) -> Option<
    Seq<u8>,
> {
    let sig = spec_cv_raw(key, spec_cv_content(th), salt);
    match sig {
        // ponytail: unreachable (DER <= 72 B, PSS <= 512 B); a length lemma over der_uint_content/i2osp removes the guard.
        Some(s) if s.len() > 0xffff => None,
        _ => sig,
    }
}

pub fn cv_content(th: &[u8; 32]) -> (r: Vec<u8>)
    ensures
        r@ == spec_cv_content(th@),
{
    let mut r: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < 64
        invariant
            i <= 64,
            r@ == Seq::new(i as nat, |_j| 0x20u8),
        decreases 64 - i,
    {
        r.push(0x20);
        i += 1;
        assert(r@ =~= Seq::new(i as nat, |_j| 0x20u8));
    }
    r.extend_from_slice(&CV_SERVER_CONTEXT);
    r.push(0x00);
    r.extend_from_slice(th);
    assert(r@ =~= spec_cv_content(th@));
    r
}

fn sign_ecdsa(d: &[u8; 32], content: &Vec<u8>) -> (r: Option<Vec<u8>>)
    requires
        content@.len() == 130,
    ensures
        r.deep_view() == spec_cv_raw(SpecSigningKey::EcdsaP256(d@), content@, Seq::empty()),
{
    hide(spec_ecdsa_p256_sha256_sign);
    let sg = p256_ecdsa_sign(d, content);
    match sg {
        None => {
            assert(spec_ecdsa_p256_sha256_sign(d@, content@) is None);
            None
        },
        Some(rs) => {
            let mut der = Vec::new();
            serialize_ecdsa_der(&rs, &mut der);
            assert(spec_ecdsa_p256_sha256_sign(d@, content@) == Some(rs@));
            assert(der@ == spec_ecdsa_der(rs@));
            Some(der)
        },
    }
}

//= https://www.rfc-editor.org/rfc/rfc8446#section-4.4.3
//# In addition, the signature algorithm MUST be compatible with the key
//# in the sender's end-entity certificate.  RSA signatures MUST use an
//# RSASSA-PSS algorithm, regardless of whether RSASSA-PKCS1-v1_5
//# algorithms appear in "signature_algorithms".  The SHA-1 algorithm
//# MUST NOT be used in any signatures of CertificateVerify messages.
/// The two key kinds sign with `ecdsa_secp256r1_sha256` (SHA-256) and `rsa_pss_rsae_sha256`
/// (RSASSA-PSS, SHA-256) only. `salt` is ignored for ECDSA (RFC 6979).
pub fn sign_cv(key: &SigningKey, th: &[u8; 32], salt: &[u8; 32]) -> (r: Result<Vec<u8>, u64>)
    requires
        key_wf(key@),
    ensures
        r matches Ok(s) ==> spec_cv_signature(key@, th@, salt@) == Some(s@),
        r matches Err(e) ==> e == ALERT_INTERNAL_ERROR,
        key@ is EcdsaP256 ==> (r is Ok <==> spec_cv_signature(key@, th@, salt@) is Some),
{
    let content = cv_content(th);
    let sig: Vec<u8> = match key {
        SigningKey::EcdsaP256(d) => {
            match sign_ecdsa(d, &content) {
                Some(s) => s,
                None => return Err(ALERT_INTERNAL_ERROR),
            }
        },
        SigningKey::Rsa(k) => match rsa_pss_sha256_sign(k, &content, salt) {
            Some(s) => s,
            None => return Err(ALERT_INTERNAL_ERROR),
        },
    };
    //= https://www.rfc-editor.org/rfc/rfc8446#section-4.4.3
    //# Servers MUST send this message when authenticating
    //# via a certificate.
    if sig.len() > 0xffff {
        return Err(ALERT_INTERNAL_ERROR);
    }
    Ok(sig)
}

} // verus!
