//! The server's certificate chains and signing keys (RFC 8446 §4.4.2.2).
//!
//! The key half of `ServerConfig::wf()` is established by the trusted PKCS#8 loader in the shell
//! (TRUSTED.md); the chain-size half is checked here by `build_config`.
use crate::codes::*;
use crate::server_msgs::*;
#[allow(unused_imports)]
use crypto::p256::*;
use crypto::rsa::*;
use vstd::prelude::*;

verus! {

pub enum SigningKey {
    EcdsaP256([u8; 32]),
    Rsa(RsaPrivateKey),
}

pub enum SpecSigningKey {
    EcdsaP256(Seq<u8>),
    Rsa(RsaKeySpec),
}

impl View for SigningKey {
    type V = SpecSigningKey;

    open spec fn view(&self) -> SpecSigningKey {
        match self {
            SigningKey::EcdsaP256(d) => SpecSigningKey::EcdsaP256(d@),
            SigningKey::Rsa(k) => SpecSigningKey::Rsa(k@),
        }
    }
}

/// `der` is end-entity first, opaque DER. `chain_schemes` lists the SignatureSchemes that sign
/// the chain's non-anchor certificates (trusted metadata from the shell); it is empty for a
/// single self-signed certificate.
pub struct CertChain {
    pub der: Vec<Vec<u8>>,
    pub chain_schemes: Vec<u16>,
    pub key: SigningKey,
}

pub struct SpecCertChain {
    pub der: Seq<Seq<u8>>,
    pub chain_schemes: Seq<u16>,
    pub key: SpecSigningKey,
}

impl View for CertChain {
    type V = SpecCertChain;

    open spec fn view(&self) -> SpecCertChain {
        SpecCertChain { der: self.der.deep_view(), chain_schemes: self.chain_schemes@, key: self.key@ }
    }
}

impl DeepView for CertChain {
    type V = SpecCertChain;

    open spec fn deep_view(&self) -> SpecCertChain {
        self@
    }
}

pub struct ServerConfig {
    pub chains: Vec<CertChain>,
}

impl View for ServerConfig {
    type V = Seq<SpecCertChain>;

    open spec fn view(&self) -> Seq<SpecCertChain> {
        self.chains.deep_view()
    }
}

pub open spec fn key_wf(k: SpecSigningKey) -> bool {
    match k {
        SpecSigningKey::EcdsaP256(d) => scalar_valid(d),
        SpecSigningKey::Rsa(k) => rsa_key_wf(k),
    }
}

/// The one SignatureScheme each key signs CertificateVerify with.
pub open spec fn key_scheme(k: SpecSigningKey) -> u16 {
    match k {
        SpecSigningKey::EcdsaP256(_) => ECDSA_SECP256R1_SHA256,
        SpecSigningKey::Rsa(_) => RSA_PSS_RSAE_SHA256,
    }
}

pub open spec fn chain_wf(c: SpecCertChain) -> bool {
    cert_chain_ok(c.der) && key_wf(c.key)
}

impl ServerConfig {
    pub open spec fn wf(&self) -> bool {
        self@.len() >= 1 && forall|i: int| 0 <= i < self@.len() ==> chain_wf(#[trigger] self@[i])
    }
}

pub(crate) fn key_scheme_of(k: &SigningKey) -> (r: u16)
    ensures
        r == key_scheme(k@),
{
    match k {
        SigningKey::EcdsaP256(_) => ECDSA_SECP256R1_SHA256,
        SigningKey::Rsa(_) => RSA_PSS_RSAE_SHA256,
    }
}

/// The signing key for the P-256 scalar `d` and its public point, or `None` unless
/// `1 <= d <= n - 1` (the range `ServerConfig::wf` needs; `p256_public_key` checks it).
pub fn p256_signing_key(d: [u8; 32]) -> (r: Option<(SigningKey, [u8; 65])>)
    ensures
        r is Some <==> scalar_valid(d@),
        r matches Some((k, q)) ==> k@ == SpecSigningKey::EcdsaP256(d@) && key_wf(k@)
            && spec_p256_public_key(d@) == Some(q@),
{
    match p256_public_key(&d) {
        None => None,
        Some(q) => Some((SigningKey::EcdsaP256(d), q)),
    }
}

/// Checks every chain's size (`cert_chain_fits`, the `serialize_certificate` precondition);
/// the keys arrive well formed from the trusted loader.
pub fn build_config(chains: Vec<CertChain>) -> (r: Option<ServerConfig>)
    requires
        forall|i: int| 0 <= i < chains@.len() ==> key_wf(#[trigger] chains@[i].key@),
    ensures
        r is Some <==> (chains@.len() >= 1 && forall|i: int|
            0 <= i < chains@.len() ==> cert_chain_ok(#[trigger] chains@[i].der.deep_view())),
        r matches Some(c) ==> c@ == chains.deep_view() && c.wf(),
{
    if chains.len() == 0 {
        return None;
    }
    let mut i: usize = 0;
    while i < chains.len()
        invariant
            i <= chains@.len(),
            forall|j: int| 0 <= j < i ==> cert_chain_ok(#[trigger] chains@[j].der.deep_view()),
        decreases chains@.len() - i,
    {
        if !cert_chain_fits(&chains[i].der) {
            return None;
        }
        i += 1;
    }
    let c = ServerConfig { chains };
    assert forall|j: int| 0 <= j < c@.len() implies chain_wf(#[trigger] c@[j]) by {
        assert(c@[j] == c.chains@[j]@);
    }
    Some(c)
}

} // verus!
