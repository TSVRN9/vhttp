//! Server-side negotiation of one ClientHello (RFC 8446 §4.1.1, §4.2.3, §4.2.8, §4.4.2.2;
//! RFC 9001 §8.1): cipher suite, then ALPN, then certificate chain and signature scheme, then
//! key-exchange group. The check order is the requirement (outline Decision 7).
use crate::ch_ext::*;
use crate::client_hello::*;
use crate::codes::*;
use crate::config::*;
use vstd::prelude::*;

verus! {

/// `Proceed`: send a ServerHello for `chain` (an index into the config), signing with `scheme`,
/// keyed on the client's `share`-th KeyShareEntry. `Retry`: send a HelloRetryRequest for
/// secp256r1.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Choice {
    Proceed { chain: usize, scheme: u16, share: usize },
    Retry,
}

//= https://www.rfc-editor.org/rfc/rfc8446#section-4.2.3
//# The keys found in certificates MUST also
//# be of appropriate type for the signature algorithms they are used
//# with.
//= https://www.rfc-editor.org/rfc/rfc8446#section-4.2.3
//# They MUST NOT be offered or negotiated by any
//# implementation.
//= https://www.rfc-editor.org/rfc/rfc8446#section-4.2.3
//# In particular, MD5 [SLOTH], SHA-224, and DSA
//# MUST NOT be used.
// We sign only with ecdsa_secp256r1_sha256 and rsa_pss_rsae_sha256 (`key_scheme`).
//= https://www.rfc-editor.org/rfc/rfc8446#section-4.2.3
//# The length of the Salt MUST be equal to the length of the output
//# of the digest algorithm.
//= https://www.rfc-editor.org/rfc/rfc8446#section-4.2.3
//# If the public key is carried in an X.509
//# certificate, it MUST use the rsaEncryption OID [RFC5280].
// rsa_pss_rsae_sha256: crypto::rsa signs with a 32-byte salt (SHA-256's output length); the
// rsaEncryption OID is a property of the configured certificate (TRUSTED.md, config row).
//= https://www.rfc-editor.org/rfc/rfc8446#section-4.2.3
//= type=exception
//= reason=rsa_pss_pss_* is never selected: an RSA key signs only rsa_pss_rsae_sha256
//# The length of the Salt MUST be equal to the length of the digest
//# algorithm.
//= https://www.rfc-editor.org/rfc/rfc8446#section-4.2.3
//= type=exception
//= reason=rsa_pss_pss_* is never selected: an RSA key signs only rsa_pss_rsae_sha256
//# If the public key is carried in an X.509 certificate,
//# it MUST use the RSASSA-PSS OID [RFC5756].
//= https://www.rfc-editor.org/rfc/rfc8446#section-4.2.3
//= type=exception
//= reason=binds certificate issuers; the server signs no certificate
//# When used in
//# certificate signatures, the algorithm parameters MUST be DER
//# encoded.
//= https://www.rfc-editor.org/rfc/rfc8446#section-4.2.3
//= type=exception
//= reason=binds certificate issuers; the server signs no certificate
//# If the corresponding public key's parameters are
//# present, then the parameters in the signature MUST be identical to
//# those in the public key.
//= https://www.rfc-editor.org/rfc/rfc8446#section-9.1
//# A TLS-compliant application MUST support digital signatures with
//# rsa_pkcs1_sha256 (for certificates), rsa_pss_rsae_sha256 (for
//# CertificateVerify and certificates), and ecdsa_secp256r1_sha256.
/// §4.2.3: "If no "signature_algorithms_cert" extension is present, then the
/// "signature_algorithms" extension also applies to signatures appearing in certificates."
pub open spec fn cert_offered(ch: SpecClientHello) -> Seq<u16> {
    match ch.sig_algs_cert {
        Some(s) => s,
        None => ch.sig_algs,
    }
}

pub open spec fn key_usable(ch: SpecClientHello, c: SpecCertChain) -> bool {
    ch.sig_algs.contains(key_scheme(c.key))
}

pub open spec fn chain_fits(c: SpecCertChain, offered: Seq<u16>) -> bool {
    forall|k: int| 0 <= k < c.chain_schemes.len() ==> offered.contains(#[trigger] c.chain_schemes[k])
}

pub open spec fn is_sha1(s: u16) -> bool {
    s == RSA_PKCS1_SHA1 || s == ECDSA_SHA1
}

pub open spec fn sha1_ok(c: SpecCertChain, offered: Seq<u16>) -> bool {
    forall|k: int|
        0 <= k < c.chain_schemes.len() && is_sha1(#[trigger] c.chain_schemes[k]) ==> offered.contains(
            c.chain_schemes[k],
        )
}

/// `strict`: the chain is signed only with offered schemes; otherwise only its SHA-1 schemes
/// need to be offered.
pub open spec fn chain_ok(ch: SpecClientHello, c: SpecCertChain, strict: bool) -> bool {
    key_usable(ch, c) && if strict {
        chain_fits(c, cert_offered(ch))
    } else {
        sha1_ok(c, cert_offered(ch))
    }
}

/// The least `i >= k` with `chain_ok(ch, cfg[i], strict)`. Indices past `usize::MAX` are not
/// searched; no exec config reaches them.
pub open spec fn scan_chain(cfg: Seq<SpecCertChain>, ch: SpecClientHello, strict: bool, k: nat) -> Option<nat>
    decreases cfg.len() - k,
{
    if k >= cfg.len() || k > usize::MAX {
        None
    } else if chain_ok(ch, cfg[k as int], strict) {
        Some(k)
    } else {
        scan_chain(cfg, ch, strict, k + 1)
    }
}

//= https://www.rfc-editor.org/rfc/rfc8446#section-4.4.2.2
//# -  The certificate type MUST be X.509v3 [RFC5280], unless explicitly
//# negotiated otherwise (e.g., [RFC7250]).
//= https://www.rfc-editor.org/rfc/rfc8446#section-4.4.2.2
//# -  The server's end-entity certificate's public key (and associated
//# restrictions) MUST be compatible with the selected authentication
//# algorithm from the client's "signature_algorithms" extension
//# (currently RSA, ECDSA, or EdDSA).
//= https://www.rfc-editor.org/rfc/rfc8446#section-4.4.2.2
//# -  The certificate MUST allow the key to be used for signing (i.e.,
//# the digitalSignature bit MUST be set if the Key Usage extension is
//# present) with a signature scheme indicated in the client's
//# "signature_algorithms"/"signature_algorithms_cert" extensions (see
//# Section 4.2.3).
// X.509v3, the key's type and digitalSignature are properties of the configured chain
// (TRUSTED.md, config row); the key's scheme must be in signature_algorithms (`key_usable`).
//= https://www.rfc-editor.org/rfc/rfc8446#section-4.4.2.2
//= type=exception
//= reason=a client SHOULD; this server selects without server_name
//# As servers
//# MAY require the presence of the "server_name" extension, clients
//# SHOULD send this extension, when applicable.
//= https://www.rfc-editor.org/rfc/rfc8446#section-4.4.2.2
//# All certificates provided by the server MUST be signed by a signature
//# algorithm advertised by the client if it is able to provide such a
//# chain (see Section 4.2.3).
//= https://www.rfc-editor.org/rfc/rfc8446#section-4.4.2.2
//# Certificates that are self-signed or
//# certificates that are expected to be trust anchors are not validated
//# as part of the chain and therefore MAY be signed with any algorithm.
// `chain_schemes` excludes the anchor's own signature, so a self-signed leaf has none.
//= https://www.rfc-editor.org/rfc/rfc8446#section-4.4.2.2
//# If the server cannot produce a certificate chain that is signed only
//# via the indicated supported algorithms, then it SHOULD continue the
//# handshake by sending the client a certificate chain of its choice
//# that may include algorithms that are not known to be supported by the
//# client.
//= https://www.rfc-editor.org/rfc/rfc8446#section-4.4.2.2
//# This fallback chain SHOULD NOT use the deprecated SHA-1 hash
//# algorithm in general, but MAY do so if the client's advertisement
//# permits it, and MUST NOT do so otherwise.
//= https://www.rfc-editor.org/rfc/rfc8446#section-4.2.3
//# TLS 1.3 servers MUST NOT offer a SHA-1 signed certificate unless
//# no valid certificate chain can be produced without it (see
//# Section 4.4.2.2).
pub open spec fn rfc_select_chain(cfg: Seq<SpecCertChain>, ch: SpecClientHello) -> Option<nat> {
    match scan_chain(cfg, ch, true, 0) {
        Some(i) => Some(i),
        None => scan_chain(cfg, ch, false, 0),
    }
}

/// The least `j >= k` with `ks[j].group == SECP256R1`, bounded like `scan_chain`.
pub open spec fn scan_share(ks: Seq<SpecKeyShare>, k: nat) -> Option<nat>
    decreases ks.len() - k,
{
    if k >= ks.len() || k > usize::MAX {
        None
    } else if ks[k as int].group == SECP256R1 {
        Some(k)
    } else {
        scan_share(ks, k + 1)
    }
}

pub open spec fn offers_p256(ch: SpecClientHello) -> bool {
    ch.groups matches Some(gs) && gs.contains(SECP256R1)
}

/// The first secp256r1 KeyShareEntry, if secp256r1 is in supported_groups (§4.2.8: a share for
/// a group the client did not list is unusable).
pub open spec fn p256_share(ch: SpecClientHello) -> Option<nat> {
    if offers_p256(ch) {
        match ch.key_shares {
            Some(ks) => scan_share(ks, 0),
            None => None,
        }
    } else {
        None
    }
}

/// `after_hrr`: `ch` is the ClientHello that answers our HelloRetryRequest.
pub open spec fn rfc_negotiate(ch: SpecClientHello, cfg: Seq<SpecCertChain>, after_hrr: bool) -> Result<Choice, u64> {
    //= https://www.rfc-editor.org/rfc/rfc8446#section-2.1
    //# If no
    //# common cryptographic parameters can be negotiated, the server MUST
    //# abort the handshake with an appropriate alert.
    //= https://www.rfc-editor.org/rfc/rfc8446#section-9.1
    //# A TLS-compliant application MUST implement the TLS_AES_128_GCM_SHA256
    //# [GCM] cipher suite and SHOULD implement the TLS_AES_256_GCM_SHA384
    //# [GCM] and TLS_CHACHA20_POLY1305_SHA256 [RFC8439] cipher suites (see
    //# Appendix B.4).
    if !ch.cipher_suites.contains(TLS_AES_128_GCM_SHA256) {
        // 1
        //= https://www.rfc-editor.org/rfc/rfc8446#section-4.1.1
        //# If the server is unable to negotiate a supported set of parameters
        //# (i.e., there is no overlap between the client and server parameters),
        //# it MUST abort the handshake with either a "handshake_failure" or
        //# "insufficient_security" fatal alert (see Section 6).
        Err(ALERT_HANDSHAKE_FAILURE)
    } else if !(ch.alpn matches Some(a) && a.contains(H3_ALPN@)) {
        // 2: an absent ALPN extension negotiates nothing either.
        //= https://www.rfc-editor.org/rfc/rfc9001#section-8.1
        //# Unless another
        //# mechanism is used for agreeing on an application protocol, endpoints
        //# MUST use ALPN for this purpose.
        //= https://www.rfc-editor.org/rfc/rfc9001#section-8.1
        //# When using ALPN, endpoints MUST immediately close a connection (see
        //# Section 10.2 of [QUIC-TRANSPORT]) with a no_application_protocol TLS
        //# alert (QUIC error code 0x0178; see Section 4.8) if an application
        //# protocol is not negotiated.
        //= https://www.rfc-editor.org/rfc/rfc9001#section-8.1
        //# Servers MUST select an application protocol compatible
        //# with the QUIC version that the client has selected.
        //= https://www.rfc-editor.org/rfc/rfc9001#section-8.1
        //# The server MUST
        //# treat the inability to select a compatible application protocol as a
        //# connection error of type 0x0178 (no_application_protocol).
        Err(ALERT_NO_APPLICATION_PROTOCOL)
    } else {
        match rfc_select_chain(cfg, ch) {
            // 3: §4.4.3 requires a scheme the client offered in signature_algorithms.
            None => Err(ALERT_HANDSHAKE_FAILURE),
            Some(i) => {
                let scheme = key_scheme(cfg[i as int].key);
                // 4
                //= https://www.rfc-editor.org/rfc/rfc8446#section-9.1
                //# A
                //# TLS-compliant application MUST support key exchange with secp256r1
                //# (NIST P-256) and SHOULD support key exchange with X25519 [RFC7748].
                //= https://www.rfc-editor.org/rfc/rfc8446#section-4.2.8
                //# This value MUST be in the same
                //# group as the KeyShareEntry value offered by the client that the
                //# server has selected for the negotiated key exchange.
                //= https://www.rfc-editor.org/rfc/rfc8446#section-4.2.8
                //# Servers
                //# MUST NOT send a KeyShareEntry for any group not indicated in the
                //# client's "supported_groups" extension and MUST NOT send a
                //# KeyShareEntry when using the "psk_ke" PskKeyExchangeMode.
                // Only a secp256r1 share is used, and only when secp256r1 is in supported_groups.
                if after_hrr {
                    // §4.1.2: CH2 replaces the shares "with a list containing a single
                    // KeyShareEntry from the indicated group".
                    if offers_p256(ch) && (ch.key_shares matches Some(ks) && ks.len() == 1
                        && ks[0].group == SECP256R1) {
                        Ok(Choice::Proceed { chain: i as usize, scheme, share: 0 })
                    } else {
                        Err(ALERT_ILLEGAL_PARAMETER)
                    }
                } else if p256_share(ch) is Some {
                    Ok(
                        Choice::Proceed {
                            chain: i as usize,
                            scheme,
                            share: p256_share(ch)->Some_0 as usize,
                        },
                    )
                } else if offers_p256(ch) {
                    //= https://www.rfc-editor.org/rfc/rfc8446#section-4.1.1
                    //# If the server selects an (EC)DHE group and the client did not offer a
                    //# compatible "key_share" extension in the initial ClientHello, the
                    //# server MUST respond with a HelloRetryRequest (Section 4.1.4) message.
                    Ok(Choice::Retry)
                } else {
                    //= https://www.rfc-editor.org/rfc/rfc8446#section-4.1.1
                    //# If there is no overlap between the received
                    //# "supported_groups" and the groups supported by the server, then the
                    //# server MUST abort the handshake with a "handshake_failure" or an
                    //# "insufficient_security" alert.
                    Err(ALERT_HANDSHAKE_FAILURE)
                }
            },
        }
    }
}

// =============================================================================
// Theorems
// =============================================================================

proof fn lemma_scan_chain(cfg: Seq<SpecCertChain>, ch: SpecClientHello, strict: bool, k: nat)
    ensures
        scan_chain(cfg, ch, strict, k) matches Some(i) ==> k <= i < cfg.len() && i <= usize::MAX
            && chain_ok(ch, cfg[i as int], strict),
    decreases cfg.len() - k,
{
    if k < cfg.len() && k <= usize::MAX && !chain_ok(ch, cfg[k as int], strict) {
        lemma_scan_chain(cfg, ch, strict, k + 1);
    }
}

proof fn lemma_scan_share(ks: Seq<SpecKeyShare>, k: nat)
    ensures
        scan_share(ks, k) matches Some(j) ==> k <= j < ks.len() && j <= usize::MAX
            && ks[j as int].group == SECP256R1,
    decreases ks.len() - k,
{
    if k < ks.len() && k <= usize::MAX && ks[k as int].group != SECP256R1 {
        lemma_scan_share(ks, k + 1);
    }
}

/// A ClientHello answering our HelloRetryRequest never gets a second one.
pub proof fn theorem_no_second_hrr(ch: SpecClientHello, cfg: Seq<SpecCertChain>)
    ensures
        rfc_negotiate(ch, cfg, true) != Ok::<Choice, u64>(Choice::Retry),
{
}

pub proof fn theorem_proceed_facts(ch: SpecClientHello, cfg: Seq<SpecCertChain>, h: bool)
    ensures
        rfc_negotiate(ch, cfg, h) matches Ok(Choice::Proceed { chain, scheme, share }) ==> {
            &&& chain < cfg.len()
            &&& scheme == key_scheme(cfg[chain as int].key)
            &&& ch.sig_algs.contains(scheme)
            &&& ch.key_shares matches Some(ks)
            &&& share < ks.len()
            &&& ks[share as int].group == SECP256R1
            &&& ch.alpn matches Some(a)
            &&& a.contains(H3_ALPN@)
        },
{
    lemma_scan_chain(cfg, ch, true, 0);
    lemma_scan_chain(cfg, ch, false, 0);
    if let Some(ks) = ch.key_shares {
        lemma_scan_share(ks, 0);
    }
}

/// Negotiation succeeds only on a ClientHello with a key_share extension (4a's §9.2
/// supported_groups ⇔ key_share check). With ALPN `h3` (step 2) and quic_transport_parameters
/// and supported_versions always present, every extension in our ServerHello,
/// HelloRetryRequest and EncryptedExtensions answers one the client sent (§4.2).
pub proof fn theorem_no_unsolicited(body: Seq<u8>, cfg: Seq<SpecCertChain>, h: bool)
    requires
        rfc_client_hello(body) is Ok,
        rfc_negotiate(rfc_client_hello(body)->Ok_0, cfg, h) is Ok,
    ensures
        rfc_client_hello(body)->Ok_0.key_shares is Some,
{
    let ch = rfc_client_hello(body)->Ok_0;
    assert(ch.groups is Some);
}

// =============================================================================
// Exec
// =============================================================================

fn has_h3(a: &Vec<Vec<u8>>) -> (r: bool)
    ensures
        r == a.deep_view().contains(H3_ALPN@),
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a@.len(),
            forall|k: int| 0 <= k < i ==> a.deep_view()[k] != H3_ALPN@,
        decreases a@.len() - i,
    {
        assert(a.deep_view()[i as int] == a@[i as int]@);
        if a[i].len() == 2 && a[i][0] == H3_ALPN[0] && a[i][1] == H3_ALPN[1] {
            assert(a.deep_view()[i as int] =~= H3_ALPN@);
            return true;
        }
        i += 1;
    }
    false
}

/// `strict ? every scheme offered : every SHA-1 scheme offered`.
fn schemes_ok(schemes: &Vec<u16>, offered: &Vec<u16>, strict: bool) -> (r: bool)
    ensures
        r == if strict {
            forall|k: int| 0 <= k < schemes@.len() ==> offered@.contains(#[trigger] schemes@[k])
        } else {
            forall|k: int|
                0 <= k < schemes@.len() && is_sha1(#[trigger] schemes@[k]) ==> offered@.contains(
                    schemes@[k],
                )
        },
{
    let mut i: usize = 0;
    while i < schemes.len()
        invariant
            i <= schemes@.len(),
            forall|k: int|
                0 <= k < i ==> (strict || is_sha1(#[trigger] schemes@[k])) ==> offered@.contains(
                    schemes@[k],
                ),
        decreases schemes@.len() - i,
    {
        let s = schemes[i];
        if (strict || s == RSA_PKCS1_SHA1 || s == ECDSA_SHA1) && !has_u16(offered, s) {
            return false;
        }
        i += 1;
    }
    true
}

fn select_chain(ch: &ClientHello, cfg: &ServerConfig, strict: bool) -> (r: Option<usize>)
    ensures
        r == (match scan_chain(cfg@, ch@, strict, 0) {
            Some(i) => Some(i as usize),
            None => None::<usize>,
        }),
        r matches Some(i) ==> i < cfg@.len() && scan_chain(cfg@, ch@, strict, 0) == Some(i as nat),
{
    let offered = match &ch.sig_algs_cert {
        Some(s) => s,
        None => &ch.sig_algs,
    };
    proof {
        assert(ch.sig_algs.deep_view() =~= ch.sig_algs@);
        if let Some(s) = &ch.sig_algs_cert {
            assert(s.deep_view() =~= s@);
        }
        assert(offered@ == cert_offered(ch@));
    }
    let mut i: usize = 0;
    while i < cfg.chains.len()
        invariant
            i <= cfg@.len(),
            offered@ == cert_offered(ch@),
            scan_chain(cfg@, ch@, strict, 0) == scan_chain(cfg@, ch@, strict, i as nat),
        decreases cfg@.len() - i,
    {
        let c = &cfg.chains[i];
        assert(cfg@[i as int] == c@);
        let usable = has_u16(&ch.sig_algs, key_scheme_of(&c.key));
        let fits = schemes_ok(&c.chain_schemes, offered, strict);
        assert(cfg@[i as int].chain_schemes == c.chain_schemes@);
        assert(offered@ == cert_offered(ch@));
        if usable && fits {
            return Some(i);
        }
        i += 1;
    }
    None
}

fn first_p256(ks: &Vec<KeyShareEntry>) -> (r: Option<usize>)
    ensures
        r == (match scan_share(ks.deep_view(), 0) {
            Some(j) => Some(j as usize),
            None => None::<usize>,
        }),
{
    let mut i: usize = 0;
    while i < ks.len()
        invariant
            i <= ks@.len(),
            scan_share(ks.deep_view(), 0) == scan_share(ks.deep_view(), i as nat),
        decreases ks@.len() - i,
    {
        assert(ks.deep_view()[i as int] == ks@[i as int]@);
        if ks[i].group == SECP256R1 {
            return Some(i);
        }
        i += 1;
    }
    None
}

pub fn negotiate(ch: &ClientHello, cfg: &ServerConfig, after_hrr: bool) -> (r: Result<Choice, u64>)
    ensures
        r == rfc_negotiate(ch@, cfg@, after_hrr),
{
    if !has_u16(&ch.cipher_suites, TLS_AES_128_GCM_SHA256) {
        return Err(ALERT_HANDSHAKE_FAILURE);
    }
    let h3 = match &ch.alpn {
        Some(a) => has_h3(a),
        None => false,
    };
    if !h3 {
        return Err(ALERT_NO_APPLICATION_PROTOCOL);
    }
    let i = match select_chain(ch, cfg, true) {
        Some(i) => i,
        None => match select_chain(ch, cfg, false) {
            Some(i) => i,
            None => return Err(ALERT_HANDSHAKE_FAILURE),
        },
    };
    let scheme = key_scheme_of(&cfg.chains[i].key);
    assert(cfg@[i as int] == cfg.chains@[i as int]@);
    let g = match &ch.groups {
        Some(gs) => {
            assert(gs.deep_view() =~= gs@);
            has_u16(gs, SECP256R1)
        },
        None => false,
    };
    if after_hrr {
        match &ch.key_shares {
            Some(ks) => {
                if g && ks.len() == 1 && ks[0].group == SECP256R1 {
                    assert(ks.deep_view()[0] == ks@[0]@);
                    return Ok(Choice::Proceed { chain: i, scheme, share: 0 });
                }
                assert(ks.len() == 1 ==> ks.deep_view()[0] == ks@[0]@);
            },
            None => {},
        }
        return Err(ALERT_ILLEGAL_PARAMETER);
    }
    if !g {
        return Err(ALERT_HANDSHAKE_FAILURE);
    }
    match &ch.key_shares {
        Some(ks) => match first_p256(ks) {
            Some(j) => Ok(Choice::Proceed { chain: i, scheme, share: j }),
            None => Ok(Choice::Retry),
        },
        None => Ok(Choice::Retry),
    }
}

} // verus!
