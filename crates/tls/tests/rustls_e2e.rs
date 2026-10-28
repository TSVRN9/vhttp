//! The handshake against rustls 0.23.45 (ring) as a real QUIC client, in memory.
mod common;

use common::*;
use rustls::client::danger::{HandshakeSignatureValid, ServerCertVerified, ServerCertVerifier};
use rustls::crypto::ring::{cipher_suite, default_provider, kx_group};
use rustls::crypto::{SupportedKxGroup, WebPkiSupportedAlgorithms};
use rustls::pki_types::{CertificateDer, ServerName, UnixTime};
use rustls::quic::{ClientConnection, KeyChange, Version};
use rustls::{DigitallySignedStruct, SignatureScheme, SupportedCipherSuite};
use std::sync::{Arc, Mutex};
use tls::config::*;
use tls::flight::*;
use tls::server::*;

const RAND: [u8; 96] = [7u8; 96];
const LOCAL_TP: &[u8] = &[0x03, 0x02, 0x45, 0xc0, 0x0e, 0x01, 0x04];
const HRR: &str = "020000340303cf21ad74e59a6111be1d8c021e65b891c2a211167abb8c5e079e09e2c8a8339c00130100000c003300020017002b00020304";

/// RFC 9001 A.2's 50-byte quic_transport_parameters.
fn client_tp() -> Vec<u8> {
    split_ch(A2_CH).1.into_iter().find(|(t, _)| *t == 0x39).unwrap().1
}

#[derive(Debug, Default)]
struct Log(Mutex<Vec<(String, Vec<u8>)>>);

impl rustls::KeyLog for Log {
    fn log(&self, label: &str, _client_random: &[u8], secret: &[u8]) {
        self.0.lock().unwrap().push((label.to_string(), secret.to_vec()));
    }
}

impl Log {
    fn get(&self, label: &str) -> Vec<u8> {
        let v = self.0.lock().unwrap();
        let hits: Vec<_> = v.iter().filter(|(l, _)| l == label).collect();
        assert_eq!(hits.len(), 1, "{label}");
        hits[0].1.clone()
    }
}

/// Test-only: no path validation (the chain is opaque DER), but the CertificateVerify
/// signature really is checked, with ring.
#[derive(Debug)]
struct Verifier {
    schemes: Vec<SignatureScheme>,
    algs: WebPkiSupportedAlgorithms,
}

impl ServerCertVerifier for Verifier {
    fn verify_server_cert(
        &self,
        _end_entity: &CertificateDer<'_>,
        _intermediates: &[CertificateDer<'_>],
        _server_name: &ServerName<'_>,
        _ocsp: &[u8],
        _now: UnixTime,
    ) -> Result<ServerCertVerified, rustls::Error> {
        Ok(ServerCertVerified::assertion())
    }

    fn verify_tls12_signature(
        &self,
        _msg: &[u8],
        _cert: &CertificateDer<'_>,
        _dss: &DigitallySignedStruct,
    ) -> Result<HandshakeSignatureValid, rustls::Error> {
        Err(rustls::Error::General("TLS 1.2".into()))
    }

    fn verify_tls13_signature(
        &self,
        msg: &[u8],
        cert: &CertificateDer<'_>,
        dss: &DigitallySignedStruct,
    ) -> Result<HandshakeSignatureValid, rustls::Error> {
        rustls::crypto::verify_tls13_signature(msg, cert, dss, &self.algs)
    }

    fn supported_verify_schemes(&self) -> Vec<SignatureScheme> {
        self.schemes.clone()
    }
}

fn client(
    kx: Vec<&'static dyn SupportedKxGroup>,
    suites: Vec<SupportedCipherSuite>,
    alpn: Vec<Vec<u8>>,
    schemes: Vec<SignatureScheme>,
) -> (ClientConnection, Arc<Log>) {
    let mut provider = default_provider();
    provider.kx_groups = kx;
    provider.cipher_suites = suites;
    let algs = provider.signature_verification_algorithms;
    let mut cfg = rustls::ClientConfig::builder_with_provider(Arc::new(provider))
        .with_protocol_versions(&[&rustls::version::TLS13])
        .unwrap()
        .dangerous()
        .with_custom_certificate_verifier(Arc::new(Verifier { schemes, algs }))
        .with_no_client_auth();
    let log = Arc::new(Log::default());
    cfg.key_log = log.clone();
    cfg.alpn_protocols = alpn;
    let name = "localhost".try_into().unwrap();
    (ClientConnection::new(Arc::new(cfg), Version::V1, name, client_tp()).unwrap(), log)
}

fn default_suites() -> Vec<SupportedCipherSuite> {
    default_provider().cipher_suites
}

fn h3() -> Vec<Vec<u8>> {
    vec![b"h3".to_vec()]
}

fn cfg(chains: Vec<(Vec<u8>, SigningKey)>) -> ServerConfig {
    let chains = chains
        .into_iter()
        .map(|(der, key)| CertChain { der: vec![der], chain_schemes: vec![], key })
        .collect();
    build_config(chains).unwrap()
}

fn ecdsa_chain() -> (Vec<u8>, SigningKey) {
    (ECDSA_CERT.to_vec(), SigningKey::EcdsaP256(ECDSA_D))
}

fn rsa_chain() -> (Vec<u8>, SigningKey) {
    (RSA_CERT.to_vec(), SigningKey::Rsa(rsa_key()))
}

#[derive(Debug)]
enum Fail {
    Server(u64),
    Client(rustls::Error),
}

/// Takes everything the client has to send, tagged with its write level. `write_hs` is called
/// after every `read_hs`, as a QUIC stack does, so bytes before a `KeyChange` are at the level
/// in force before it (rustls pops a queued message before reporting pending handshake keys).
fn drain(c: &mut ClientConnection, level: &mut Level, out: &mut Vec<(Level, Vec<u8>)>) {
    loop {
        let mut buf = Vec::new();
        let kc = c.write_hs(&mut buf);
        if !buf.is_empty() {
            out.push((*level, buf));
        }
        match kc {
            Some(KeyChange::Handshake { .. }) => *level = Level::Handshake,
            Some(KeyChange::OneRtt { .. }) => *level = Level::OneRtt,
            None => return,
        }
    }
}

/// Shuttles CRYPTO data both ways; returns the server events of each `on_crypto` call.
fn run(
    c: &mut ClientConnection,
    hs: &mut ServerHandshake,
    tamper: Option<fn(Level, &mut Vec<u8>)>,
) -> Result<Vec<Vec<TlsEvent>>, Fail> {
    let mut level = Level::Initial;
    let mut out = Vec::new();
    let mut calls = Vec::new();
    drain(c, &mut level, &mut out);
    for _ in 0..10 {
        if !c.is_handshaking() && hs.is_complete() {
            break;
        }
        for (l, mut data) in std::mem::take(&mut out) {
            if let Some(t) = tamper {
                t(l, &mut data);
            }
            let mut ev = Vec::new();
            if let Err(e) = hs.on_crypto(l, &data, &RAND, &mut ev) {
                assert!(ev.is_empty());
                return Err(Fail::Server(e));
            }
            for e in &ev {
                if let TlsEvent::Send { data, .. } = e {
                    c.read_hs(data).map_err(Fail::Client)?;
                    drain(c, &mut level, &mut out);
                }
            }
            calls.push(ev);
        }
    }
    Ok(calls)
}

fn all(calls: &[Vec<TlsEvent>]) -> Vec<&TlsEvent> {
    calls.iter().flatten().collect()
}

fn initial_sends(calls: &[Vec<TlsEvent>]) -> usize {
    all(calls).iter().filter(|e| matches!(e, TlsEvent::Send { level: Level::Initial, .. })).count()
}

fn complete(c: &ClientConnection, hs: &ServerHandshake) {
    assert!(!c.is_handshaking());
    assert!(hs.is_complete());
    assert_eq!(c.alpn_protocol(), Some(&b"h3"[..]));
    assert_eq!(c.quic_transport_parameters(), Some(LOCAL_TP));
}

/// Both levels' secrets in the server's events equal what rustls derived.
fn secrets_match(calls: &[Vec<TlsEvent>], log: &Log) {
    let mut n = 0;
    for e in all(calls) {
        if let TlsEvent::Secrets { level, client, server } = e {
            let (c, s) = match level {
                Level::Handshake => ("CLIENT_HANDSHAKE_TRAFFIC_SECRET", "SERVER_HANDSHAKE_TRAFFIC_SECRET"),
                Level::OneRtt => ("CLIENT_TRAFFIC_SECRET_0", "SERVER_TRAFFIC_SECRET_0"),
                Level::Initial => panic!("Secrets(Initial)"),
            };
            assert_eq!(log.get(c), client.to_vec(), "{c}");
            assert_eq!(log.get(s), server.to_vec(), "{s}");
            n += 1;
        }
    }
    assert_eq!(n, 2);
}

/// The CertificateVerify's SignatureScheme, found by walking the Handshake-level flight.
fn cv_scheme(calls: &[Vec<TlsEvent>]) -> [u8; 2] {
    let d = all(calls)
        .into_iter()
        .find_map(|e| match e {
            TlsEvent::Send { level: Level::Handshake, data } => Some(data),
            _ => None,
        })
        .unwrap();
    let mut i = 0;
    while i < d.len() {
        let len = u32::from_be_bytes([0, d[i + 1], d[i + 2], d[i + 3]]) as usize;
        if d[i] == 15 {
            return [d[i + 4], d[i + 5]];
        }
        i += 4 + len;
    }
    panic!("no CertificateVerify");
}

#[test]
fn rustls_hrr_ecdsa() {
    let cfg = cfg(vec![ecdsa_chain()]);
    let mut hs = ServerHandshake::new(&cfg, LOCAL_TP.to_vec());
    let kx = vec![kx_group::X25519, kx_group::SECP256R1];
    let (mut c, log) = client(kx, default_suites(), h3(), vec![SignatureScheme::ECDSA_NISTP256_SHA256]);
    let calls = run(&mut c, &mut hs, None).unwrap();
    assert_eq!(calls[0], vec![TlsEvent::Send { level: Level::Initial, data: hex(HRR) }]);
    assert_eq!(initial_sends(&calls), 2);
    complete(&c, &hs);
    let peer: Vec<_> = all(&calls).into_iter().filter(|e| matches!(e, TlsEvent::PeerParams(_))).collect();
    assert_eq!(peer, vec![&TlsEvent::PeerParams(client_tp())]);
    secrets_match(&calls, &log);
}

#[test]
fn rustls_direct_rsa() {
    let cfg = cfg(vec![rsa_chain()]);
    let mut hs = ServerHandshake::new(&cfg, LOCAL_TP.to_vec());
    let (mut c, log) =
        client(vec![kx_group::SECP256R1], default_suites(), h3(), vec![SignatureScheme::RSA_PSS_SHA256]);
    let calls = run(&mut c, &mut hs, None).unwrap();
    assert_eq!(initial_sends(&calls), 1);
    complete(&c, &hs);
    secrets_match(&calls, &log);
}

#[test]
fn rustls_two_chains() {
    let cfg = cfg(vec![ecdsa_chain(), rsa_chain()]);
    for (scheme, want) in
        [(SignatureScheme::RSA_PSS_SHA256, [8, 4]), (SignatureScheme::ECDSA_NISTP256_SHA256, [4, 3])]
    {
        let mut hs = ServerHandshake::new(&cfg, LOCAL_TP.to_vec());
        let (mut c, log) = client(vec![kx_group::SECP256R1], default_suites(), h3(), vec![scheme]);
        let calls = run(&mut c, &mut hs, None).unwrap();
        assert_eq!(cv_scheme(&calls), want, "{scheme:?}");
        complete(&c, &hs);
        secrets_match(&calls, &log);
    }
}

#[test]
fn rustls_doomed() {
    let ecdsa = cfg(vec![ecdsa_chain()]);
    let rsa = cfg(vec![rsa_chain()]);
    let p256 = vec![SignatureScheme::ECDSA_NISTP256_SHA256];
    let cases = [
        (&ecdsa, default_suites(), vec![b"h3-29".to_vec()], p256.clone(), 0x178),
        (&ecdsa, vec![cipher_suite::TLS13_AES_256_GCM_SHA384], h3(), p256.clone(), 0x128),
        (&rsa, default_suites(), h3(), p256, 0x128),
    ];
    for (i, (cfg, suites, alpn, schemes, want)) in cases.into_iter().enumerate() {
        let kx = || default_provider().kx_groups;
        let mut hs = ServerHandshake::new(cfg, LOCAL_TP.to_vec());
        let (mut c, _) = client(kx(), suites.clone(), alpn.clone(), schemes.clone());
        assert!(matches!(run(&mut c, &mut hs, None), Err(Fail::Server(e)) if e == want), "case {i}");
        // The same ClientHello fails on the first call, with no events.
        let mut hs = ServerHandshake::new(cfg, LOCAL_TP.to_vec());
        let (mut c, _) = client(kx(), suites, alpn, schemes);
        let mut ch = Vec::new();
        assert!(c.write_hs(&mut ch).is_none());
        let mut ev = Vec::new();
        assert_eq!(hs.on_crypto(Level::Initial, &ch, &RAND, &mut ev), Err(want), "case {i}");
        assert!(ev.is_empty(), "case {i}");
    }
}

#[test]
fn rustls_tampered_finished() {
    let cfg = cfg(vec![ecdsa_chain()]);
    let mut hs = ServerHandshake::new(&cfg, LOCAL_TP.to_vec());
    let (mut c, _) =
        client(vec![kx_group::SECP256R1], default_suites(), h3(), vec![SignatureScheme::ECDSA_NISTP256_SHA256]);
    fn flip(l: Level, d: &mut Vec<u8>) {
        if l == Level::Handshake {
            *d.last_mut().unwrap() ^= 1;
        }
    }
    assert!(matches!(run(&mut c, &mut hs, Some(flip)), Err(Fail::Server(0x133))));
    assert!(!hs.is_complete());
}

#[test]
fn verifier_is_live() {
    let cfg = cfg(vec![(ECDSA_CERT.to_vec(), SigningKey::EcdsaP256([0x42; 32]))]);
    let mut hs = ServerHandshake::new(&cfg, LOCAL_TP.to_vec());
    let (mut c, _) =
        client(vec![kx_group::SECP256R1], default_suites(), h3(), vec![SignatureScheme::ECDSA_NISTP256_SHA256]);
    let r = run(&mut c, &mut hs, None);
    assert!(
        matches!(r, Err(Fail::Client(rustls::Error::InvalidCertificate(rustls::CertificateError::BadSignature)))),
        "{r:?}"
    );
}
