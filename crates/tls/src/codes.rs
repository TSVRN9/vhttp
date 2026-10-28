//! TLS 1.3 codepoints (RFC 8446) and the QUIC error codes the TLS layer reports
//! (RFC 9000 §20.1, RFC 9001 §4.8). Later sub-phases add their own.
use vstd::prelude::*;

verus! {

// HandshakeType (RFC 8446 §4)
pub const HT_CLIENT_HELLO: u8 = 1;  // client_hello
pub const HT_SERVER_HELLO: u8 = 2;  // server_hello
pub const HT_ENCRYPTED_EXTENSIONS: u8 = 8;  // encrypted_extensions
pub const HT_CERTIFICATE: u8 = 11;  // certificate
pub const HT_CERTIFICATE_VERIFY: u8 = 15;  // certificate_verify
pub const HT_FINISHED: u8 = 20;  // finished

// ProtocolVersion (RFC 8446 §4.1.2, §4.2.1, Appendix D)
pub const LEGACY_VERSION: u16 = 0x0303;  // legacy_version (TLS 1.2)
pub const TLS13: u16 = 0x0304;  // TLS 1.3
pub const SSL30: u16 = 0x0300;  // SSL 3.0

// CipherSuite (RFC 8446 Appendix B.4)
pub const TLS_AES_128_GCM_SHA256: u16 = 0x1301;  // TLS_AES_128_GCM_SHA256

// ExtensionType (RFC 8446 §4.2; RFC 9001 §8.2)
pub const EXT_SERVER_NAME: u16 = 0;  // server_name
pub const EXT_SUPPORTED_GROUPS: u16 = 10;  // supported_groups
pub const EXT_SIGNATURE_ALGORITHMS: u16 = 13;  // signature_algorithms
pub const EXT_ALPN: u16 = 16;  // application_layer_protocol_negotiation
pub const EXT_PRE_SHARED_KEY: u16 = 41;  // pre_shared_key
pub const EXT_EARLY_DATA: u16 = 42;  // early_data
pub const EXT_SUPPORTED_VERSIONS: u16 = 43;  // supported_versions
pub const EXT_COOKIE: u16 = 44;  // cookie
pub const EXT_PSK_KEY_EXCHANGE_MODES: u16 = 45;  // psk_key_exchange_modes
pub const EXT_OID_FILTERS: u16 = 48;  // oid_filters
pub const EXT_SIGNATURE_ALGORITHMS_CERT: u16 = 50;  // signature_algorithms_cert
pub const EXT_KEY_SHARE: u16 = 51;  // key_share
pub const EXT_QUIC_TRANSPORT_PARAMETERS: u16 = 0x39;  // quic_transport_parameters (RFC 9001)

// The HelloRetryRequest Random, SHA-256 of "HelloRetryRequest" (RFC 8446 §4.1.3).
pub const HRR_RANDOM: [u8; 32] = [
    0xcf, 0x21, 0xad, 0x74, 0xe5, 0x9a, 0x61, 0x11,
    0xbe, 0x1d, 0x8c, 0x02, 0x1e, 0x65, 0xb8, 0x91,
    0xc2, 0xa2, 0x11, 0x16, 0x7a, 0xbb, 0x8c, 0x5e,
    0x07, 0x9e, 0x09, 0xe2, 0xc8, 0xa8, 0x33, 0x9c,
];

// The HTTP/3 ALPN protocol ID (RFC 9114 §3.1).
pub const H3_ALPN: [u8; 2] = *b"h3";

// QUIC transport error codes (RFC 9000 §20.1)
pub const CRYPTO_ERROR_BASE: u64 = 0x100;  // CRYPTO_ERROR, 0x0100-0x01ff
pub const PROTOCOL_VIOLATION: u64 = 0x0a;
pub const CRYPTO_BUFFER_EXCEEDED: u64 = 0x0d;

// CRYPTO_ERROR_BASE + AlertDescription (RFC 8446 §6; RFC 9001 §4.8)
pub const ALERT_UNEXPECTED_MESSAGE: u64 = 0x10a;  // unexpected_message(10)
pub const ALERT_ILLEGAL_PARAMETER: u64 = 0x12f;  // illegal_parameter(47)
pub const ALERT_DECODE_ERROR: u64 = 0x132;  // decode_error(50)
pub const ALERT_PROTOCOL_VERSION: u64 = 0x146;  // protocol_version(70)
pub const ALERT_MISSING_EXTENSION: u64 = 0x16d;  // missing_extension(109)

// HandshakeType (RFC 8446 §4.4.1)
pub const HT_MESSAGE_HASH: u8 = 254;  // message_hash

// NamedGroup (RFC 8446 §4.2.7)
pub const SECP256R1: u16 = 0x0017;  // secp256r1

// SignatureScheme (RFC 8446 §4.2.3)
pub const ECDSA_SECP256R1_SHA256: u16 = 0x0403;  // ecdsa_secp256r1_sha256
pub const RSA_PSS_RSAE_SHA256: u16 = 0x0804;  // rsa_pss_rsae_sha256
pub const RSA_PKCS1_SHA1: u16 = 0x0201;  // rsa_pkcs1_sha1
pub const ECDSA_SHA1: u16 = 0x0203;  // ecdsa_sha1
pub const DSA_SHA1_RESERVED: u16 = 0x0202;  // dsa_sha1_RESERVED (Appendix B.3.1.3)

// CRYPTO_ERROR_BASE + AlertDescription (RFC 8446 §6; RFC 9001 §4.8)
pub const ALERT_HANDSHAKE_FAILURE: u64 = 0x128;  // handshake_failure(40)
pub const ALERT_DECRYPT_ERROR: u64 = 0x133;  // decrypt_error(51)
pub const ALERT_INTERNAL_ERROR: u64 = 0x150;  // internal_error(80)
pub const ALERT_NO_APPLICATION_PROTOCOL: u64 = 0x178;  // no_application_protocol(120)

/// Random bytes per handshake: [0..32] ServerHello random, [32..64] ECDHE scalar, [64..96] PSS salt.
pub const TLS_RAND_LEN: usize = 96;

// HKDF-Expand-Label (RFC 8446 §7.1)
pub const LABEL_PREFIX: [u8; 6] = *b"tls13 ";
pub const LABEL_DERIVED: [u8; 7] = *b"derived";
pub const LABEL_C_HS: [u8; 12] = *b"c hs traffic";
pub const LABEL_S_HS: [u8; 12] = *b"s hs traffic";
pub const LABEL_C_AP: [u8; 12] = *b"c ap traffic";
pub const LABEL_S_AP: [u8; 12] = *b"s ap traffic";
pub const LABEL_FINISHED: [u8; 8] = *b"finished";

// CertificateVerify context string (RFC 8446 §4.4.3)
pub const CV_SERVER_CONTEXT: [u8; 33] = *b"TLS 1.3, server CertificateVerify";

// ponytail: largest legal ClientHello is ~131 KiB; every observed client is < 2 KiB (curl 1532 B with an ML-KEM share); raise if a client needs more.
pub const MAX_HS_BODY: usize = 1 << 16;

} // verus!
