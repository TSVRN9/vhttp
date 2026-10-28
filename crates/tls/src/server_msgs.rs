//! Server-sent handshake messages: ServerHello (RFC 8446 §4.1.3), HelloRetryRequest
//! (§4.1.4) and EncryptedExtensions (§4.3.1), each a serializer proven equal to its
//! `spec_*_bytes`. There is no EndOfEarlyData serializer, no cookie in the HRR, and no
//! `early_data`, `post_handshake_auth`, `psk_key_exchange_modes`, `pre_shared_key` or
//! `status_request_v2` extension in any message.
//!
//= https://www.rfc-editor.org/rfc/rfc8446#section-4.5
//# Servers MUST NOT send this message, and clients receiving it MUST
//# terminate the connection with an "unexpected_message" alert.
use vstd::prelude::*;
use crate::codes::*;
use crate::ext::*;
use crate::handshake::*;
use crate::pl::*;

verus! {

// =============================================================================
// Serialization specs
// =============================================================================

/// `key_share` in a ServerHello: `KeyShareEntry server_share`.
pub open spec fn spec_sh_key_share(group: u16, kx: Seq<u8>) -> Seq<u8> {
    spec_ext_bytes(EXT_KEY_SHARE, spec_be_bytes(group as nat, 2) + spec_vec_bytes(0xffff, kx))
}

/// `supported_versions` in a ServerHello or HelloRetryRequest: the selected version.
pub open spec fn spec_sh_versions() -> Seq<u8> {
    spec_ext_bytes(EXT_SUPPORTED_VERSIONS, spec_be_bytes(TLS13 as nat, 2))
}

/// The ServerHello / HelloRetryRequest body around its extension block.
pub open spec fn spec_hello_body(random: Seq<u8>, sid: Seq<u8>, exts: Seq<u8>) -> Seq<u8> {
    spec_be_bytes(LEGACY_VERSION as nat, 2) + random + spec_vec_bytes(32, sid) + spec_be_bytes(
        TLS_AES_128_GCM_SHA256 as nat,
        2,
    ) + seq![0u8] + spec_vec_bytes(0xffff, exts)
}

pub open spec fn spec_server_hello_bytes(
    random: Seq<u8>,
    sid: Seq<u8>,
    group: u16,
    kx: Seq<u8>,
) -> Seq<u8> {
    spec_hs_bytes(
        HT_SERVER_HELLO,
        spec_hello_body(random, sid, spec_sh_key_share(group, kx) + spec_sh_versions()),
    )
}

pub open spec fn spec_hello_retry_request_bytes(sid: Seq<u8>, selected_group: u16) -> Seq<u8> {
    spec_hs_bytes(
        HT_SERVER_HELLO,
        spec_hello_body(
            HRR_RANDOM@,
            sid,
            spec_ext_bytes(EXT_KEY_SHARE, spec_be_bytes(selected_group as nat, 2))
                + spec_sh_versions(),
        ),
    )
}

pub open spec fn spec_encrypted_extensions_bytes(tp: Seq<u8>) -> Seq<u8> {
    spec_hs_bytes(
        HT_ENCRYPTED_EXTENSIONS,
        spec_vec_bytes(
            0xffff,
            spec_ext_bytes(EXT_ALPN, spec_vec_bytes(0xffff, spec_vec_bytes(255, H3_ALPN@)))
                + spec_ext_bytes(EXT_QUIC_TRANSPORT_PARAMETERS, tp),
        ),
    )
}

// =============================================================================
// Exec
// =============================================================================

fn put_bytes(out: &mut Vec<u8>, c: &[u8])
    ensures
        final(out)@ == old(out)@ + c@,
{
    out.extend_from_slice(c);
    assert(final(out)@ =~= old(out)@ + c@);
}

fn put_ext(out: &mut Vec<u8>, ty: u16, data: &[u8])
    requires
        data@.len() <= 0xffff,
    ensures
        final(out)@ == old(out)@ + spec_ext_bytes(ty, data@),
{
    put_u16(out, ty);
    put_vec(out, 0xffff, data);
    assert(final(out)@ =~= old(out)@ + spec_ext_bytes(ty, data@));
}

/// A complete handshake message.
fn put_hs(out: &mut Vec<u8>, ty: u8, body: &[u8])
    requires
        body@.len() <= 0xff_ffff,
    ensures
        final(out)@ == old(out)@ + spec_hs_bytes(ty, body@),
{
    out.push(ty);
    put_vec(out, 0xff_ffff, body);
    assert(final(out)@ =~= old(out)@ + spec_hs_bytes(ty, body@));
}

// RFC 8446 §4.1.3 and §4.1.4: ServerHello and HelloRetryRequest share one layout.
//= https://www.rfc-editor.org/rfc/rfc8446#section-4.1.3
//# legacy_version:  In previous versions of TLS, this field was used for
//# version negotiation and represented the selected version number
//# for the connection.  Unfortunately, some middleboxes fail when
//# presented with new values.  In TLS 1.3, the TLS server indicates
//# its version using the "supported_versions" extension
//# (Section 4.2.1), and the legacy_version field MUST be set to
//# 0x0303, which is the version number for TLS 1.2.  (See Appendix D
//# for details about backward compatibility.)
//= https://www.rfc-editor.org/rfc/rfc8446#section-4.2.1
//# It MUST set the ServerHello.legacy_version field to
//# 0x0303 (TLS 1.2).
//= https://www.rfc-editor.org/rfc/rfc8446#appendix-D.5
//# Implementations MUST NOT send a ClientHello.legacy_version or
//# ServerHello.legacy_version set to 0x0300 or less.
//= https://www.rfc-editor.org/rfc/rfc8446#section-4.1.3
//# legacy_compression_method:  A single byte which MUST have the
//# value 0.
/// `exts` is the extension block content; the cipher suite is the constant 0x1301.
fn put_hello(out: &mut Vec<u8>, random: &[u8], sid: &[u8], exts: &[u8])
    requires
        random@.len() == 32,
        sid@.len() <= 32,
        exts@.len() <= 0xffff,
    ensures
        final(out)@ == old(out)@ + spec_hs_bytes(
            HT_SERVER_HELLO,
            spec_hello_body(random@, sid@, exts@),
        ),
{
    let mut body: Vec<u8> = Vec::new();
    put_u16(&mut body, LEGACY_VERSION);
    put_bytes(&mut body, random);
    put_vec(&mut body, 32, sid);
    // RFC 9001 §4.2: only TLS 1.3 is ever negotiated, with its one suite.
    put_u16(&mut body, TLS_AES_128_GCM_SHA256);
    body.push(0);
    put_vec(&mut body, 0xffff, exts);
    assert(body@ =~= spec_hello_body(random@, sid@, exts@));
    put_hs(out, HT_SERVER_HELLO, &body);
}

/// The `supported_versions` extension of a ServerHello or HelloRetryRequest.
//= https://www.rfc-editor.org/rfc/rfc8446#section-4.2.1
//# A server which negotiates TLS 1.3 MUST respond by sending
//# a "supported_versions" extension containing the selected version
//# value (0x0304).
fn put_sh_versions(out: &mut Vec<u8>)
    ensures
        final(out)@ == old(out)@ + spec_sh_versions(),
{
    let mut v: Vec<u8> = Vec::new();
    put_u16(&mut v, TLS13);
    put_ext(out, EXT_SUPPORTED_VERSIONS, &v);
}

// RFC 8446 §4.1.3 and §9.2: key_share then supported_versions, nothing else.
//= https://www.rfc-editor.org/rfc/rfc8446#section-4.1.3
//# The ServerHello MUST only include
//# extensions which are required to establish the cryptographic
//# context and negotiate the protocol version.  All TLS 1.3
//# ServerHello messages MUST contain the "supported_versions"
//# extension.
//= https://www.rfc-editor.org/rfc/rfc8446#section-9.2
//# All implementations MUST send and use these extensions when offering
//# applicable features:
// ponytail: every non-PQ NamedGroup fits; 4b passes 65.
pub fn serialize_server_hello(
    random: &[u8; 32],
    session_id_echo: &[u8],
    group: u16,
    key_exchange: &[u8],
    out: &mut Vec<u8>,
)
    requires
        session_id_echo@.len() <= 32,
        1 <= key_exchange@.len() <= 256,
    ensures
        final(out)@ == old(out)@ + spec_server_hello_bytes(
            random@,
            session_id_echo@,
            group,
            key_exchange@,
        ),
{
    let mut share: Vec<u8> = Vec::new();
    put_u16(&mut share, group);
    put_vec(&mut share, 0xffff, key_exchange);
    let mut exts: Vec<u8> = Vec::new();
    put_ext(&mut exts, EXT_KEY_SHARE, &share);
    put_sh_versions(&mut exts);
    assert(exts@ =~= spec_sh_key_share(group, key_exchange@) + spec_sh_versions());
    put_hello(out, random.as_slice(), session_id_echo, &exts);
}

//= https://www.rfc-editor.org/rfc/rfc8446#section-4.1.4
//# The server's extensions MUST contain "supported_versions".
//= https://www.rfc-editor.org/rfc/rfc8446#section-4.1.4
//# As
//# with the ServerHello, a HelloRetryRequest MUST NOT contain any
//# extensions that were not first offered by the client in its
//# ClientHello, with the exception of optionally the "cookie" (see
//# Section 4.2.2) extension.
pub fn serialize_hello_retry_request(
    session_id_echo: &[u8],
    selected_group: u16,
    out: &mut Vec<u8>,
)
    requires
        session_id_echo@.len() <= 32,
    ensures
        final(out)@ == old(out)@ + spec_hello_retry_request_bytes(session_id_echo@, selected_group),
{
    let mut sel: Vec<u8> = Vec::new();
    put_u16(&mut sel, selected_group);
    let mut exts: Vec<u8> = Vec::new();
    put_ext(&mut exts, EXT_KEY_SHARE, &sel);
    put_sh_versions(&mut exts);
    put_hello(out, HRR_RANDOM.as_slice(), session_id_echo, &exts);
}

// RFC 8446 §4.3.1 and RFC 9001 §8.2: ALPN `h3`, then quic_transport_parameters.
//= https://www.rfc-editor.org/rfc/rfc9001#section-8.2
//# Endpoints
//# MUST send the quic_transport_parameters extension; endpoints that
//# receive ClientHello or EncryptedExtensions messages without the
//# quic_transport_parameters extension MUST close the connection with an
// ponytail: 3b's server TPs are < 256 bytes.
pub fn serialize_encrypted_extensions(transport_params: &[u8], out: &mut Vec<u8>)
    requires
        transport_params@.len() <= 1024,
    ensures
        final(out)@ == old(out)@ + spec_encrypted_extensions_bytes(transport_params@),
{
    let mut names: Vec<u8> = Vec::new();
    put_vec(&mut names, 255, H3_ALPN.as_slice());
    let mut alpn: Vec<u8> = Vec::new();
    put_vec(&mut alpn, 0xffff, &names);
    let mut exts: Vec<u8> = Vec::new();
    put_ext(&mut exts, EXT_ALPN, &alpn);
    put_ext(&mut exts, EXT_QUIC_TRANSPORT_PARAMETERS, transport_params);
    let mut body: Vec<u8> = Vec::new();
    put_vec(&mut body, 0xffff, &exts);
    assert(body@ =~= spec_vec_bytes(
        0xffff,
        spec_ext_bytes(EXT_ALPN, spec_vec_bytes(0xffff, spec_vec_bytes(255, H3_ALPN@)))
            + spec_ext_bytes(EXT_QUIC_TRANSPORT_PARAMETERS, transport_params@),
    ));
    put_hs(out, HT_ENCRYPTED_EXTENSIONS, &body);
}

} // verus!
