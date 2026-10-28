//! Server-sent handshake messages: ServerHello (RFC 8446 §4.1.3), HelloRetryRequest
//! (§4.1.4) and EncryptedExtensions (§4.3.1), each a serializer proven equal to its
//! `spec_*_bytes`. There is no EndOfEarlyData serializer, no cookie in the HRR, and no
//! `early_data`, `post_handshake_auth`, `psk_key_exchange_modes`, `pre_shared_key` or
//! `status_request_v2` extension in any message.
//!
//= https://www.rfc-editor.org/rfc/rfc8446#section-4.5
//# Servers MUST NOT send this message, and clients receiving it MUST
//# terminate the connection with an "unexpected_message" alert.
//
//= https://www.rfc-editor.org/rfc/rfc8446#section-4.2.6
//# Servers MUST NOT send this
//# extension.
//
//= https://www.rfc-editor.org/rfc/rfc8446#section-4.2.9
//# The server MUST NOT send a "psk_key_exchange_modes" extension.
use vstd::prelude::*;
use crate::codes::*;
#[allow(unused_imports)] // spec-only under plain cargo
use crate::ext::*;
#[allow(unused_imports)]
use crate::handshake::*;
use crate::pl::*;

verus! {

// =============================================================================
// Serialization specs
// =============================================================================

/// `key_share` in a ServerHello: `KeyShareEntry server_share`.
pub open spec fn spec_sh_key_share_bytes(group: u16, kx: Seq<u8>) -> Seq<u8> {
    spec_ext_bytes(EXT_KEY_SHARE, spec_be_bytes(group as nat, 2) + spec_vec_bytes(0xffff, kx))
}

/// `supported_versions` in a ServerHello or HelloRetryRequest: the selected version.
pub open spec fn spec_sh_versions_bytes() -> Seq<u8> {
    spec_ext_bytes(EXT_SUPPORTED_VERSIONS, spec_be_bytes(TLS13 as nat, 2))
}

/// The ServerHello / HelloRetryRequest body around its extension block.
pub open spec fn spec_hello_body_bytes(random: Seq<u8>, sid: Seq<u8>, exts: Seq<u8>) -> Seq<u8> {
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
        spec_hello_body_bytes(random, sid, spec_sh_key_share_bytes(group, kx) + spec_sh_versions_bytes()),
    )
}

pub open spec fn spec_hello_retry_request_bytes(sid: Seq<u8>, selected_group: u16) -> Seq<u8> {
    spec_hs_bytes(
        HT_SERVER_HELLO,
        spec_hello_body_bytes(
            HRR_RANDOM@,
            sid,
            spec_ext_bytes(EXT_KEY_SHARE, spec_be_bytes(selected_group as nat, 2))
                + spec_sh_versions_bytes(),
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

/// The `CertificateEntry` list: each is `cert_data<1..2^24-1>` and an empty
/// `extensions<0..2^16-1>`.
pub open spec fn spec_cert_entries_bytes(chain: Seq<Seq<u8>>) -> Seq<u8>
    decreases chain.len(),
{
    if chain.len() == 0 {
        seq![]
    } else {
        spec_cert_entries_bytes(chain.drop_last()) + spec_vec_bytes(0xff_ffff, chain.last())
            + spec_vec_bytes(0xffff, seq![])
    }
}

pub open spec fn spec_certificate_bytes(chain: Seq<Seq<u8>>) -> Seq<u8> {
    spec_hs_bytes(
        HT_CERTIFICATE,
        spec_vec_bytes(255, seq![]) + spec_vec_bytes(0xff_ffff, spec_cert_entries_bytes(chain)),
    )
}

pub open spec fn cert_chain_ok(chain: Seq<Seq<u8>>) -> bool {
    chain.len() >= 1 && (forall|i: int| 0 <= i < chain.len() ==> 1 <= #[trigger] chain[i].len()
        <= 0xff_ffff) && spec_cert_entries_bytes(chain).len() + 4 <= 0xff_ffff
}

pub open spec fn spec_certificate_verify_bytes(scheme: u16, sig: Seq<u8>) -> Seq<u8> {
    spec_hs_bytes(HT_CERTIFICATE_VERIFY, spec_be_bytes(scheme as nat, 2) + spec_vec_bytes(0xffff, sig))
}

pub open spec fn spec_finished_bytes(vd: Seq<u8>) -> Seq<u8> {
    spec_hs_bytes(HT_FINISHED, vd)
}

/// `Finished.verify_data` is exactly `Hash.length` (32 for SHA-256) bytes.
pub open spec fn rfc_finished(body: Seq<u8>) -> Result<Seq<u8>, u64> {
    if body.len() == 32 {
        Ok(body)
    } else {
        Err(ALERT_DECODE_ERROR)
    }
}

proof fn lemma_vec_len(ceiling: nat, c: Seq<u8>)
    ensures
        spec_vec_bytes(ceiling, c).len() == len_width(ceiling) + c.len(),
{
    assert(spec_be_bytes(c.len(), len_width(ceiling)).len() == len_width(ceiling));
}

/// The entries list only grows as certificates are added.
proof fn lemma_entries_mono(chain: Seq<Seq<u8>>, i: int)
    requires
        0 <= i <= chain.len(),
    ensures
        spec_cert_entries_bytes(chain.take(i)).len() <= spec_cert_entries_bytes(chain).len(),
    decreases chain.len() - i,
{
    if i < chain.len() {
        let t = chain.take(i + 1);
        assert(t.drop_last() =~= chain.take(i));
        assert(t.last() == chain[i]);
        lemma_vec_len(0xff_ffff, chain[i]);
        lemma_vec_len(0xffff, seq![]);
        lemma_entries_mono(chain, i + 1);
    } else {
        assert(chain.take(i) =~= chain);
    }
}

// RFC 8446 Appendix B.3.1.3, SignatureScheme "Reserved Code Points" (the `_RESERVED` entries).
pub open spec fn spec_reserved_scheme(s: u16) -> bool {
    s <= 0x0200 || s == 0x0202 || (0x0204 <= s <= 0x0400) || s == 0x0402 || (0x0404 <= s
        <= 0x0500) || s == 0x0502 || (0x0504 <= s <= 0x0600) || s == 0x0602 || (0x0604 <= s
        <= 0x06FF)
}

// RFC 8446 Appendix B.3.1.4, NamedGroup: unallocated_RESERVED(0x0000) and the
// `obsolete_RESERVED` ranges.
pub open spec fn spec_reserved_group(g: u16) -> bool {
    g <= 0x0016 || (0x001A <= g <= 0x001C) || (0xFF01 <= g <= 0xFF02)
}

pub fn is_reserved_scheme(s: u16) -> (r: bool)
    ensures
        r == spec_reserved_scheme(s),
{
    s <= 0x0200 || s == 0x0202 || (0x0204 <= s && s <= 0x0400) || s == 0x0402 || (0x0404 <= s
        && s <= 0x0500) || s == 0x0502 || (0x0504 <= s && s <= 0x0600) || s == 0x0602 || (0x0604
        <= s && s <= 0x06FF)
}

pub fn is_reserved_group(g: u16) -> (r: bool)
    ensures
        r == spec_reserved_group(g),
{
    g <= 0x0016 || (0x001A <= g && g <= 0x001C) || (0xFF01 <= g && g <= 0xFF02)
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
            spec_hello_body_bytes(random@, sid@, exts@),
        ),
{
    let mut body: Vec<u8> = Vec::new();
    put_u16(&mut body, LEGACY_VERSION);
    put_bytes(&mut body, random);
    put_vec(&mut body, 32, sid);
    //= https://www.rfc-editor.org/rfc/rfc9001#section-4.2
    //# An endpoint MUST terminate the connection if a
    //# version of TLS older than 1.3 is negotiated.
    // Only 0x0304 is ever sent, with its one suite.
    put_u16(&mut body, TLS_AES_128_GCM_SHA256);
    body.push(0);
    put_vec(&mut body, 0xffff, exts);
    assert(body@ =~= spec_hello_body_bytes(random@, sid@, exts@));
    put_hs(out, HT_SERVER_HELLO, &body);
}

/// The `supported_versions` extension of a ServerHello or HelloRetryRequest.
//= https://www.rfc-editor.org/rfc/rfc8446#section-4.2.1
//# A server which negotiates TLS 1.3 MUST respond by sending
//# a "supported_versions" extension containing the selected version
//# value (0x0304).
fn put_sh_versions(out: &mut Vec<u8>)
    ensures
        final(out)@ == old(out)@ + spec_sh_versions_bytes(),
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
        !spec_reserved_group(group),
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
    assert(exts@ =~= spec_sh_key_share_bytes(group, key_exchange@) + spec_sh_versions_bytes());
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
        !spec_reserved_group(selected_group),
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
//# MUST send the quic_transport_parameters extension
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

// RFC 8446 §4.4.2: X509 entries only (`server_certificate_type` is never negotiated), no
// OpenPGP, no extensions in any entry, and a zero-length context.
//= https://www.rfc-editor.org/rfc/rfc8446#section-4.4.2
//# Otherwise (in the case of server authentication),
//# this field SHALL be zero length.
//= https://www.rfc-editor.org/rfc/rfc8446#section-4.4.2
//# The server's certificate_list MUST always be non-empty.
//= https://www.rfc-editor.org/rfc/rfc8446#section-4.4.2
//# The OpenPGP certificate type [RFC6091] MUST NOT be used with TLS 1.3.
//= https://www.rfc-editor.org/rfc/rfc8446#section-4.4.2
//# Extensions in the Certificate message from the server MUST
//# correspond to ones from the ClientHello message.
//= https://www.rfc-editor.org/rfc/rfc8446#section-4.4.2
//# If the RawPublicKey certificate type was negotiated, then the
//# certificate_list MUST contain no more than one CertificateEntry,
//# which contains an ASN1_subjectPublicKeyInfo value as defined in
//# [RFC7250], Section 3.
//= https://www.rfc-editor.org/rfc/rfc8446#section-4.4.2.1
//# TLS 1.3 servers MUST NOT act upon its presence or information in it
//# when processing ClientHello messages; in particular, they MUST NOT
//# send the status_request_v2 extension in the EncryptedExtensions,
//# CertificateRequest, or Certificate messages.
//= https://www.rfc-editor.org/rfc/rfc8446#appendix-B
//# TLS 1.3 implementations MUST NOT send them but might receive them
//# from older TLS implementations.
//= https://www.rfc-editor.org/rfc/rfc9001#section-4.4
//# More specifically, servers MUST NOT send post-
//# handshake TLS CertificateRequest messages, and clients MUST treat
//# receipt of such messages as a connection error of type
//# PROTOCOL_VIOLATION.
// ponytail: chain is opaque DER; 4b passes the config's chain unchanged.
pub fn serialize_certificate(chain: &Vec<Vec<u8>>, out: &mut Vec<u8>)
    requires
        cert_chain_ok(chain.deep_view()),
    ensures
        final(out)@ == old(out)@ + spec_certificate_bytes(chain.deep_view()),
{
    let ghost cs = chain.deep_view();
    let mut entries: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < chain.len()
        invariant
            i <= chain.len(),
            cs == chain.deep_view(),
            cert_chain_ok(cs),
            entries@ == spec_cert_entries_bytes(cs.take(i as int)),
        decreases chain.len() - i,
    {
        proof {
            assert(chain.deep_view()[i as int] == chain[i as int]@);
            assert(cs[i as int].len() <= 0xff_ffff);
            lemma_vec_len(0xff_ffff, cs[i as int]);
            lemma_vec_len(0xffff, seq![]);
            lemma_entries_mono(cs, i as int + 1);
        }
        let ghost before = entries@;
        put_vec(&mut entries, 0xff_ffff, &chain[i]);
        let empty: Vec<u8> = Vec::new();
        put_vec(&mut entries, 0xffff, &empty);
        proof {
            let t = cs.take(i as int + 1);
            assert(t.drop_last() =~= cs.take(i as int));
            assert(t.last() == cs[i as int]);
            assert(empty@ =~= Seq::<u8>::empty());
            assert(entries@ =~= before + spec_vec_bytes(0xff_ffff, cs[i as int])
                + spec_vec_bytes(0xffff, seq![]));
        }
        i += 1;
    }
    proof {
        assert(cs.take(i as int) =~= cs);
    }
    let empty: Vec<u8> = Vec::new();
    let mut body: Vec<u8> = Vec::new();
    put_vec(&mut body, 255, &empty);
    put_vec(&mut body, 0xff_ffff, &entries);
    proof {
        assert(empty@ =~= Seq::<u8>::empty());
        assert(body@ =~= spec_vec_bytes(255, seq![]) + spec_vec_bytes(
            0xff_ffff,
            spec_cert_entries_bytes(cs),
        ));
        lemma_vec_len(255, seq![]);
        lemma_vec_len(0xff_ffff, spec_cert_entries_bytes(cs));
    }
    put_hs(out, HT_CERTIFICATE, &body);
}

/// Decides `serialize_certificate`'s precondition for a runtime chain. Each length is checked
/// before it is added, so the running total stays below 2^25 and cannot overflow.
pub fn cert_chain_fits(chain: &Vec<Vec<u8>>) -> (r: bool)
    ensures
        r == cert_chain_ok(chain.deep_view()),
{
    let ghost cs = chain.deep_view();
    if chain.len() == 0 {
        return false;
    }
    let mut total: usize = 0;
    let mut i: usize = 0;
    assert(cs.take(0) =~= Seq::<Seq<u8>>::empty());
    while i < chain.len()
        invariant
            i <= chain.len(),
            cs == chain.deep_view(),
            cs.len() >= 1,
            forall|k: int| 0 <= k < i ==> 1 <= #[trigger] cs[k].len() <= 0xff_ffff,
            total == spec_cert_entries_bytes(cs.take(i as int)).len(),
            total + 4 <= 0xff_ffff,
        decreases chain.len() - i,
    {
        assert(chain.deep_view()[i as int] == chain[i as int]@);
        let n = chain[i].len();
        if n == 0 || n > 0xff_ffff {
            assert(!(1 <= cs[i as int].len() <= 0xff_ffff));
            return false;
        }
        proof {
            let t = cs.take(i as int + 1);
            assert(t.drop_last() =~= cs.take(i as int));
            assert(t.last() == cs[i as int]);
            lemma_vec_len(0xff_ffff, cs[i as int]);
            lemma_vec_len(0xffff, seq![]);
            lemma_entries_mono(cs, i as int + 1);
        }
        if total + n + 5 + 4 > 0xff_ffff {
            return false;
        }
        total = total + n + 5;
        i += 1;
    }
    assert(cs.take(i as int) =~= cs);
    true
}

pub fn serialize_certificate_verify(scheme: u16, signature: &[u8], out: &mut Vec<u8>)
    requires
        !spec_reserved_scheme(scheme),
        signature@.len() <= 0xffff,
    ensures
        final(out)@ == old(out)@ + spec_certificate_verify_bytes(scheme, signature@),
{
    let mut body: Vec<u8> = Vec::new();
    put_u16(&mut body, scheme);
    put_vec(&mut body, 0xffff, signature);
    assert(body@ =~= spec_be_bytes(scheme as nat, 2) + spec_vec_bytes(0xffff, signature@));
    put_hs(out, HT_CERTIFICATE_VERIFY, &body);
}

pub fn serialize_finished(verify_data: &[u8; 32], out: &mut Vec<u8>)
    ensures
        final(out)@ == old(out)@ + spec_finished_bytes(verify_data@),
{
    put_hs(out, HT_FINISHED, verify_data.as_slice());
}

pub fn parse_finished(body: &[u8]) -> (r: Result<[u8; 32], u64>)
    ensures
        match r {
            Ok(a) => rfc_finished(body@) == Ok::<Seq<u8>, u64>(a@),
            Err(e) => rfc_finished(body@) == Err::<Seq<u8>, u64>(e),
        },
{
    if body.len() != 32 {
        return Err(ALERT_DECODE_ERROR);
    }
    let mut a = [0u8; 32];
    let mut i: usize = 0;
    while i < 32
        invariant
            i <= 32,
            body@.len() == 32,
            forall|k: int| 0 <= k < i ==> a[k] == body@[k],
        decreases 32 - i,
    {
        a[i] = body[i];
        i += 1;
    }
    assert(a@ =~= body@);
    Ok(a)
}

} // verus!
