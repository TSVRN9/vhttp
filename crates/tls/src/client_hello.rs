//! RFC 8446 §4.1.2 ClientHello, server side: a transcribed field layer proven canonical,
//! and the validation that turns it into a `ClientHello` or the one alert a fixed check
//! order picks (Decision 9).
use vstd::prelude::*;
use crate::ch_ext::*;
use crate::codes::*;
use crate::ext::*;
use crate::pl::*;
use vstd::slice::{slice_subrange, slice_to_vec};

verus! {

// =============================================================================
// Field layer: RFC 8446 §4.1.2 transcription
// =============================================================================

pub struct SpecChFields {
    pub legacy_version: u16,
    pub random: Seq<u8>,
    pub legacy_session_id: Seq<u8>,
    pub cipher_suites: Seq<u16>,
    pub compression: Seq<u8>,
    pub exts: Option<Seq<SpecExt>>,
}

// RFC 8446 §4.1.2:
//   uint16 ProtocolVersion; opaque Random[32]; uint8 CipherSuite[2];
//   struct {
//       ProtocolVersion legacy_version = 0x0303;    /* TLS v1.2 */
//       Random random;
//       opaque legacy_session_id<0..32>;
//       CipherSuite cipher_suites<2..2^16-2>;
//       opaque legacy_compression_methods<1..2^8-1>;
//       Extension extensions<8..2^16-1>;
//   } ClientHello;
// "All versions of TLS allow an extensions field to optionally follow the compression_methods
// field.": the end of the body there means no extension block. The block's floor is 0, not
// TLS 1.3's 8: without supported_versions this is a TLS 1.2 ClientHello (§4.1.2), whose block
// is `<0..2^16-1>`, and Appendix D.2 answers it with protocol_version, not decode_error. Every
// accepted ClientHello still has at least 8 bytes of extensions (step 9).
/// The `extensions` field after the compression methods: `Some(None)` when absent.
pub open spec fn rfc_ch_ext_block(rest: Seq<u8>) -> Option<Option<Seq<SpecExt>>> {
    if rest.len() == 0 {
        Some(None)
    } else {
        match rfc_vec_exact(rest, 0, 0xffff) {
            None => None,
            Some(c) => match rfc_ext_list(c) {
                None => None,
                Some(l) => Some(Some(l)),
            },
        }
    }
}

pub open spec fn rfc_ch_fields(body: Seq<u8>) -> Option<SpecChFields> {
    if body.len() < 34 {
        None
    } else {
        match rfc_vec(body.skip(34), 0, 32) {
            None => None,
            Some((sid, r1)) => match rfc_vec(r1, 2, 0xfffe) {
                None => None,
                Some((cs, r2)) => match rfc_u16_list(cs) {
                    None => None,
                    Some(suites) => match rfc_vec(r2, 1, 255) {
                        None => None,
                        Some((comp, r3)) => match rfc_ch_ext_block(r3) {
                            None => None,
                            Some(exts) => Some(
                                SpecChFields {
                                    legacy_version: be(body, 2) as u16,
                                    random: body.subrange(2, 34),
                                    legacy_session_id: sid,
                                    cipher_suites: suites,
                                    compression: comp,
                                    exts,
                                },
                            ),
                        },
                    },
                },
            },
        }
    }
}

pub open spec fn spec_ch_ext_block_bytes(exts: Option<Seq<SpecExt>>) -> Seq<u8> {
    match exts {
        None => seq![],
        Some(l) => spec_vec_bytes(0xffff, spec_ext_list_bytes(l)),
    }
}

pub open spec fn spec_ch_fields_bytes(f: SpecChFields) -> Seq<u8> {
    spec_be_bytes(f.legacy_version as nat, 2) + f.random + spec_vec_bytes(32, f.legacy_session_id)
        + spec_vec_bytes(0xfffe, spec_u16_list_bytes(f.cipher_suites)) + spec_vec_bytes(
        255,
        f.compression,
    ) + spec_ch_ext_block_bytes(f.exts)
}

pub proof fn lemma_ch_ext_block_canonical(rest: Seq<u8>)
    ensures
        rfc_ch_ext_block(rest) matches Some(e) ==> spec_ch_ext_block_bytes(e) == rest,
{
    if rest.len() == 0 {
        assert(rest =~= seq![]);
    } else if let Some(Some(l)) = rfc_ch_ext_block(rest) {
        let (c, e) = rfc_vec(rest, 0, 0xffff).unwrap();
        lemma_vec_canonical(rest, 0, 0xffff, c, e);
        theorem_ext_list_canonical(c);
        assert(e =~= seq![]);
        assert(rest =~= spec_vec_bytes(0xffff, c));
    }
}

/// A parsed ClientHello body is exactly the canonical encoding of its fields.
pub proof fn theorem_ch_fields_canonical(body: Seq<u8>)
    ensures
        rfc_ch_fields(body) matches Some(f) ==> spec_ch_fields_bytes(f) == body,
{
    if let Some(f) = rfc_ch_fields(body) {
        let (sid, r1) = rfc_vec(body.skip(34), 0, 32).unwrap();
        let (cs, r2) = rfc_vec(r1, 2, 0xfffe).unwrap();
        let (comp, r3) = rfc_vec(r2, 1, 255).unwrap();
        let p0 = spec_be_bytes(f.legacy_version as nat, 2);
        let a = spec_vec_bytes(32, sid);
        let b = spec_vec_bytes(0xfffe, spec_u16_list_bytes(f.cipher_suites));
        let c = spec_vec_bytes(255, comp);
        let t = spec_ch_ext_block_bytes(f.exts);
        lemma_be_canonical(body, 2);
        assert(be(body, 2) as u16 as nat == be(body, 2));
        assert(p0 == body.take(2));
        lemma_ch_ext_block_canonical(r3);
        assert(r3 == t);
        lemma_vec_canonical(r2, 1, 255, comp, r3);
        assert(r2 == c + t);
        lemma_u16_list_canonical(cs, f.cipher_suites);
        lemma_vec_canonical(r1, 2, 0xfffe, cs, r2);
        assert(r1 == b + (c + t));
        lemma_vec_canonical(body.skip(34), 0, 32, sid, r1);
        assert(body.skip(34) == a + (b + (c + t)));
        assert(body =~= p0 + f.random + (a + (b + (c + t))));
        assert(spec_ch_fields_bytes(f) == p0 + f.random + a + b + c + t);
        assert(p0 + f.random + a + b + c + t =~= p0 + f.random + (a + (b + (c + t))));
    }
}

// =============================================================================
// Validation: the check order is the requirement (Decision 9)
// =============================================================================

#[derive(Debug, PartialEq, Eq)]
pub struct ClientHello {
    pub random: [u8; 32],
    pub legacy_session_id: Vec<u8>,
    pub cipher_suites: Vec<u16>,
    pub versions: Vec<u16>,
    pub groups: Option<Vec<u16>>,
    pub key_shares: Option<Vec<KeyShareEntry>>,
    pub sig_algs: Vec<u16>,
    pub sig_algs_cert: Option<Vec<u16>>,
    pub alpn: Option<Vec<Vec<u8>>>,
    pub server_name: Option<Vec<u8>>,
    pub transport_params: Vec<u8>,
}

pub struct SpecClientHello {
    pub random: Seq<u8>,
    pub legacy_session_id: Seq<u8>,
    pub cipher_suites: Seq<u16>,
    pub versions: Seq<u16>,
    pub groups: Option<Seq<u16>>,
    pub key_shares: Option<Seq<SpecKeyShare>>,
    pub sig_algs: Seq<u16>,
    pub sig_algs_cert: Option<Seq<u16>>,
    pub alpn: Option<Seq<Seq<u8>>>,
    pub server_name: Option<Seq<u8>>,
    pub transport_params: Seq<u8>,
}

impl View for ClientHello {
    type V = SpecClientHello;

    open spec fn view(&self) -> SpecClientHello {
        SpecClientHello {
            random: self.random@,
            legacy_session_id: self.legacy_session_id@,
            cipher_suites: self.cipher_suites@,
            versions: self.versions@,
            groups: self.groups.deep_view(),
            key_shares: self.key_shares.deep_view(),
            sig_algs: self.sig_algs@,
            sig_algs_cert: self.sig_algs_cert.deep_view(),
            alpn: self.alpn.deep_view(),
            server_name: self.server_name.deep_view(),
            transport_params: self.transport_params@,
        }
    }
}

/// The extensions of `f`, empty when the block is absent.
pub open spec fn rfc_ch_exts(f: SpecChFields) -> Seq<SpecExt> {
    match f.exts {
        Some(l) => l,
        None => seq![],
    }
}

/// The ClientHello a server accepts, or the alert for the first failing check:
/// 1. the field layer does not parse: decode_error;
/// 2. the extension-block rules (duplicates, pre_shared_key last, oid_filters);
/// 3. a recognized extension whose body does not parse: decode_error;
/// 4. legacy_version <= 0x0300: protocol_version;
/// 5. no supported_versions offering 0x0304: protocol_version;
/// 6. compression other than [0]: illegal_parameter;
/// 7. a non-empty legacy_session_id: PROTOCOL_VIOLATION;
/// 8. a cookie: illegal_parameter;
/// 9. a missing extension: missing_extension;
/// 10. otherwise the parsed fields.
/// Unknown and GREASE suites, extensions and list values are kept in wire order and are
/// otherwise ignored. early_data (ignored: the first of §4.2.10's three ways),
/// pre_shared_key (syntax only, PSK is declined), status_request_v2 (17, unrecognized) and
/// the quic_transport_parameters content (4c parses it with quic::tp) are not acted on.
pub open spec fn rfc_client_hello(body: Seq<u8>) -> Result<SpecClientHello, u64> {
    match rfc_ch_fields(body) {
        //= https://www.rfc-editor.org/rfc/rfc8446#section-6
        //# Peers which receive a message which
        //# cannot be parsed according to the syntax (e.g., have a length
        //# extending beyond the message boundary or contain an out-of-range
        //# length) MUST terminate the connection with a "decode_error" alert.
        None => Err(ALERT_DECODE_ERROR),
        Some(f) => {
            let x = rfc_ch_exts(f);
            let sn = spec_find(x, EXT_SERVER_NAME);
            let sg = spec_find(x, EXT_SUPPORTED_GROUPS);
            let sa = spec_find(x, EXT_SIGNATURE_ALGORITHMS);
            let al = spec_find(x, EXT_ALPN);
            let pk = spec_find(x, EXT_PRE_SHARED_KEY);
            let ed = spec_find(x, EXT_EARLY_DATA);
            let sv = spec_find(x, EXT_SUPPORTED_VERSIONS);
            let ck = spec_find(x, EXT_COOKIE);
            let pm = spec_find(x, EXT_PSK_KEY_EXCHANGE_MODES);
            let sc = spec_find(x, EXT_SIGNATURE_ALGORITHMS_CERT);
            let ks = spec_find(x, EXT_KEY_SHARE);
            let tp = spec_find(x, EXT_QUIC_TRANSPORT_PARAMETERS);
            //= https://www.rfc-editor.org/rfc/rfc8446#section-6
            //# Peers which receive a message which is syntactically correct but
            //# semantically invalid (e.g., a DHE share of p - 1, or an invalid enum)
            //# MUST terminate the connection with an "illegal_parameter" alert.
            if rfc_ch_ext_check(x) is Err {
                // 2: duplicates, pre_shared_key not last, oid_filters (ext.rs).
                Err(rfc_ch_ext_check(x)->Err_0)
            //= https://www.rfc-editor.org/rfc/rfc8446#section-6
            //# Peers which receive a message which
            //# cannot be parsed according to the syntax (e.g., have a length
            //# extending beyond the message boundary or contain an out-of-range
            //# length) MUST terminate the connection with a "decode_error" alert.
            // 3: each recognized body by its grammar; step 2 left one of each type at most.
            } else if sn matches Some(d) && rfc_server_name(d) is None {
                Err(ALERT_DECODE_ERROR)
            } else if sg matches Some(d) && rfc_groups(d) is None {
                Err(ALERT_DECODE_ERROR)
            } else if sa matches Some(d) && rfc_sig_schemes(d) is None {
                Err(ALERT_DECODE_ERROR)
            } else if al matches Some(d) && rfc_alpn(d) is None {
                Err(ALERT_DECODE_ERROR)
            } else if pk matches Some(d) && !rfc_offered_psks_ok(d) {
                Err(ALERT_DECODE_ERROR)
            } else if ed matches Some(d) && !rfc_early_data_ok(d) {
                Err(ALERT_DECODE_ERROR)
            } else if sv matches Some(d) && rfc_versions(d) is None {
                Err(ALERT_DECODE_ERROR)
            } else if ck matches Some(d) && !rfc_cookie_ok(d) {
                Err(ALERT_DECODE_ERROR)
            } else if pm matches Some(d) && rfc_psk_modes(d) is None {
                Err(ALERT_DECODE_ERROR)
            } else if sc matches Some(d) && rfc_sig_schemes(d) is None {
                Err(ALERT_DECODE_ERROR)
            } else if ks matches Some(d) && rfc_key_shares(d) is None {
                Err(ALERT_DECODE_ERROR)
            } else if f.legacy_version <= SSL30 {
                // 4
                //= https://www.rfc-editor.org/rfc/rfc8446#appendix-D.5
                //# Any endpoint
                //# receiving a Hello message with ClientHello.legacy_version or
                //# ServerHello.legacy_version set to 0x0300 MUST abort the handshake
                //# with a "protocol_version" alert.
                Err(ALERT_PROTOCOL_VERSION)
            } else if sv is None || !rfc_versions(sv.unwrap()).unwrap().contains(TLS13) {
                // 5
                //= https://www.rfc-editor.org/rfc/rfc8446#section-4.2.1
                //# If this extension is present in the ClientHello, servers MUST NOT use
                //# the ClientHello.legacy_version value for version negotiation and MUST
                //# use only the "supported_versions" extension to determine client
                //# preferences.
                //= https://www.rfc-editor.org/rfc/rfc8446#section-4.2.1
                //# Servers MUST only select a version of TLS present in
                //# that extension and MUST ignore any unknown versions that are present
                //# in that extension.
                //= https://www.rfc-editor.org/rfc/rfc8446#section-4.2.1
                //# Servers MUST be prepared to
                //# receive ClientHellos that include this extension but do not include
                //# 0x0304 in the list of versions.
                //= https://www.rfc-editor.org/rfc/rfc8446#appendix-D.2
                //# If the "supported_versions" extension is absent and the
                //# server only supports versions greater than
                //# ClientHello.legacy_version, the server MUST abort the handshake with
                //# a "protocol_version" alert.
                Err(ALERT_PROTOCOL_VERSION)
            } else if f.compression != seq![0u8] {
                // 6
                //= https://www.rfc-editor.org/rfc/rfc8446#section-4.1.2
                //# For every TLS 1.3 ClientHello, this vector
                //# MUST contain exactly one byte, set to zero, which corresponds to
                //# the "null" compression method in prior versions of TLS.
                //= https://www.rfc-editor.org/rfc/rfc8446#section-4.1.2
                //# If a
                //# TLS 1.3 ClientHello is received with any other value in this
                //# field, the server MUST abort the handshake with an
                //# "illegal_parameter" alert.
                Err(ALERT_ILLEGAL_PARAMETER)
            } else if f.legacy_session_id.len() != 0 {
                // 7
                //= https://www.rfc-editor.org/rfc/rfc9001#section-8.4
                //# A server SHOULD treat the receipt of a
                //# TLS ClientHello with a non-empty legacy_session_id field as a
                //# connection error of type PROTOCOL_VIOLATION.
                Err(PROTOCOL_VIOLATION)
            } else if ck is Some {
                // 8
                //= https://www.rfc-editor.org/rfc/rfc8446#section-9.2
                //# In the absence of an application profile standard specifying
                //# otherwise, a TLS-compliant application MUST implement the following
                //# TLS extensions:
                // cookie: parsed at step 3 by its grammar; any cookie here is one we never
                // issued (Decision 5: no cookie in the HelloRetryRequest), so it is rejected.
                Err(ALERT_ILLEGAL_PARAMETER)
            } else if sa is None || (pk is None && sg is None) || ((sg is Some) != (ks is Some))
                || (pk is Some && pm is None) || tp is None {
                // 9
                //= https://www.rfc-editor.org/rfc/rfc8446#section-4.2.3
                //# If a server is authenticating via
                //# a certificate and the client has not sent a "signature_algorithms"
                //# extension, then the server MUST abort the handshake with a
                //# "missing_extension" alert (see Section 9.2).
                //= https://www.rfc-editor.org/rfc/rfc8446#section-9.2
                //# -  If not containing a "pre_shared_key" extension, it MUST contain
                //# both a "signature_algorithms" extension and a "supported_groups"
                //# extension.
                //= https://www.rfc-editor.org/rfc/rfc8446#section-9.2
                //# -  If containing a "supported_groups" extension, it MUST also contain
                //# a "key_share" extension, and vice versa.
                //= https://www.rfc-editor.org/rfc/rfc8446#section-9.2
                //# Servers receiving a ClientHello which does not conform to these
                //# requirements MUST abort the handshake with a "missing_extension"
                //# alert.
                //= https://www.rfc-editor.org/rfc/rfc8446#section-4.2.9
                //# If clients offer
                //# "pre_shared_key" without a "psk_key_exchange_modes" extension,
                //# servers MUST abort the handshake.
                //= https://www.rfc-editor.org/rfc/rfc9001#section-8.2
                //# endpoints that
                //# receive ClientHello or EncryptedExtensions messages without the
                //# quic_transport_parameters extension MUST close the connection with an
                //# error of type 0x016d (equivalent to a fatal TLS missing_extension
                //# alert, see Section 4.8).
                Err(ALERT_MISSING_EXTENSION)
            } else {
                // 10
                //= https://www.rfc-editor.org/rfc/rfc8446#section-4.1.2
                //# If the list contains cipher suites that the server
                //# does not recognize, support, or wish to use, the server MUST
                //# ignore those cipher suites and process the remaining ones as
                //# usual.
                //= https://www.rfc-editor.org/rfc/rfc8446#section-4.1.2
                //# Servers MUST ignore unrecognized extensions.
                //= https://www.rfc-editor.org/rfc/rfc8446#section-9.3
                //# A server receiving a ClientHello MUST correctly ignore all
                //# unrecognized cipher suites, extensions, and other parameters.
                //= https://www.rfc-editor.org/rfc/rfc8446#section-4.2.10
                //# A server which receives an "early_data" extension MUST behave in one
                //# of three ways:
                //= https://www.rfc-editor.org/rfc/rfc8446#section-4.4.2.1
                //# TLS 1.3 servers MUST be
                //# able to process ClientHello messages that include it
                Ok(
                    SpecClientHello {
                        random: f.random,
                        legacy_session_id: f.legacy_session_id,
                        cipher_suites: f.cipher_suites,
                        versions: rfc_versions(sv.unwrap()).unwrap(),
                        groups: match sg {
                            Some(d) => rfc_groups(d),
                            None => None,
                        },
                        key_shares: match ks {
                            Some(d) => rfc_key_shares(d),
                            None => None,
                        },
                        sig_algs: rfc_sig_schemes(sa.unwrap()).unwrap(),
                        sig_algs_cert: match sc {
                            Some(d) => rfc_sig_schemes(d),
                            None => None,
                        },
                        alpn: match al {
                            Some(d) => rfc_alpn(d),
                            None => None,
                        },
                        server_name: match sn {
                            Some(d) => rfc_server_name(d).unwrap(),
                            None => None,
                        },
                        transport_params: tp.unwrap(),
                    },
                )
            }
        },
    }
}

/// Facts about an accepted ClientHello that the serializers' preconditions and negotiation
/// rely on.
pub proof fn lemma_client_hello_ok(body: Seq<u8>)
    requires
        rfc_client_hello(body) is Ok,
    ensures
        ({
            let s = rfc_client_hello(body)->Ok_0;
            &&& s.legacy_session_id.len() == 0
            &&& s.versions.contains(TLS13)
            &&& s.random.len() == 32
            &&& s.key_shares matches Some(ks) ==> forall|i: int|
                0 <= i < ks.len() ==> 1 <= #[trigger] ks[i].key_exchange.len() <= 0xffff
        }),
{
    let f = rfc_ch_fields(body).unwrap();
    let ks = spec_find(rfc_ch_exts(f), EXT_KEY_SHARE);
    if let Some(d) = ks {
        if let Some(c) = rfc_vec_exact(d, 0, 0xffff) {
            lemma_key_share_list_lens(c);
        }
    }
}

// =============================================================================
// Exec
// =============================================================================

struct ChFields {
    legacy_version: u16,
    random: [u8; 32],
    legacy_session_id: Vec<u8>,
    cipher_suites: Vec<u16>,
    compression: Vec<u8>,
    exts: Option<Vec<Ext>>,
}

impl View for ChFields {
    type V = SpecChFields;

    closed spec fn view(&self) -> SpecChFields {
        SpecChFields {
            legacy_version: self.legacy_version,
            random: self.random@,
            legacy_session_id: self.legacy_session_id@,
            cipher_suites: self.cipher_suites@,
            compression: self.compression@,
            exts: self.exts.deep_view(),
        }
    }
}

fn parse_ch_fields(b: &[u8]) -> (r: Option<ChFields>)
    ensures
        match r {
            Some(f) => rfc_ch_fields(b@) == Some(f@),
            None => rfc_ch_fields(b@) is None,
        },
{
    if b.len() < 34 {
        return None;
    }
    let legacy_version = b[0] as u16 * 256 + b[1] as u16;
    let mut random = [0u8; 32];
    let mut i: usize = 0;
    while i < 32
        invariant
            i <= 32,
            b@.len() >= 34,
            forall|j: int| 0 <= j < i ==> random@[j] == b@[2 + j],
        decreases 32 - i,
    {
        random[i] = b[2 + i];
        i += 1;
    }
    assert(random@ =~= b@.subrange(2, 34));
    let (s1, e1) = match read_vec(b, 34, 0, 32) {
        Some(se) => se,
        None => return None,
    };
    let (s2, e2) = match read_vec(b, e1, 2, 0xfffe) {
        Some(se) => se,
        None => return None,
    };
    let cipher_suites = match parse_u16_list(slice_subrange(b, s2, e2)) {
        Some(v) => v,
        None => return None,
    };
    assert(cipher_suites.deep_view() =~= cipher_suites@);
    let (s3, e3) = match read_vec(b, e2, 1, 255) {
        Some(se) => se,
        None => return None,
    };
    let exts = if e3 == b.len() {
        None
    } else {
        let rest = slice_subrange(b, e3, b.len());
        assert(rest@ =~= b@.skip(e3 as int));
        match read_exact(rest, 0, 0xffff) {
            None => return None,
            Some((s, e)) => match parse_ext_list(slice_subrange(rest, s, e)) {
                None => return None,
                Some(l) => Some(l),
            },
        }
    };
    let f = ChFields {
        legacy_version,
        random,
        legacy_session_id: slice_to_vec(slice_subrange(b, s1, e1)),
        cipher_suites,
        compression: slice_to_vec(slice_subrange(b, s3, e3)),
        exts,
    };
    assert(b@.skip(e3 as int).len() == 0 <==> e3 == b.len());
    Some(f)
}

/// The data of the first extension of type `ty`.
fn ext_data(x: &Vec<Ext>, ty: u16) -> (r: Option<&[u8]>)
    ensures
        match r {
            Some(d) => spec_find(x.deep_view(), ty) == Some(d@),
            None => spec_find(x.deep_view(), ty) is None,
        },
{
    match find_ext(x, ty) {
        None => None,
        Some(i) => Some(x[i].data.as_slice()),
    }
}

fn has_u16(v: &Vec<u16>, t: u16) -> (r: bool)
    ensures
        r == v@.contains(t),
{
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v@.len(),
            forall|k: int| 0 <= k < i ==> v@[k] != t,
        decreases v@.len() - i,
    {
        if v[i] == t {
            return true;
        }
        i += 1;
    }
    false
}

/// `body` is the ClientHello after its 4-byte handshake header.
pub fn parse_client_hello(body: &[u8]) -> (r: Result<ClientHello, u64>)
    ensures
        rfc_client_hello(body@) matches Ok(s) ==> r matches Ok(c) && c@ == s,
        rfc_client_hello(body@) matches Err(e) ==> r == Err::<ClientHello, u64>(e),
{
    // 1
    let f = match parse_ch_fields(body) {
        Some(f) => f,
        None => return Err(ALERT_DECODE_ERROR),
    };
    let ghost fv = f@;
    let x = match f.exts {
        Some(l) => l,
        None => Vec::new(),
    };
    assert(x.deep_view() =~= rfc_ch_exts(fv));
    // 2
    if let Err(e) = check_ch_exts(&x) {
        return Err(e);
    }
    // 3
    let server_name = match ext_data(&x, EXT_SERVER_NAME) {
        None => None,
        Some(d) => match parse_server_name(d) {
            None => return Err(ALERT_DECODE_ERROR),
            Some(n) => n,
        },
    };
    let groups = match ext_data(&x, EXT_SUPPORTED_GROUPS) {
        None => None,
        Some(d) => match parse_groups(d) {
            None => return Err(ALERT_DECODE_ERROR),
            Some(g) => Some(g),
        },
    };
    let sig_algs = match ext_data(&x, EXT_SIGNATURE_ALGORITHMS) {
        None => None,
        Some(d) => match parse_sig_schemes(d) {
            None => return Err(ALERT_DECODE_ERROR),
            Some(s) => Some(s),
        },
    };
    let alpn = match ext_data(&x, EXT_ALPN) {
        None => None,
        Some(d) => match parse_alpn(d) {
            None => return Err(ALERT_DECODE_ERROR),
            Some(a) => Some(a),
        },
    };
    let psk = match ext_data(&x, EXT_PRE_SHARED_KEY) {
        None => false,
        Some(d) => if offered_psks_ok(d) {
            true
        } else {
            return Err(ALERT_DECODE_ERROR);
        },
    };
    if let Some(d) = ext_data(&x, EXT_EARLY_DATA) {
        if !early_data_ok(d) {
            return Err(ALERT_DECODE_ERROR);
        }
    }
    let versions = match ext_data(&x, EXT_SUPPORTED_VERSIONS) {
        None => None,
        Some(d) => match parse_versions(d) {
            None => return Err(ALERT_DECODE_ERROR),
            Some(v) => Some(v),
        },
    };
    let cookie = match ext_data(&x, EXT_COOKIE) {
        None => false,
        Some(d) => if cookie_ok(d) {
            true
        } else {
            return Err(ALERT_DECODE_ERROR);
        },
    };
    let psk_modes = match ext_data(&x, EXT_PSK_KEY_EXCHANGE_MODES) {
        None => false,
        Some(d) => if parse_psk_modes(d).is_some() {
            true
        } else {
            return Err(ALERT_DECODE_ERROR);
        },
    };
    let sig_algs_cert = match ext_data(&x, EXT_SIGNATURE_ALGORITHMS_CERT) {
        None => None,
        Some(d) => match parse_sig_schemes(d) {
            None => return Err(ALERT_DECODE_ERROR),
            Some(s) => Some(s),
        },
    };
    let key_shares = match ext_data(&x, EXT_KEY_SHARE) {
        None => None,
        Some(d) => match parse_key_shares(d) {
            None => return Err(ALERT_DECODE_ERROR),
            Some(k) => Some(k),
        },
    };
    let transport_params = match ext_data(&x, EXT_QUIC_TRANSPORT_PARAMETERS) {
        None => None,
        Some(d) => Some(slice_to_vec(d)),
    };
    // 4
    if f.legacy_version <= SSL30 {
        return Err(ALERT_PROTOCOL_VERSION);
    }
    // 5
    let versions = match versions {
        Some(v) => if has_u16(&v, TLS13) {
            v
        } else {
            assert(v.deep_view() =~= v@);
            return Err(ALERT_PROTOCOL_VERSION);
        },
        None => return Err(ALERT_PROTOCOL_VERSION),
    };
    assert(versions.deep_view() =~= versions@);
    // 6
    if f.compression.len() != 1 || f.compression[0] != 0 {
        assert(f.compression@ != seq![0u8]) by {
            if f.compression@.len() == 1 {
                assert(f.compression@[0] != seq![0u8][0]);
            }
        }
        return Err(ALERT_ILLEGAL_PARAMETER);
    }
    assert(f.compression@ =~= seq![0u8]);
    // 7
    if f.legacy_session_id.len() != 0 {
        return Err(PROTOCOL_VIOLATION);
    }
    // 8
    if cookie {
        return Err(ALERT_ILLEGAL_PARAMETER);
    }
    // 9
    let (sig_algs, transport_params) = match (sig_algs, transport_params) {
        (Some(s), Some(t)) => if (!psk && groups.is_none()) || (groups.is_some()
            != key_shares.is_some()) || (psk && !psk_modes) {
            return Err(ALERT_MISSING_EXTENSION);
        } else {
            (s, t)
        },
        _ => return Err(ALERT_MISSING_EXTENSION),
    };
    assert(sig_algs.deep_view() =~= sig_algs@);
    // 10
    Ok(
        ClientHello {
            random: f.random,
            legacy_session_id: f.legacy_session_id,
            cipher_suites: f.cipher_suites,
            versions,
            groups,
            key_shares,
            sig_algs,
            sig_algs_cert,
            alpn,
            server_name,
            transport_params,
        },
    )
}

} // verus!
