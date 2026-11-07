# Phase 9 inventory: acceptance clauses and proved closes

Read-only survey of `main` at `ecd54a2`. It covers every verified error path in `wire`, `quic`, `quictls`, `h3` and `tls`, measured against two goals:

1. **Acceptance.** Each handler gets `Err(code) ==> allowed_err(state, input, code)`, where `allowed_err` is one RFC-cited spec fn per handler. For codecs the goal is `spec_parse(b) is Some ==> res is Ok`.
2. **Proved closes.**
   - (a) The error path leaves the connection Closing with that exact code.
   - (b) In Closing, any emitted datagram carries CONNECTION_CLOSE with that code at the right key level (RFC 9000 §10.2.3).

Terms used in the tables:

- **reject ensures**: the ensures says which inputs give `Err(c)` (input condition ==> Err, or an iff).
- **acceptance ensures**: the ensures says `Err(c) ==>` a stated condition. Under the user's rule, a condition with no RFC basis (or no named own-limit predicate) counts as over-strict.
- **exact ≡ `rfc_x`**: the exec result is proved *equal* to a hand-written spec fn. Both directions then hold, but only relative to that spec. The remaining acceptance work is a pure spec lemma, `rfc_x(..) == Err(c) ==> allowed_x(.., c)`. It adds nothing to the exec fn's VC, so it carries no rlimit risk.

---

## 1. vest_lib (pinned `=0.2.2`)

`Cargo.lock:796-799` pins `vest_lib 0.2.2`, checksum `3cb28df4…`. The source is `~/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/vest_lib-0.2.2/`.

**Vest's `Parser` trait proves soundness and completeness (an iff), relative to the combinator's `spec_parse`.** From `src/core/exec/parser.rs:17-24` and `:44-49`:

```rust
pub open spec fn parse_matches_spec<O: DeepView>(
    r: PResult<O>,
    spec_parse: Option<(int, O::V)>,
) -> bool {
    &&& r is Ok <==> spec_parse is Some
    &&& r is Err <==> spec_parse is None
    &&& r matches Ok((n, v)) ==> spec_parse == Some((n as int, v.deep_view()))
}

    fn parse(&self, ibuf: &Input) -> (r: PResult<Self::PT>)
        requires
            self.exec_inv(),
        ensures
            parse_matches_spec(r, self.spec_parse(ibuf@)),
    ;
```

`FnParser` (`src/core/exec/fns.rs:309-326`) moves the same iff into `exec_inv` through `call_ensures`. Every combinator that implements `Parser` must meet this trait ensures, so completeness (`spec_parse is Some ==> Ok`) is built in.

**What inherits it in this project: one leaf only, the QUIC varint.**

| Parser | Built on | Inherits Vest iff? |
|---|---|---|
| `wire::varint::QuicVarInt<MINIMAL>` (`wire/src/varint.rs:206-211`, `:981-1025`) | The spec is a Vest combinator, `quic_varint_fmt` (`:140`, `Mapped{Bind(U8,…)}`). The exec `parse` is hand-written, but it implements `Parser`, so it is proved against the trait's `parse_matches_spec`. | **Yes.** `theorem_matches_rfc` (`:793-800`) also ties `spec_parse` to `rfc_varint_decode`. |
| `wire::varint::parse_varint` (`:1206-1221`) | Calls `QuicVarInt::<false>.parse` | Yes. Ensures `None ==> rfc_varint_decode(b@) is None`. |
| `quic::ack::varint_at` (`ack.rs:524`) and every `quic`/`h3` field read built on it | `parse_varint` | Yes, for the varint leaf only |
| `quic::frame::{parse_frame_type, parse_frame_body, parse_frame}`, `ack::parse_ack`, `payload::parse_payload`, `header::{parse_long_header, parse_header}`, `tp::parse_transport_params`, `protect::Rx::open_one` | Hand-written exec, proved **exact ≡** hand-written `rfc_*` spec fns | No. `use vest_lib::core::spec::*` is imported in `quic/src/{frame,ack,header}.rs` and `h3/src/frame.rs`, but none of them calls `spec_parse` or implements `SpecParser`. |
| `h3::frame::{parse_frame_payload, parse_settings}`, `h3::qpack::*`, `h3::message::validate_request` | Hand-written, exact ≡ `rfc_*` | No |
| `tls::client_hello::parse_client_hello`, `ext::check_ch_exts`, `server_msgs::parse_finished`, `handshake::HsReader::next_message` | Hand-written, exact ≡ `rfc_*` (tls imports nothing from vest, see 4c plan :18) | No |

**Consequence.** The codec goal `spec Some ==> Ok` is already met everywhere, because every codec ensures is a `match r { Ok(..) => rfc_x(b) == Ok(..), Err(e) => rfc_x(b) == Err(e) }` equivalence. What is left is **spec fidelity**: whether each `rfc_*` spec rejects only what the RFC allows. That is a spec-only audit plus `allowed_*` lemmas. No exec codec ensures needs to change.

---

## 2. Error sites

How to read the table:

- One row per (fn, distinct code). Line numbers are the `Err`/close statements.
- RFC clauses come from the nearby duvet `//=` blocks. For exact ≡ fns, the clause sits on the `rfc_*` spec, whose location is given.
- Class values:
  - **MUST**: the RFC requires this code.
  - **MAY-chosen**: the RFC permits the error (MAY or SHOULD) and we chose to raise it.
  - **own-limit**: our own limit.
  - **chosen (no code)**: the RFC requires an abort or error but names no code, or names nothing at all. These need a named predicate, or they fail the new rule.
- Propagating sites that only forward a code into a close are listed in §3, not here.
- **The MUST / MAY-chosen labels are provisional** where they come from a nearby duvet heading rather than a quoted MUST sentence. Examples: tls `step` :1290, the tp duplicate SHOULD, qpack `TooLarge`, 9114 §7.2.4.1. P3 (§4.3) re-derives each `allowed_x` from the RFC text.
- The h3 and tls tables omit the rlimit column: no fn in either crate is on the tight list, and the per-crate note says so.

### wire (3 sites, 2 rows; parse rejections with no code)

| crate::fn (file:line) | code | RFC clause | class | reject ensures | acceptance ensures | rlimit |
|---|---|---|---|---|---|---|
| `wire::QuicVarInt::parse` (varint.rs:994, :999) | `unexpected_eof` (ParseError) | 9000 §16 | MUST (grammar) | trait iff `parse_matches_spec` | **yes** (Vest iff) | low |
| `wire::QuicVarInt::<true>::parse` (varint.rs:1022) | `non_canonical` | 9000 §12.4 (minimal frame type) | MAY-chosen (used only after the lenient parse, frame.rs:1411-1418) | trait iff | **yes** | low |

### quic (36 rows)

Codecs, all exact ≡ `rfc_*`, so acceptance needs a spec lemma only:

| crate::fn (file:line) | code | RFC clause | class | reject | acceptance | rlimit |
|---|---|---|---|---|---|---|
| `frame::parse_frame_type` (frame.rs:1413) | FRAME_ENCODING_ERROR (truncated) | 9000 §12.4, §20.1 (`rfc_frame_type` frame.rs:128-148) | MUST | exact ≡ `rfc_frame_type` | spec-relative | low |
| `frame::parse_frame_type` (frame.rs:1417) | PROTOCOL_VIOLATION (non-minimal type) | 9000 §12.4 "An endpoint MAY treat…" (frame.rs:133) | MAY-chosen | exact | spec-relative | low |
| `frame::parse_frame_body` (frame.rs:1432) | PROTOCOL_VIOLATION (NEW_TOKEN, HANDSHAKE_DONE from client) | 9000 §19.7, §19.20 (frame.rs:440-450) | MUST | exact ≡ `rfc_frame_body` | spec-relative | low |
| `frame::parse_frame_body` (frame.rs:1442, including `parse_one_varint` :1268 >2^60, `parse_new_connection_id` rpt>seq) | FRAME_ENCODING_ERROR | 9000 §19.11, §19.15, §20.1 | MUST | exact | spec-relative | low |
| `ack::parse_ack` (ack.rs:562-670, 11 sites) | FRAME_ENCODING_ERROR | 9000 §19.3, §19.3.1, §20.1 (ack.rs:173-187) | MUST | exact ≡ `rfc_ack` | spec-relative | low |
| `payload::parse_payload` (payload.rs:496) | PROTOCOL_VIOLATION (no frames) | 9000 §12.4 (payload.rs:128) | MUST | exact ≡ `rfc_payload` | spec-relative | low |
| `payload::parse_payload` (payload.rs:527) | FRAME_ENCODING_ERROR (unknown type) | 9000 §12.4 | MUST | exact | spec-relative | low |
| `payload::parse_payload` (payload.rs:530) | PROTOCOL_VIOLATION (frame not permitted in packet type) | 9000 §12.4, §17.2.2, §17.2.4 (payload.rs:60-74) | MUST | exact | spec-relative | low |
| `protect::Rx::open_one` (protect.rs:1350) | PROTOCOL_VIOLATION (reserved bits) | 9000 §17.2, §17.3.1 (protect.rs:1338-1348) | MUST | exact ≡ `rfc_open` | spec-relative | low |
| `header::parse_long_header` / `parse_header` (header.rs:636, :718) | `None` (packet dropped, no code) | 9000 §17 | MUST (grammar) | exact ≡ `rfc_long_header`/`rfc_header` | spec-relative | low |
| `tp::parse_transport_params` (tp.rs:1036, :1041, :1045, :1054; values `tp_value` :924-926) | TRANSPORT_PARAMETER_ERROR | 9000 §18, §18.2 (max_ack_delay ≥2^14), §4.6 (>2^60), §7.4 (duplicate: SHOULD) (`rfc_tp_from` tp.rs:308-344) | MUST, plus SHOULD for duplicates | exact ≡ `rfc_transport_params` | spec-relative | low |

Connection state:

| crate::fn (file:line) | code | RFC clause | class | reject | acceptance | rlimit |
|---|---|---|---|---|---|---|
| `crypto_stream::CryptoStream::on_crypto` (crypto_stream.rs:93) | CRYPTO_BUFFER_EXCEEDED | 9000 §7.5 (:79-92); floor 4096 (:12) | MUST when not expanding; window `MAX_CRYPTO_BUFFER`=16384 is own-limit ≥ floor | **iff** `r is Err <==> offset+len > base+MAX_CRYPTO_BUFFER` (:62) | **yes** (iff), but the window-end semantics are loose, see §4 | low |
| `sent::SentPackets::on_ack` (sent.rs:347) | PROTOCOL_VIOLATION (ack of an unsent pn) | 9000 §13.1 SHOULD (sent.rs:302) | MAY-chosen | iff `(r is Err) == (a.largest >= next_pn)` (:327) | **yes** (iff) | low |
| `cid::LocalCids::on_retire` (cid.rs:592) | PROTOCOL_VIOLATION (seq > max sent) | 9000 §19.16 MUST (cid.rs:547) | MUST | iff (:573-575) | **yes** | low |
| `cid::LocalCids::on_retire` (cid.rs:609) | PROTOCOL_VIOLATION (retires the packet's own DCID) | 9000 §19.16 "MAY treat" (cid.rs:552) | MAY-chosen | iff | **yes** | low |
| `cid::PeerCids::on_new_cid` (cid.rs:1552) | PROTOCOL_VIOLATION (we use zero-length CIDs) | 9000 §19.15 MUST (cid.rs:1416) | MUST | iff (:1498) | **yes** | low |
| `cid::PeerCids::on_new_cid` (cid.rs:1577) | PROTOCOL_VIOLATION (`peer_clash`) | 9000 §19.15 "MAY treat" (cid.rs:1426) | MAY-chosen | iff | **yes** | low |
| `cid::PeerCids::on_new_cid` (cid.rs:1568, :1601) | CONNECTION_ID_LIMIT_ERROR | 9000 §5.1.1, §5.1.2 (cid.rs:1438-1455) | MUST | iff (:1500-1505) | **yes** | low |
| `stream_id::StreamIds::on_peer_stream` (stream_id.rs:259) | STREAM_LIMIT_ERROR | 9000 §4.6, §19.11 (:214-224) | MUST | iff (:233-234) | **yes** | low |
| `streams::Streams::check` (streams.rs:1081-1088) | STREAM_STATE_ERROR | 9000 §19.4, §19.5, §19.8, §19.10, §19.13 (streams.rs:149-181) | MUST, **except** RESET_STREAM / STREAM_DATA_BLOCKED on a server-bidi ID: streams.rs:143-146 says "the RFC names no code … and we use the same one" | exact ≡ `rfc_stream_frame_check` (:1072) | spec-relative. **First candidate the new rule flags.** | low |
| `streams::Streams::check` (streams.rs:1090, :1095) | STREAM_LIMIT_ERROR | 9000 §4.6, §19.11 | MUST | exact | spec-relative | low |
| `streams::Streams::on_frame` → `rx_outcome` (streams.rs:245-247, spec :238-255) | FLOW_CONTROL_ERROR (connection credit) | 9000 §4.1, §19.9 (:209-219) | MUST | exact `frame_post` (`r == match rfc_stream_frame_check … rx_outcome`, :1678 / :296) | spec-relative | low (spec lemma) |
| `recv_stream::RecvStream::on_data` (recv_stream.rs:1282) | FINAL_SIZE_ERROR | 9000 §4.5 SHOULD (×2, :1268-1281) | MAY-chosen | exact three-way vs `rfc_recv` + `conn_room` (:274-290) | spec-relative | **HIGH: 11.79M. Do not touch the exec ensures; spec lemma on `rfc_recv`/`recv_data` (recv_stream.rs:139) only.** |
| `recv_stream::RecvStream::on_data` (recv_stream.rs:1298) | FLOW_CONTROL_ERROR (stream limit) | 9000 §4.1, §19.10 (:1284-1292) | MUST | exact | spec-relative | **HIGH (same)** |
| `recv_stream::RecvStream::on_data` (recv_stream.rs:1326) | FLOW_CONTROL_ERROR (connection room) | 9000 §4.1, §19.9 | MUST | exact | spec-relative | **HIGH (same)** |
| `recv_stream::RecvStream::on_reset` (recv_stream.rs:1449) | FINAL_SIZE_ERROR | 9000 §4.5 SHOULD | MAY-chosen | exact vs `rfc_recv` (:306-318) | spec-relative | med (97-line body next to on_data; spec lemma only) |
| `recv_stream::RecvStream::on_reset` (recv_stream.rs:1452, :1470) | FLOW_CONTROL_ERROR | 9000 §4.5, §3.2 (:1455) | MUST | exact | spec-relative | med |
| `handshake::HandshakeIds::check_peer_tp` (handshake.rs:373, :375) | TRANSPORT_PARAMETER_ERROR | 9000 §7.3 (:339-360) | MUST | iff `Ok <==> isci == client_scid` (:366) | **yes** | low |
| `handshake::check_alpn` (handshake.rs:464) | 0x178 no_application_protocol | 9001 §8.1; 9000 §7 (:442) | MUST | iff `Ok <==> alpn == "h3"` (:454) | **yes** | low |
| `conn::Connection::on_handshake_complete` (conn.rs:3205) | INTERNAL_ERROR (`peer_tp`/`streams` None, said to be unreachable) | none | own-limit (internal) | **none** (ensures: `wf` and `out_log` only) | **none**. Name it `internal_unreachable`, or prove it unreachable | low |
| `conn::Connection::on_tls_alert` (conn.rs:3232) | CRYPTO_ERROR_BASE + alert | 9001 §4.8 | MUST | **none** | **none** | low |
| `conn::Connection::poll_transmit` (conn.rs:6702-6705), `next_pn_len` (:5740), `build_space_packet` (:4314), `build_close` (:6014), `build_path_datagram` (:6595) | **silent close** (Closed, no code) | 9000 §12.3 (:6693) | MUST | `phase Open && next_pn == PN_MAX ==> r is None && Closed` (:6650-6653) | n/a (no code) | **poll_transmit 7.13M**. Unchanged by Phase 9 |
| `conn::Connection::fall_back` / `timeout_phase` (conn.rs:7818, :7829, :7884), `rewrite_active` (:2282) | silent close (no viable path, idle timeout, CID exhaustion) | 9000 §10.1, §9 | MUST / chosen | partial (`timed_out`) | n/a | `Paths::on_timeout` 11.04M sits under `fail_paths`. Unchanged |
| `h3_server::H3Server::pump` (h3_server.rs:1032) | H3_GENERAL_PROTOCOL_ERROR (app close; peer allows fewer than 3 uni streams) | 9114 §6.2 MUST (:1023), which names no code | chosen (no code) | **none** on the code | **none** | low |
| `h3_server::H3Server::send_response` (h3_server.rs:1088) | `SendError::Busy` (API) | none | own-limit (`pending` not drained) | iff `idle_spec == !Busy` (:1081) | **yes** (named) | low |
| `h3_server::H3Server::send_response` (h3_server.rs:1091, :1111) | `SendError::Rejected` (API: not started, or h3 refuses) | none | own-limit | `Err ==> emitted unchanged` only | **none**. Name `!started || !h3.req_respondable(id)` | low |

### quictls (5 rows)

| crate::fn (file:line) | code | RFC clause | class | reject | acceptance | rlimit |
|---|---|---|---|---|---|---|
| `server::QuicServer::superseded` (server.rs:603) | PROTOCOL_VIOLATION (Initial CRYPTO past `init_end` after the key change) | 9001 §4.1.3 (:563-579) | MUST | one direction: `!Initial && crypto_end(I) > init_end && Open ==> !cont && !Open` (:594-595), **no code** | **none**. The 753ec2d bug lived here (§4) | low |
| `server::QuicServer::superseded` (server.rs:610) | PROTOCOL_VIOLATION (newly contiguous Initial bytes) | 9001 §4.1.3 | MUST | **none** | **none** | low |
| `server::QuicServer::key_changes` (server.rs:777, :782) | PROTOCOL_VIOLATION (unread data at a key change) | 9001 §4.1.3 (the "unread" clause, :740-755) | MUST | **none** (ensures `wf`, `out_log`, `hs` only) | **none** | low |
| `server::QuicServer::on_params` (server.rs:817) | TRANSPORT_PARAMETER_ERROR (any `parse_transport_params` Err) | 9000 §7.4, §18 | MUST | **none** | **none**. The wire code is fixed, so allowed = `rfc_transport_params(b) is Err` | low |
| `server::report` (server.rs:146-151) | the TLS code; CRYPTO_ERROR_BASE+alert; else INTERNAL_ERROR | 9001 §4.8, 8446 §6.2 (:99-136) | MUST (pass-through) | **none**. The comment at :120-125 says the code is test-pinned (`tampered_finished_0x133`, `error_ranges`, `a2_closes_0x178`) | n/a (sink) | low |

### h3 (31 rows)

All exact ≡ an `rfc_*` spec unless noted, so acceptance is a spec lemma. rlimit is low throughout: no h3 fn is on the tight list.

| crate::fn (file:line) | code | RFC clause (spec location) | class | reject | acceptance |
|---|---|---|---|---|---|
| `frame::parse_frame_payload` (frame.rs:478-498) | H3_FRAME_ERROR | 9114 §7.1 (`rfc_frame_payload` frame.rs:142-188) | MUST | exact | spec-relative |
| `frame::parse_settings` (frame.rs:534, :539) | H3_FRAME_ERROR | 9114 §7.1 | MUST | exact | spec-relative |
| `frame::parse_settings` (frame.rs:570) | H3_SETTINGS_ERROR | 9114 §7.2.4.1 | MUST | exact | spec-relative |
| `message::validate_request` (message.rs:1454-1501, 6 sites) | H3_MESSAGE_ERROR | 9114 §4.3, §4.3.1, §4.4 (`rfc_validate_request` message.rs:747-803) | MUST | exact | spec-relative |
| `qpack::field_section::decode_field_section` (field_section.rs:669-696) | QPACK_DECOMPRESSION_FAILED | 9204 §4.5.1, §4.5.1.1, §2.1.2, §4.5.1.2 (:173-195) | MUST | exact | spec-relative |
| `qpack::field_section::decode_field_line_bounded` (field_section.rs:790-857, 10 sites) | QPACK_DECOMPRESSION_FAILED | as above | MUST | exact (`rfc_field_line is None`) | spec-relative |
| `qpack::field_section::decode_field_line_bounded` / `_section_bounded` (:782, :979) | `BoundedError::OverBudget` (maps to H3_EXCESSIVE_LOAD in request.rs:860) | 9114 §4.2.2 "MAY impose a limit" | own-limit | exact (`field_line_size > left`) | **yes** (named) |
| `qpack::instructions::process_encoder_stream` (instructions.rs:130, :139, :142) | QPACK_ENCODER_STREAM_ERROR | 9204 §4.3.1, §3.2.2, §2.2.3 (:69-85); `PrefixInt::TooLarge` vs 9204 §4.1.1 (62-bit floor) | MUST; TooLarge is own-limit if above 62 bits | exact ≡ `rfc_encoder_stream` | spec-relative |
| `qpack::instructions::process_decoder_stream` (instructions.rs:253, :262) | QPACK_DECODER_STREAM_ERROR | 9204 §4.4.1, §4.4.3 (:196-209) | MUST | exact | spec-relative |
| `request::req_header_error` (request.rs:827, :830) | H3_FRAME_UNEXPECTED (conn) | 9114 §4.1, §7.2.3-§7.2.8 (`rfc_req_header_error` request.rs:177-220) | MUST | exact | spec-relative |
| `request::req_header_error` (request.rs:832) | H3_EXCESSIVE_LOAD (stream) | 9114 §4.2.2 MAY (limit `MAX_FIELD_SECTION_SIZE`) | own-limit | exact | spec-relative |
| `request::headers_frame` (request.rs:860) | H3_EXCESSIVE_LOAD (stream, OverBudget) | 9114 §4.2.2 | own-limit | exact ≡ `rfc_headers` | spec-relative |
| `request::headers_frame` (request.rs:870, :878) | H3_MESSAGE_ERROR (stream) | 9114 §4.1.2 (:222-230) | MUST | exact | spec-relative |
| `request::headers_frame` (request.rs:881) | H3_FRAME_UNEXPECTED (HEADERS after trailers) | 9114 §4.1 | MUST | exact | spec-relative |
| `request::step_data` (request.rs:1049, :1054) | H3_MESSAGE_ERROR (content-length) | 9114 §4.1.2 | MUST | `stepped(..)` exact | spec-relative |
| `request::RequestStream::on_data` (request.rs:1561) | H3_FRAME_ERROR (FIN inside a frame) | 9114 §7.1 (`cut` request.rs:129-140) | MUST | exact ≡ `rfc_request_stream` (:272) | spec-relative |
| `request::RequestStream::on_data` (request.rs:1564) | H3_REQUEST_INCOMPLETE (stream) | 9114 §4.1 (:153) | MAY-chosen (SHOULD) | exact | spec-relative |
| `request::RequestStream::on_data` (request.rs:1570) | H3_MESSAGE_ERROR (content-length at FIN) | 9114 §4.1.2 (:158) | MUST | exact | spec-relative |
| `uni::control_header_error` (uni.rs:672) | H3_MISSING_SETTINGS | 9114 §6.2.1 (`rfc_control_header_error` uni.rs:113-167) | MUST | exact | spec-relative |
| `uni::control_header_error` (uni.rs:675) | H3_FRAME_UNEXPECTED | 9114 §7.2.1, §7.2.2, §7.2.4, §7.2.5, §7.2.8 | MUST | exact | spec-relative |
| `uni::control_header_error` (uni.rs:677) | H3_FRAME_ERROR (one-varint payload >8 bytes) | 9114 §7.1 | MUST | exact | spec-relative |
| `uni::control_header_error` (uni.rs:679) | H3_ID_ERROR (CANCEL_PUSH) | 9114 §7.2.3 | MUST | exact | spec-relative |
| `uni::control_header_error` (uni.rs:681) | H3_EXCESSIVE_LOAD (SETTINGS > `MAX_SETTINGS_FRAME`=1024) | none (limits.rs:9) | own-limit | exact | spec-relative |
| `uni::control_frame` (uni.rs:823) | H3_ID_ERROR (MAX_PUSH_ID decrease, GOAWAY increase) | 9114 §7.2.7, §5.2 (`rfc_control_frame` uni.rs:169-215) | MUST | exact ≡ `rfc_control` (:819) | spec-relative |
| `uni::UniStream::determine` (uni.rs:1265) | H3_STREAM_CREATION_ERROR (client push stream; second control/encoder/decoder) | 9114 §6.2.1, §6.2.2; 9204 §4.2 (`rfc_uni_stream` uni.rs:330-366) | MUST | exact (`kind_of_bytes`) | spec-relative |
| `uni::UniStream::consume_control` (uni.rs:1430) | H3_CLOSED_CRITICAL_STREAM | 9114 §6.2.1 (`fin_err` uni.rs:95-111) | MUST | `consumed(..)` exact | spec-relative |
| `uni::UniStream::consume_qpack` (uni.rs:1780) | H3_CLOSED_CRITICAL_STREAM | 9204 §4.2 | MUST | exact ≡ `rfc_uni_stream` (:334) | spec-relative |
| `conn::H3Conn::on_stream_data` (conn.rs:2916) | H3_STREAM_CREATION_ERROR (server-initiated ID) | 9114 §6.1 names the client side only. Unreachable through quic: `Streams::check` rejects first with STREAM_STATE_ERROR | chosen (no code) | exact (`added == [Close{0x103}]`, :2879) | **none**. Name it `server_initiated(id)` |
| `conn::H3Conn::on_stream_reset` (conn.rs:3423) | H3_CLOSED_CRITICAL_STREAM | 9114 §6.2.1; 9204 §4.2 (:3350-3356) | MUST | exact (:3386) | spec-relative |
| `conn::H3Conn::on_stop_sending` (conn.rs:3530) | H3_CLOSED_CRITICAL_STREAM (our control stream 3) | 9114 §6.2.1 (:3489) | MUST | exact (:3506) | spec-relative |
| `conn::reset_outs` / `answer` / `reject` (conn.rs:3456-3458, :1315, :1325, :1361, :1367) | H3_REQUEST_CANCELLED / INCOMPLETE / NO_ERROR / REQUEST_REJECTED (stream codes we send, not errors we detect) | 9114 §4.1, §4.1.1 (`rejected_outs` :388-396) | chosen | exact (`reset_outs`, `answered_outs`, `rejected_outs`) | n/a |

### tls (24 rows)

Codes are QUIC wire values: alert X is sent as `0x100+X`, and `PROTOCOL_VIOLATION`/`CRYPTO_BUFFER_EXCEEDED` are transport codes. All rows are exact ≡ an `rfc_*`/`spec_*` spec unless noted. rlimit is low: tls is not on the tight list, though `spec_drain` is noted as sensitive in the 4c plan.

| crate::fn (file:line) | code | RFC clause (spec location) | class | reject | acceptance |
|---|---|---|---|---|---|
| `client_hello::parse_client_hello` (client_hello.rs:592-679, 12 sites) | 0x132 decode_error | 8446 §6 (`rfc_client_hello` :237-265) | MUST | `spec Err(e) ==> r == Err(e)`; `spec Ok ==> Ok` (:586-587) | spec-relative |
| … (client_hello.rs:689, :697, :699) | 0x146 protocol_version | 8446 App D.5, §4.2.1, App D.2 (:294-322) | MUST | same | spec-relative |
| … (client_hello.rs:709) | 0x12f illegal_parameter (compression) | 8446 §4.1.2 (:323-334) | MUST | same | spec-relative |
| … (client_hello.rs:714) | PROTOCOL_VIOLATION (legacy_session_id) | 9001 §8.4 SHOULD (:335-341) | MAY-chosen | same | spec-relative |
| … (client_hello.rs:718) | 0x12f illegal_parameter (cookie we never issued) | none; "Decision 5" (:342-348) | chosen (no clause) | same | spec-relative. **Needs a named predicate** |
| … (client_hello.rs:724, :728) | 0x16d missing_extension | 8446 §4.2.3, §9.2; 9001 §8.2; §4.2.9 (psk w/o modes: "MUST abort", no alert named) (:352-380) | MUST (the §4.2.9 alert is chosen) | same | spec-relative |
| `ext::check_ch_exts` (ext.rs:291, :295) | 0x12f illegal_parameter (duplicate ext; psk not last) | 8446 §4.2, §4.2.11 (:76-104) | MUST | exact ≡ `rfc_ch_ext_check` | spec-relative |
| `handshake::HsReader::next_message` (handshake.rs:173) | 0x10a unexpected_message | 8446 §4 (:168) | MUST | exact ≡ `rfc_next_message` | spec-relative |
| `handshake::HsReader::next_message` (handshake.rs:181) | CRYPTO_BUFFER_EXCEEDED (body > `MAX_HS_BODY`=2^16) | none for the size | own-limit | exact | spec-relative |
| `negotiate::negotiate` (negotiate.rs:533, :548, :575) | 0x128 handshake_failure | 8446 §4.1.1, §9.1 (`rfc_negotiate` :226-322) | MUST | exact ≡ `rfc_negotiate` | spec-relative |
| `negotiate::negotiate` (negotiate.rs:540) | 0x178 no_application_protocol | 9001 §8.1 | MUST | exact | spec-relative |
| `negotiate::negotiate` (negotiate.rs:572) | 0x12f illegal_parameter (key_share group checks) | 8446 §4.2.8 (:278-290) | MAY-chosen ("servers MAY check") | exact | spec-relative |
| `server_msgs::parse_finished` (server_msgs.rs:569) | 0x132 decode_error | 8446 §6 | MUST | exact ≡ `rfc_finished` | spec-relative |
| `flight::build_flight` (flight.rs:457, :505) | 0x150 internal_error | none | own-limit (internal; :457 `assert(false)`) | `Err ==> e == INTERNAL` (:422) | **none** |
| `flight::build_flight` (flight.rs:515, :523) | 0x12f illegal_parameter (bad point, zero shared secret) | 8446 §7.4.2, §4.2.8.2 (:509-526) | MUST abort, alert chosen | exact ≡ `spec_flight` | spec-relative |
| `sign::sign_cv` (sign.rs:113, :122) | 0x150 internal_error (RSA until Phase 7) | 8446 §4.4.3 (:92, :118) | own-limit | iff `Ok <==> spec_cv_signature is Some` | **yes** (named) |
| `server::step` (server.rs:1274) | 0x133 decrypt_error (Finished MAC) | 8446 §4.4.4 | MUST | `match spec_step` (:1248-1253) | spec-relative |
| `server::step` (server.rs:1290) | 0x12f illegal_parameter (CH2 ≠ CH1 beyond shares) | 8446 §4.1.2 | MUST | same | spec-relative |
| `server::step` (server.rs:1317) | 0x12f illegal_parameter (CH2 would need a second HRR) | 8446 §4.1.4 is client-side; the server choice is in the comment (:1309-1316) | chosen | same | spec-relative. **Named predicate needed** |
| `server::step` (server.rs:1393) | 0x10a unexpected_message | 8446 §4 | MUST | same | spec-relative |
| `server::step`, Ok-spec branch (server.rs:1252) | 0x150 internal_error **where the spec says Ok** (build_flight Err, i.e. RSA) | none | own-limit | `Ok(..) ==> (r Ok…) \|\| (r == Err(INTERNAL) && WaitFinished)` | **none**. This is an over-strict escape: name it `signing_unavailable(cfg, chain)` |
| `server::on_crypto` (server.rs:1452-1453) | 0x10a unexpected_message (bytes at an unexpected level; KeyUpdate) | 8446 §4.1.2; 9001 §6 (`spec_on_crypto` :324-367) | MUST | exact (:115-119) | spec-relative |
| `server::on_crypto`, Ok-spec branch (server.rs:1433-1434, :1534) | 0x150 internal_error where the spec says Ok | none | own-limit | as `step` | **none**. Same escape as above |
| `server::on_crypto` (server.rs:1447) | `self.err` (latched Failed) | n/a | repeat of the first error | exact | n/a |

**Row totals** (basis: distinct fn × code rows above): wire 2 (3 sites), quic 36, quictls 5, h3 31, tls 24. That is **98 rows** over about 190 literal sites.

---

## 3. Close paths

### 3.1 The primitives (quic/src/lifecycle.rs)

| fn | proves |
|---|---|
| `Lifecycle::enter_closing(now, pto, app, code, reason)` (:412-454) | `old Open ==> phase == Closing && close_spec() matches Some((a,c,r)) && a == app && c == code && r == reason@.take(min(len,64))` and `owed && !first_sent`; `!old Open ==>` everything unchanged (first error wins). **The exact-code fact exists here.** |
| `enter_draining` (:457-481) | Open or Closing goes to Draining; `close_spec` unchanged |
| `close_silently` (:483-492) | goes to Closed; nothing about `close_spec` |
| `close_frame(app, code, reason, space)` (:199-228) | `ConnectionClose{frame_type:0}`; if `app && space != OneRtt`: `!a && c == APPLICATION_ERROR && reason empty` (9000 §10.2.3), else `a == app && c == code && r == reason` |
| `close_spaces(confirmed, i, h, o)` (:253-281) | `confirmed ==> [OneRtt]`, else `spec_close_spaces(i,h,o)` (9000 §10.2.3) |

### 3.2 Every entry into Closing (or out of Open)

**Gap common to every row:** `Connection` exposes no close code. No `pub closed spec fn` on `Connection` returns `self.lc.close_spec()`. `Connection::close_info()` (conn.rs:8125-8130) has `requires wf` and **no ensures**. `Connection::close` (conn.rs:3025-3053) proves only `old Open ==> Closing`, `!Open ==> phase unchanged`, `paths_kept`, `events_spec` unchanged and `keeps_later`. So in the table, "code proved" means proved at the `Lifecycle` level and lost at the `Connection` boundary.

| # | Site | Trigger and code | Proved today about state and code after |
|---|---|---|---|
| C1 | `Connection::on_counted` (conn.rs:762-769), `on_packet` Err → `close_internal(c)` | any frame error, `c` from `on_frame` | `on_frame` / `on_packet` / `on_frames` ensure only `Err(c) ==> c <= VARINT_MAX` (:1141, :1203, :1258). `on_datagram`'s close clause covers only `packets.len() == 0` (:620-624). **Nothing proves Closing or the code for a frame error inside a packet.** |
| C2 | `Connection::on_stream_frame` (conn.rs:1425-1432): `lc.enter_closing(now, pto, false, c, [])`, then returns `Err(c)`. C1's `close_internal` is then a no-op (first error wins) | Streams error | `r is Err ==> !Open && streams is None` (:1416). Code: no |
| C3 | `Connection::close_on_error` (conn.rs:800-829) → `close(code,false,[])` | unprotect / payload error from `protect` (PROTOCOL_VIOLATION, FRAME_ENCODING_ERROR) | `dcid == first && gate && has(path) ==> Closing` (:812-813). Code: no. 9000 §14 gate cited (:792) |
| C4 | `Connection::on_peer_params` (conn.rs:3174-3176) → `close_internal(c)` | `check_peer_tp` TRANSPORT_PARAMETER_ERROR | ensures `wf`, `out_log` only. Phase: no. Code: no |
| C5 | `Connection::on_handshake_complete` (conn.rs:3204-3211) | INTERNAL_ERROR; `check_alpn` 0x178 | `wf`, `out_log` only |
| C6 | `Connection::on_tls_alert` (conn.rs:3222-3233) | `CRYPTO_ERROR_BASE + alert` | `wf`, `out_log` only |
| C7 | `Connection::close` (pub, conn.rs:3025) | called by C3, `close_internal`, h3_server, quictls `shut` | phase only (above) |
| C8 | `quictls::shut` (server.rs:86-97) | wraps `close(code,false,[])` | `old Open ==> !(final Open)` (:93). **Not even Closing**, and no code |
| C9 | `quictls::report` (server.rs:139-153), called from `feed` (:664) on `hs.on_crypto` Err | TLS code: alert branch → `on_tls_alert` (round-trips to the same value); `<= VARINT_MAX` → `shut(code)`; else `shut(INTERNAL_ERROR)` | `wf`, `out_log` only. The code is pinned by tests (comment :120-125) |
| C10 | `QuicServer::superseded` (:603, :610), `key_changes` (:777, :782), `on_params` (:817) | `shut(PROTOCOL_VIOLATION / TRANSPORT_PARAMETER_ERROR)` | `superseded`: one direction to `!Open` (:594-595). Others: nothing |
| C11 | `H3Server::apply`, `Output::CloseConnection` (h3_server.rs:747-755): `conn.close(wire_code(code), true, [], now)`. Sources: `H3Conn::close` (h3/conn.rs:2601-2626) proves `added == [CloseConnection{code}]` and `closed`. Callers: :2916, :3189 (uni `Err(c)`), :3423, :3530, and the request path :1904-1906 `ReqError::Connection(c)` | h3 codes | h3 side: exact per `step`/`one_call` (h3_server.rs:86-114). quic side: phase only. `wire_code` (:219-228) maps `> VARINT_MAX` to H3_INTERNAL_ERROR because "no contract of h3's says so", so h3 needs `CloseConnection{code} ==> code <= VARINT_MAX` before (a) can state "that exact code" |
| C12 | `H3Server::pump` (h3_server.rs:1029-1034) | H3_GENERAL_PROTOCOL_ERROR, app | none on code or phase |
| — | Not Closing: `on_frame` CONNECTION_CLOSE → `enter_draining` (conn.rs:1280-1285); `on_reset_candidate` → Draining (:3398-3418, proved); §12.3 / no-path / idle / CID-exhaustion → `close_silently` (Closed, no code; :2282, :4314, :6014, :6595, :6704, :7818, :7829, :7884) | — | These are not error paths under the (a)/(b) rule. Out of scope apart from noting that `close_silently` at `build_close` :6014 can leave a Closing connection Closed before its CONNECTION_CLOSE was ever sent (§12.3 MUST, allowed) |

### 3.3 What 3d/3d2 prove about `poll_transmit` in Closing

`Connection::poll_transmit` (conn.rs:6614-6765):

```rust
// P3.
old(self).phase_spec() is Draining || old(self).phase_spec() is Closed ==> r is None,
r matches Some(d) ==> (old(self).phase_spec() is Closing ==> only_close(d@) && final(self).close_sent(
    *old(self),
    out_datagram_len(d@),
)),
```

The supporting spec fns:

- `only_close(d)` (conn.rs:8706-8711): every frame of every packet `is ConnectionClose`. **No code, no app flag, no packet kinds.**
- `close_sent(o, n)` (conn.rs:5323-5329): `o.lc.may_send_spec(n)`, `first_sent`, `!owed`, and the budget trace push. This covers the amplification limits (9000 §10.2.1), not content.
- `build_close` (conn.rs:5971-6072) ensures `transmit_ok`, `only_close`, `same_dcid`, `close_sent` and `path_rules`. Inside, it reads `lc.close_info()` (:6001), takes `close_spaces(self.complete, live_i, live_h, self.complete)` (:6005) and calls `close_packets` → `close_packet` → `close_frame`.
- `close_built(p, k)` (conn.rs:5778-5786): `kind == k`, `pn == next_pn(k)`, `dcid == space_dcid(k)`, `out_packet_wf`, size, `frames.len()==1`, and `frames[0] is ConnectionClose`. **`close_packet` (:5748-5776) gets the full `close_frame` ensures (code, app, reason) and then drops it**, because `close_built` keeps only `is ConnectionClose`.
- `lemma_only_close` (conn.rs:9108) turns `only_close` into P2/P17.
- On the wire, `pipeline::transmit` (pipeline.rs:280-296) and `QuicServer::transmit` (quictls/server.rs:393-409) ensure `final(out)@ == rfc_protect_datagram(l, keys)` and `transmit_ok`. **Neither forwards `only_close`/`close_sent`.** `protect_keyed` (protect.rs:130-141) silently drops a packet whose space has `keys[k] is None`. quictls `keys_ok` (server.rs:219-222) proves only `keys[k] is Some ==> live(k)`, not the converse.

### 3.4 Can (b) be a separate lemma over the transmit spec?

**Not over today's spec.** The output facts `only_close` and `close_sent` lose three things that (b) needs:

1. **The code.** `close_built` drops `close_frame`'s ensures.
2. **The key level.** The packet kinds equal `close_spaces(complete, live_i, live_h, complete)` inside `build_close`, but nothing exported says so.
3. **The §10.2.3 conversion.** An app close in Initial/Handshake goes out as `APPLICATION_ERROR` with an empty reason, so "that exact code" must read "that code, or APPLICATION_ERROR where §10.2.3 requires the conversion". Alternatively, prove app ⇒ `complete`: every app close comes from h3, which starts only after `handshake_complete() && Open` (h3_server.rs:1015-1017).

**It becomes a separate lemma after one change at the source.** Strengthen `close_built` so that `p.frames[0] == close_frame_spec(app, code, reason, k)`, where the triple is the current `lc.close_spec()`. Then export one closed predicate from `build_close` and thread it through poll_transmit's existing Closing conjunct, in place of `only_close`. A pure lemma `lemma_close_dgram_rfc` then proves the RFC statement (§10.2.3 levels and code) from that predicate. The wire-level form also needs `live(k) ==> keys[k] is Some` in quictls for the close spaces. Otherwise the bytes may omit a packet even though `out_log` has it. (See §4, step P4.)

---

## 4. Pilot and task order

### 4.1 Pilot A: `CryptoStream::on_crypto` and the 753ec2d bug

**Correction to the premise.** `on_crypto` never returned PROTOCOL_VIOLATION. Its only error has always been CRYPTO_BUFFER_EXCEEDED, and its ensures is already an iff (crypto_stream.rs:62-63). The false PROTOCOL_VIOLATION came from quictls:

1. An empty CRYPTO frame at an offset past the received end reached `Reassembly::insert`.
2. Its grow loop (reassembly.rs:351) extended the window with unreceived slots, so `crypto_end_spec(k)` (conn.rs:262-269, `base + buf_len`) moved.
3. `superseded` (quictls:602-603, `crypto_end(Initial) > init_end`) or `key_changes` (:776-783, `unread > 0`) then shut with PROTOCOL_VIOLATION.

Tests `empty_gapped_initial_ok` and `empty_initial_after_switch_ok` (quictls/tests/server.rs:336-353) pin the fix. The 753ec2d commit message names both checks: "not unread data at a key change nor Initial data past init_end".

**Why no proof caught it.** `Reassembly::wf` (reassembly.rs:233-249) and `insert` (:341-346) bound the window end only from above (`received k ==> k < base+buf_len`; `end' <= max(end, off+len)`). Nothing says the end *is* the end of received data. So `superseded`'s "past the end of previously received data" (9001 §4.1.3) was stated over an implementation number.

Clauses to add:

```rust
// reassembly.rs: the window ends at a received byte (tight end). A separate closed predicate, NOT in wf.
pub closed spec fn tight_end(&self) -> bool {
    self.buf@.len() > self.head ==> rfc_received(self.ins@).contains_key(
        (self.base + self.buf@.len() - self.head - 1) as nat)
}
// insert ensures: old(self).tight_end() && data@.len() > 0 ==> final(self).tight_end()
// pop ensures:    old(self).tight_end() ==> final(self).tight_end();  new/new_at ensure it
// CryptoStream::wf adds: self.reassembly().tight_end()
```

```rust
// crypto_stream.rs, RFC 9000 §7.5 (MUST close if not expanding; §7.5 floor 4096).
pub open spec fn crypto_allowed_err(s: CryptoStream, offset: u64, len: nat, c: u64) -> bool {
    c == CRYPTO_BUFFER_EXCEEDED && offset + len > s.reassembly().base() + MAX_CRYPTO_BUFFER
        && MAX_CRYPTO_BUFFER >= 4096   // own-limit, named
}
// CryptoStream::on_crypto ensures (replaces nothing; the existing iff already implies it):
r matches Err(c) ==> crypto_allowed_err(*old(self), offset, data@.len(), c),
```

```rust
// quictls/server.rs, RFC 9001 §4.1.3.
spec fn past_received(c: Connection, k: PacketKind, end: nat) -> bool {
    exists|p: nat| p >= end && #[trigger] rfc_received(c.crypto_inserted(k)).contains_key(p)
}
// needs a new `pub closed spec fn crypto_inserted(&self, k) -> Seq<(nat, Seq<u8>)>` on Connection
// superseded ensures (acceptance + close):
!cont && old(self).conn_spec().phase_spec() is Open ==> {
    &&& !(old(self).level is Initial)
    &&& past_received(old(self).conn_spec(), PacketKind::Initial, old(self).init_end)
    &&& final(self).conn_spec().phase_spec() is Closing
    &&& final(self).conn_spec().close_spec() == Some((false, PROTOCOL_VIOLATION, Seq::<u8>::empty()))
},
// key_changes ensures:
!ok && old(self).conn_spec().phase_spec() is Open ==> {
    &&& (key_events(ev).0 && old(self).unread(Level::Initial, PacketKind::Initial) > 0)
        || (key_events(ev).1 && old(self).unread(Level::Handshake, PacketKind::Handshake) > 0)
    &&& final(self).conn_spec().close_spec() == Some((false, PROTOCOL_VIOLATION, Seq::<u8>::empty()))
},
// plus a lemma: unread(l,k) > 0 ==> reader non-empty || past_received(c, k, c.crypto_base_spec(k))  (from the tight end)
```

The tight-end conjunct is the one that fails on the pre-753ec2d code: an empty insert leaves an unreceived last slot. **It cannot go into `Reassembly::wf`, nor be an unconditional `insert` ensures.** `insert`'s grow loop (reassembly.rs:351) still extends the window for empty `data` at an offset past the end, and 753ec2d filters that only in `CryptoStream`.

The workable form:

- Define a `closed spec fn tight_end()`.
- `insert` ensures `old.tight_end() && data@.len() > 0 ==> final.tight_end()`.
- `pop` preserves it.
- `CryptoStream::wf` requires it.

`RecvStream` never unfolds it, which keeps `RecvStream::on_data` (11.79M) untouched.

**Sibling to audit.** `RecvStream::on_data` calls `re.insert(off, data)` (recv_stream.rs:1336) without an emptiness filter. An empty STREAM frame (legal, e.g. a bare FIN at a high offset) grows the stream's reassembly window with unreceived slots too. Flow control uses `high`/`counted`, not the window end, so no false error follows. The same pattern does cost memory up to the window, though. List it as an audit item, not a fix.

**Prerequisite for `superseded`'s `!cont ==>` clause (branch :610, newly contiguous bytes).** Locally, "newly contiguous Initial bytes" does not imply `past_received(.., init_end)`. It needs a `QuicServer` invariant, `!(level is Initial) ==> conn.crypto_base_spec(Initial) >= init_end`. That follows from three facts:

- `on_secrets` sets `init_end = crypto_end(Initial)` at the switch (server.rs:881).
- `key_changes` closes unless `unread(Initial) == 0` at that moment (`core_ok`'s `KeyChange{unread == 0}` log clause, :212-215).
- `base` only grows.

Today no `wf`/`core_ok` conjunct states it. Add it to `core_ok` first.

### 4.2 Pilot B: quictls `report` / `shut` (part a)

Prerequisites in quic/src/conn.rs. Each is a small spinoff fn:

```rust
// Connection
pub closed spec fn close_spec(&self) -> Option<(bool, u64, Seq<u8>)> { self.lc.close_spec() }
pub open spec fn reason_cap(r: Seq<u8>) -> Seq<u8> { r.take(if r.len() > 64 { 64int } else { r.len() as int }) }

// Connection::close ensures, added:
old(self).phase_spec() is Open ==> final(self).close_spec() == Some((app, code, reason_cap(reason@))),
!(old(self).phase_spec() is Open) ==> final(self).close_spec() == old(self).close_spec(),
// close_internal: the same with app = false, reason = Seq::empty(), plus
old(self).phase_spec() is Open ==> final(self).phase_spec() is Closing,
!(old(self).phase_spec() is Open) ==> final(self).phase_spec() == old(self).phase_spec(),
// on_tls_alert:
old(self).phase_spec() is Open ==> final(self).phase_spec() is Closing
    && final(self).close_spec() == Some((false, (CRYPTO_ERROR_BASE + alert) as u64, Seq::<u8>::empty())),
!(old(self).phase_spec() is Open) ==> final(self).close_spec() == old(self).close_spec()
    && final(self).phase_spec() == old(self).phase_spec(),
```

Then quictls:

```rust
// shut: replaces `old(c).phase_spec() is Open ==> !(final(c).phase_spec() is Open)` (server.rs:93)
old(c).phase_spec() is Open ==> final(c).phase_spec() is Closing
    && final(c).close_spec() == Some((false, code, Seq::<u8>::empty())),
!(old(c).phase_spec() is Open) ==> final(c).phase_spec() == old(c).phase_spec()
    && final(c).close_spec() == old(c).close_spec(),

// report
pub open spec fn report_code(code: u64) -> u64 { if code <= VARINT_MAX { code } else { INTERNAL_ERROR } }
old(c).phase_spec() is Open ==> final(c).phase_spec() is Closing
    && final(c).close_spec() == Some((false, report_code(code), Seq::<u8>::empty())),
!(old(c).phase_spec() is Open) ==> final(c).phase_spec() == old(c).phase_spec()
    && final(c).close_spec() == old(c).close_spec(),
```

The alert branch needs `(CRYPTO_ERROR_BASE + ((code - CRYPTO_ERROR_BASE) as u8)) == code` for `code` in `[0x100, 0x1ff]`, which is one `by (bit_vector)` or `nonlinear` line. Acceptance for `report` belongs at its caller `feed` (:650-666): `Err(code) ==> allowed_tls_err(cfg, tp, h0, l, b, rand, code)`. It reduces to a spec lemma over `spec_on_crypto`, plus the named own-limit for the INTERNAL_ERROR escape (`server.rs:1433`). Proving `allowed_tls(..) ==> code <= 0x1ff` also makes `report_code`'s INTERNAL_ERROR branch dead. Once this lands, tests `tampered_finished_0x133`, `error_ranges` and `a2_closes_0x178` become regression checks rather than the only evidence, and the comment at server.rs:120-125 can drop "not an ensures".

### 4.3 Recommended task order, smallest risk first

| Step | Work | Touches | rlimit notes |
|---|---|---|---|
| P0 | `Connection::close_spec`; `close`, `close_internal`, `on_tls_alert` ensures (§4.2) | conn.rs:3009-3053, :3222 | Low. Small spinoff fns, but `close` is called from ~8 sites, so every caller's context gains two conjuncts. Watch `on_counted`, `close_on_error`, `H3Server::apply` |
| P1 | Pilot B: `shut`, `report` | quictls/server.rs:86-153 | low |
| P2 | Pilot A: `Reassembly::tight_end` (closed; `insert` preserves it for non-empty data), `CryptoStream` `crypto_allowed_err`, `Connection::crypto_inserted`, the `core_ok` invariant `!(level is Initial) ==> crypto_base(Initial) >= init_end`, quictls `superseded`/`key_changes`/`on_params` acceptance and close code. Audit the empty STREAM insert at recv_stream.rs:1336 | reassembly.rs, crypto_stream.rs, quictls | Medium **only if** the tight-end conjunct reaches `RecvStream::on_data` (11.79M). Keep it closed and out of `Reassembly::wf` and `RecvStream::wf` |
| P3 | Spec-only `allowed_*` lemmas for every exact ≡ codec and h3/tls spec (§2 "spec-relative" rows). One lemma per `rfc_*` fn: `rfc_x(..) == Err(c) ==> allowed_x(.., c)`, where `allowed_x` is a disjunction of MUST / MAY-chosen / named own-limit predicates. Fix the 5 "chosen (no clause)" rows first (streams.rs server-bidi RESET/SDB; client_hello cookie; tls step :1317; h3 conn.rs:2916; h3_server pump :1032), each by naming a predicate | spec fns only | **None.** Proof fns, so exec VCs are untouched. Recursive specs (`rfc_frames`, `rfc_recv`, `rfc_request_stream`, `rfc_control`, `rfc_uni_stream`) need inductive lemmas. Budget each at rlimit 4 on its own |
| P4 | Part (b): strengthen `close_built` with `frames[0] == close_frame_spec(..)`; a closed `close_dgram_ok(o, d)` := every packet's kind ∈ `close_spaces(o.complete, o.live_i, o.live_h, o.complete)` and its frame is `close_frame_spec(o.close_spec(), kind)`; ensure it in `build_close`; in `poll_transmit` replace `only_close(d@)` in the Closing conjunct (:6634) by `close_dgram_ok(*old(self), d@)`, with `lemma_close_dgram_only_close` for callers; then the pure `lemma_close_dgram_rfc` (9000 §10.2.3) | conn.rs:5748-6072, :6634, :8706 | **poll_transmit 7.13M**, the one tight fn this phase touches. Swapping a conjunct for a closed predicate keeps the count equal. The early `return r` in the Closing arm (:6677-6693) is the only path that proves it. Do not add any conjunct outside the existing `phase is Closing ==>` guard (4c plan :328). Lift to `pipeline::transmit` / `QuicServer::transmit` with `live(k) ==> keys[k] is Some` for close spaces (quictls `keys_ok` converse), or state (b) on `out_log` only |
| P5 | (a) for frame errors: `on_frame`/`on_ack_frame`/`on_crypto_frame`/`on_cid_frame` gain `Err(c) ==> allowed_frame_err(*old(self), k, f@, c)` (a closed disjunction over the sub-handlers' `allowed_*`); `on_stream_frame` gains `Err(c) ==> final.close_spec() == Some((false, c, []))`; `on_packet`, `on_frames` lift to "some frame of p"; `on_counted`/`on_datagram` gain `old Open && final Closing ==> final.close_spec() matches Some((false, c, _)) && allowed_datagram_err(old, packets, error, c)` | conn.rs:595-1435 | **Medium/high.** `on_counted` and `on_frame` are large dispatch fns (spinoff, unmeasured). **Split:** hide `allowed_frame_err` as `closed` and reveal per arm in a per-frame-kind proof fn; keep `on_counted`'s loop invariant as-is and prove the close fact only at the two `return`s after `close_internal`/`close_on_error` |
| P6 | h3 → quic: h3 `CloseConnection{code} ==> code <= VARINT_MAX` (h3 `step`/`one_call`), so `wire_code` is the identity; `H3Server::apply`/`pump` ensure `close_spec == Some((true, code, []))`; (b) at app level uses the §10.2.3 conversion or app ⇒ `complete` | h3/conn.rs, quic/h3_server.rs:219-228, :747-755, :1029 | Medium: `H3Server::pump` has a large ensures (:149-175). Add the close clause behind a closed predicate |
| P7 | tls own-limit escapes: name `signing_unavailable` for the INTERNAL_ERROR-on-Ok-spec branches (server.rs:1252, :1433), so `allowed_tls_err` is total; then wire `feed` (P1) to it | tls/server.rs, flight.rs, sign.rs | Medium: the 4c plan notes `spec_drain` sensitivity at rlimit 4 in tls. Keep the lemma in a separate module that does not import quic |

**Needs a split to stay under rlimit 4:** `poll_transmit` (P4: conjunct swap only, closed predicate). `on_counted` / `on_frame` (P5: per-arm proof fns, closed `allowed_frame_err`). `H3Server::pump` (P6: closed predicate). **Must not be touched:** `RecvStream::on_data` (11.79M), `datagram::pick` (12.10M, no error sites), `Paths::on_timeout` (11.04M, silent close only). Their acceptance comes entirely from spec lemmas (P3).
