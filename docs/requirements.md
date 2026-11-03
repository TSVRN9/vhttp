# RFC requirements matrix

Scopes every phase of the verified HTTP/3 server. Each row is one RFC section (or, for a requirement that is not simply "implemented in phase N", one requirement inside a section, marked `(req)` with the quoted text in Notes). Source of truth for the keyword counts: the RFC `.txt` files at rfc-editor.org. Duvet (`.duvet/config.toml`) tracks the same six RFCs; `duvet report` writes `.duvet/reports/report.html`.

Columns: `§` section, `Topic`, `#MUST/MUST NOT` (MUST, MUST NOT, REQUIRED, SHALL, SHALL NOT in that section's own text; a `(req)` row's count is a subset of its section row, not additional), `Server applies?`, `Phase`, `Notes`.

## Legend

### Phases

| Phase | Crate / scope |
|---|---|
| 1 | `wire`: QUIC variable-length integers (RFC 9000 §16 only) — proven: `theorem_matches_rfc`, `theorem_serialize_matches_rfc` in crates/wire/src/varint.rs |
| 2 | `h3`: HTTP/3 framing, streams, settings, errors (RFC 9114), QPACK (RFC 9204), HTTP message validation |
| 3 | `quic`: QUIC transport (RFC 9000 except §16), incl. anti-amplification, connection IDs, path validation, stateless reset, version negotiation; RFC 9001 §5.4.1–§5.4.2 header protection (3e) |
| 4 | `tls`: TLS 1.3 server handshake, key schedule, record/AEAD use (RFC 8446) and QUIC-TLS (RFC 9001) |
| 5 | `crypto`: requirements on the primitive algorithms themselves |
| 6 | `recovery`: loss detection and congestion control (RFC 9002) |
| 7 | Full conformance and browsers: h3spec, h3i, interop runner, Chrome/Firefox; Duvet report with no unannotated MUSTs |

### Non-phase values

- `N/A (client-only)`: the rule binds a client.
- `N/A (IANA procedure)`: registry or codepoint-allocation rules for IANA/IESG or specification authors, not endpoint behavior.
- `N/A (intermediary-only)`: translation/forwarding rules for proxies and gateways (RFC 9204 §4.5.4 forwarding rule and §7.1.3; RFC 9114 §4.1.2, §4.2, both §4.3.1 rows). We are an origin server.
- `N/A (binds spec authors)`: the rule binds authors of future specifications, extensions or applications, not an implementation (RFC 9001 §5.1, §6.6, §9.2, §9.4; RFC 8446 Appendix E exporters).
- `N/A (boilerplate)`: the BCP 14 keyword-definition paragraph; the keywords there are not requirements.
- `Declined (optional: X)`: the rule only matters for an optional feature we decline. Declined features: 0-RTT, resumption/PSK, connection migration (initiating it), Retry, NEW_TOKEN issuance (sending NEW_TOKEN is a MAY, RFC 9000 §8.1.3; receiving-side rules stay Phase 3), server push, QPACK dynamic table (capacity advertised as 0), ChaCha20-Poly1305, AES-256-GCM, X25519, client certificates, HTTP/3 extensions (datagrams, WebTransport, extended CONNECT), TLS 1.2-and-older compatibility, and CONNECT/proxying. A MUST about how to refuse or ignore a declined feature (discard 0-RTT packets, no `early_data` in EncryptedExtensions, reject PUSH_PROMISE, still answer PATH_CHALLENGE) is not declined; it carries its phase.

### Notes that bind later phases

- CONNECT: RFC 9114 §4.4 rows are `Declined (optional: CONNECT/proxying)`. An origin server need not implement CONNECT (RFC 9110 §9.1 mandates only GET and HEAD), but Phase 2b answers a well-formed CONNECT with `501 Not Implemented` and a malformed one with H3_MESSAGE_ERROR (not drop or reset).
- RFC 8446 §9.2 cookie: Phase 4 parses the cookie extension and rejects a cookie we never issued.
- Tracking granularity: a section row with `partial` covers every non-`(req)` keyword in the section as Phase-N work; the `(req)` rows under it are the exceptions.

## Keyword totals and reconciliation

Matrix total = sum of the section rows' counts (`(req)` rows excluded). It equals the raw `grep -o` count of the RFC text for every RFC.

| RFC | Matrix total | Sections | Gap vs raw grep |
|---|---|---|---|
| 9114 | 157 | 44 | matches raw count; no gap. |
| 9204 | 44 | 22 | matches raw count; no gap. |
| 9000 | 307 | 115 | matches raw count; no gap. |
| 9001 | 88 | 35 | the extraction tables totalled 83 against raw 88; the 5 missing are the BCP 14 boilerplate in §2, added here as an `N/A (boilerplate)` row. |
| 9002 | 38 | 19 | the extraction tables totalled 33 against raw 38; the 5 missing are the BCP 14 boilerplate in §2, added here as an `N/A (boilerplate)` row. |
| 8446 | 345 | 57 | the extraction tables totalled 317 against raw 345; the 28 missing are in Appendices B (2), C (1), D (18), E (7), which the extraction skipped. Added here as rows. References and the boilerplate (§1.1) hold no other keywords. |

## RFC 9114 — HTTP/3

| § | Topic | #MUST/MUST NOT | Server applies? | Phase | Notes |
|---|---|---|---|---|---|
| 2.2 | Conventions and Terminology | 5 | no | N/A (boilerplate) | BCP 14 boilerplate listing the keywords; not a requirement |
| 3.1 | Discovering an HTTP/3 Endpoint | 2 | no | N/A (client-only) | Client verifies server certificate / authority |
| 3.1.2 | Other Schemes | 1 | no | N/A (client-only) | Client ensures server willing to serve non-https scheme |
| 3.2 | Connection Establishment | 3 | partial | 2 | Server must send SETTINGS as initial control-stream frame ✅ 2b: crates/h3/src/conn.rs (`start`; stream 3 is `ctrl_preamble()` then only GOAWAYs: `theorem_wf`, `theorem_ctrl_preamble`) |
| 3.2 (req) | SNI support | 1 | no | N/A (client-only) | "HTTP/3 clients MUST support a mechanism to indicate the target host to the server during the TLS handshake." |
| 3.2 (req) | SNI send | 1 | no | N/A (client-only) | "clients MUST send the Server Name Indication (SNI) TLS extension unless an alternative mechanism ..." |
| 3.3 | Connection Reuse | 2 | no | N/A (client-only) | Client validates certificate for new origin / does not reuse |
| 4.1 | HTTP Message Framing | 9 | partial | 2 | Server: multiple requests / extra response = malformed; invalid frame sequence = H3_FRAME_UNEXPECTED; no Transfer-Encoding; close send side after final response ✅ 2b (receive side: HEADERS, DATA*, optional trailer HEADERS, FIN; DATA before HEADERS or any HEADERS/DATA after the trailers = H3_FRAME_UNEXPECTED, so a second request cannot arrive; unknown frames allowed anywhere; FIN before a complete header section = H3_REQUEST_INCOMPLETE): crates/h3/src/request.rs; ✅ 2b (send side: one final response per request (status 200-599, never a lone 1xx), written with FIN; a second `send_response` is `Err`): crates/h3/src/conn.rs |
| 4.1 (req) | Single request per stream | 1 | no | N/A (client-only) | "A client MUST send only a single request on a given stream." |
| 4.1 (req) | PUSH_PROMISE on push stream | 1 | no | N/A (client-only) | "a pushed response that includes PUSH_PROMISE frames MUST be treated as a connection error of type H3_FRAME_UNEXPECTED" (client receives push streams; we never send them) |
| 4.1 (req) | Client closes send side | 1 | no | N/A (client-only) | "After sending a request, a client MUST close the stream for sending." |
| 4.1 (req) | Stream closure not dependent on response | 1 | no | N/A (client-only) | "Unless using the CONNECT method, clients MUST NOT make stream closure dependent on receiving a response" |
| 4.1 (req) | Do not discard complete responses | 1 | no | N/A (client-only) | "Clients MUST NOT discard complete responses as a result of having their request terminated abruptly" |
| 4.1.1 | Request Cancellation and Rejection | 2 | partial | 2 | Server MUST NOT use H3_REQUEST_REJECTED for partially/fully processed requests ✅ 2b: crates/h3/src/conn.rs (`rejected_outs`, the only use, cites the MUST: a new stream at or above our GOAWAY ID, whose machine is never fed, or a 501/421 the peer's limit doesn't admit, which is fed but never delivered to the application; "processed" means delivered); cancellation SHOULD (terminate only the directions still open): stream errors, rejections and peer resets reset our sending part only while open and send STOP_SENDING only while the peer is still sending |
| 4.1.1 (req) | Client use of H3_REQUEST_REJECTED | 1 | no | N/A (client-only) | "Clients MUST NOT use the H3_REQUEST_REJECTED error code, except when a server has requested closure ..." |
| 4.1.2 | Malformed Requests and Responses | 3 | partial | 2 | Detected malformed request = stream error H3_MESSAGE_ERROR ✅ 2b: crates/h3/src/request.rs (header/trailer validation failure, and content-length ≠ sum of DATA lengths: more content than declared as soon as it arrives, less at FIN); ✅ 2b (responses we send are never malformed: content-length equals the body length except on a HEAD response or a 304, which may carry the GET/200 value, and never appears on a 204; a valid content-length value always; no content on HEAD, 204, 205 or 304, per RFC 9110 §8.6, §9.3.2, §15.3.5, §15.3.6, §15.4.5; the HEAD flag is proven to equal "this stream's delivered request had method HEAD" (`req_fed`), so `send_response`'s `valid_response(resp, is_head)` is the right rule per request; `valid_response`): crates/h3/src/message.rs, crates/h3/src/conn.rs |
| 4.1.2 (req) | Intermediary must not forward malformed | 1 | no | N/A (intermediary-only) | "Intermediaries ... MUST NOT forward a malformed request or response." We are an origin server, not an intermediary; nothing is forwarded. We do still reject (row above) |
| 4.1.2 (req) | Client must not accept malformed response | 1 | no | N/A (client-only) | "Clients MUST NOT accept a malformed response." |
| 4.2 | HTTP Fields | 6 | partial | 2 | Lowercase names on encode; uppercase names malformed; no connection-specific fields generated, malformed on receipt (2); TE only "trailers", and only in a request header (`te` in a response is refused by `check_response`, `te` in a trailer section is malformed) ✅ 2b: crates/h3/src/message.rs; ✅ 2b (`send_response` runs `check_response` before encoding; peer SETTINGS_MAX_FIELD_SECTION_SIZE respected, the §4.2.2 SHOULD NOT): crates/h3/src/conn.rs; §4.2.2 size limit (a MAY): HEADERS payload or decoded field section (Σ name + value + 32) over MAX_FIELD_SECTION_SIZE = stream error H3_EXCESSIVE_LOAD ✅ 2b: crates/h3/src/request.rs, crates/h3/src/qpack/field_section.rs (`decode_field_section_bounded`), crates/h3/src/limits.rs |
| 4.2 (req) | Intermediary HTTP/1.x to HTTP/3 transform | 1 | no | N/A (intermediary-only) | "An intermediary transforming an HTTP/1.x message to HTTP/3 MUST remove connection-specific header fields" - we are not an intermediary and never translate from HTTP/1.x |
| 4.2.1 | Field Compression | 1 | yes | 2 | Concatenate multiple cookie lines with "; " before passing to a non-h2/h3 context (e.g. a generic handler); do at the handler boundary ✅ 2b: crates/h3/src/message.rs (cookie merge in `validate_request`) |
| 4.3 | HTTP Control Data | 7 | yes | 2 | Pseudo-header rules: only defined ones generated, request/response-specific placement, none in trailers, undefined/invalid = malformed, must precede regular fields (2) ✅ 2b: crates/h3/src/message.rs (request, trailer and response sides); ✅ 2b (responses: `:status` first, no other pseudo-header): crates/h3/src/conn.rs |
| 4.3.1 | Request Pseudo-Header Fields | 10 | partial | 2 | Validate: authority without userinfo; :path non-empty and "/" for empty path (2); exactly one :method/:scheme/:path (non-CONNECT); :authority or Host required for http/https; not empty; equal if both present; absent if scheme has no authority ✅ 2b: crates/h3/src/message.rs; ✅ 2b (a non-http(s) :scheme is answered 421 and never delivered, so the no-authority-scheme clause never reaches the app): crates/h3/src/conn.rs |
| 4.3.1 (req) | Omit :authority when translating from HTTP/1.1 | 1 | no | N/A (intermediary-only) | "this pseudo-header field MUST be omitted when translating from an HTTP/1.1 request that has a request target in a method-specific form" - applies to a translator/client, we never translate |
| 4.3.1 (req) | Intermediary creates Host | 1 | no | N/A (intermediary-only) | "An intermediary that converts an HTTP/3 request to HTTP/1.1 MUST create a Host field ..." - we are not an intermediary. (Handler boundary may still expose :authority as Host.) |
| 4.3.2 | Response Pseudo-Header Fields | 1 | yes | 2 | :status MUST be in every response we generate ✅ 2b: crates/h3/src/conn.rs (`resp_fields`: `:status` first; `response_wire` proves the HEADERS payload decodes back to it); `check_response` forbids pseudo-headers in `Response.headers` (crates/h3/src/message.rs) |
| 4.4 | The CONNECT Method | 4 | partial | 2 | A well-formed CONNECT is answered with `501 Not Implemented` (RFC 9110 §9.1: an origin server SHOULD answer an unimplemented method with 501). A malformed CONNECT (RFC 9114 §4.4 form rules: no :scheme or :path, and an :authority in authority-form, `host ":" 1*DIGIT` with a non-empty host and no userinfo, RFC 9110 §9.3.6) is H3_MESSAGE_ERROR. Both are Phase 2b. ✅ 2b: crates/h3/src/message.rs (validation half: `RequestHead::Connect`); ✅ 2b (a well-formed CONNECT is answered 501 with FIN, then STOP_SENDING(H3_NO_ERROR); never delivered): crates/h3/src/conn.rs |
| 4.4 (req) | CONNECT request construction | 1 | no | N/A (client-only) | "A CONNECT request MUST be constructed as follows ..." (sender-side) |
| 4.4 (req) | Only DATA after CONNECT completes | 1 | no | Declined (optional: CONNECT/proxying) | "Receipt of any other known frame type MUST be treated as a connection error of type H3_FRAME_UNEXPECTED." Applies only to an established tunnel; we never accept CONNECT, so no tunnel exists |
| 4.4 (req) | Proxy closes TCP on stream/QUIC error | 1 | no | Declined (optional: CONNECT/proxying) | "if a proxy detects an error with the stream or the QUIC connection, it MUST close the TCP connection." No TCP connection is ever opened |
| 4.4 (req) | Proxy closes TCP on client reset | 1 | no | Declined (optional: CONNECT/proxying) | "If the proxy detects that the client has reset the stream or aborted reading from the stream, it MUST close the TCP connection." No TCP connection is ever opened |
| 4.6 | Server Push | 8 | no | Declined (optional: server push) | Push not implemented (we never send PUSH_PROMISE or push streams, advertise no push support); the 8 MUSTs cover pusher authority/identical promises (3) and client push-stream/validation/caching rules (5) |
| 5.2 | Connection Shutdown | 3 | yes | 2 | No new requests/pushes after GOAWAY received (we never initiate); our GOAWAY ids non-increasing; received GOAWAY with larger id = H3_ID_ERROR (client GOAWAY carries a push ID) ✅ 2b (peer GOAWAY with larger id = H3_ID_ERROR): crates/h3/src/uni.rs; ✅ 2b (our GOAWAY ids non-increasing, client-bidi (≡ 0 mod 4, RFC 9114 §7.2.6) and above every accepted request: `theorem_wf` over `highest_accepted`, which `req_call` raises to each accepted stream's ID; new requests at or above it rejected with H3_REQUEST_REJECTED): crates/h3/src/conn.rs |
| 5.4 | Transport Closure | 1 | no | N/A (client-only) | Client assumption about unacknowledged requests |
| 6.1 | Bidirectional Streams | 1 | no | N/A (client-only) | Client treats server-initiated bidi stream as H3_STREAM_CREATION_ERROR |
| 6.2 | Unidirectional Streams | 5 | yes | 2 | Our transport params must allow peer >=3 uni streams (value chosen in h3 config, encoded in phase 3/4); unknown stream types: abort reading/discard, never an error (2); no state-changing stream types until peer supports; tolerate uni stream closed/reset before header ✅ 2b: crates/h3/src/uni.rs; crates/h3/src/limits.rs (`MIN_PEER_UNI_STREAMS`); ✅ 2b (sender side: we open only the control stream, stream 3): crates/h3/src/conn.rs ✅ 3d: crates/quic/src/handshake.rs (local_tp_ok: 3 <= initial_max_streams_uni <= MAX_LOCAL_STREAMS) |
| 6.2.1 | Control Streams | 6 | yes | 2 | Open one control stream with SETTINGS first; non-SETTINGS first frame = H3_MISSING_SETTINGS; second control stream = H3_STREAM_CREATION_ERROR; never close it nor STOP_SENDING it (2); closure = H3_CLOSED_CRITICAL_STREAM ✅ 2b (receive side): crates/h3/src/uni.rs; ✅ 2b (sender side: our control stream opened with SETTINGS first and never FIN-ed or reset, `start`/`shutdown` outputs pinned exactly; STOP_SENDING and RESET_STREAM only on request streams, so never on the peer's control stream; a second peer control stream = H3_STREAM_CREATION_ERROR end to end, `uni_fed` over `uni_seen()`; peer STOP_SENDING on stream 3 = H3_CLOSED_CRITICAL_STREAM; peer reset of its control stream = H3_CLOSED_CRITICAL_STREAM): crates/h3/src/conn.rs (`outs_ok`) |
| 6.2.2 | Push Streams | 3 | partial | 2 | Client-initiated push stream received = connection error H3_STREAM_CREATION_ERROR (rejection rule, implemented) ✅ 2b: crates/h3/src/uni.rs |
| 6.2.2 (req) | Push ID used once per push stream header | 1 | no | Declined (optional: server push) | "Each push ID MUST only be used once in a push stream header." We send no push streams |
| 6.2.2 (req) | Client detects duplicate push ID | 1 | no | N/A (client-only) | Client treats duplicate push ID as H3_ID_ERROR |
| 6.2.3 | Reserved Stream Types | 1 | yes | 2 | Reserved (0x1f*N+0x21) streams have no meaning on receipt; treated as unknown ✅ 2b: crates/h3/src/uni.rs |
| 7.1 | Frame Layout | 4 | yes | 2 | Payload exactly the fields: extra or short = H3_FRAME_ERROR; redundant lengths self-consistent; truncated last frame on clean stream end = H3_FRAME_ERROR ✅ 2a (layout only): crates/h3/src/frame.rs; ✅ 2b (placement: crates/h3/src/uni.rs, crates/h3/src/request.rs; truncated last frame at a clean FIN on a request stream = H3_FRAME_ERROR): crates/h3/src/request.rs |
| 7.2.1 | DATA | 2 | yes | 2 | DATA only on request/response streams; DATA on control stream = H3_FRAME_UNEXPECTED ✅ 2b (control stream): crates/h3/src/uni.rs; ✅ 2b (request stream: DATA before HEADERS or after the trailers = H3_FRAME_UNEXPECTED; payload passed on as it arrives, never buffered): crates/h3/src/request.rs |
| 7.2.2 | HEADERS | 1 | yes | 2 | HEADERS on control stream = H3_FRAME_UNEXPECTED ✅ 2b (control stream): crates/h3/src/uni.rs; ✅ 2b (request stream: header and trailer sections, HEADERS after the trailers = H3_FRAME_UNEXPECTED): crates/h3/src/request.rs |
| 7.2.3 | CANCEL_PUSH | 3 | yes | 2 | Not on control stream = H3_FRAME_UNEXPECTED; push ID above allowed = H3_ID_ERROR; server receiving for unmentioned push ID = H3_ID_ERROR (with push declined, always H3_ID_ERROR) ✅ 2a (layout only): crates/h3/src/frame.rs; ✅ 2b (control stream: every CANCEL_PUSH = H3_ID_ERROR, or H3_FRAME_ERROR if longer than 8 bytes, from the header alone): crates/h3/src/uni.rs; ✅ 2b (CANCEL_PUSH on a request stream = H3_FRAME_UNEXPECTED, from the header alone): crates/h3/src/request.rs |
| 7.2.4 | SETTINGS | 7 | yes | 2 | Once, first on control stream; second SETTINGS or SETTINGS elsewhere = H3_FRAME_UNEXPECTED; no duplicate identifiers; ignore unknown identifiers ✅ 2a (layout only): crates/h3/src/frame.rs; ✅ 2b (first on the control stream, else H3_MISSING_SETTINGS; second = H3_FRAME_UNEXPECTED): crates/h3/src/uni.rs; ✅ 2b (SETTINGS on a request stream = H3_FRAME_UNEXPECTED): crates/h3/src/request.rs; ✅ 2b (applying peer SETTINGS: only MAX_FIELD_SECTION_SIZE is used, every other identifier ignored): crates/h3/src/conn.rs |
| 7.2.4.1 | Defined SETTINGS Parameters | 3 | yes | 2 | Grease settings have no meaning; reserved HTTP/2-era identifiers never sent, receipt = H3_SETTINGS_ERROR ✅ 2a: crates/h3/src/frame.rs (payload decode rejects reserved and duplicate IDs; grease/unknown are ignored by construction) |
| 7.2.4.2 | Initialization | 10 | partial | 2 | Server: no frames/requests invalid under peer settings; no waiting for peer data before sending SETTINGS; send SETTINGS as soon as transport ready (3 total) ✅ 2b: crates/h3/src/conn.rs (`start` needs no peer data; responses respect the peer's MAX_FIELD_SECTION_SIZE; no dynamic table, so the QPACK settings constrain nothing) |
| 7.2.4.2 (req) | Client complies with stored settings (0-RTT) | 1 | no | N/A (client-only) | "A client MUST comply with stored settings ... when attempting 0-RTT." |
| 7.2.4.2 (req) | Client complies with new server settings | 1 | no | N/A (client-only) | "Once a server has provided new settings, clients MUST comply with those values." |
| 7.2.4.2 (req) | Server MUST NOT accept 0-RTT if settings compatibility unknown | 1 | yes | 4 | We never accept 0-RTT, so this holds by always rejecting (no early_data, 0-RTT packets dropped); realised in TLS/QUIC phases ✅ 4b: crates/tls/src/server.rs (no 0-RTT level; no client_early_traffic_secret or binder key is derived) |
| 7.2.4.2 (req) | SETTINGS must not reduce limits after 0-RTT accept | 1 | no | Declined (optional: 0-RTT) | Only relevant when 0-RTT is accepted |
| 7.2.4.2 (req) | Server includes all non-default settings | 1 | no | Declined (optional: 0-RTT) | Sentence is scoped to the 0-RTT-accepted case |
| 7.2.4.2 (req) | Incompatible settings after 0-RTT = H3_SETTINGS_ERROR | 1 | no | N/A (client-only) | Client-side check (client receives server SETTINGS) |
| 7.2.4.2 (req) | Omitted non-default setting after 0-RTT = H3_SETTINGS_ERROR | 1 | no | N/A (client-only) | Client-side check |
| 7.2.5 | PUSH_PROMISE | 8 | partial | 2 | Server receiving PUSH_PROMISE (client MUST NOT send) = connection error H3_FRAME_UNEXPECTED ✅ 2b (control stream, dispatched on type before payload parse): crates/h3/src/uni.rs; ✅ 2b (request stream, dispatched on type before payload parse): crates/h3/src/request.rs |
| 7.2.5 (req) | Server push ID within MAX_PUSH_ID | 1 | no | Declined (optional: server push) | "A server MUST NOT use a push ID that is larger than the client has provided in a MAX_PUSH_ID frame" |
| 7.2.5 (req) | Client rejects larger push ID | 1 | no | N/A (client-only) | Client H3_ID_ERROR |
| 7.2.5 (req) | Repeated push ID has identical request headers | 2 | no | Declined (optional: server push) | "the decompressed request header sets MUST contain the same fields in the same order, and ... exact matches" |
| 7.2.5 (req) | Client detects promise mismatch | 1 | no | N/A (client-only) | Client H3_GENERAL_PROTOCOL_ERROR |
| 7.2.5 (req) | PUSH_PROMISE on control stream (client) | 1 | no | N/A (client-only) | Client H3_FRAME_UNEXPECTED |
| 7.2.5 (req) | Client MUST NOT send PUSH_PROMISE | 1 | no | N/A (client-only) | Sender-side client rule (server-side enforcement is the section row) |
| 7.2.6 | GOAWAY | 2 | no | N/A (client-only) | Both MUSTs are client receive rules (stream ID type check; GOAWAY not on control stream) |
| 7.2.7 | MAX_PUSH_ID | 4 | partial | 2 | Server: MAX_PUSH_ID not on control stream = H3_FRAME_UNEXPECTED; smaller value than before = H3_ID_ERROR; never send MAX_PUSH_ID ✅ 2a (layout only): crates/h3/src/frame.rs; ✅ 2b (smaller MAX_PUSH_ID = H3_ID_ERROR; never sent: no MAX_PUSH_ID serializer exists): crates/h3/src/uni.rs; ✅ 2b (MAX_PUSH_ID on a request stream = H3_FRAME_UNEXPECTED): crates/h3/src/request.rs |
| 7.2.7 (req) | Client treats MAX_PUSH_ID as error | 1 | no | N/A (client-only) | "A client MUST treat the receipt of a MAX_PUSH_ID frame as a connection error of type H3_FRAME_UNEXPECTED." |
| 7.2.8 | Reserved Frame Types | 3 | yes | 2 | Grease frames ignored on receipt; HTTP/2-era reserved types never sent, receipt = H3_FRAME_UNEXPECTED ✅ 2a (layout only): crates/h3/src/frame.rs; ✅ 2b (control stream: HTTP/2-reserved = H3_FRAME_UNEXPECTED, grease/unknown ignored): crates/h3/src/uni.rs; ✅ 2b (request streams: HTTP/2-reserved = H3_FRAME_UNEXPECTED, grease/unknown skipped without buffering): crates/h3/src/request.rs |
| 8 | Error Handling | 1 | yes | 2 | Unexpected-context or unknown error code treated as H3_NO_ERROR ✅ 2b: crates/h3/src/conn.rs (`on_stream_reset` / `on_stop_sending` ignore the code) |
| 9 | Extensions to HTTP/3 | 4 | partial | 2 | Ignore unknown values in extensible elements; discard unknown uni stream types; no extension used without negotiation (we implement none) ✅ 2b (uni streams + control frames): crates/h3/src/uni.rs; ✅ 2b (request streams: unknown and grease frames skipped without buffering, in every phase): crates/h3/src/request.rs |
| 9 (req) | Extension setting defaults disabled | 1 | no | Declined (optional: HTTP/3 extensions) | Obligation on extension definitions |
| 10.3 | Intermediary-Encapsulation Attacks | 2 | yes | 2 | Invalid field names / invalid field-value characters = malformed ✅ 2b: crates/h3/src/message.rs; ✅ 2b (request path: header and trailer sections validated before delivery): crates/h3/src/request.rs; ✅ 2b (response path: `check_response` before encoding): crates/h3/src/conn.rs |
| 10.4 | Cacheability of Pushed Responses | 1 | no | Declined (optional: server push) | Multi-tenant push authority; we never push |
| 10.6 | Use of Compression | 2 | yes | 2 | Satisfied structurally: static-table-only QPACK (no dynamic table) and no content compression ✅ 2b: crates/h3/src/qpack/field_section.rs (no dynamic table), crates/h3/src/conn.rs (bodies sent as given) |
| 10.8 | Frame Parsing | 1 | yes | 2 | Frame length must exactly match its fields (see 7.1) ✅ 2a: crates/h3/src/frame.rs |
| 10.9 | Early Data | 1 | no | Declined (optional: 0-RTT) | Anti-replay mitigations apply only when HTTP/3 accepts 0-RTT; we never do |
| 11.2.1 | Frame Types | 4 | no | N/A (IANA procedure) | IANA registry rules; not endpoint behavior |
| 11.2.2 | Settings Parameters | 3 | no | N/A (IANA procedure) | IANA registry rules; not endpoint behavior |
| 11.2.3 | Error Codes | 3 | no | N/A (IANA procedure) | IANA registry rules; not endpoint behavior |
| 11.2.4 | Stream Types | 4 | no | N/A (IANA procedure) | IANA registry rules; not endpoint behavior |

Total keyword count: 157 across 44 sections.

## RFC 9204 — QPACK: Field Compression for HTTP/3

| § | Topic | #MUST/MUST NOT | Server applies? | Phase | Notes |
|---|---|---|---|---|---|
| 1.1 | Conventions and Definitions | 5 | no | N/A (boilerplate) | BCP 14 boilerplate listing the keywords; not a requirement. |
| 2.1 | Encoder: field order | 1 | yes | 2 | Response encoder MUST emit representations in input order. ✅ 2a: crates/h3/src/qpack/field_section.rs |
| 2.1.1 | Limits on dynamic table insertions | 1 | no | Declined (optional: QPACK dynamic table) | Encoder must not insert when nothing evictable; we never insert. |
| 2.1.2 | Blocked streams | 2 | partial | 2 | Encoder limit on blocked streams is moot (no dynamic refs); decoder rule row below binds. (summary; sub-rows carry status) |
| 2.1.2 (req) | Encoder limits blocked streams | 1 | no | Declined (optional: QPACK dynamic table) | "An encoder MUST limit the number of streams that could become blocked to the value of SETTINGS_QPACK_BLOCKED_STREAMS at all times." |
| 2.1.2 (req) | Decoder: too many blocked streams | 1 | yes | 2 | "If a decoder encounters more blocked streams than it promised to support, it MUST treat this as a connection error of type QPACK_DECOMPRESSION_FAILED." With capacity 0 and blocked-streams limit 0, any Required Insert Count > 0 is this error. ✅ 2a: crates/h3/src/qpack/field_section.rs |
| 2.2 | Decoder: field order | 1 | yes | 2 | Request decoder MUST emit field lines in encoded order. ✅ 2a: crates/h3/src/qpack/field_section.rs |
| 2.2.1 | Blocked decoding | 1 | yes | 2 | RIC smaller than expected is QPACK_DECOMPRESSION_FAILED. ✅ 2a: crates/h3/src/qpack/field_section.rs |
| 2.2.2.1 | Section Acknowledgment emission | 1 | no | Declined (optional: QPACK dynamic table) | Only after decoding dynamic-table references, which we reject (see 2.2.3); never emitted. |
| 2.2.3 | Invalid references | 2 | yes | 2 | Dynamic ref in field line -> QPACK_DECOMPRESSION_FAILED; encoder-instruction ref to evicted entry -> QPACK_ENCODER_STREAM_ERROR (at capacity 0 any such instruction is an error). ✅ 2a (field-line half): crates/h3/src/qpack/field_section.rs; ✅ 2a (encoder-instruction half): crates/h3/src/qpack/instructions.rs |
| 3.1 | Static table | 2 | yes | 2 | Invalid static index: QPACK_DECOMPRESSION_FAILED on request stream, QPACK_ENCODER_STREAM_ERROR on encoder stream. ✅ 2a (table + lookup): crates/h3/src/qpack/static_table.rs; ✅ 2a (request-stream index error): crates/h3/src/qpack/field_section.rs; ✅ 2a (encoder-stream half): crates/h3/src/qpack/instructions.rs |
| 3.2 | Dynamic table: duplicates | 1 | no | Declined (optional: QPACK dynamic table) | Duplicates not an error; no inserts are possible at capacity 0. |
| 3.2.2 | Capacity and eviction | 2 | partial | 2 | Encoder eviction rule is declined; decoder error rule binds. (summary; sub-rows carry status) |
| 3.2.2 (req) | Encoder must not evict non-evictable | 1 | no | Declined (optional: QPACK dynamic table) | "The encoder MUST NOT cause a dynamic table entry to be evicted unless that entry is evictable." |
| 3.2.2 (req) | Entry larger than capacity | 1 | yes | 2 | "the decoder MUST treat this as a connection error of type QPACK_ENCODER_STREAM_ERROR." At capacity 0 every Insert is oversized. ✅ 2a: crates/h3/src/qpack/instructions.rs |
| 3.2.3 | Maximum dynamic table capacity | 4 | partial | 2 | Mixed; see rows. (summary; sub-rows carry status) |
| 3.2.3 (req) | Encoder capacity <= maximum | 1 | no | Declined (optional: QPACK dynamic table) | "The encoder MUST NOT set a dynamic table capacity that exceeds this maximum" (we never send Set Capacity). |
| 3.2.3 (req) | Remembered non-zero value (0-RTT) | 1 | no | Declined (optional: 0-RTT) | "If the remembered value is non-zero, the server MUST send the same non-zero value in its SETTINGS frame." We never accept 0-RTT; advertised value is always 0. |
| 3.2.3 (req) | Capacity zero: no inserts, no encoder instructions | 2 | yes | 2 | "the encoder MUST NOT insert entries into the dynamic table and MUST NOT send any encoder instructions on the encoder stream." Binds our response encoder; we advertise 0. Encoder side holds by absence: this crate has no encoder-instruction serializer. ✅ 2a: crates/h3/src/qpack/instructions.rs |
| 4.1.1 | Prefixed integers | 1 | yes | 2 | Decode integers up to 62 bits (prefix-integer codec, distinct from QUIC varint). ✅ 2a: crates/h3/src/qpack/int.rs |
| 4.2 | Encoder and decoder streams | 6 | yes | 2 | One of each at most (second -> H3_STREAM_CREATION_ERROR); never close; closure -> H3_CLOSED_CRITICAL_STREAM; MUST accept peer-created QPACK streams even though capacity is 0. ✅ 2b (receive side): crates/h3/src/uni.rs; ✅ 2b (sender side: we open no QPACK streams; STOP_SENDING and RESET_STREAM only on request streams; a second peer encoder or decoder stream = H3_STREAM_CREATION_ERROR end to end, `uni_fed` over `uni_seen()`; peer QPACK stream reset = H3_CLOSED_CRITICAL_STREAM): crates/h3/src/conn.rs |
| 4.3.1 | Set Dynamic Table Capacity | 3 | partial | 2 | Mixed; see rows. (summary; sub-rows carry status) |
| 4.3.1 (req) | New capacity <= limit (sender) | 1 | no | Declined (optional: QPACK dynamic table) | "The new capacity MUST be lower than or equal to the limit described in Section 3.2.3." We never send it. |
| 4.3.1 (req) | Decoder rejects over-limit capacity | 1 | yes | 2 | "The decoder MUST treat a new dynamic table capacity value that exceeds this limit as a connection error of type QPACK_ENCODER_STREAM_ERROR." Any non-zero capacity is over our limit of 0. ✅ 2a: crates/h3/src/qpack/instructions.rs |
| 4.3.1 (req) | No eviction of non-evictable entries | 1 | no | Declined (optional: QPACK dynamic table) | "This MUST NOT cause the eviction of entries that are not evictable." |
| 4.4.1 | Section Acknowledgment received | 1 | yes | 2 | We send no dynamic refs, so any Section Acknowledgment is QPACK_DECODER_STREAM_ERROR. ✅ 2a: crates/h3/src/qpack/instructions.rs |
| 4.4.3 | Insert Count Increment received | 1 | yes | 2 | Increment of zero, or beyond what we sent (always 0 sent), is QPACK_DECODER_STREAM_ERROR. ✅ 2a: crates/h3/src/qpack/instructions.rs |
| 4.5.1.1 | Required Insert Count | 1 | yes | 2 | Unproducible EncodedInsertCount -> QPACK_DECOMPRESSION_FAILED. ✅ 2a: crates/h3/src/qpack/field_section.rs |
| 4.5.1.2 | Base | 2 | yes | 2 | Base MUST NOT be negative; Sign=1 invalid when RIC <= Delta Base (decoder check on request field sections). ✅ 2a: crates/h3/src/qpack/field_section.rs |
| 4.5.4 | Literal with name reference | 2 | partial | 2 | Decoder must accept N bit; forwarding rule below is intermediary-only. ✅ 2a: crates/h3/src/qpack/field_section.rs |
| 4.5.4 (req) | N-bit literal must be forwarded as literal | 1 | no | N/A (intermediary-only) | "when a peer sends a field line that it received represented as a literal field line with the 'N' bit set, it MUST use a literal representation to forward this field line." We are an origin server and never forward request fields, so the rule is read as not applying. Cheap to honor if a proxy mode is ever added. |
| 7.1.3 | Never-indexed literals | 3 | no | N/A (intermediary-only) | All three MUSTs govern intermediaries re-encoding fields ("An intermediary MUST NOT re-encode a value that uses a literal representation with the 'N' bit set..."). Origin server, never re-encodes received fields; read as not applying. |
| 7.4 | Implementation limits | 1 | yes | 2 | Value too large to decode: QPACK_DECOMPRESSION_FAILED (request stream) or appropriate connection error (encoder/decoder stream). A TooLarge value on a request stream is reported as QPACK_DECOMPRESSION_FAILED and escalated by the HTTP/3 layer to a connection error, as permitted by RFC 9114 §8 ("An endpoint MAY choose to treat a stream error as a connection error"). ✅ 2a (prefix ints): crates/h3/src/qpack/int.rs; ✅ 2a (string lengths): crates/h3/src/qpack/field_section.rs; ✅ 2a (encoder/decoder streams): crates/h3/src/qpack/instructions.rs |

Total keyword count: 44 across 22 sections.

## RFC 9000 — QUIC: A UDP-Based Multiplexed and Secure Transport

| § | Topic | #MUST/MUST NOT | Server applies? | Phase | Notes |
|---|---|---|---|---|---|
| 1.2 | Terms and Definitions (BCP 14 boilerplate) | 5 | no | N/A (boilerplate) | Keyword-definition boilerplate, not a requirement; no phase bucket fits, N/A used. |
| 2.1 | Stream types and identifiers | 1 | yes | 3 | Never reuse a stream ID. ✅ 3c: crates/quic/src/stream_id.rs |
| 2.2 | Sending and receiving data | 3 | yes | 3 | Ordered delivery; same data at same offset; respect peer flow limits. ✅ 3c: crates/quic/src/streams.rs (peer flow limits; ordered delivery in crates/quic/src/reassembly.rs and crates/quic/src/recv_stream.rs, unchanged retransmitted data in crates/quic/src/send_stream.rs) |
| 3.2 | Receiving stream states | 1 | yes | 3 | Opening stream N implicitly creates all lower-numbered streams of that type. ✅ 3c: crates/quic/src/streams.rs |
| 3.3 | Permitted frame types | 2 | yes | 3 | No frames from terminal states; no STREAM/STREAM_DATA_BLOCKED after RESET_STREAM. ✅ 3c: crates/quic/src/send_stream.rs |
| 3.5 | Solicited state transitions | 1 | yes | 3 | STOP_SENDING in Ready/Send must trigger RESET_STREAM. ✅ 3c: crates/quic/src/streams.rs |
| 4.1 | Data flow control | 3 | yes | 3 | Do not exceed limits; FLOW_CONTROL_ERROR on violation; ignore non-increasing MAX_DATA/MAX_STREAM_DATA. ✅ 3c: crates/quic/src/streams.rs (non-increasing limits ignored in crates/quic/src/flow.rs) |
| 4.2 | Increasing flow control limits | 1 | yes | 3 | Do not wait for *_BLOCKED before raising credit. ✅ 3c: crates/quic/src/streams.rs |
| 4.4 | Handling stream cancellation | 1 | yes | 3 | Keep flow control state until terminal. ✅ 3c: crates/quic/src/streams.rs |
| 4.5 | Stream final size | 2 | yes | 3 | Account final size in connection flow control; no data at/after final size. ✅ 3c: crates/quic/src/streams.rs |
| 4.6 | Controlling concurrency | 5 | yes | 3 | Stream limit > 2^60 is an error; STREAM_LIMIT_ERROR; ignore non-increasing MAX_STREAMS. ✅ 3c: crates/quic/src/stream_id.rs |
| 5.1 | Connection ID | 3 | yes | 3 | CIDs must not be correlatable by observers; no zero-length-CID port sharing (we issue non-zero CIDs). zero-length port-sharing MUST: exception: LOCAL_CID_LEN = 8. ✅ 3d: crates/quic/src/cid.rs |
| 5.1 (req) | Same CID not issued twice on a connection | 1 | yes | 3 | "the same connection ID MUST NOT be issued more than once on the same connection". ✅ 3d: crates/quic/src/cid.rs |
| 5.1.1 | Issuing connection IDs | 4 | yes | 3 | See req rows below. ✅ 3d: crates/quic/src/cid.rs |
| 5.1.1 (req) | Sequence number increases by 1 | 1 | yes | 3 | "The sequence number on each newly issued connection ID MUST increase by 1." ✅ 3d: crates/quic/src/cid.rs |
| 5.1.1 (req) | Accept issued CID until retired | 1 | yes | 3 | Must accept packets with an issued CID for the connection lifetime or until RETIRE_CONNECTION_ID. ✅ 3d: crates/quic/src/conn.rs + cid.rs + route.rs |
| 5.1.1 (req) | Do not exceed peer's active_connection_id_limit | 1 | yes | 3 | "MUST NOT provide more connection IDs than the peer's limit." ✅ 3d: crates/quic/src/cid.rs |
| 5.1.1 (req) | CONNECTION_ID_LIMIT_ERROR on excess active CIDs | 1 | yes | 3 | If active CIDs exceed our advertised active_connection_id_limit after processing NEW_CONNECTION_ID, close with CONNECTION_ID_LIMIT_ERROR. ✅ 3d: crates/quic/src/cid.rs |
| 5.1.2 | Consuming and retiring connection IDs | 2 | yes | 3 | Retire CIDs below increased Retire Prior To before activating new one; never forget a CID without retiring it. ✅ 3d: crates/quic/src/cid.rs |
| 5.2 | Matching packets to connections | 1 | yes | 3 | Error on bad packet content or fully revert changes. ✅ 3d: crates/quic/src/conn.rs |
| 5.2.1 | Client packet handling | 1 | no | N/A (client-only) | Client discards packets with a different version. |
| 5.2.2 | Server packet handling | 2 | yes | 3 | Drop smaller-than-1200 packets with unsupported version (no VN); drop all other unmatched packets. ✅ 3d: crates/quic/src/route.rs |
| 5.2.3 | Considerations for simple load balancers | 1 | yes | 3 | Conditional on simple LB deployment; avoid stateless reset oracle (see 21.11). ✅ 3d: route.rs (exception: never sends resets, no static key) |
| 6.1 | Sending Version Negotiation packets | 1 | yes | 3 | Never send VN in response to VN. ✅ 3b: crates/quic/src/stateless.rs |
| 6.2 | Handling Version Negotiation packets | 3 | no | N/A (client-only) | Client behavior. |
| 7 | Cryptographic and transport handshake | 2 | yes | 3 | Handshake properties and explicit ALPN negotiation; TLS-side mechanics land in phase 4. ✅ 3d: crates/quic/src/handshake.rs (ALPN here; handshake properties Phase 4 TLS) |
| 7.2 | Negotiating connection IDs | 6 | partial | 3 | Server rows below; 4 client-only MUSTs. ✅ 3d: crates/quic/src/handshake.rs |
| 7.2 (req) | Client DCID/SCID handling (DCID >= 8 bytes, keep same DCID, discard differing SCID, change DCID only on first Initial/Retry) | 4 | no | N/A (client-only) | Server only needs to accept a client's Initial DCID >= 8 bytes. |
| 7.2 (req) | Server sets DCID from first received Initial | 1 | yes | 3 | "A server MUST set the Destination Connection ID it uses for sending packets based on the first received Initial packet." ✅ 3d: crates/quic/src/handshake.rs |
| 7.2 (req) | Discard later Initial with different SCID | 1 | yes | 3 | Further DCID changes only via NEW_CONNECTION_ID. ✅ 3d: crates/quic/src/handshake.rs |
| 7.3 | Authenticating connection IDs | 4 | partial | 3 | Server rows below; client-side checks are client-only. ✅ 3d: crates/quic/src/handshake.rs |
| 7.3 (req) | Validate/send initial_source_connection_id; original_destination_connection_id sent by server | 3 | yes | 3 | Server sends correct values; validates client's initial_source_connection_id; absence is TRANSPORT_PARAMETER_ERROR. ✅ 3d: crates/quic/src/handshake.rs |
| 7.3 (req) | retry_source_connection_id presence/absence/mismatch checks | 1 | no | N/A (client-only) | Client check; server never sends Retry (declined) so never sends retry_source_connection_id. Client sending it is an error per 18.2. |
| 7.4 | Transport parameters | 2 | yes | 3 | Invalid value is TRANSPORT_PARAMETER_ERROR; each parameter at most once. ✅ 3b: crates/quic/src/tp.rs |
| 7.4.1 | Values of transport parameters for 0-RTT | 9 | partial | 3 | Mostly 0-RTT / client rows below. ✅ 3d: crates/quic/src/handshake.rs |
| 7.4.1 (req) | New-parameter 0-RTT storage rule | 1 | no | N/A (client-only) | Requirement on parameter definers, not an endpoint. |
| 7.4.1 (req) | Client remembered-parameter rules (do not use some remembered values, use server's new values, remember others, only remembered values in 0-RTT) | 5 | no | N/A (client-only) | Lines on client 0-RTT use (incl. the two MUSTs in the last sentence). |
| 7.4.1 (req) | Server accepting 0-RTT must not reduce limits or alter values | 2 | no | Declined (optional: 0-RTT) | We never accept 0-RTT. |
| 7.4.1 (req) | Server MUST reject 0-RTT if restored values unsupported | 1 | yes | 3 | Refusal path: we always reject 0-RTT. ✅ 3d: crates/quic/src/handshake.rs (exception: we never accept 0-RTT; no PacketKind, 3e drops, no early_data) |
| 7.4.2 | New transport parameters | 1 | yes | 3 | Ignore unknown transport parameters. ✅ 3b: crates/quic/src/tp.rs |
| 7.5 | Cryptographic message buffering | 3 | yes | 3 | Buffer >= 4096 bytes out-of-order CRYPTO; CRYPTO_BUFFER_EXCEEDED; ACK packets whose CRYPTO was discarded. ✅ 3c: crates/quic/src/crypto_stream.rs |
| 8 | Address validation | 1 | yes | 3 | 3x limit before validation; see 8.1 row. ✅ 3d: crates/quic/src/conn.rs |
| 8.1 | Address validation during connection establishment | 5 | partial | 3 | Server rows below; 3 client-only MUSTs. ✅ 3d: crates/quic/src/conn.rs |
| 8.1 (req) | Anti-amplification: send at most 3x bytes received before validation | 1 | yes | 3 | "Prior to validating the client address, servers MUST NOT send more than three times as many bytes as the number of bytes they have received." ✅ 3d: crates/quic/src/conn.rs |
| 8.1 (req) | Count payload bytes of datagrams attributable to one connection | 1 | yes | 3 | Servers MUST count all payload bytes received in datagrams uniquely attributed to a single connection. ✅ 3d: crates/quic/src/conn.rs |
| 8.1 (req) | Client pads Initial datagrams to 1200 | 1 | no | N/A (client-only) | Client behavior. |
| 8.1 (req) | Client sends packet on PTO to avoid deadlock | 1 | no | N/A (client-only) | Client behavior. |
| 8.1 (req) | Client Initial >= 1200 bytes if no Handshake keys, else Handshake packet | 1 | no | N/A (client-only) | Client behavior. |
| 8.1.1 | Token construction | 1 | no | Declined (optional: NEW_TOKEN issuance) | Tokens come only via Retry/NEW_TOKEN; we send neither. |
| 8.1.2 | Address validation using Retry packets | 1 | no | N/A (client-only) | Client repeats Retry token. |
| 8.1.3 | Address validation for future connections | 7 | partial | 3 | Rows below. ✅ 3d: crates/quic/src/handshake.rs |
| 8.1.3 (req) | Client token inclusion/reuse rules | 4 | no | N/A (client-only) | Client include token, no Retry token reuse, no inapplicable token, Retry token used immediately. |
| 8.1.3 (req) | NEW_TOKEN unlinkability and uniqueness | 2 | no | Declined (optional: NEW_TOKEN issuance) | We do not send NEW_TOKEN. |
| 8.1.3 (req) | Server MUST attempt to validate a token in Initial | 1 | yes | 3 | We issue no tokens, so any token fails validation; must still handle without erroring (invalid NEW_TOKEN token: proceed as unvalidated; Retry-style invalid: INVALID_TOKEN). ✅ 3d: crates/quic/src/handshake.rs |
| 8.1.4 | Address validation token integrity | 5 | no | Declined (optional: Retry) | Applies to tokens we issue; none issued. Anti-amplification still applies via 8.1. |
| 8.2.1 | Initiating path validation | 4 | yes | 3 | Server initiates validation of a peer's new address (not migration). ✅ 3d: crates/quic/src/conn.rs + path.rs |
| 8.2.1 (req) | Unpredictable PATH_CHALLENGE data | 1 | yes | 3 | RNG from shell. ✅ 3d: crates/quic/src/conn.rs + path.rs |
| 8.2.1 (req) | Expand PATH_CHALLENGE datagrams to 1200 unless anti-amplification forbids | 1 | yes | 3 | Padding rule. ✅ 3d: crates/quic/src/conn.rs + path.rs |
| 8.2.1 (req) | Second validation with 1200-byte datagram for MTU | 1 | yes | 3 | If first validation used a smaller datagram. ✅ 3d: crates/quic/src/conn.rs + path.rs |
| 8.2.1 (req) | Do NOT discard small datagrams carrying PATH_CHALLENGE/PATH_RESPONSE | 1 | yes | 3 | Exception to the 14.1 discard rule (Initial-only), watch interaction. ✅ 3d: crates/quic/src/conn.rs |
| 8.2.2 | Path validation responses | 7 | yes | 3 | Each requirement has its own row. ✅ 3d: crates/quic/src/conn.rs + path.rs |
| 8.2.2 (req) | Echo PATH_CHALLENGE data in PATH_RESPONSE | 1 | yes | 3 | "MUST respond by echoing the data contained in the PATH_CHALLENGE frame in a PATH_RESPONSE frame." Required even though we decline initiating migration. ✅ 3d: crates/quic/src/conn.rs + path.rs |
| 8.2.2 (req) | Do not delay PATH_RESPONSE packet except for congestion control | 1 | yes | 3 | ✅ 3d: crates/quic/src/conn.rs + path.rs |
| 8.2.2 (req) | PATH_RESPONSE sent on the path the PATH_CHALLENGE arrived on | 1 | yes | 3 | ✅ 3d: crates/quic/src/conn.rs + path.rs |
| 8.2.2 (req) | Initiator MUST NOT enforce same-path for responses | 1 | yes | 3 | Applies when we initiate validation (9.3.3 attack). ✅ 3d: crates/quic/src/conn.rs + path.rs |
| 8.2.2 (req) | Expand PATH_RESPONSE datagram to 1200 | 1 | yes | 3 | ✅ 3d: crates/quic/src/conn.rs + path.rs |
| 8.2.2 (req) | Do not expand PATH_RESPONSE past anti-amplification limit | 1 | yes | 3 | ✅ 3d: crates/quic/src/conn.rs + path.rs |
| 8.2.2 (req) | At most one PATH_RESPONSE per PATH_CHALLENGE | 1 | yes | 3 | See 13.3. ✅ 3d: crates/quic/src/conn.rs + path.rs |
| 8.2.3 | Successful path validation | 1 | yes | 3 | Re-validate with expanded datagram if MTU not yet confirmed. ✅ 3d: crates/quic/src/conn.rs + path.rs |
| 9 | Connection migration | 5 | partial | 3 | Rows below. ✅ 3d: crates/quic/src/conn.rs |
| 9 (req) | MUST NOT initiate migration before handshake confirmed | 1 | no | Declined (optional: connection migration) | We never initiate migration. |
| 9 (req) | disable_active_migration: no sends from different local address | 1 | no | Declined (optional: connection migration) | Parameter is server-sent; we never change local address. |
| 9 (req) | Peer violating disable_active_migration: drop without Stateless Reset or validate path | 1 | yes | 3 | We advertise disable_active_migration; choose drop or validate. ✅ 3d: crates/quic/src/conn.rs |
| 9 (req) | Path validation on any peer address change unless previously validated | 1 | yes | 3 | Includes NAT rebinding. ✅ 3d: crates/quic/src/conn.rs |
| 9 (req) | Client discards packets from unknown server address | 1 | no | N/A (client-only) |  |
| 9.3 | Responding to connection migration | 3 | yes | 3 | If we permit migration: send to new address and validate; protect against attacks while unvalidated. ✅ 3d: crates/quic/src/conn.rs |
| 9.3.2 | On-path address spoofing | 2 | yes | 3 | Revert to last validated address on failure; close silently if no such state. In every state before Closed: `next_timeout` names the validation deadlines in Closing and Draining too, and a revert in Closing sends the repeated CONNECTION_CLOSE to the validated address (final review I1, option (a)). ✅ 3d: crates/quic/src/conn.rs + path.rs |
| 9.3.3 | Off-path packet forwarding | 1 | yes | 3 | Validate previous path with PATH_CHALLENGE on apparent migration. ✅ 3d: crates/quic/src/conn.rs |
| 9.4 | Loss detection and congestion control | 3 | yes | 3 | Reset CC/RTT on new path (unless port-only change); hooks into phase 6 recovery. Port-only MAY not used; RTT/CC reset is Recovery::on_path_validated (placeholder until Phase 6); old-path clause open until Phase 6 (TRUSTED.md). ✅ 3d: crates/quic/src/conn.rs + path.rs |
| 9.5 | Privacy implications of connection migration | 2 | partial | 3 | Rows below. ✅ 3d: crates/quic/src/conn.rs |
| 9.5 (req) | Do not reuse CID from more than one local address | 1 | no | Declined (optional: connection migration) | Applies when initiating/probing. |
| 9.5 (req) | Do not reuse CID when sending to more than one destination address | 1 | yes | 3 | Applies when responding to a migrated peer. Proved per state (`wf_dcids`: at each send, a path sharing the CID has the same `peer_used`), not as a theorem over send history (TRUSTED.md); where only sharing could keep a path sending, the connection closes silently. ✅ 3d: crates/quic/src/conn.rs |
| 9.6.1 | Communicating a preferred address | 1 | no | N/A (client-only) | Client keeps using original address; we never advertise preferred_address. |
| 9.6.2 | Migration to a preferred address | 4 | no | Declined (optional: connection migration) | Client-only MUSTs are the rows below; server MUSTs apply only when advertising preferred_address, which we do not. |
| 9.6.2 (req) | Client validates the preferred address before migrating | 1 | no | N/A (client-only) | "A client that migrates to a preferred address MUST validate the address it chooses before migrating" |
| 9.6.2 (req) | Client does not reuse preferred addresses for other connections | 1 | no | N/A (client-only) | "A client MUST NOT use these for other connections, including connections that are resumed from the current connection." |
| 9.6.3 | Interaction of client migration and preferred address | 2 | no | Declined (optional: connection migration) | Client-only abandon rule is the row below; server protection rule only for preferred_address. |
| 9.6.3 (req) | Client abandons original-address validation once the preferred address validates | 1 | no | N/A (client-only) | "the client MUST abandon validation of the original address and migrate to using the server's preferred address" |
| 9.7 | Use of IPv6 flow label and migration | 1 | yes | 3 | Conditional on setting IPv6 flow labels; shell leaves kernel default. |
| 10.1 | Idle timeout | 1 | yes | 3 | Idle timeout at least 3x PTO. ✅ 3d: crates/quic/src/lifecycle.rs |
| 10.2.1 | Closing connection state | 2 | yes | 3 | Limit closing-state sends to 3x received / unvalidated address. Byte cap only; the rate SHOULD is not implemented. ✅ 3d: crates/quic/src/conn.rs |
| 10.2.2 | Draining connection state | 2 | yes | 3 | No packets sent while draining. ✅ 3d: crates/quic/src/conn.rs |
| 10.2.3 | Immediate close during the handshake | 3 | yes | 3 | 1-RTT CONNECTION_CLOSE once confirmed; 0x1d to 0x1c replacement; clear reason phrase. ✅ 3d: crates/quic/src/lifecycle.rs |
| 10.3 | Stateless reset | 5 | yes | 3 | CONNECTION_CLOSE if able; reset < 3x trigger; discard too-small packets; short header; any packet ending in valid token is a reset. Sending rows (short header, < 3x trigger) vacuous: we never send a Stateless Reset (sending is a MAY); Duvet exceptions in crates/quic/src/stateless.rs. ✅ 3d: crates/quic/src/conn.rs |
| 10.3.1 | Detecting a stateless reset | 4 | yes | 3 | Constant-time token comparison; only for used, unretired CIDs; enter draining. ✅ 3d: crates/quic/src/conn.rs |
| 10.3.2 | Calculating a stateless reset token | 5 | yes | 3 | Hard to guess; unique per CID; CID length handling; no CID reuse across static-key nodes. static-key MUSTs: exception (no static key, tokens are fresh randomness). ✅ 3d: crates/quic/src/cid.rs |
| 10.3.3 | Looping | 1 | yes | 3 | Reset must be smaller than trigger. ✅ 3b: exception — we never send a Stateless Reset (stateless.rs) |
| 11 | Error handling | 1 | yes | 3 | No stateless reset if connection state exists. ✅ 3d: exception — no stateless reset is ever sent |
| 11.1 | Connection errors | 1 | yes | 3 | Fatal errors via CONNECTION_CLOSE. ✅ 3d: crates/quic/src/conn.rs |
| 11.2 | Stream errors | 1 | yes | 3 | RESET_STREAM only instigated by the application (HTTP/3 layer). ✅ 3c: crates/quic/src/streams.rs |
| 12.2 | Coalescing packets | 4 | yes | 3 | Process coalesced packets; same CID within datagram; ack separately. ✅ 3d: crates/quic/src/conn.rs |
| 12.3 | Packet numbers | 5 | yes | 3 | Monotonic, never reused, 2^62-1 limit closes silently, duplicate suppression after decryption. ✅ 3d: conn.rs + sent.rs/ack_track.rs |
| 12.4 | Frames and frame types | 5 | yes | 3 | Rows for frame-type encoding below; no-frame packet and disallowed frame are PROTOCOL_VIOLATION; unknown frame FRAME_ENCODING_ERROR. ✅ 3b: crates/quic/src/payload.rs |
| 12.4 (req) | Frame type MUST use shortest possible encoding | 1 | yes | 3 | "a frame type MUST use the shortest possible encoding"; sender must emit minimal type varint; receiver should reject non-minimal (relies on phase 1 minimal-encoding decision for varint). ✅ 3b: crates/quic/src/frame.rs |
| 12.5 | Frames and number spaces | 2 | yes | 3 | Frame/space restrictions (0x1d only in application space). ✅ 3b: crates/quic/src/payload.rs |
| 13.1 | Packet processing | 1 | yes | 3 | ACK only after decryption and full frame processing. ✅ 3d: crates/quic/src/conn.rs |
| 13.2.1 | Sending ACK frames | 5 | yes | 3 | Immediate ACK for Initial/Handshake; max_ack_delay; one ACK-only packet per ack-eliciting; no feedback loops. ✅ 3d: conn.rs + sent.rs/ack_track.rs |
| 13.2.3 | Managing ACK ranges | 2 | yes | 3 | Retain ranges; retain largest PN. ✅ 3d: crates/quic/src/ack_track.rs |
| 13.2.5 | Measuring and reporting host delay | 1 | yes | 3 | Exclude delays not under endpoint control. ✅ 3d: crates/quic/src/ack_track.rs |
| 13.2.6 | ACK frames and packet protection | 3 | yes | 3 | Same-space ACK; 0-RTT-ack rule vacuous (we reject 0-RTT). ✅ 3d: crates/quic/src/conn.rs |
| 13.3 | Retransmission of information | 4 | yes | 3 | RESET_STREAM unchanged; HANDSHAKE_DONE retransmitted; accept outdated frames; congestion action on loss. ✅ 3d: crates/quic/src/conn.rs (retransmission routing) + recovery.rs (AIMD placeholder congestion action, Phase 6 replaces) |
| 13.4.1 | Reporting ECN counts | 1 | yes | 3 | Provide ECN feedback if accessible; needs IP_RECVTOS in shell (otherwise relies on "if accessible"). ✅ 3d: exception — ECN not accessible, no ECT set (ack_track.rs ecn: None) |
| 13.4.2.1 | Receiving ACK frames with ECN counts | 1 | yes | 3 | Only if we send ECT; vacuous otherwise. ✅ 3d: exception — ECN not accessible, no ECT set (ack_track.rs ecn: None) |
| 13.4.2.2 | ECN validation outcomes | 2 | yes | 3 | Only if we send ECT; vacuous otherwise. ✅ 3d: exception — ECN not accessible, no ECT set (ack_track.rs ecn: None) |
| 14 | Datagram size | 4 | yes | 3 | 1200-byte minimum path; no IP fragmentation; DF where possible; never close on bad-size datagram. |
| 14.1 | Initial datagram size | 4 | partial | 3 | Server rows below; client padding is client-only. ✅ 3d: crates/quic/src/conn.rs |
| 14.1 (req) | Client expands Initial datagrams to 1200 | 1 | no | N/A (client-only) |  |
| 14.1 (req) | Server expands ack-eliciting Initial datagrams to 1200 | 1 | yes | 3 | ✅ 3d: crates/quic/src/conn.rs |
| 14.1 (req) | Server discards Initial in datagram < 1200 bytes | 1 | yes | 3 | "A server MUST discard an Initial packet that is carried in a UDP datagram with a payload that is smaller than ... 1200 bytes." Do not close the connection (see 14). ✅ 3d: crates/quic/src/conn.rs |
| 14.1 (req) | Server limits bytes sent before address validation | 1 | yes | 3 | See 8.1 3x row. ✅ 3d: crates/quic/src/conn.rs |
| 14.2 | Path maximum transmission unit | 1 | yes | 3 | Cease sending if PMTU < 1200 (except probes/CONNECTION_CLOSE). ✅ 3d: crates/quic/src/conn.rs (P17 send gate) + path.rs (mtu_failed) |
| 14.2.1 | Handling of ICMP messages by PMTUD | 3 | yes | 3 | Only if shell processes ICMP; vacuous otherwise. |
| 17.1 | Packet number encoding and decoding | 2 | yes | 3 | Full PN before first ACK; size covers > 2x range. ✅ 3b: crates/quic/src/pn.rs; A.2 pseudocode under-sizes at exact powers of two; §17.1 prose used. Decoding is A.3 (`decode_pn`, result <= PN_MAX); `theorem_pn_len_decodes` proves a `pn_len_ok` length decodes back at a receiver that has seen the acknowledged packet; `pn_encode_len` None (more than 2^31 unacked) is a 3d internal limit |
| 17.2 | Long header packets | 7 | yes | 3 | Fixed bit; CID length <= 20 (drop); reserved bits PROTOCOL_VIOLATION. 3b codec: crates/quic/src/header.rs (closed in 3e) |
| 17.2.1 | Version Negotiation packet | 6 | partial | 3 | Server rows are phase 3; one client-only. ✅ 3b: crates/quic/src/stateless.rs |
| 17.2.1 (req) | Client ignores Unused field | 1 | no | N/A (client-only) |  |
| 17.2.1 (req) | VN: Version 0, CIDs echoed, no version-specific CID influence, one VN per datagram | 5 | yes | 3 | Includes DCID from client SCID, SCID from client DCID, at most one VN per datagram. ✅ 3b: crates/quic/src/stateless.rs (caller binding: 3d route) |
| 17.2.2 | Initial packet | 2 | partial | 3 | Server sends Token Length 0 (no tokens issued); client discard is client-only. ✅ 3b: crates/quic/src/header.rs (server Token Length 0) |
| 17.2.3 | 0-RTT | 3 | partial | 3 | Two client-only MUSTs; ack-in-1-RTT rule applies. ✅ 3d: crates/quic/src/conn.rs |
| 17.2.3 (req) | New PNs; client stops 0-RTT once 1-RTT processed | 2 | no | N/A (client-only) |  |
| 17.2.3 (req) | ACK for a 1-RTT packet MUST be in a 1-RTT packet | 1 | yes | 3 | ✅ 3d: crates/quic/src/conn.rs |
| 17.2.4 | Handshake packet | 1 | yes | 3 | Handshake packet with disallowed frames is PROTOCOL_VIOLATION. ✅ 3b: crates/quic/src/payload.rs |
| 17.2.5 | Retry packet | 1 | no | N/A (client-only) | Client ignores Unused bits. |
| 17.2.5.1 | Sending a Retry packet | 4 | no | Declined (optional: Retry) | Server MUSTs (SCID differs, at most one Retry) not applicable; 2 client rows client-only. |
| 17.2.5.2 | Handling a Retry packet | 5 | no | N/A (client-only) |  |
| 17.2.5.3 | Continuing a handshake after Retry | 2 | no | N/A (client-only) |  |
| 17.3.1 | 1-RTT packet | 3 | yes | 3 | Fixed bit; reserved bits PROTOCOL_VIOLATION. 3b codec: crates/quic/src/header.rs (closed in 3e) |
| 17.4 | Latency spin bit | 4 | yes | 3 | Simplest compliance: not support it and keep it disabled (set arbitrary, ignore incoming). ✅ 3b: crates/quic/src/header.rs; spin bit unsupported, so always disabled: serializer takes a caller-chosen `spin` (RECOMMENDED random per packet or per CID, supplied by 3e), never read on parse; no admin switch is needed for a feature that cannot be enabled |
| 18.2 | Transport parameter definitions | 9 | partial | 3 | Rows below. ✅ 3b: crates/quic/src/tp.rs |
| 18.2 (req) | stateless_reset_token not sent by clients | 1 | yes | 3 | Server sends it; receipt from a client is an error (see server-only row). ✅ 3b: crates/quic/src/tp.rs |
| 18.2 (req) | preferred_address receiver rules (no new local address toward handshake address) | 1 | no | N/A (client-only) | Sent only by servers; receiver is a client. |
| 18.2 (req) | Server with zero-length CID MUST NOT give preferred_address, nor zero-length CID in it | 2 | no | Declined (optional: connection migration) | We never send preferred_address. |
| 18.2 (req) | Client treats preferred_address violations as TRANSPORT_PARAMETER_ERROR | 1 | no | N/A (client-only) |  |
| 18.2 (req) | active_connection_id_limit MUST be at least 2 (our advertised value) | 1 | yes | 3 | We advertise >= 2. ✅ 3b: crates/quic/src/tp.rs |
| 18.2 (req) | Receiving active_connection_id_limit < 2 is TRANSPORT_PARAMETER_ERROR | 1 | yes | 3 | ✅ 3b: crates/quic/src/tp.rs |
| 18.2 (req) | Client MUST NOT include server-only parameters | 1 | no | N/A (client-only) | Client obligation. |
| 18.2 (req) | Server treats receipt of server-only parameter as TRANSPORT_PARAMETER_ERROR | 1 | yes | 3 | original_destination_connection_id, preferred_address, retry_source_connection_id, stateless_reset_token. ✅ 3b: crates/quic/src/tp.rs |
| 19.3 | ACK frames | 1 | yes | 3 | Handle both ACK types (with/without ECN). ✅ 3b: crates/quic/src/ack.rs |
| 19.3.1 | ACK ranges | 1 | yes | 3 | Negative computed PN is FRAME_ENCODING_ERROR. ✅ 3b: crates/quic/src/ack.rs |
| 19.4 | RESET_STREAM frames | 1 | yes | 3 | STREAM_STATE_ERROR for send-only stream. ✅ 3c: crates/quic/src/streams.rs |
| 19.5 | STOP_SENDING frames | 2 | yes | 3 | STREAM_STATE_ERROR cases. ✅ 3c: crates/quic/src/streams.rs |
| 19.6 | CRYPTO frames | 1 | yes | 3 | Offset limit error. ✅ 3b: crates/quic/src/frame.rs |
| 19.7 | NEW_TOKEN frames | 4 | partial | 3 | Server row below; others client-only/declined. ✅ 3b: crates/quic/src/frame.rs |
| 19.7 (req) | Token MUST NOT be empty | 1 | no | Declined (optional: NEW_TOKEN issuance) | Sender rule; we never send NEW_TOKEN. |
| 19.7 (req) | Client empty-token error; clients MUST NOT send NEW_TOKEN | 2 | no | N/A (client-only) |  |
| 19.7 (req) | Server treats receipt of NEW_TOKEN as PROTOCOL_VIOLATION | 1 | yes | 3 | ✅ 3b: crates/quic/src/frame.rs |
| 19.8 | STREAM frames | 2 | yes | 3 | STREAM_STATE_ERROR; offset/length limit. ✅ 3c: crates/quic/src/streams.rs |
| 19.9 | MAX_DATA frames | 2 | yes | 3 | FLOW_CONTROL_ERROR on excess. ✅ 3c: crates/quic/src/streams.rs |
| 19.10 | MAX_STREAM_DATA frames | 4 | yes | 3 | ✅ 3c: crates/quic/src/streams.rs |
| 19.11 | MAX_STREAMS frames | 4 | yes | 3 | ✅ 3c: crates/quic/src/stream_id.rs |
| 19.13 | STREAM_DATA_BLOCKED frames | 1 | yes | 3 | ✅ 3c: crates/quic/src/streams.rs |
| 19.14 | STREAMS_BLOCKED frames | 1 | yes | 3 | ✅ 3b: crates/quic/src/frame.rs |
| 19.15 | NEW_CONNECTION_ID frames | 8 | yes | 3 | Each requirement has its own row. ✅ 3d: crates/quic/src/cid.rs |
| 19.15 (req) | Length < 1 or > 20 is FRAME_ENCODING_ERROR | 1 | yes | 3 | ✅ 3b: crates/quic/src/frame.rs |
| 19.15 (req) | MUST NOT send if peer requires zero-length DCID | 1 | yes | 3 | exception: LOCAL_CID_LEN = 8. ✅ 3d: crates/quic/src/cid.rs |
| 19.15 (req) | Zero-length-DCID sender receiving NEW_CONNECTION_ID is PROTOCOL_VIOLATION | 1 | yes | 3 | ✅ 3d: crates/quic/src/cid.rs |
| 19.15 (req) | Duplicate frame not a connection error | 1 | yes | 3 | ✅ 3d: crates/quic/src/cid.rs |
| 19.15 (req) | Retire Prior To <= Sequence Number (sending) | 1 | yes | 3 | ✅ 3b: crates/quic/src/frame.rs |
| 19.15 (req) | Retire Prior To > Sequence Number received is FRAME_ENCODING_ERROR | 1 | yes | 3 | ✅ 3b: crates/quic/src/frame.rs |
| 19.15 (req) | Ignore non-increasing Retire Prior To | 1 | yes | 3 | ✅ 3d: crates/quic/src/cid.rs |
| 19.15 (req) | Send RETIRE_CONNECTION_ID for sequence below earlier Retire Prior To | 1 | yes | 3 | ✅ 3d: crates/quic/src/cid.rs |
| 19.16 | RETIRE_CONNECTION_ID frames | 3 | yes | 3 | Each requirement has its own row. ✅ 3d: crates/quic/src/cid.rs |
| 19.16 (req) | Sequence number greater than any sent is PROTOCOL_VIOLATION | 1 | yes | 3 | ✅ 3d: crates/quic/src/cid.rs |
| 19.16 (req) | Sequence MUST NOT refer to the packet's own DCID | 1 | yes | 3 | ✅ 3d: crates/quic/src/cid.rs |
| 19.16 (req) | Zero-length-CID provider receiving RETIRE_CONNECTION_ID is PROTOCOL_VIOLATION | 1 | yes | 3 | exception: LOCAL_CID_LEN = 8. ✅ 3d: crates/quic/src/cid.rs |
| 19.17 | PATH_CHALLENGE frames | 1 | yes | 3 | Recipient MUST generate PATH_RESPONSE with same data (see 8.2.2 rows). Owed responses capped at MAX_RESPONSES (4) per path; further challenges are dropped until responses go out (the peer retransmits). ✅ 3d: crates/quic/src/path.rs |
| 19.20 | HANDSHAKE_DONE frames | 2 | yes | 3 | Server sends only after handshake complete; receipt is PROTOCOL_VIOLATION. ✅ 3d: crates/quic/src/conn.rs |
| 19.21 | Extension frames | 3 | no | Declined (optional: HTTP/3 extensions) | Applies only to endpoints using extension frames; unknown frame handling is in 12.4. |
| 21.5 | Request forgery attacks | 1 | no | N/A (binds spec authors) | Requirement on future extensions, not an endpoint. |
| 21.5.3 | Request forgery with preferred addresses | 1 | no | N/A (client-only) | Client must not send non-probing frames to unvalidated preferred address. |
| 21.11 | Stateless reset oracle | 2 | yes | 3 | No reset for CIDs possibly active elsewhere with same static key. ✅ 3d: route.rs (exception: never sends resets, no static key) |
| 21.12 | Version downgrade | 1 | no | N/A (binds spec authors) | Requirement on future versions, not an endpoint. |
| 22.1.2 | Selecting codepoints | 1 | no | N/A (IANA procedure) | IANA procedure, not an endpoint requirement. |
| 22.1.3 | Reclaiming provisional codepoints | 3 | no | N/A (IANA procedure) | IANA procedure. |
| 22.1.4 | Permanent registrations | 1 | no | N/A (IANA procedure) | IANA procedure. |
| 22.2 | QUIC versions registry | 2 | no | N/A (IANA procedure) | IANA procedure. |
| 22.3 | QUIC transport parameters registry | 3 | no | N/A (IANA procedure) | IANA procedure. |
| 22.4 | QUIC frame types registry | 1 | no | N/A (IANA procedure) | IANA procedure. |
| 22.5 | QUIC transport error codes registry | 1 | no | N/A (IANA procedure) | IANA procedure. |

Total keyword count: 307 across 115 sections.

## RFC 9001 — Using TLS to Secure QUIC

| § | Topic | #MUST/MUST NOT | Server applies? | Phase | Notes |
|---|---|---|---|---|---|
| 4 | Carrying TLS Messages | 1 | yes | 4 | Retransmitted CRYPTO data MUST use the same keys as the original, even after TLS moves to newer keys. |
| 4.1.2 | Handshake Confirmed | 1 | yes | 4 | Server MUST send HANDSHAKE_DONE as soon as the handshake completes. 4b: crates/tls/src/server.rs: `TlsEvent::Complete` / `is_complete()` (closed in 4c) |
| 4.1.3 | Sending and Receiving Handshake Messages | 3 | yes | 4 | CRYPTO data from an earlier level MUST NOT extend past previously received data (PROTOCOL_VIOLATION); unconsumed lower-level data when higher-level keys arrive is PROTOCOL_VIOLATION. 4b: crates/tls/src/server.rs: `pending(level)` for the data TLS has not consumed; 4c checks CRYPTO offsets per level before `on_crypto`, which returns 0x10a for new data at a finished level (closed in 4c) |
| 4.2 | TLS Version | 2 | partial | 4 | Server only negotiates 1.3, so the "terminate if older than 1.3 is negotiated" rule holds by construction; ✅ 4a: crates/tls/src/client_hello.rs + server_msgs.rs |
| 4.2 (req) | Clients MUST NOT offer TLS older than 1.3 | 1 | no | N/A (client-only) | "Clients MUST NOT offer TLS versions older than 1.3." |
| 4.4 | Peer Authentication | 4 | partial | 4 | Server MUST NOT use post-handshake client auth and MUST NOT send post-handshake CertificateRequest. We never request client certificates at all; ✅ 4a: crates/tls/src/server_msgs.rs |
| 4.4 (req) | Client authenticates server | 1 | no | N/A (client-only) | "A client MUST authenticate the identity of the server." |
| 4.4 (req) | Client reaction to post-handshake CertificateRequest | 1 | no | N/A (client-only) | "clients MUST treat receipt of such messages as a connection error of type PROTOCOL_VIOLATION." |
| 4.6.1 | Enabling 0-RTT | 2 | no | Declined (optional: 0-RTT) | Server MUST NOT send early_data in NewSessionTicket with max_early_data_size other than 0xffffffff. We send no NewSessionTicket and no early_data (EncryptedExtensions has none), so this holds vacuously. |
| 4.6.1 (req) | Client treatment of bad early_data in NewSessionTicket | 1 | no | N/A (client-only) | "A client MUST treat receipt of a NewSessionTicket that contains an early_data extension with any other value as a connection error of type PROTOCOL_VIOLATION." |
| 4.6.2 | Accepting and Rejecting 0-RTT | 2 | partial | 4 | "When rejecting 0-RTT, a server MUST NOT process any 0-RTT packets, even if it could." We always reject: discard all 0-RTT packets. |
| 4.6.2 (req) | Client resets stream state on rejection | 1 | no | N/A (client-only) | "The client therefore MUST reset the state of all streams, including application state bound to those streams." |
| 4.8 | TLS Errors | 1 | yes | 4 | Any TLS alert MUST be treated as fatal. 4b: crates/tls/src/server.rs: every TLS failure is `CRYPTO_ERROR_BASE + AlertDescription` (closed in 4c) |
| 4.9 | Discarding Unused Keys | 2 | yes | 4 | CRYPTO retransmissions MUST be sent at the same encryption level as the original; new data MUST be sent at the highest available level. |
| 4.9.1 | Discarding Initial Keys | 3 | partial | 4 | Server MUST discard Initial keys when it first successfully processes a Handshake packet; endpoints MUST NOT send Initial packets after that. |
| 4.9.1 (req) | Client discards Initial keys | 1 | no | N/A (client-only) | "a client MUST discard Initial keys when it first sends a Handshake packet" |
| 4.9.2 | Discarding Handshake Keys | 1 | yes | 4 | Handshake keys MUST be discarded when the handshake is confirmed (server: when it completes). |
| 4.9.3 | Discarding 0-RTT Keys | 1 | yes | 4 | "servers MUST discard 0-RTT keys within a short time" after a 1-RTT packet. We never derive 0-RTT keys, so vacuous. |
| 5.1 | Packet Protection Keys | 1 | no | N/A (binds spec authors) | "Other versions of TLS MUST provide a similar function in order to be used with QUIC." Requirement on specs for other TLS versions; we implement TLS 1.3 only, so it does not apply to an implementation. |
| 5.2 | Initial Secrets | 1 | yes | 4 | HKDF-Expand-Label from TLS 1.3 MUST be used for Initial packets. The HKDF primitive itself is Phase 5. |
| 5.3 | AEAD Usage | 3 | yes | 4 | Cipher suite MUST NOT be negotiated without a header protection scheme (we offer only AES-128-GCM); MUST NOT reject a ClientHello offering unsupported suites; MUST initiate key update before exceeding AEAD limits (see 6.6). |
| 5.4.1 | Header Protection Application | 1 | yes | 3 | A header protection algorithm MUST be specified for each AEAD; we use the AES-128 HP defined in §5.4.3. ✅ 3e: crates/quic/src/hp.rs (AES-128 HP per §5.4.3, the HP of our only AEAD) |
| 5.4.2 | Header Protection Sample | 1 | yes | 4 | Endpoint MUST discard packets too short to contain a complete sample. |
| 5.5 | Receiving Protected Packets | 2 | yes | 4 | Discard higher-numbered packets that cannot be unprotected with the same or a subsequent key; discard packets that appear to trigger a key update but fail to unprotect. |
| 5.6 | Use of 0-RTT Keys | 6 | partial | 4 | Server MUST NOT use 0-RTT keys to protect packets (never has them). Remaining rules are client-side or application profile. |
| 5.6 (req) | Client 0-RTT use policy | 1 | no | N/A (client-only) | "A client therefore MUST NOT use 0-RTT for application data unless specifically requested by the application" |
| 5.6 (req) | Application protocol 0-RTT profile | 1 | no | Declined (optional: 0-RTT) | "An application protocol that uses QUIC MUST include a profile that defines acceptable use of 0-RTT" Applies to the application protocol spec (HTTP/3), not enforced by an implementation that has no 0-RTT. |
| 5.6 (req) | Client MUST NOT decrypt 0-RTT it receives | 2 | no | N/A (client-only) | "A client MUST NOT attempt to decrypt 0-RTT packets it receives and instead MUST discard them." |
| 5.6 (req) | Client stops 0-RTT once 1-RTT installed | 1 | no | N/A (client-only) | "Once a client has installed 1-RTT keys, it MUST NOT send any more 0-RTT packets." |
| 5.7 | Receiving Out-of-Order Protected Packets | 3 | partial | 4 | Endpoints MUST NOT decrypt 1-RTT packets before the handshake completes; server MUST NOT process incoming 1-RTT packets before the TLS handshake is complete (buffer or drop; no ACKs for them). |
| 5.7 (req) | Client MUST NOT process 1-RTT before handshake complete | 1 | no | N/A (client-only) | "a client MUST NOT process incoming 1-RTT protected packets before the TLS handshake is complete." |
| 6 | Key Update | 2 | yes | 4 | Endpoints MUST NOT send a TLS KeyUpdate message and MUST treat receipt as connection error 0x010a (unexpected_message). ✅ 4b: crates/tls/src/server.rs (no KeyUpdate serializer; a KeyUpdate at Handshake or 1-RTT is 0x10a) |
| 6.1 | Initiating a Key Update | 3 | yes | 4 | MUST NOT initiate before handshake confirmed; MUST NOT initiate again until an ACK for a packet in the current phase; MUST retain old receive keys until a packet with the new keys is unprotected. |
| 6.2 | Responding to a Key Update | 2 | yes | 4 | Peer-initiated update MUST be answered by updating send keys, before sending an ACK for the triggering packet. |
| 6.3 | Timing of Receive Key Generation | 2 | yes | 4 | MUST be able to retain two sets of receive keys (current and next). The MUST NOT on timing side channels is a known gap: constant-time execution is a non-goal in the design spec. Phase 7a's dudect-style tests time crypto primitives only, not key update. |
| 6.4 | Sending with Updated Keys | 2 | yes | 4 | Higher packet numbers MUST use same or newer keys; successfully removing old-key protection from a packet after newer-key packets with lower numbers is KEY_UPDATE_ERROR. |
| 6.6 | Limits on AEAD Usage | 8 | partial | 4 | Count encrypted packets per key and failed-authentication packets per connection; initiate key update before the AES-128-GCM confidentiality limit; on integrity limit close with AEAD_LIMIT_REACHED. If no key update is possible, stop and only send stateless resets (stateless reset itself is Phase 3). |
| 6.6 (req) | Cipher suite specs MUST define AEAD limits | 2 | no | N/A (binds spec authors) | "Any TLS cipher suite that is specified for use with QUIC MUST define limits..." Requirement on specification authors; AES-128-GCM limits are already in §6.6. |
| 8.1 | Protocol Negotiation | 6 | partial | 4 | MUST use ALPN (`h3`); MUST close with no_application_protocol (0x0178) if none negotiated; MUST select a protocol compatible with the QUIC version ✅ 4b: crates/tls/src/negotiate.rs (checked at ClientHello, before any HRR; ALPN grammar in crates/tls/src/client_hello.rs, 4a) |
| 8.1 (req) | Client uses 0x0178 on ALPN failure | 2 | no | N/A (client-only) | "QUIC clients MUST use error 0x0178 to terminate a connection when ALPN negotiation fails"; "a client MUST treat the selection of an incompatible application protocol by a server as a connection error of type 0x0178". |
| 8.2 | QUIC Transport Parameters Extension | 4 | yes | 4 | Server MUST send quic_transport_parameters in EncryptedExtensions and MUST close with 0x016d if ClientHello lacks it. MUST NOT send / MUST alert unsupported_extension for non-QUIC TLS: vacuous, our TLS only runs under QUIC; ✅ 4a: crates/tls/src/client_hello.rs + server_msgs.rs |
| 8.3 | Removing the EndOfEarlyData Message | 2 | partial | 4 | "A server MUST treat receipt of a CRYPTO frame in a 0-RTT packet as a connection error of type PROTOCOL_VIOLATION." We discard 0-RTT packets unprocessed. |
| 8.3 (req) | Clients MUST NOT send EndOfEarlyData | 1 | no | N/A (client-only) | "Clients MUST NOT send the EndOfEarlyData message." |
| 8.4 | Prohibit TLS Middlebox Compatibility Mode | 1 | no | N/A (client-only) | "A client MUST NOT request the use of the TLS 1.3 compatibility mode." The server-side rule is a SHOULD; server SHOULD taken: non-empty legacy_session_id → PROTOCOL_VIOLATION (crates/tls/src/client_hello.rs, 4a) |
| 9.2 | Replay Attacks with 0-RTT | 6 | no | Declined (optional: 0-RTT) | Replay protections, ticket/token opacity and application 0-RTT descriptions only matter when 0-RTT is accepted. We never accept it, issue no tickets and no tokens. |
| 9.2 (req) | QUIC extensions / application protocols describe replay handling | 2 | no | N/A (binds spec authors) | "QUIC extensions MUST either describe how replay attacks affect their operation or prohibit the use of the extension in 0-RTT." Requirement on specification authors. |
| 9.3 | Packet Reflection Attack Mitigation | 1 | no | N/A (client-only) | "the packet containing a ClientHello MUST be padded to a minimum size." Client sends it; server-side enforcement (drop Initial datagrams under 1200 bytes, 3x limit) is RFC 9000 §14.1/§8.1, Phase 3. |
| 9.4 | Header Protection Analysis | 1 | no | N/A (binds spec authors) | "Future header protection variants based on this construction MUST use a PRF." Requirement on future specs; AES-ECB (§5.4.3) is the PRF here. |
| 9.5 | Header Protection Timing Side Channels | 2 | yes | 4 | HP removal, PN recovery and unprotect MUST be applied together without timing side channels, and sending MUST not leak PN or encoded size. Known gap: constant-time is a non-goal (unverified check later); crypto primitives in Phase 5 follow constant-time style. |
| 2 | Notational Conventions | 5 | no | N/A (boilerplate) | BCP 14 boilerplate listing the keywords; not a requirement. (The extraction omitted this row; added so totals match the raw grep.) |

Total keyword count: 88 across 35 sections.

## RFC 9002 — QUIC Loss Detection and Congestion Control

| § | Topic | #MUST/MUST NOT | Server applies? | Phase | Notes |
|---|---|---|---|---|---|
| 5.1 | Generating RTT samples | 1 | yes | 6 | MUST NOT generate an RTT sample on an ACK that does not newly acknowledge at least one ack-eliciting packet. |
| 5.2 | Estimating min_rtt | 2 | yes | 6 | min_rtt set to latest_rtt on first sample; otherwise min(min_rtt, latest_rtt). |
| 5.3 | smoothed_rtt and rttvar | 2 | yes | 6 | Use lesser of ack delay and peer max_ack_delay after handshake confirmed; MUST NOT subtract ack delay if result < min_rtt. |
| 6.1.2 | Time threshold | 1 | yes | 6 | Time threshold MUST be at least kGranularity. |
| 6.2 | Probe timeout | 1 | yes | 6 | PTO expiry MUST NOT mark prior unacked packets lost. |
| 6.2.1 | Computing PTO | 5 | yes | 6 | PTO period >= kGranularity; earlier of Initial/Handshake timer when both in flight; MUST NOT set Application Data PTO until handshake confirmed; backoff doubles on PTO expiry; PTO MUST NOT be set while time-threshold loss timer is set. |
| 6.2.2 | Handshakes and new paths | 1 | yes | 6 | Loss detection and PTO timers MUST be reset when Initial/Handshake keys are discarded. |
| 6.2.2.1 | Before address validation | 4 | partial | 6 | Server rows below; client row split out. Server MUST NOT arm PTO when amplification-blocked: interplay with RFC 9000 §8.1 anti-amplification (Phase 3); Phase 6 recovery must consult the Phase 3 limit. |
| 6.2.2.1 (req) | Server PTO not armed when amplification-limited | 1 | yes | 6 | "If no additional data can be sent, the server's PTO timer MUST NOT be armed until datagrams have been received from the client". Cross-ref RFC 9000 §8.1 (Phase 3): the 3x limit is owned by Phase 3; PTO probes count against it and nothing may be sent beyond it. |
| 6.2.2.1 (req) | Client sets PTO until Handshake ACKed | 1 | no | N/A (client-only) | "the client MUST set the PTO timer if the client has not received an acknowledgment for any of its Handshake packets and the handshake is not confirmed". |
| 6.2.2.1 (req) | Client PTO probe contents | 2 | no | N/A (client-only) | "the client MUST send a Handshake packet if it has Handshake keys, otherwise it MUST send an Initial packet in a UDP datagram with a payload of at least 1200 bytes". |
| 6.2.4 | Sending probe packets | 2 | yes | 6 | On PTO send at least one ack-eliciting packet; all PTO probes ack-eliciting. Probes sent by a server before address validation count against RFC 9000 §8.1 limit (Phase 3). |
| 6.4 | Discarding keys and packet state | 2 | yes | 6 | Discard recovery state for Initial/Handshake packets and remove them from bytes_in_flight when keys are discarded. |
| 7 | Congestion control | 2 | yes | 6 | Alternate controller MUST follow RFC 8085 §3.1 (satisfied by implementing NewReno as specified); MUST NOT send if bytes_in_flight would exceed cwnd, except PTO probes; the key proof invariant. |
| 7.3.1 | Slow start | 1 | yes | 6 | MUST exit slow start and enter recovery on loss or increase in ECN-CE count (server need not use ECN; loss path required). |
| 7.3.2 | Recovery | 2 | yes | 6 | On entering recovery set ssthresh to half cwnd; cwnd set to reduced ssthresh before exiting recovery. |
| 7.3.3 | Congestion avoidance | 1 | yes | 6 | cwnd increase limited to at most one max datagram size per cwnd acknowledged. |
| 7.4 | Ignoring loss of undecryptable packets | 1 | yes | 6 | MUST NOT ignore loss of packets sent after the earliest acknowledged packet in a space. |
| 7.5 | Probe timeout (cc) | 2 | yes | 6 | Probe packets MUST NOT be blocked by congestion controller; MUST be counted as additionally in flight. |
| 7.6.2 | Establishing persistent congestion | 2 | yes | 6 | The two packets bounding persistent congestion MUST be ack-eliciting; on persistent congestion cwnd MUST be reduced to kMinimumWindow. |
| 7.7 | Pacing | 1 | yes | 6 | Senders MUST either use pacing or limit bursts (SHOULD limit to initial cwnd). Limiting bursts satisfies the MUST. |
| 2 | Conventions and Definitions | 5 | no | N/A (boilerplate) | BCP 14 boilerplate listing the keywords; not a requirement. (The extraction omitted this row; added so totals match the raw grep.) |

Total keyword count: 38 across 19 sections.

## RFC 8446 — TLS 1.3

| § | Topic | #MUST/MUST NOT | Server applies? | Phase | Notes |
|---|---|---|---|---|---|
| 1.1 | Conventions and Terminology | 5 | no | N/A (boilerplate) | BCP 14 boilerplate listing the keywords; no requirement |
| 2 | Protocol Overview | 2 | yes | 4 | Server key share in same group as a client share; no application data before server Finished ✅ 4b: crates/tls/src/flight.rs (secp256r1 share answers a secp256r1 KeyShareEntry; the 1-RTT secrets are the last event, after the server Finished) |
| 2.1 | Incorrect DHE Share | 1 | yes | 4 | Abort with alert if no common parameters ✅ 4b: crates/tls/src/negotiate.rs (no suite, chain or group: handshake_failure; no ALPN: no_application_protocol) |
| 2.2 | Resumption and Pre-Shared Key (PSK) | 1 | no | Declined (optional: resumption/PSK) | Out-of-band PSK provisioning |
| 4 | Handshake Protocol | 2 | yes | 4 | Message ordering; unexpected_message on out-of-order handshake message ✅ 4b: crates/tls/src/server.rs (`spec_expected`: one message type at one level per phase, anything else unexpected_message; first-byte check in handshake.rs, 4a) |
| 4.1.1 | Cryptographic Negotiation | 4 | partial | 4 | Abort (handshake_failure/insufficient_security) when no group/parameter overlap; HelloRetryRequest when no compatible key_share ✅ 4b: crates/tls/src/negotiate.rs (handshake_failure; `Retry` when secp256r1 is offered without a share; PSK row below declined) |
| 4.1.1 (req) | PSK key establishment mode selection | 1 | no | Declined (optional: resumption/PSK) | "If the server selects a PSK, then it MUST also select a key establishment mode from the set indicated by the client" |
| 4.1.2 | Client Hello | 16 | partial | 4 | Server-side rules: reject non-null compression (illegal_parameter), ignore unknown cipher suites/extensions, unexpected_message on ClientHello after handshake ✅ 4b: crates/tls/src/server.rs (CH2's typed fields must equal CH1's except key_share, else illegal_parameter; a ClientHello after the ServerHello is unexpected_message; compression and unknown suites/extensions in client_hello.rs, 4a) |
| 4.1.2 (req) | Client sends ClientHello first / same ClientHello after HRR / legacy_version 0x0303 / legacy_session_id rules | 6 | no | N/A (client-only) | "it is REQUIRED to send the ClientHello as its first TLS message"; "the client MUST send the same ClientHello without modification"; client-side field constraints |
| 4.1.2 (req) | Compatibility-mode legacy_session_id | 2 | no | Declined (optional: TLS 1.2-and-older compatibility) | "In compatibility mode this field MUST be non-empty"; QUIC forbids compat mode (RFC 9001 §8.4); server SHOULD error on non-empty value (see RFC 9001 table) |
| 4.1.2 (req) | renegotiation of pre-1.3 sessions / pre-1.3 extension-block rules | 5 | no | Declined (optional: TLS 1.2-and-older compatibility) | "MUST retain the previous protocol version"; "MUST NOT negotiate TLS 1.3"; prior-version procedures |
| 4.1.3 | Server Hello | 16 | partial | 4 | Server-side: legacy_version 0x0303, random independent of ClientHello.random, compression 0, supported_versions present, only required extensions ✅ 4b: crates/tls/src/flight.rs (random = rand[0..32]; downgrade sentinel vacuous, TLS 1.3 only; layout in server_msgs.rs, 4a) |
| 4.1.3 (req) | Client-side ServerHello checks | 4 | no | N/A (client-only) | "A client which receives a legacy_session_id_echo ... / cipher suite not offered MUST abort"; downgrade-sentinel checks |
| 4.1.3 (req) | Downgrade sentinel in ServerHello.Random | 4 | no | Declined (optional: TLS 1.2-and-older compatibility) | "TLS 1.3 servers which negotiate TLS 1.2 or below ... MUST set the last 8 bytes"; we never negotiate older versions; crates/tls/src/flight.rs cites the three server MUSTs as vacuous (4a rejects every ClientHello without 0x0304) |
| 4.1.4 | Hello Retry Request | 11 | partial | 4 | Server: supported_versions in HRR, no unoffered extensions except cookie, same cipher suite on updated ClientHello ✅ 4b: crates/tls/src/server.rs (one suite, and CH2's suites equal CH1's; never a second HRR; layout in server_msgs.rs, 4a) |
| 4.1.4 (req) | Client-side HRR processing | 6 | no | N/A (client-only) | "Clients MUST abort ... if the HelloRetryRequest would not result in any change"; second HRR; cipher suite/version checks |
| 4.2 | Extensions | 5 | yes | 4 | No unsolicited extension responses (cookie excepted), unsupported_extension / illegal_parameter aborts, no duplicate extension types ✅ 4b: crates/tls/src/server.rs (no unsolicited responses: key_share is answered only when the client sent one (`theorem_no_unsolicited`); supported_versions and quic_transport_parameters are required by 4a's ClientHello parser, and ALPN `h3` by `negotiate` step 2; duplicates, psk-last, oid_filters in ext.rs, 4a) |
| 4.2.1 | Supported Versions | 16 | partial | 4 | Server: use only supported_versions (not legacy_version), ignore unknown versions, reply with 0x0304 and legacy_version 0x0303; ✅ 4a: crates/tls/src/client_hello.rs + server_msgs.rs |
| 4.2.1 (req) | Server supporting TLS 1.2 / negotiating pre-1.3 | 3 | no | Declined (optional: TLS 1.2-and-older compatibility) | "servers ... which also support TLS 1.2 MUST negotiate TLS 1.2"; "MUST NOT send supported_versions" when negotiating pre-1.3 |
| 4.2.1 (req) | Client-side supported_versions rules | 6 | no | N/A (client-only) | Client MUST send extension, check it first in ServerHello, abort on bad selected version |
| 4.2.2 | Cookie | 3 | yes | 4 | Client copies cookie; clients MUST NOT reuse cookies; "Servers operating statelessly MUST ignore these records" refers to CCS records, which QUIC lacks (RFC 9001 §8.4). We emit no cookies. All three MUSTs are client-side or vacuous, so the controller accepted closure on policy (Phase 4a final review); ✅ 4a: crates/tls/src/client_hello.rs + server_msgs.rs (no cookie in HRR; any received cookie rejected) |
| 4.2.3 | Signature Algorithms | 16 | partial | 4 | Server: missing signature_algorithms when authenticating with certificate -> missing_extension; key type must match signature algorithm; no SHA-1-signed certificate unless unavoidable ✅ 4b: crates/tls/src/negotiate.rs (key type fixes the scheme, which must be in signature_algorithms; a SHA-1-signed chain only when no SHA-1-free chain fits, and only with SHA-1 the client offered; missing_extension in crates/tls/src/client_hello.rs, 4a; the client "MUST send signature_algorithms" a Duvet exception, client-only) |
| 4.2.3 (req) | RSA signature scheme requirements (rsaEncryption OID, RSASSA-PSS OID, salt length, DER params, identical params) | 6 | yes | 4 | User decision 2026-10-27 (design spec, "Calls I made": RSA (RFC 8446 §9.1)): rsa_pkcs1_sha256 and rsa_pss_rsae_sha256 are recognized in signature_algorithms / signature_algorithms_cert when selecting the chain to send; the server only signs, so peer-signature MUSTs do not arise. ✅ 4b: crates/tls/src/negotiate.rs (rsae salt 32 = hash length; rsaEncryption OID trusted (TRUSTED.md); rsa_pss_pss and certificate-signature parameters are Duvet exceptions: never selected / we sign no certificate) |
| 4.2.3 (req) | Deprecated algorithms MUST NOT be offered or negotiated (MD5, SHA-224, DSA) | 2 | yes | 4 | We sign with ecdsa_secp256r1_sha256 and rsa_pss_rsae_sha256 (RSA key supported) ✅ 4b: crates/tls/src/negotiate.rs (`key_scheme` yields only 0x0403 / 0x0804) |
| 4.2.3 (req) | TLS 1.2 negotiation rules for signature schemes / curves / PSS | 3 | no | Declined (optional: TLS 1.2-and-older compatibility) | "implementations MUST be prepared to accept a signature that uses any curve ..." when TLS 1.2 negotiated |
| 4.2.3 (req) | Client lists legacy algorithms lowest priority | 1 | no | N/A (client-only) | "Clients offering these values MUST list them as the lowest priority" |
| 4.2.5 | OID Filters | 6 | no | Declined (optional: client certificates) | Only in CertificateRequest, which we never send |
| 4.2.6 | Post-Handshake Client Authentication | 2 | partial | 4 | Server MUST NOT send the post_handshake_auth extension (we never do); ✅ 4a: crates/tls/src/client_hello.rs + server_msgs.rs (never sent; no serializer) |
| 4.2.6 (req) | "Servers MUST NOT send a post-handshake CertificateRequest to clients which do not offer this extension" | 1 | no | Declined (optional: client certificates) | We never send CertificateRequest |
| 4.2.7 | Supported Groups | 1 | no | N/A (client-only) | "Clients MUST NOT act upon any information found in supported_groups prior to ..." |
| 4.2.8 | Key Share | 13 | partial | 4 | Server: key_share in same group as selected client share, MUST NOT send entry for group not in supported_groups; only secp256r1 supported; ignore other groups' shares ✅ 4b: crates/tls/src/negotiate.rs (the first secp256r1 share, used only when secp256r1 is in supported_groups; key_share grammar in crates/tls/src/ch_ext.rs, 4a) |
| 4.2.8 (req) | Client key_share construction and HRR/ServerHello checks | 9 | no | N/A (client-only) | Entries match supported_groups order, no duplicates, replace key_share after HRR, illegal_parameter checks |
| 4.2.8.1 | Diffie-Hellman Parameters | 1 | no | Declined (optional: X25519) | Finite-field DH; only secp256r1 supported (groups beyond secp256r1 declined) |
| 4.2.8.2 | ECDHE Parameters | 1 | yes | 5 | Validate peer public value Q is on curve for secp256r1; secp384r1/secp521r1 not supported; 3a spec: crates/crypto/src/p256.rs ✅ 5c: crates/crypto/src/p256.rs (sec1_decode_exec proven against sec1_decode: 65 octets, 0x04, x, y < p, curve equation; p256_ecdh verified) |
| 4.2.9 | Pre-Shared Key Exchange Modes | 7 | partial | 4 | Server: abort if pre_shared_key offered without psk_key_exchange_modes; MUST NOT send psk_key_exchange_modes; never select an unlisted mode; ✅ 4a: crates/tls/src/client_hello.rs + server_msgs.rs |
| 4.2.9 (req) | psk_ke / psk_dhe_ke modes (client must send, key_share rules per mode) | 4 | no | Declined (optional: resumption/PSK) | "In order to use PSKs, clients MUST also send ..."; psk_ke "MUST NOT supply a key_share" |
| 4.2.10 | Early Data Indication | 12 | partial | 4 | Server receiving early_data must not accept it: ignore/reject path (do not echo extension; skip/discard 0-RTT); ✅ 4a: crates/tls/src/client_hello.rs + server_msgs.rs (ignored; EE never echoes; 0-RTT packets dropped by 3e) |
| 4.2.10 (req) | Accepting early data (ticket age, same PSK params, bad_record_mac on 0-RTT failure) | 6 | no | Declined (optional: 0-RTT) | "In order to accept early data, the server MUST have accepted a PSK cipher suite ..." |
| 4.2.10 (req) | Client early_data behaviour | 3 | no | N/A (client-only) | "A client MUST NOT include early_data in its followup ClientHello"; no auto-resend |
| 4.2.11 | Pre-Shared Key Extension | 11 | partial | 4 | Server: "pre_shared_key MUST be the last extension"; fail with illegal_parameter otherwise (parse of an unsupported extension); ✅ 4a: crates/tls/src/client_hello.rs |
| 4.2.11 (req) | PSK selection, binder validation, externally provisioned PSKs | 5 | no | Declined (optional: resumption/PSK) | "The server MUST ensure that it selects a compatible PSK"; binder must validate |
| 4.2.11 (req) | Client checks of selected_identity | 5 | no | N/A (client-only) | Client verifies server's selected_identity and key_share |
| 4.2.11.1 | Ticket Age | 1 | no | N/A (client-only) | "Clients MUST NOT attempt to use tickets which have ages greater than ticket_lifetime" |
| 4.2.11.3 | Processing Order | 1 | no | Declined (optional: 0-RTT) | Server flight ordering when accepting early_data |
| 4.3.1 | Encrypted Extensions | 3 | partial | 4 | Server MUST send EncryptedExtensions immediately after ServerHello; client forbidden-extension check is client-side ✅ 4b: crates/tls/src/flight.rs (EncryptedExtensions is the first Handshake-level message; layout in server_msgs.rs, 4a) |
| 4.3.2 | Certificate Request | 6 | no | Declined (optional: client certificates) | We never send CertificateRequest |
| 4.4.2 | Certificate | 12 | partial | 4 | Server: send Certificate, empty certificate_request_context (SHALL be zero length), extensions match ClientHello, end-entity first, non-empty list, no OpenPGP certs ✅ 4b: crates/tls/src/flight.rs (every flight carries the configured chain's Certificate; layout in server_msgs.rs, 4a) |
| 4.4.2 (req) | Client Certificate message rules | 4 | no | Declined (optional: client certificates) | "The client MUST send a Certificate message if and only if the server has requested client authentication"; empty-certificate and Finished rules |
| 4.4.2 (req) | RawPublicKey certificate type | 1 | no | 4 | X.509v3 only; RawPublicKey not negotiated; ✅ 4a: crates/tls/src/server_msgs.rs |
| 4.4.2.1 | OCSP Status and SCT Extensions | 5 | partial | 4 | Server: MUST NOT act on/send status_request_v2, MUST be able to process (ignore) ClientHello carrying it; we send no OCSP/SCT; ✅ 4a: crates/tls/src/server_msgs.rs |
| 4.4.2.1 (req) | Client OCSP status_request body | 1 | no | Declined (optional: client certificates) | "If the client opts to send an OCSP response ..." |
| 4.4.2.2 | Server Certificate Selection | 7 | yes | 4 | X.509v3, P-256 or RSA key compatible with client's signature_algorithms, digitalSignature key usage, chain signed with client-advertised algorithms; abort alert is client-side ✅ 4b: crates/tls/src/negotiate.rs (P-256 or RSA key; chain metadata trusted (TRUSTED.md); first chain signed only with offered non-SHA-1 schemes, else the first signed only with offered schemes, else the first whose SHA-1 schemes are offered; client abort alert a Duvet exception) |
| 4.4.2.3 | Client Certificate Selection | 3 | no | Declined (optional: client certificates) | Client-side |
| 4.4.2.4 | Receiving a Certificate Message | 2 | no | Declined (optional: client certificates) | Server never receives a Certificate; empty-cert check is client-side; MD5 check applies to chain validation |
| 4.4.3 | Certificate Verify | 10 | partial | 4 | Server MUST send; algorithm one offered by client, compatible with key; SHA-1 MUST NOT be used; ecdsa_secp256r1_sha256 and rsa_pss_rsae_sha256 signing supported ✅ 4b: crates/tls/src/sign.rs (content and signature proven against crypto::{ecdsa,rsa}; algorithm choice in negotiate.rs; layout in server_msgs.rs, 4a) |
| 4.4.3 (req) | "RSA signatures MUST use an RSASSA-PSS algorithm" | 1 | yes | 4 | User decision 2026-10-27 (design spec, "Calls I made": RSA (RFC 8446 §9.1)): an RSA certificate signs CertificateVerify with rsa_pss_rsae_sha256 only (RSASSA-PSS, MGF1-SHA256, salt length 32). ✅ 4b: crates/tls/src/sign.rs |
| 4.4.3 (req) | Client CertificateVerify send/verify | 3 | no | Declined (optional: client certificates) | "Clients MUST send this message whenever authenticating via a certificate"; "receiver ... MUST verify the signature" (server never receives one) |
| 4.4.4 | Finished | 3 | yes | 4 | Verify client Finished, decrypt_error on mismatch; following records under application traffic keys (QUIC keys via RFC 9001 §5) ✅ 4b: crates/tls/src/server.rs (client Finished compared with `ct_eq32`, decrypt_error on mismatch; layout in server_msgs.rs, 4a) |
| 4.5 | End of Early Data | 4 | partial | 4 | "Servers MUST NOT send this message" (QUIC also forbids it; RFC 9001 §8.3); ✅ 4a: crates/tls/src/client_hello.rs + server_msgs.rs (never sent; no serializer) |
| 4.5 (req) | Client EndOfEarlyData rules | 3 | no | Declined (optional: 0-RTT) | "the client MUST send an EndOfEarlyData message after receiving the server Finished" |
| 4.6.1 | New Session Ticket Message | 7 | no | Declined (optional: resumption/PSK) | Server sends no tickets |
| 4.6.2 | Post-Handshake Authentication | 6 | no | Declined (optional: client certificates) | Post-handshake auth declined |
| 4.6.3 | Key and Initialization Vector Update | 7 | no | 4 | TLS KeyUpdate replaced by QUIC key update (RFC 9001 §6) ✅ 4b: crates/tls/src/server.rs (replaced by QUIC key update; receipt is 0x10a) |
| 4.6.3 (req) | "Implementations that receive a KeyUpdate message ... MUST terminate the connection with unexpected_message" | 1 | yes | 4 | RFC 9001 §6: endpoints MUST NOT send TLS KeyUpdate and treat receipt as connection error 0x010a ✅ 4b: crates/tls/src/server.rs |
| 5 | Record Protocol | 5 | no | 4 | replaced by QUIC (RFC 9001 §4); CCS: QUIC carries no change_cipher_spec (RFC 9001 §8.4) |
| 5.1 | Record Layer | 17 | no | 4 | replaced by QUIC (RFC 9001 §4) |
| 5.1 (req) | Handshake messages MUST NOT span key changes; verify message alignment at key change | 3 | yes | 4 | QUIC analogue: leftover handshake data at a lower encryption level when keys advance is PROTOCOL_VIOLATION (RFC 9001 §4.1.3); 4a codec: HsReader::is_empty (closed in 4c); 4b: crates/tls/src/server.rs: `pending(level)` (closed in 4c) |
| 5.2 | Record Payload Protection | 5 | no | 4 | replaced by QUIC (RFC 9001 §4); packet protection in RFC 9001 §5 |
| 5.3 | Per-Record Nonce | 3 | no | 4 | replaced by QUIC (RFC 9001 §4); nonce from packet number per RFC 9001 §5.3 |
| 5.4 | Record Padding | 6 | no | 4 | replaced by QUIC (RFC 9001 §4) |
| 6 | Alert Protocol | 7 | partial | 4 | Alerts become CRYPTO_ERROR (0x0100 + alert) and are always fatal (RFC 9001 §4.8); decode_error/illegal_parameter mapping; forget secrets of failed connections; 4a codec: crates/tls/src/client_hello.rs (closed in 4c); 4b: crates/tls/src/server.rs: `0x100 + alert` codes; `client_vd` overwritten on `Failed`; transcript and CH1 dropped; handshake and master secrets never retained in `ServerHandshake` (no zeroization) (closed in 4c) |
| 6.1 | Closure Alerts | 4 | no | 4 | replaced by QUIC (RFC 9001 §4): connection close via CONNECTION_CLOSE, no close_notify |
| 6.2 | Error Alerts | 3 | yes | 4 | Fatal error closes connection; alert maps to QUIC error code |
| 7.4.2 | Elliptic Curve Diffie-Hellman | 2 | partial | 4 | Do not truncate leading zeros of shared secret (P-256 X coordinate, 32 bytes) ✅ 4b: crates/tls/src/flight.rs (shared secret is a [u8; 32]; all-zero secret aborts with illegal_parameter) |
| 7.4.2 (req) | All-zero shared secret check (RFC 7748 §6) | 1 | no | Declined (optional: X25519) | Applies to X25519/X448 ("For these curves"), not negotiated; crates/tls/src/flight.rs also rejects an all-zero P-256 secret with illegal_parameter (4b, brief Step 3) |
| 7.5 | Exporters | 2 | no | 4 | QUIC does not use TLS exporters; "Future specifications MUST NOT define a use of exporters ..." is N/A (binds spec authors), a Duvet exception in crates/tls/src/schedule.rs; ✅ 4b: crates/tls/src/schedule.rs (no exporter derived; QUIC uses none) |
| 8 | 0-RTT and Anti-Replay | 3 | no | Declined (optional: 0-RTT) | We never accept 0-RTT |
| 8.2 | Client Hello Recording | 3 | no | Declined (optional: 0-RTT) | Anti-replay storage for 0-RTT |
| 9.1 | Mandatory-to-Implement Cipher Suites | 3 | partial | 4 | MUST implement TLS_AES_128_GCM_SHA256 (our only suite; primitives in Phase 5); MUST support secp256r1 key exchange and ecdsa_secp256r1_sha256 ✅ 4b: crates/tls/src/negotiate.rs (TLS_AES_128_GCM_SHA256, secp256r1, signing with 0x0403 / 0x0804; certificate schemes, rsa_pkcs1_sha256 included, matched in chain selection) |
| 9.1 (req) | "MUST support digital signatures with rsa_pkcs1_sha256 (for certificates), rsa_pss_rsae_sha256 (for CertificateVerify and certificates)" | 1 | yes | 5 | User decision 2026-10-27 (design spec, "Calls I made": RSA (RFC 8446 §9.1)): RSASSA-PSS-SHA256 signing primitive (bignum modexp without CRT, MGF1, EMSA-PSS, verified and CT-checked at MIR level (5e); RSA certificates not deployable yet, see TRUSTED.md), 2048-4096-bit modulus. No RSA verification: client certificates are declined, so the server verifies no peer signatures; 3a spec: crates/crypto/src/rsa.rs (exec external_body until 5) |
| 9.2 | Mandatory-to-Implement Extensions | 13 | partial | 4 | Implement supported_versions, signature_algorithms, signature_algorithms_cert, supported_groups, key_share, server_name; missing_extension abort for CH lacking required extensions; send supported_versions/key_share when applicable (use: 4b negotiate); ✅ 4a: crates/tls/src/client_hello.rs + server_msgs.rs |
| 9.2 (req) | "MUST implement ... cookie" | 1 | yes | 4 | "MUST implement ... cookie". Basis is RFC 8446 §4.2.2 (server cookie emission is a MAY), so "implement" means handle the extension; rejecting a cookie we never issued is our policy choice, not a MUST. Not a reinterpretation; ✅ 4a: crates/tls/src/client_hello.rs: parsed; any cookie rejected (never issued) |
| 9.2 (req) | pre_shared_key / psk_key_exchange_modes REQUIRED for PSK | 2 | no | Declined (optional: resumption/PSK) | "\"pre_shared_key\" is REQUIRED for PSK key agreement"; "\"psk_key_exchange_modes\" is REQUIRED for PSK key agreement". PSK declined. |
| 9.3 | Protocol Invariants | 10 | partial | 4 | Server MUST correctly ignore unrecognized cipher suites, extensions, and other parameters; client/middlebox invariants do not apply; ✅ 4a: crates/tls/src/client_hello.rs |
| 11 | IANA Considerations | 2 | no | N/A (IANA procedure) | Registry policy for IANA/IESG; no implementation requirement |
| Appendix B | Protocol Data Structures and Constant Values | 2 | yes | 4 | Never send the deprecated/obsolete_RESERVED values; we offer and accept one suite, so this holds by construction; ✅ 4a: crates/tls/src/server_msgs.rs |
| Appendix C | Implementation Notes | 1 | partial | 4 | "applications MUST NOT use TLS in such a way absent explicit configuration" (no authentication mechanism): the server always authenticates with its certificate. ✅ 4b: crates/tls/src/flight.rs (every flight carries Certificate and CertificateVerify) |
| Appendix D | Backward Compatibility | 18 | partial | 4 | Server rows: legacy_version / legacy_record_version ignored; negotiate via supported_versions; abort protocol_version when no TLS 1.3 offer (never fall back); never send or negotiate RC4, <112-bit ciphers, SSL 2.0/3.0, SSL 2.0-format ClientHello, legacy_version <= 0x0300 (abort protocol_version), truncated HMAC. All hold by construction (TLS 1.3 only, one suite) but each needs its Phase 4 check. Rows below carve out the exceptions; ✅ 4a: crates/tls/src/client_hello.rs + server_msgs.rs |
| Appendix D (req) | Client-side backward-compat rules (client aborts on unacceptable version, fails 0-RTT on TLS 1.2 ServerHello, does not send SSLv2 hello) | 3 | no | N/A (client-only) | Client behaviour. |
| Appendix D (req) | Negotiate min(legacy_version, TLS 1.2) when supported_versions absent; send change_cipher_spec in compatibility mode | 2 | no | Declined (optional: TLS 1.2-and-older compatibility) | "the server MUST negotiate the minimum of ClientHello.legacy_version and TLS 1.2"; QUIC forbids compatibility mode (RFC 9001 §8.4). We abort with protocol_version instead. |
| Appendix E | Overview of Security Properties | 7 | partial | 4 | Server rows: TLS implementations MUST NOT enable 0-RTT unless the application requests it (we never do); MUST provide a way to learn that the handshake has completed (feeds RFC 9001 §4.1.2 HANDSHAKE_DONE). Rows below carve out the rest. ✅ 4b: crates/tls/src/server.rs (`is_complete`; no 0-RTT level exists) |
| Appendix E (req) | Combine external PSKs with certificate authentication | 1 | no | Declined (optional: resumption/PSK) | "MUST NOT combine external PSKs with certificate-based authentication" - no PSK support. |
| Appendix E (req) | Exporter output size for channel bindings | 1 | no | N/A (binds spec authors) | Binds applications that use exporters; we expose none. |
| Appendix E (req) | Client sends only replay-safe early data / does not auto-resend; applications need a 0-RTT profile | 3 | no | N/A (client-only) | Client and application-profile obligations; we never accept 0-RTT. |

Total keyword count: 345 across 57 sections.

