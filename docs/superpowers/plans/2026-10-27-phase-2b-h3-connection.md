# Phase 2b: HTTP/3 Message Validation + Connection State Machine — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** A verified, sans-IO HTTP/3 **server connection**. It consumes QUIC stream events and produces transport actions plus application events. Every RFC 9114 / RFC 9204 MUST that Phase 2a left open is proven against a per-stream spec.

**Architecture:**
- **Pure state machines**, built on the Phase 2a codecs:
  - `h3::message`: request/response field validation;
  - `h3::uni`: peer unidirectional streams (stream-type dispatch, the control stream, QPACK streams);
  - `h3::request`: one machine per request stream;
  - `h3::conn`: the integration layer that dispatches by stream ID, plus SETTINGS, GOAWAY and the connection-error latch.
- **Spec style for the stream machines:** each spec is a total function of *all bytes received on that stream so far, plus a FIN flag*. It returns the cumulative event sequence and an optional terminal error. The exec machine is fed arbitrary chunks. After every call, its cumulative outputs must equal the spec of the concatenated input. Chunking can therefore never change behaviour, and that is proven.
- **The QUIC layer (Phase 3) is abstract here.** Stream IDs follow RFC 9000 §2.1, so a stream's initiator and direction come from `id % 4`.

**Tech Stack:** Verus 0.2026.10.04.426d8b0, vstd `=0.0.0-2026-10-04-0306`, vest_lib `=0.2.2`, duvet 0.4.3.

**Spec:** `docs/superpowers/specs/2026-10-27-verified-http3-design.md`

## Global Constraints

- **Everything in Phase 2a's Global Constraints applies unchanged:** pins, no escapes, Duvet citations, the four checks, fresh-`CARGO_TARGET_DIR` evidence, sans-IO, no panics, no allocation sized by untrusted lengths, and per-task matrix bookkeeping with `✅ 2b: <file>`.
- **Reuse Phase 2a's APIs.** Check the exact signatures in the files:
  - `h3::codes::*`;
  - `h3::frame::{parse_frame_header, FrameHeader, parse_frame_payload, Frame, serialize_frame_header, serialize_settings, serialize_goaway, rfc_frame_header, rfc_frame_payload}`;
  - `h3::qpack::field_section::{decode_field_section, encode_field_section, FieldLine, rfc_decode_field_section}`;
  - `h3::qpack::instructions::{process_encoder_stream, process_decoder_stream}`.
- **Dispatch on `FrameHeader.ty` before calling `parse_frame_payload`.** A frame type that is forbidden on the current stream gets its error code from the type alone, with no buffering and no payload parse. For example, PUSH_PROMISE from a client is H3_FRAME_UNEXPECTED even if its payload is malformed (RFC 9114 §7.2.5). This also applies to HEADERS, DATA and HTTP/2-reserved types on the control stream, and to control-only frames on request streams.
- **Ruling (Phase 2a final review): every `Err(code)` from the 2a QPACK codecs is a connection error.** RFC 9204 §7.4's request-stream TooLarge, a stream error by the letter, is escalated as RFC 9114 §8 permits.
- **Never add a MAX_PUSH_ID, CANCEL_PUSH or PUSH_PROMISE serializer.** The server "never sends" rules (RFC 9114 §7.2.5, §7.2.7) hold because those serializers don't exist.
- **Limits we choose.** These are constants in `h3::conn`, each with a `ponytail:` comment.
  - `MAX_FIELD_SECTION_SIZE: u64 = 65536` is advertised in our SETTINGS. A HEADERS frame payload longer than this is a stream error `H3_EXCESSIVE_LOAD`. `// ponytail: caps the encoded size; RFC 9114 §4.2.2 measures the decoded size; refine if needed.`
  - `MAX_CONTROL_FRAME: u64 = 16384`. A larger non-DATA frame on the control stream is a connection error `H3_EXCESSIVE_LOAD`.
  - `MAX_SETTINGS_FRAME: u64 = 1024`. A larger SETTINGS frame is a connection error `H3_EXCESSIVE_LOAD`. This bounds the O(n²) duplicate scan in `parse_frame_payload` to at most 512 pairs.
  - `MAX_FIELD_SECTION_SIZE` is also the **decoded** budget: Σ(name.len + value.len + 32) over the field lines (RFC 9114 §4.2.2's definition). It is enforced by the bounded decoder in Task 3, which checks before every allocation.
- **Our SETTINGS frame is exactly `[(0x06, 65536), (0x21, 0)]`:** MAX_FIELD_SECTION_SIZE plus one grease setting (RFC 9114 §7.2.4.1 SHOULD). QPACK settings are left at their defaults of 0, which is what we want, so they aren't sent.
- **Field syntax (RFC 9110):**
  - **Name:** non-empty, with every byte a lowercase `tchar` (`!#$%&'*+-.^_`|~`, DIGIT, lowercase ALPHA). An uppercase letter makes the message malformed (RFC 9114 §4.1.2).
  - **Value:** the `field-content` rule of §5.5. It is either empty, or its first and last bytes are field-vchars (0x21–0x7e or 0x80–0xff) and every interior byte is a field-vchar, SP or HTAB. That forbids NUL, CR, LF, other controls and leading/trailing whitespace (RFC 9114 §10.3).

## Matrix rows this plan closes

All Phase-2 rows that are not marked `✅ 2a` or that carry an "open for 2b" tail:
- **RFC 9114:** §3.2, §4.1, §4.1.1, §4.1.2, §4.2, §4.2.1, §4.3, §4.3.1, §4.3.2, §4.4, §5.2, §6.2, §6.2.1, §6.2.2, §6.2.3, §7.1 (truncated last frame), the 2b tails of §7.2.1–§7.2.8, §7.2.4.2, §8, §9, §10.3 and §10.6.
- **RFC 9204:** §4.2.

## Review Focus

1. **Chunking independence:** the same request bytes delivered one byte at a time and all at once give identical events. This is proven by the spec style; pinned by tests in Tasks 2, 3 and 4.
2. **A request stream that ends mid-frame:** with a clean FIN this is a connection error `H3_FRAME_ERROR`. A FIN before any complete HEADERS is a stream error `H3_REQUEST_INCOMPLETE`. Pinned in Task 3: `truncation`.
3. **Content-length mismatch:** content-length 5 with 4 DATA bytes then FIN, or with 6 DATA bytes, is a stream error `H3_MESSAGE_ERROR`. Pinned in Task 3: `content_length`.
4. **Control-stream misuse:** a missing initial SETTINGS, a second SETTINGS, DATA on the control stream, a FIN on the control stream and a second control stream each produce their RFC error code. Pinned in Task 2: `control_rules`.
5. **Responses from unverified app code that would violate the RFC:** an uppercase header name, `connection: close`, a `:path` pseudo-header in a response or a status outside 100–599. Each is rejected by `send_response` with `Err`, and nothing is sent. Pinned in Task 4: `bad_response_rejected`.

---

### Task 1: Message validation (`h3::message`)

**Files:**
- Create: `crates/h3/src/message.rs`
- Test: `crates/h3/tests/message.rs`

**Interfaces:**
- Consumes: `FieldLine`, `H3_MESSAGE_ERROR`.
- Produces:
  - `pub struct Request { pub method: Vec<u8>, pub scheme: Vec<u8>, pub authority: Vec<u8>, pub path: Vec<u8>, pub headers: Vec<FieldLine> }`. `headers` holds regular fields in received order, with cookie lines merged.
  - `pub enum RequestHead { Request(Request), Connect { authority: Vec<u8> } }`. A well-formed CONNECT is surfaced so the connection can answer 501.
  - `pub open spec fn valid_field_name(n: Seq<u8>) -> bool` and `pub open spec fn valid_field_value(v: Seq<u8>) -> bool`, which transcribe the Global Constraints field syntax, plus exec twins.
  - `pub open spec fn rfc_validate_request(fields: Seq<(Seq<u8>, Seq<u8>)>) -> Result<SpecRequestHead, u64>`, covering RFC 9114 §4.2, §4.3, §4.3.1 and §4.4. Any violation is `Err(H3_MESSAGE_ERROR)`:
    - every name passes `valid_field_name` or is a pseudo-header, and every value passes `valid_field_value`;
    - pseudo-headers (names starting with `:`) all come before regular fields;
    - the only allowed pseudo-headers are `:method`, `:scheme`, `:authority` and `:path`, each at most once;
    - connection-specific fields (`connection`, `keep-alive`, `proxy-connection`, `transfer-encoding`, `upgrade`) are forbidden, and `te` is allowed only with the value `trailers`;
    - **non-CONNECT requests:** `:method`, `:scheme` and `:path` are required. `:path` is non-empty. For `http`/`https`, `:authority` or `host` is required, both are non-empty, they must be equal if both are present, and `:authority` has no `@` (userinfo).
    - **CONNECT:** only `:method` and `:authority` are present, and `:authority` is non-empty.
    - **`content-length`:** if any are present, every value is ASCII digits only and all values are equal.
    - **Cookie merging (§4.2.1):** multiple `cookie` lines become one, joined with `"; "`, at the position of the first one.
  - `pub fn validate_request(fields: &[FieldLine]) -> (r: Result<RequestHead, u64>)`. It ensures `r@ == rfc_validate_request(fields@)`.
  - `pub open spec fn rfc_validate_trailers(fields) -> bool`: no pseudo-headers, and names and values valid. Plus an exec `validate_trailers`.
  - `pub fn content_length(fields: &[FieldLine]) -> Option<u64>`. It returns the parsed value when present. A value that overflows u64 is treated as invalid, which `validate_request` already rejects.
  - `pub struct Response { pub status: u16, pub headers: Vec<FieldLine>, pub body: Vec<u8> }`.
  - `pub open spec fn valid_response(r) -> bool`: status in 100..=599, header names pass `valid_field_name` with no `:` prefix, values are valid, there are no connection-specific fields, and every name and value length is ≤ `PREFIX_INT_MAX`. That last clause is `encode_field_section`'s precondition.
  - `pub fn check_response(r: &Response) -> (ok: bool)`, which ensures `ok == valid_response(r@)`.

- [ ] **Step 1: Failing tests:**
  - `valid_get`: `[(:method,GET),(:scheme,https),(:authority,example.com),(:path,/),(accept,*/*)]` → `Request` with those fields.
  - `malformed_cases`. Each case is `Err(H3_MESSAGE_ERROR)`:
    - an uppercase name `Accept`;
    - a value with a trailing space `"x "`;
    - a value containing `\r`;
    - a pseudo-header after a regular field;
    - a duplicate `:path`;
    - an unknown `:protocol`;
    - a missing `:scheme`;
    - an empty `:path`;
    - `:authority` of `user@host`;
    - `connection: close`;
    - `te: gzip`;
    - `:authority` of `a` with `host: b`;
    - `content-length` of `12a`;
    - two content-lengths, `3` and `4`.
  - `connect`: `[(:method,CONNECT),(:authority,example.com:443)]` → `Connect`. Adding a `:path` → `Err`.
  - `cookie_merge`: `cookie: a=1` and `cookie: b=2` → a single `cookie: a=1; b=2`.
  - `response_check`:
    - status 200 with `content-type: text/plain` → true;
    - status 99 → false;
    - name `Content-Type` → false;
    - `connection: x` → false.
- [ ] **Step 2:** Run the tests and confirm they fail.
- [ ] **Step 3:** Implement with Duvet citations of RFC 9114 §4.2, §4.2.1, §4.3, §4.3.1, §4.4 and §10.3 (contiguous quotes).
- [ ] **Step 4:** Run the four checks.
- [ ] **Step 5: Commit:** `feat(h3): verified request/response field validation (RFC 9114 §4.2-4.4, §10.3)`

---

### Task 2: Peer unidirectional streams (`h3::uni`)

**Files:**
- Create: `crates/h3/src/uni.rs`
- Test: `crates/h3/tests/uni.rs`

**Interfaces:**
- Consumes: the frame codec, `process_encoder_stream`, `process_decoder_stream` and the codes.
- Produces:
  - `pub enum UniKind { Undetermined, Control, QpackEncoder, QpackDecoder, Ignored }`.
    - Push streams from a client are rejected (RFC 9114 §6.2.2).
    - Unknown and grease types are discarded without reading (§6.2, §6.2.3).
  - `pub enum UniEvent { PeerSettings(Vec<(u64, u64)>), PeerGoaway(u64), PeerMaxPushId(u64) }`.
  - `pub struct UniStream { /* buffered bytes, kind, control-stream state */ }`.
    - `UniStream::new()`.
    - `pub fn on_data(&mut self, data: &[u8], fin: bool, seen: &mut SeenUni, events: &mut Vec<UniEvent>) -> Result<(), u64>`. `Err(code)` is a **connection** error.
    - `SeenUni { control: bool, encoder: bool, decoder: bool }` is shared across all uni streams. A second stream of any of the three critical kinds is `H3_STREAM_CREATION_ERROR` (RFC 9114 §6.2.1, RFC 9204 §4.2).
  - **Spec:** `pub open spec fn rfc_uni_stream(bytes: Seq<u8>, fin: bool, seen_before: SpecSeen) -> (Seq<SpecUniEvent>, Option<u64>)`.
    - The stream type is the first varint (lenient).
    - **Control stream rules:**
      - the first frame must be SETTINGS, else `H3_MISSING_SETTINGS`;
      - a later SETTINGS is `H3_FRAME_UNEXPECTED`;
      - DATA, HEADERS, PUSH_PROMISE and the HTTP/2-reserved types are `H3_FRAME_UNEXPECTED`;
      - any CANCEL_PUSH is `H3_ID_ERROR`, because we never promised a push (§7.2.3);
      - a MAX_PUSH_ID smaller than an earlier one is `H3_ID_ERROR` (§7.2.7);
      - a GOAWAY ID larger than an earlier peer GOAWAY ID is `H3_ID_ERROR` (§5.2);
      - unknown types are ignored;
      - any payload error from `rfc_frame_payload` is passed through;
      - a non-DATA frame with `len > MAX_CONTROL_FRAME` is `H3_EXCESSIVE_LOAD`;
      - a FIN, at any point, is `H3_CLOSED_CRITICAL_STREAM` (§6.2.1).
    - **QPACK streams:** bytes go through `rfc_encoder_stream` / `rfc_decoder_stream`, and a FIN is `H3_CLOSED_CRITICAL_STREAM` (RFC 9204 §4.2).
    - **Ignored:** everything after the type is dropped, and no error is ever raised.
    - Exec ensures, after each call: the cumulative events and error equal `rfc_uni_stream(all_bytes_so_far, fin, seen_before)`. `seen` is updated exactly when the type is determined.
  - Transport parameters: Phase 3 must allow the peer at least 3 uni streams (§6.2). Record that as a doc comment and a `pub const MIN_PEER_UNI_STREAMS: u64 = 3`.

- [ ] **Step 0: Export the lemmas 2b's chunking proofs need** (Phase 2a final review). Prove each and make it `pub`:
  - `lemma_frame_bytes_roundtrip(ty, p, rest)` in frame.rs: `rfc_frame_header(spec_frame_bytes(ty, p) + rest) == Some((hdr_len, ty, p.len()))`, and the payload slice equals `p`;
  - split lemmas for `rfc_encoder_stream` / `rfc_decoder_stream` in instructions.rs: if `f(b) == Ok(n)`, then `f(b + t)` equals `f(b.skip(n) + t)` with `n` added to an `Ok` result;
  - prefix stability of `rfc_frame_header`. The existing `lemma_decode_prefix` / `lemma_decode_extend` are now pub; wrap them if a cleaner statement is needed.
- [ ] **Step 1: Failing tests:**
  - **`control_rules`:**
    - `[0x00, 0x04, 0x00]` (control + empty SETTINGS) → `Ok`, with an event `PeerSettings([])`;
    - `[0x00, 0x07, 0x01, 0x00]` (GOAWAY first) → `Err(H3_MISSING_SETTINGS)`;
    - SETTINGS then SETTINGS → `Err(H3_FRAME_UNEXPECTED)`;
    - SETTINGS then DATA `[0x00, 0x00]` → `Err(H3_FRAME_UNEXPECTED)`;
    - SETTINGS then CANCEL_PUSH(0) → `Err(H3_ID_ERROR)`;
    - MAX_PUSH_ID 5 then 3 → `Err(H3_ID_ERROR)`;
    - SETTINGS with `fin = true` → `Err(H3_CLOSED_CRITICAL_STREAM)`;
    - a second control stream (seen.control = true) → `Err(H3_STREAM_CREATION_ERROR)`.
  - **`stream_types`:**
    - `[0x01]` (push) → `Err(H3_STREAM_CREATION_ERROR)`;
    - `[0x21, 0xff, 0xff]` (grease) → `Ok`, no events, and further data is ignored, including a FIN;
    - `[0x02, 0x20]` (encoder, capacity 0) → `Ok`;
    - `[0x02, 0x3f, 0xbd, 0x01]` → `Err(QPACK_ENCODER_STREAM_ERROR)`;
    - `[0x03]` then FIN → `Err(H3_CLOSED_CRITICAL_STREAM)`.
  - **`chunking`:** a valid control stream (SETTINGS with two pairs, unknown frame 0x21 with 3 bytes, GOAWAY 8) gives identical events and result whether fed all at once or byte by byte.
- [ ] **Step 2:** Run the tests and confirm they fail.
- [ ] **Step 3:** Implement with Duvet citations of RFC 9114 §6.2, §6.2.1, §6.2.2, §6.2.3, §7.2.3, §7.2.4, §7.2.7, §7.2.8, §5.2 and RFC 9204 §4.2.
- [ ] **Step 4:** Run the four checks.
- [ ] **Step 5: Commit:** `feat(h3): verified peer uni-stream + control-stream machine (RFC 9114 §6.2, §7.2)`

---

### Task 3: Request stream machine (`h3::request`)

**Files:**
- Create: `crates/h3/src/request.rs`
- Test: `crates/h3/tests/request.rs`

**Interfaces:**
- Consumes: the frame codec, `decode_field_section`, `validate_request`, `validate_trailers`, `content_length`, `MAX_FIELD_SECTION_SIZE` and the codes.
- Produces:
  - `pub enum ReqEvent { Head(RequestHead), Body(Vec<u8>), Trailers(Vec<FieldLine>), End }`.
  - `pub enum ReqError { Connection(u64), Stream(u64) }`.
  - `pub struct RequestStream { /* phase: AwaitHeaders | Body{remaining_in_data, received, content_length} | AfterTrailers | Done; header buffer */ }`.
    - `RequestStream::new()`.
    - `pub fn on_data(&mut self, data: &[u8], fin: bool, events: &mut Vec<ReqEvent>) -> Result<(), ReqError>`.
  - **Spec:** `pub open spec fn rfc_request_stream(bytes: Seq<u8>, fin: bool) -> (Seq<SpecReqEvent>, Option<SpecReqError>)`, where `Body` events are specified by **concatenation**. The spec's event sequence has `Head`, one `BodyBytes(all body bytes so far)`, `Trailers?` and `End?`. The exec emits `Body` chunks whose concatenation must equal that. RFC 9114 §4.1:
    - **Frame order:** HEADERS, then DATA*, then an optional HEADERS (trailers), then FIN.
    - **Wrong frames:** DATA before the first HEADERS, any frame after the trailers, and SETTINGS, CANCEL_PUSH, GOAWAY, MAX_PUSH_ID, PUSH_PROMISE or HTTP/2-reserved types are all `Connection(H3_FRAME_UNEXPECTED)`. Unknown and grease frames are ignored anywhere (§9).
    - **HEADERS processing:** a HEADERS payload longer than MAX_FIELD_SECTION_SIZE is `Stream(H3_EXCESSIVE_LOAD)`, rejected before buffering it. Otherwise the payload goes through a **new bounded decoder**, `decode_field_section_bounded(b, budget) -> Result<Vec<FieldLine>, BoundedError>` with `pub enum BoundedError { Qpack(u64), OverBudget }`, added to field_section.rs.
      - Its spec `rfc_decode_field_section_bounded(b, budget)` is `rfc_decode_field_section` plus a running Σ(name+value+32) check. It reports OverBudget at the first field line whose size pushes the total over budget.
      - The exec checks the budget before allocating each literal. Static entries and literal lengths are known before allocation; a Huffman output is bounded by the input slice and is checked right after decoding.
      - `Qpack(code)` maps to `Connection(code)`, and `OverBudget` maps to `Stream(H3_EXCESSIVE_LOAD)`. The result is then validated; a validation error is `Stream(H3_MESSAGE_ERROR)`. Trailers are validated with `validate_trailers`.
    - **DATA payload bytes are emitted as they arrive, never buffered whole.**
    - **content-length (§4.1.2):** if present, receiving more DATA bytes than the content-length is `Stream(H3_MESSAGE_ERROR)` immediately. At FIN, `received != content_length` is `Stream(H3_MESSAGE_ERROR)`.
    - **FIN handling:** a FIN that lands inside a frame (header or payload incomplete) is `Connection(H3_FRAME_ERROR)` (§7.1). A FIN before any complete HEADERS is `Stream(H3_REQUEST_INCOMPLETE)` (§8.1). Any other FIN gives `End`.
    - Exec ensures, after each call: the cumulative events (with Body chunks concatenated) and the error equal the spec of all bytes so far.

- [ ] **Step 1: Failing tests.** Build field sections with `encode_field_section` and frames with `serialize_frame_header`.
  - `simple_get`: HEADERS(GET https example.com /) + FIN → `[Head, End]`.
  - `post_body`: HEADERS(POST, content-length 5), DATA "he", DATA "llo", FIN → Head, Body chunks concatenating to "hello", End.
  - `content_length`: content-length 5 with DATA "hell" + FIN → `Stream(H3_MESSAGE_ERROR)`; content-length 5 with DATA "hello!" → `Stream(H3_MESSAGE_ERROR)`.
  - `frame_order`: DATA first → `Connection(H3_FRAME_UNEXPECTED)`; HEADERS, HEADERS (trailers), DATA → `Connection(H3_FRAME_UNEXPECTED)`; HEADERS + SETTINGS → `Connection(H3_FRAME_UNEXPECTED)`.
  - `truncation`: HEADERS header announcing 10 bytes with only 3 present, then FIN → `Connection(H3_FRAME_ERROR)`; an empty stream with FIN → `Stream(H3_REQUEST_INCOMPLETE)`.
  - `qpack_failure`: HEADERS with the B.2 payload `0381 10 11` → `Connection(QPACK_DECOMPRESSION_FAILED)`.
  - `decoded_budget`: a field section of 2,000 copies of indexed static entry 31 (`accept-encoding: gzip, deflate, br`, 34 bytes + 32 overhead = 66 bytes each), so about 2 KB encoded and about 132 KB decoded → `Stream(H3_EXCESSIVE_LOAD)`.
  - `push_promise_rejected_by_type`: a PUSH_PROMISE frame with a garbage payload → `Connection(H3_FRAME_UNEXPECTED)`, not H3_FRAME_ERROR.
  - `malformed_request`: HEADERS whose field section has an uppercase name → `Stream(H3_MESSAGE_ERROR)`.
  - `unknown_frames_ignored`: unknown frame type 0x21 interleaved before HEADERS and between DATA frames → the same events as without it.
  - `chunking`: `post_body`'s bytes fed one at a time give the same events, with the body concatenation identical.
- [ ] **Step 2:** Run the tests and confirm they fail.
- [ ] **Step 3:** Implement with Duvet citations of RFC 9114 §4.1, §4.1.2, §7.1, §7.2.1, §7.2.2 and §9.
- [ ] **Step 4:** Run the four checks.
- [ ] **Step 5: Commit:** `feat(h3): verified request-stream machine (RFC 9114 §4.1, §7.1)`

---

### Task 4: Connection integration (`h3::conn`)

**Files:**
- Create: `crates/h3/src/conn.rs`
- Test: `crates/h3/tests/conn.rs`

**Interfaces:**
- Consumes: Tasks 1–3, `serialize_settings`, `serialize_goaway`, `encode_field_section` and `serialize_frame_header`.
- Produces:
  - `pub enum Output`:
    - `StreamWrite { stream_id: u64, data: Vec<u8>, fin: bool }`;
    - `ResetStream { stream_id: u64, code: u64 }`;
    - `StopSending { stream_id: u64, code: u64 }`;
    - `CloseConnection { code: u64 }`;
    - `Request { stream_id: u64, head: Request }`;
    - `RequestBody { stream_id: u64, data: Vec<u8> }`;
    - `RequestEnd { stream_id: u64, trailers: Vec<FieldLine> }`.
  - `pub struct H3Conn`. `H3Conn::new()`.
  - `pub fn start(&mut self, out: &mut Vec<Output>)` writes, on server uni stream 3, `[0x00]` followed by SETTINGS `[(0x06, 65536), (0x21, 0)]`. It doesn't wait for peer data (§7.2.4.2, §3.2).
  - `pub fn on_stream_data(&mut self, stream_id: u64, data: &[u8], fin: bool, out: &mut Vec<Output>)`:
    - `id % 4 == 0` (client bidi) goes to the `RequestStream`;
    - `id % 4 == 2` (client uni) goes to the `UniStream`;
    - any other ID is `CloseConnection(H3_STREAM_CREATION_ERROR)`;
    - a `Connection(code)` error gives `CloseConnection(code)` and latches the connection closed, after which every method outputs nothing;
    - a `Stream(code)` error gives `ResetStream` + `StopSending` with that code and drops the stream;
    - a well-formed CONNECT is answered with a `501` response and FIN (§4.4, via RFC 9110 §9.1);
    - requests on IDs ≥ our sent GOAWAY ID get `ResetStream(H3_REQUEST_REJECTED)` and are never processed (§5.2, §4.1.1).
  - `pub fn on_stream_reset(&mut self, stream_id: u64, code: u64, out)`. A reset of a critical peer uni stream is `CloseConnection(H3_CLOSED_CRITICAL_STREAM)`; a reset of a request stream drops it silently.
  - `pub fn send_response(&mut self, stream_id: u64, resp: &Response, out) -> Result<(), ()>`.
    - It returns `Err` with no output if `!check_response(resp)`, if the stream isn't an open request stream whose `Head` was delivered, or if the connection is closed.
    - Otherwise it writes HEADERS (`:status` first via `encode_field_section`), then DATA (if the body is non-empty), then FIN.
    - It never sends a field section larger than the peer's MAX_FIELD_SECTION_SIZE, if one was received; otherwise it returns `Err` (§4.2.2 SHOULD).
  - `pub fn shutdown(&mut self, out)` sends GOAWAY(id = highest client bidi ID accepted + 4, or 0). GOAWAY IDs we send never increase (§5.2).
  - **Proof obligations:**
    - every `StreamWrite` on stream 3 begins with exactly one SETTINGS frame;
    - nothing is output after `CloseConnection`;
    - the per-stream outputs are exactly those of the verified machines (delegation lemmas);
    - every response we send satisfies `valid_response`, and its bytes decode back via `rfc_decode_field_section`.

- [ ] **Step 1: Failing tests:**
  - `start_sends_settings`: `start` → one `StreamWrite{3, [0x00, 0x04, …], fin:false}` whose frame parses to Settings `[(6, 65536), (0x21, 0)]`.
  - `end_to_end_get`:
    1. client control stream 2: `[0x00]` + SETTINGS;
    2. request stream 0: HEADERS(GET https example.com /index.html) + FIN;
    3. this yields `Request{0, head}` and `RequestEnd{0, []}`;
    4. `send_response(0, 200, [content-type: text/plain], "hi")` writes bytes on stream 0;
    5. parse them with `parse_frame_header`/`parse_frame_payload` and `decode_field_section`: they give `:status 200`, `content-type text/plain` and the body "hi", then FIN.
  - `bad_response_rejected`: names `X-Up`, `connection: close`, `:path` in headers, status 600 → each returns `Err`, with an empty `out`.
  - `connect_gets_501`: a well-formed CONNECT → a response with `:status 501` on that stream.
  - `goaway`: after `shutdown` with stream 0 accepted, GOAWAY(4) is written on stream 3, and a new request on stream 4 → `ResetStream{4, H3_REQUEST_REJECTED}`.
  - `latch`: a connection error from a malformed control stream gives `CloseConnection`; any later `on_stream_data` produces no output.
  - `bad_stream_id`: data on stream 1 → `CloseConnection(H3_STREAM_CREATION_ERROR)`.
- [ ] **Step 2:** Run the tests and confirm they fail.
- [ ] **Step 3:** Implement with Duvet citations of RFC 9114 §3.2, §4.1.1, §4.4, §5.2, §6.2.1 and §7.2.4.2.
- [ ] **Step 4:** Run the four checks.
- [ ] **Step 5: Commit:** `feat(h3): verified HTTP/3 server connection integration`

---

## Exit criteria (Phase 2b)

- All four checks pass. Every row under "Matrix rows this plan closes" carries `✅ 2b` or an explicit `N/A`/`Declined` reason. A grep of `docs/requirements.md` for Phase-2 rows without a ✅ returns nothing.
- `phase-2b` is merged into `main`.
