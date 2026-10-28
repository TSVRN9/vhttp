# Phase 3b: QUIC Wire Codecs — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Verified, sans-IO codecs for every QUIC v1 wire format a server reads or writes, each proven against an RFC-transcribed spec:
- packet-number encoding and decoding;
- long and short headers, split around header protection;
- Version Negotiation and Stateless Reset packets;
- the ACK frame and every other transport frame;
- per-packet-type frame permissions;
- transport parameters.

**Architecture:**
- **New crate `crates/quic`.** It depends on `wire` by path, and has no `crypto` dependency until 3e.
- **Every spec is hand-written** over `wire::varint::rfc_varint_decode`, with no Vest combinators beyond `QuicVarInt`. The reasons:
  - STREAM, ACK and CONNECTION_CLOSE fields are conditional on bits in the type;
  - each failure must map to a distinct RFC error code;
  - `h3::frame` already works this way.
- **Results come in two shapes:**
  - `Option` means "drop the packet silently". This is header-level, per RFC 9000 §5.2 and §17.2.
  - `Result<_, u64>` carries a transport error code, which means a connection error. Closing the connection is 3d's job.

**Tech Stack:** Verus 0.2026.10.04.426d8b0, vstd `=0.0.0-2026-10-04-0306`, vest_lib `=0.2.2`, duvet 0.4.3.

**Spec:** `docs/superpowers/specs/2026-10-27-verified-http3-design.md`. See Phase 3; "Calls I made" (server only; no migration initiation; sans-IO); Non-goals (0-RTT, Retry, NEW_TOKEN issuance).

**Phase 3 split, and why.** RFC 9000 separates wire formats (§12.4, §16–§19, App. A) from stream behaviour (§2–§4) and connection behaviour (§5–§14), and RFC 9001 §5 layers protection on top.
So: **3b** stateless codecs (this plan); **3c** streams and flow control (§2–§4, §7.5, §19.4–§19.14 semantics; what `h3::conn` consumes); **3d** connection (PN spaces/ACK, CIDs, handshake CIDs and TP semantics, address and path validation, datagram sizes, idle/close/reset); **3e** packet protection, pipelines, the shell and the Initial-exchange harness.
The suggested 3c is split in two because it held 107 of the 139 Phase-3 rows across two RFC chapters, and the suggested 3d becomes 3e. Outlines: `phase-3-outlines.md`.

## Controller rulings (2026-10-28, on the planner's open decisions)

- **Phase 3 is split into four sub-plans:** 3b codecs, 3c streams/flow control, 3d connection, 3e protection + shell. Phase 3a's references to "3b" for packet protection mean 3e.
- **Packet-number length (§17.1):** the prose ("more than twice as large a range") overrides Appendix A.2's pseudocode at exact powers of two. Before any ACK in a space, the full packet number is included, untruncated.
- **Specs are hand-written over `rfc_varint_decode`.** This departs from the design spec's "use vest_lib combinators" wording, following the `h3::frame`/QPACK precedent; the spec's architecture line is updated to "Vest where it composes cleanly; otherwise hand-written RFC specs over `rfc_varint_decode`". Cost if wrong: none for correctness, since each parser is still proven equal to an RFC transcription.
- **Non-malleability is waived** except for frame types. RFC 9000 §16 allows non-minimal varints, so `serialize(parse(b)) == b` can't hold in general; proofs cover exec ≡ spec and `parse(serialize(x)) == x`.
- **Spin bit (§17.4):** never enabled, so it is always disabled, and that meets the "MUST allow administrators to disable" requirement trivially. A reviewer may still ask for an explicit switch.
- **Error-code choices** are accepted as listed in the tasks. Each one cites the RFC sentence that allows the choice.
- **Branching:** 3b branches from `main` after Phase 2b merges, because Task 2 edits h3/src/frame.rs.

## Global Constraints

- **These Phase 2a Global Constraints apply unchanged.** The escape rule is different (next bullet), and 2a's h3-specific code tables don't apply:
  - the pins;
  - the Duvet citations: `//= https://www.rfc-editor.org/rfc/rfc9000#section-X` + `//#` with a contiguous quote;
  - the four checks;
  - sans-IO: no async, no trait objects, no closures in exec code;
  - no panics;
  - no allocation sized by an untrusted length before it is checked against the bytes present;
  - per-task matrix bookkeeping, written here as `✅ 3b: <file>`.
- **Escapes:**
  - `crates/quic` contains zero escape tokens.
  - `scripts/verify.sh`'s gate must pass unchanged: 2a's zero-escape grep, or 3a's per-hit accounting once `phase-3a` merges. This plan never edits `verify.sh`.
  - The derived `Debug`/`PartialEq`/`Eq` impls on quic types get one TRUSTED.md row, which each task extends with its type names. This follows the `h3::frame` row.
- **Base branch:** `phase-3b` branches from `main` *after* `phase-2b` merges, because Task 2 edits `crates/h3/src/frame.rs`.
- **Fresh verification evidence:** run `(cd crates/quic && CARGO_TARGET_DIR=<scratch>/vt-3b-tN cargo verus verify)`. It must print `verification results:: … 0 errors` for quic. Task 2 also runs it for `wire` and `h3`.
- **`crates/quic/Cargo.toml`:** the same layout as `crates/h3/Cargo.toml`, with `name = "quic"`. Dependencies are `vstd`, `vest_lib` and `wire = { path = "../wire" }`.
- **Import spec items by glob only** (`use wire::varint::*;`, `use crate::codes::*;`). A named `use` of a spec fn fails under plain `cargo build` with E0432 (3a probe).
- **Exec types with `Vec` or array fields each have a `Spec*` twin** (`Seq` fields) and a `View`. Ensures clauses compare `r@` (or `r.deep_view()` for `Option`/`Result`) with the spec fn.
- **Which theorems are proven, per codec:**
  - (a) exec ≡ spec;
  - (b) `parse(serialize(x)) == x` for every value we send.
  - **Not proven:** `serialize(parse(b)) == b`. RFC 9000 §16 lets every varint except the frame type be non-minimal, so parsing is deliberately many-to-one. The design spec's non-malleability obligation is therefore met for frame types only (§12.4), and §16 waives it everywhere else. This matches 2a's lenient frame header.
- **Where the RFC gives a choice of error code, we pick:**
  - a frame type with a non-minimal encoding is PROTOCOL_VIOLATION (§12.4 MAY);
  - an unknown frame type is FRAME_ENCODING_ERROR;
  - STREAMS_BLOCKED > 2⁶⁰ is FRAME_ENCODING_ERROR (§19.14);
  - STREAM/CRYPTO offset + length > 2⁶²−1 is FRAME_ENCODING_ERROR (§19.6, §19.8);
  - a duplicate known transport parameter is TRANSPORT_PARAMETER_ERROR (§7.4 SHOULD).
- **Server-only, so some serializers are never written:**
  - NEW_TOKEN, Retry, 0-RTT headers, `preferred_address` and `retry_source_connection_id`.
  - The "we never send" MUSTs (§17.2.5.1, §19.7, §18.2) hold because these serializers don't exist.
  - The parser rejects NEW_TOKEN and HANDSHAKE_DONE *as received by a server* (§19.7, §19.20).
- **Codepoints in `quic::codes`** (`pub const`, `u64` unless noted), copied from RFC 9000:
  - **Version:** `QUIC_V1: u32 = 0x0000_0001`.
  - **Frame types (Table 3):**
    - PADDING 0x00, PING 0x01, ACK 0x02 / ACK_ECN 0x03;
    - RESET_STREAM 0x04, STOP_SENDING 0x05, CRYPTO 0x06, NEW_TOKEN 0x07, STREAM 0x08–0x0f;
    - MAX_DATA 0x10, MAX_STREAM_DATA 0x11, MAX_STREAMS_BIDI 0x12 / UNI 0x13;
    - DATA_BLOCKED 0x14, STREAM_DATA_BLOCKED 0x15, STREAMS_BLOCKED_BIDI 0x16 / UNI 0x17;
    - NEW_CONNECTION_ID 0x18, RETIRE_CONNECTION_ID 0x19, PATH_CHALLENGE 0x1a, PATH_RESPONSE 0x1b;
    - CONNECTION_CLOSE 0x1c / CONNECTION_CLOSE_APP 0x1d, HANDSHAKE_DONE 0x1e.
  - **Transport parameters (§18.2):**
    - original_destination_connection_id 0x00, max_idle_timeout 0x01, stateless_reset_token 0x02, max_udp_payload_size 0x03;
    - initial_max_data 0x04, initial_max_stream_data_bidi_local 0x05, initial_max_stream_data_bidi_remote 0x06, initial_max_stream_data_uni 0x07;
    - initial_max_streams_bidi 0x08, initial_max_streams_uni 0x09;
    - ack_delay_exponent 0x0a, max_ack_delay 0x0b, disable_active_migration 0x0c, preferred_address 0x0d;
    - active_connection_id_limit 0x0e, initial_source_connection_id 0x0f, retry_source_connection_id 0x10;
    - reserved: `31·N + 27`.
  - **Transport errors (§20.1):**
    - NO_ERROR 0x00, INTERNAL_ERROR 0x01, CONNECTION_REFUSED 0x02, FLOW_CONTROL_ERROR 0x03;
    - STREAM_LIMIT_ERROR 0x04, STREAM_STATE_ERROR 0x05, FINAL_SIZE_ERROR 0x06, FRAME_ENCODING_ERROR 0x07;
    - TRANSPORT_PARAMETER_ERROR 0x08, CONNECTION_ID_LIMIT_ERROR 0x09, PROTOCOL_VIOLATION 0x0a, INVALID_TOKEN 0x0b;
    - APPLICATION_ERROR 0x0c, CRYPTO_BUFFER_EXCEEDED 0x0d, KEY_UPDATE_ERROR 0x0e, AEAD_LIMIT_REACHED 0x0f;
    - NO_VIABLE_PATH 0x10, CRYPTO_ERROR_BASE 0x0100 (the range is 0x0100–0x01ff).
  - **Limits:**
    - `MAX_CID_LEN: usize = 20` (§17.2);
    - `MIN_INITIAL_DATAGRAM: usize = 1200` (§14.1);
    - `PN_MAX: u64 = VARINT_MAX` (2⁶²−1, §12.3);
    - `MAX_STREAMS_LIMIT: u64 = 1 << 60` (§4.6);
    - `MIN_SHORT_PACKET: usize = 21` (§10.3);
    - `RESET_TOKEN_LEN: usize = 16`;
    - `MAX_ACK_DELAY_LIMIT: u64 = 1 << 14` (§18.2).

## Matrix rows this plan closes

All RFC 9000. Labels are exactly as in `docs/requirements.md`.
- **Task 1:** §17.1.
- **Task 2:** §17.2.2 and §17.4.
- **Task 3:** §6.1, §17.2.1, §17.2.1 (req) "VN: Version 0, CIDs echoed, …" and §10.3.3.
- **Task 4:** §19.3 and §19.3.1.
- **Task 5:**
  - §12.4 (req) "Frame type MUST use shortest possible encoding";
  - §19.6, §19.7, §19.7 (req) "Server treats receipt of NEW_TOKEN …";
  - §19.14;
  - three §19.15 (req) rows: "Length < 1 or > 20 …", "Retire Prior To <= Sequence Number (sending)" and "Retire Prior To > Sequence Number received …".
- **Task 6:** §12.4, §12.5 and §17.2.4.
- **Task 7:** §7.4, §7.4.2, §18.2 and its four (req) rows: "stateless_reset_token not sent by clients", "active_connection_id_limit MUST be at least 2 …", "Receiving active_connection_id_limit < 2 …" and "Server treats receipt of server-only parameter …".

That's 27 rows.

**Rows touched but not closed.** For each, the task appends `3b codec: <file> (closed in 3x)` to Notes:

| Row | Touched by | 3b provides | Closed in |
|---|---|---|---|
| §17.2 | Task 2 | header layout | 3e (reserved bits checked after AEAD) |
| §17.3.1 | Task 2 | header layout | 3e |
| §5.2.2 | Task 3 | no VN below 1200 bytes | 3d |
| §10.3 | Task 3 | reset format and size | 3d |
| §19.8 | Task 5 | 2⁶²−1 offset limit | 3c |
| §19.11 | Task 5 | 2⁶⁰ limit | 3c |
| §19.20 | Task 5 | receipt is PROTOCOL_VIOLATION | 3d |
| §4.6 | Task 7 | transport parameter > 2⁶⁰ | 3c |

## Review Focus

1. **An ACK whose range count exceeds what the packet can carry** (§20.1 names this case). Range count 2⁶²−1 followed by 3 bytes must return FRAME_ENCODING_ERROR, with no allocation sized by the count. Pinned in Task 4: `ack_count_exceeds_bytes`.
2. **Packet-number length at an exact power-of-two distance.**
   - §17.1 says "more than twice as large a range". A.2's `log(n,2)+1` pseudocode gives 2 bytes for distance 0x8000, which violates that. The prose MUST wins, so the answer is 3 bytes; 0x7fff gives 2.
   - Pinned in Task 1: `pn_len_boundary`.
3. **Permission and type are judged before the body.**
   - A STREAM type byte with a truncated body inside an Initial is PROTOCOL_VIOLATION, not FRAME_ENCODING_ERROR.
   - PING encoded as `[0x40, 0x01]` is PROTOCOL_VIOLATION.
   - Pinned in Task 6: `permission_before_body`, and in Task 5: `frame_type_encoding`.
4. **Version-independent connection-ID lengths** (§17.2.1: version-specific CID rules MUST NOT influence VN).
   - An unsupported version with a 21-byte or 255-byte DCID in a datagram of at least 1200 bytes gets a VN.
   - Version 1 with a 21-byte DCID is dropped.
   - Version 0, or a datagram of 1199 bytes, gets nothing.
   - Pinned in Task 3: `vn_cid_lengths`.
5. **Arithmetic at the 2⁶² edge.**
   - STREAM/CRYPTO with offset VARINT_MAX and length 0 is accepted; with length 1 it is rejected.
   - Packet-number decode next to 2⁶²−1 follows A.3's overflow guards.
   - Pinned in Task 5: `offset_limit`, and in Task 1: `decode_pn_edges`.

---

### Task 1: `quic` crate, codes, packet numbers

**Files:**
- Create: `crates/quic/Cargo.toml`, `crates/quic/src/lib.rs`, `crates/quic/src/codes.rs`, `crates/quic/src/pn.rs`
- Modify: `Cargo.lock`
- Test: `crates/quic/tests/pn.rs`

**Interfaces:**
- Produces (`quic::codes`): every constant in the Global Constraints.
- Produces (`quic::pn`):
  - **`pub open spec fn pn_len_ok(full: u64, largest_acked: Option<u64>, n: nat) -> bool`** (§17.1). It holds when `1 <= n <= 4` and:
    - `largest_acked` is `None`: `pow2(8n) > full` ("the full packet number MUST be included");
    - `largest_acked` is `Some(a)`: `pow2(8n) > 2·(full − a)` ("more than twice as large a range").
  - **`pub fn pn_encode_len(full: u64, largest_acked: Option<u64>) -> (r: Option<u8>)`**.
    - requires `full <= PN_MAX`, and `largest_acked matches Some(a) ==> a < full`;
    - ensures `r == Some(n)` ⇒ `pn_len_ok(full, la, n)` and no smaller `m` is ok;
    - ensures `r is None` ⇒ `!pn_len_ok(full, la, 4)`. That means more than 2³¹ packets are unacked; 3d treats it as an internal limit.
  - **`pub open spec fn rfc_decode_pn(largest: Option<u64>, truncated: u64, nbits: nat) -> int`**. This is a literal transcription of the A.3 pseudocode, with `expected_pn = largest + 1`, or 0 when `largest` is `None`.
  - **`pub fn decode_pn(largest: Option<u64>, truncated: u64, pn_len: u8) -> (r: u64)`**.
    - requires `1 <= pn_len <= 4`, `truncated < pow2(8·pn_len)`, and `largest matches Some(l) ==> l < PN_MAX`;
    - ensures `r == rfc_decode_pn(largest, truncated, 8·pn_len)`.
  - **`pub proof fn theorem_decode_pn_recovers(full: u64, largest: Option<u64>, pn_len: u8)`**.
    - requires `1 <= pn_len <= 4`, `full <= PN_MAX`, and `expected − pow2(8·pn_len − 1) < full <= expected + pow2(8·pn_len − 1)`;
    - ensures `rfc_decode_pn(largest, full % pow2(8·pn_len), 8·pn_len) == full`.
  - **`pub fn put_pn(full: u64, pn_len: u8, out: &mut Vec<u8>)`** writes the low `pn_len` bytes, big-endian.
  - **`pub fn read_pn(b: &[u8]) -> (r: u64)`**, which requires `1 <= b.len() <= 4`. It is the big-endian inverse of `put_pn`; prove `read_pn(put_pn(full, n)) == full % pow2(8n)`.

- [ ] **Step 1: Failing tests** in `crates/quic/tests/pn.rs`:
  - `a2_encode`: `pn_encode_len(0xac5c02, Some(0xabe8b3)) == Some(2)` and `pn_encode_len(0xace8fe, Some(0xabe8b3)) == Some(3)` (RFC 9000 A.2).
  - `a3_decode`: `decode_pn(Some(0xa82f30ea), 0x9b32, 2) == 0xa82f9b32` (RFC 9000 A.3).
  - `rfc9001_a5_decode`: `decode_pn(Some(654360563), 0x00bff4, 3) == 654360564`. A.5's packet number, decoded from the previous one.
  - `pn_len_boundary`:
    - `pn_encode_len(0x8000, Some(0)) == Some(3)` and `pn_encode_len(0x7fff, Some(0)) == Some(2)`;
    - `pn_encode_len((1 << 31) - 1, Some(0)) == Some(4)` and `pn_encode_len(1 << 31, Some(0)) == None`;
    - `pn_encode_len(255, None) == Some(1)` and `pn_encode_len(256, None) == Some(2)`.
  - `decode_pn_edges`:
    - `decode_pn(None, 0, 1) == 0`;
    - `decode_pn(Some(0xff), 0x00, 1) == 0x100`;
    - `decode_pn(Some(0x100), 0xff, 1) == 0xff`;
    - `decode_pn(Some(PN_MAX - 1), 0xff, 1) == PN_MAX`;
    - `decode_pn(Some(0x3fff_ffff_ffff_ff7f), 0x00, 1) == 0x3fff_ffff_ffff_ff00`. A.3's `< (1 << 62) - pn_win` guard blocks the `+ pn_win`.
  - `pn_bytes`: `put_pn(0x2700bff4, 3)` writes `[0x00, 0xbf, 0xf4]`, and `read_pn` of that is `0x00bff4`.
- [ ] **Step 2:** `cargo test -p quic`. Expected to fail: the crate doesn't exist yet.
- [ ] **Step 3: Implement `codes.rs` and `pn.rs`.**
  - Duvet-cite §17.1 (both MUST sentences), Appendix A.2 and Appendix A.3 (the pseudocode lines).
  - `pn_encode_len` loops n = 1..=4 and tests `pn_len_ok` with u64 arithmetic: `2·(full − a) < 2⁶³`, so nothing overflows.
- [ ] **Step 4:** Run the four checks. `cargo test -p quic` passes 6 tests.
- [ ] **Step 5: Commit:** `feat(quic): crate, RFC 9000 codepoints, verified packet-number encode/decode (§17.1, A.2-A.3)`
- [ ] **Step 6: Matrix commit:** add `✅ 3b: crates/quic/src/pn.rs` to §17.1, and note "A.2 pseudocode under-sizes at exact powers of two; §17.1 prose used". Commit: `docs: mark RFC 9000 §17.1 closed in 3b`.

---

### Task 2: Varint helpers into `wire`; long and short headers

**Files:**
- Modify:
  - `crates/wire/src/varint.rs`: add the helpers listed below.
  - `crates/h3/src/frame.rs`: delete the moved items, and change `use wire::varint::*;` to `pub use wire::varint::*;` so `h3::frame::parse_varint` and the others still resolve for 2b code.
  - `TRUSTED.md`.
- Create: `crates/quic/src/header.rs`
- Test: `crates/quic/tests/header.rs`

**Interfaces:**
- **Produces (`wire::varint`).** These move from `h3::frame` with their signatures unchanged:
  - `pub open spec fn spec_varint(v)`;
  - `pub fn parse_varint(b: &[u8]) -> Option<(usize, u64)>`;
  - `pub fn put_varint(v: u64, out: &mut Vec<u8>)` (now `pub`);
  - `pub proof fn lemma_decode_len_bounds(b)` (now `pub`);
  - `lemma_decode_prefix`, `completes`, `lemma_decode_extend`;
  - the private `lemma_decode_zero`.
  - New: `pub fn varint_len(v: u64) -> (n: usize)`, which requires `v <= VARINT_MAX` and ensures `n == rfc_varint_min_len(v)`.
- **Produces (`quic::header`).** Header protection covers byte 0's low bits and the packet-number bytes, so parsing stops at `pn_offset`. 3e removes protection and then uses the first-byte helpers below.
  - `pub enum LongType { Initial, ZeroRtt, Handshake }`.
  - `pub enum Header`, with three variants:
    - `Long { ty: LongType, dcid: Vec<u8>, scid: Vec<u8>, token: Vec<u8>, pn_offset: usize, packet_end: usize }`. The version is always QUIC_V1. `packet_end = pn_offset + Length` is what §12.2 coalescing needs.
    - `Short { dcid: Vec<u8>, pn_offset: usize }`.
    - `UnsupportedVersion { version: u32, dcid: Vec<u8>, scid: Vec<u8> }`.
  - **`pub open spec fn rfc_long_header(b: Seq<u8>) -> Option<SpecHeader>`** (§17.2, §17.2.2, §17.2.3, §17.2.4, §17.2.5). It returns `None` (drop) in these cases:
    - `b[0] & 0x80 == 0` (not a long header);
    - the input is shorter than the fields it announces;
    - the version is 0. A server never receives VN, and §6.1 forbids answering one;
    - for version 1:
      - fixed bit `0x40` is 0;
      - DCID length > 20 or SCID length > 20;
      - the type is Retry (3);
      - Initial's token is truncated;
      - `Length > b.len() − pn_offset`.
    - For any other version, it returns `UnsupportedVersion` with CIDs of 0–255 bytes, and checks no fixed bit.
  - **`pub open spec fn rfc_header(b: Seq<u8>, dcid_len: nat) -> Option<SpecHeader>`** dispatches on bit `0x80`.
    - A long header goes to `rfc_long_header`.
    - A short header returns `None` if `b.len() < MIN_SHORT_PACKET` (§10.3) or if the fixed bit is 0 (§17.3.1). Otherwise it returns `Short { dcid: b[1..1+dcid_len], pn_offset: 1 + dcid_len }`. The spin bit is never read (§17.4).
  - `pub fn parse_long_header(b: &[u8]) -> Option<Header>` and `pub fn parse_header(b: &[u8], dcid_len: usize) -> Option<Header>`. The latter requires `1 <= dcid_len <= MAX_CID_LEN`, because we issue non-zero CIDs (matrix §5.1). Both are exec ≡ spec.
  - **`pub fn serialize_long_header(ty: LongType, dcid: &[u8], scid: &[u8], pn: u64, pn_len: u8, payload_len: usize, out: &mut Vec<u8>) -> (pn_offset: usize)`.**
    - requires `ty != ZeroRtt`, CIDs ≤ 20 bytes, `1 <= pn_len <= 4`, and `pn_len + payload_len <= VARINT_MAX`.
    - It writes:
      - first byte `0xc0 | type << 4 | (pn_len − 1)` (reserved bits 0);
      - the version, the CID lengths and the CIDs;
      - Token Length 0 for Initial (§17.2.2);
      - `Length = pn_len + payload_len`;
      - then `put_pn`.
    - `payload_len` counts the protected payload, including the 16-byte AEAD tag. The return value is the PN offset relative to the first byte written.
  - **`pub fn serialize_short_header(dcid: &[u8], key_phase: bool, pn: u64, pn_len: u8, out: &mut Vec<u8>) -> (pn_offset: usize)`.** First byte `0x40 | key_phase << 2 | (pn_len − 1)`: spin bit 0 (§17.4), reserved 0. A DCID of 0..=20 bytes is allowed, since the client may use an empty CID.
  - **Theorem:** for every `p` with `p.len() == payload_len` and any `rest`, `rfc_long_header(written ++ p ++ rest)` gives `Long` with the serialized fields, `token == []`, `pn_offset` and `packet_end == written.len() + payload_len`. Prove the same for short headers with `dcid_len == dcid.len() >= 1`, when the whole packet is at least `MIN_SHORT_PACKET` bytes.
  - **First-byte helpers, used after header-protection removal:**
    - `pub fn first_byte_pn_len(b0: u8) -> u8` = `(b0 & 3) + 1`;
    - `pub fn first_byte_key_phase(b0: u8) -> bool` = `b0 & 0x04 != 0`;
    - `pub fn reserved_bits_zero(b0: u8, long: bool) -> bool`, with mask `0x0c` for long headers and `0x18` for short ones.
    - Each has a cited spec twin. Turning a `false` into PROTOCOL_VIOLATION happens only after AEAD succeeds, which is 3e's job.

- [ ] **Step 1: Failing tests** in `crates/quic/tests/header.rs`. Use RFC 9001 Appendix A, unprotected headers only:
  - **`a2_client_initial_header`:**
    - `serialize_long_header(Initial, 8394c8f03e515708, [], pn=2, pn_len=4, payload_len=1178)` writes exactly `c300000001088394c8f03e5157080000449e00000002` and returns 18.
    - The *protected* A.2 header prefix `c000000001088394c8f03e5157080000449e`, padded with zero bytes to 1200, parses with `parse_header(_, 8)` to `Long{Initial, dcid=8394c8f03e515708, scid=[], token=[], pn_offset=18, packet_end=1200}`.
  - **`a3_server_initial_header`:** `serialize_long_header(Initial, [], f067a5502a4262b5, pn=1, pn_len=2, payload_len=115)` writes exactly `c1000000010008f067a5502a4262b50040750001`.
  - **`a5_short_header`:** `serialize_short_header([], false, 654360564, 3)` writes `4200bff4`. Also check `first_byte_pn_len(0x42) == 3` and `first_byte_key_phase(0x42) == false`.
  - **`header_drops`.** Each case returns `None`:
    - version 1 with fixed bit 0 (`0x80` first byte);
    - version 1 with a DCID length of 21;
    - a version-1 Retry (`0xf0` first byte);
    - version 0;
    - an Initial whose Length is 1 byte more than remains;
    - an Initial whose token length is 5 with 2 bytes left;
    - a 20-byte short packet;
    - a short packet with fixed bit 0;
    - `[]`.
  - **`unsupported_version`:** `0x80`, `1a2a3a4a`, DCID length 21 (21 bytes), SCID length 0 → `UnsupportedVersion{0x1a2a3a4a, 21 bytes, []}`. The fixed bit is 0, which is accepted because the check is version-specific.
  - **`reserved_bits`:**
    - `reserved_bits_zero(0xc3, true)` and `reserved_bits_zero(0x44, false)` are true;
    - `reserved_bits_zero(0xcb, true)` and `reserved_bits_zero(0x48, false)` are false;
    - `first_byte_key_phase(0x44)` is true.
  - **`header_roundtrip`:**
    - a Handshake header with 20-byte CIDs and pn_len 1, plus a 30-byte payload, parses back;
    - a short header with an 8-byte DCID, a key phase and pn_len 2, padded to 40 bytes, parses back with `dcid_len = 8`.
- [ ] **Step 2:** Run the tests and confirm they fail.
- [ ] **Step 3: Implement.**
  - Do the helper move first, then re-run `cargo test -p h3` and verify `h3`; it must pass unchanged.
  - Then write `header.rs` with Duvet citations of §17.2, §17.2.1, §17.2.2, §17.3.1, §17.4 and §10.3. For §17.4, cite "MUST ignore any incoming value" and "An endpoint that does not support this feature MUST disable it".
  - Allocate a CID or token only after its length has been checked against `b.len()`.
  - Add the TRUSTED.md row "Derived `Debug`/`PartialEq`/`Eq` on `quic::header::{Header, LongType}`" (test support, never removed). Tasks 4–7 extend it with `AckFrame`, `Frame`, `PacketKind` and `TransportParams`.
- [ ] **Step 4:** Run the four checks. That means fresh-target `cargo verus verify` for `wire`, `h3` and `quic`; and `cargo test` across the workspace, which still passes every 2a/2b test.
- [ ] **Step 5: Commit:** `feat(quic): verified long/short header codec split around header protection (RFC 9000 §17.2-17.4); move varint helpers to wire`
- [ ] **Step 6: Matrix commit:**
  - `✅ 3b: crates/quic/src/header.rs` on §17.2.2 (server Token Length 0).
  - On §17.4: "spin bit unsupported, so always disabled: written 0, never read; no admin switch is needed for a feature that cannot be enabled".
  - "touched" notes on §17.2 and §17.3.1.

---

### Task 3: Version Negotiation and Stateless Reset

**Files:**
- Create: `crates/quic/src/stateless.rs`
- Test: `crates/quic/tests/stateless.rs`

**Interfaces:**
- Consumes: `rfc_long_header`, `parse_long_header`, `Header::UnsupportedVersion`, `QUIC_V1` and `MIN_INITIAL_DATAGRAM`.
- **Produces `pub fn version_negotiation(datagram: &[u8]) -> (r: Option<Vec<u8>>)`,** ensuring `r.deep_view() == rfc_version_negotiation(datagram@)`.
  - The spec returns `Some` iff `datagram.len() >= 1200` and the datagram's first packet is `UnsupportedVersion{dcid, scid}`.
  - The bytes are `0xc0` (§17.2.1: Unused, with 0x40 set), version `00000000`, `scid.len()`, `scid`, `dcid.len()`, `dcid`, then `00000001`.
  - It covers:
    - §6.1: version 0 parses to `None`;
    - §5.2.2's small-datagram drop;
    - §17.2.1's echo rules;
    - at most one VN per datagram, because the shell calls this once per datagram, which 3e pins.
- **Produces `pub fn stateless_reset(trigger_len: usize, unpredictable: &[u8], token: &[u8]) -> (r: Option<Vec<u8>>)`.**
  - requires `unpredictable.len() >= 27` and `token.len() == RESET_TOKEN_LEN`.
  - `r` is `None` iff `trigger_len <= MIN_SHORT_PACKET`. Then no reset can be at least 21 bytes and also smaller than the trigger.
  - Otherwise the length is `L = min(trigger_len − 1, 43)` and the bytes are `[0x40 | (u[0] & 0x3f)] ++ u[1..L−16] ++ token`.
  - Ensures:
    - `21 <= L < trigger_len` (§10.3.3);
    - `L < 3·trigger_len` (§10.3);
    - `r[0] & 0xc0 == 0x40`, the short-header form (§10.3);
    - the last 16 bytes equal `token`.
  - `// ponytail: fixed 43-byte cap for large triggers; vary the length if reset fingerprinting matters.`
  - Detection is 3d's job.

- [ ] **Step 1: Failing tests:**
  - **`vn_response`:** a 1200-byte datagram `c0 1a2a3a4a 08 0001020304050607 04 0a0b0c0d` followed by zeros → `Some(c0 00000000 04 0a0b0c0d 08 0001020304050607 00000001)`.
  - **`vn_cid_lengths`:**
    - a DCID of 21 bytes and one of 255 bytes, with an unsupported version, in 1200-byte datagrams → `Some`, each echoed as the VN's SCID;
    - the same 21-byte DCID with version 1 → `None`.
  - **`vn_not_sent`.** Each case returns `None`:
    - the `vn_response` input truncated to 1199 bytes;
    - version `00000001`;
    - version `00000000`;
    - a 1200-byte short-header datagram.
  - **`stateless_reset_sizes`** (`u = 0..27`, `token = [0xaa; 16]`):
    - trigger 21 → `None`;
    - trigger 22 → length 21;
    - trigger 43 → length 42;
    - trigger 44 → length 43;
    - trigger 1200 → length 43;
    - in every `Some` case, `r[0] & 0xc0 == 0x40` and the last 16 bytes are `0xaa`.
- [ ] **Step 2:** Run the tests and confirm they fail.
- [ ] **Step 3:** Implement with Duvet citations of §6.1, §17.2.1 (Version 0, the SCID→DCID and DCID→SCID echo, "MUST NOT influence"), §10.3 (size and short-header form) and §10.3.3.
- [ ] **Step 4:** Run the four checks.
- [ ] **Step 5: Commit:** `feat(quic): verified Version Negotiation and Stateless Reset builders (RFC 9000 §6, §10.3, §17.2.1)`
- [ ] **Step 6: Matrix commit:**
  - `✅ 3b: crates/quic/src/stateless.rs` on §6.1, §17.2.1, §17.2.1 (req) and §10.3.3;
  - "touched" notes on §5.2.2 and §10.3.

---

### Task 4: ACK frame codec

**Files:**
- Create: `crates/quic/src/ack.rs`
- Modify: `TRUSTED.md` (extend the derived-impl row)
- Test: `crates/quic/tests/ack.rs`

**Interfaces:**
- Consumes: `parse_varint`, `put_varint` and `FRAME_ENCODING_ERROR`.
- Produces (`quic::ack`):
  - `pub struct AckFrame { pub largest: u64, pub delay: u64, pub first_range: u64, pub ranges: Vec<(u64, u64)>, pub ecn: Option<(u64, u64, u64)> }`. `ranges` holds (Gap, ACK Range Length) pairs in wire order.
  - **`pub open spec fn rfc_ack_ranges_valid(largest: u64, first_range: u64, ranges: Seq<(u64, u64)>) -> bool`** (§19.3.1):
    - `first_range <= largest`;
    - then, with `smallest = largest − first_range`, each `(gap, len)` gives `largest' = smallest − gap − 2 ≥ 0` and `smallest' = largest' − len ≥ 0`.
  - **`pub open spec fn ack_contains(a: SpecAck, pn: u64) -> bool`**: `pn` lies in one of the ranges. 3d uses it.
  - **`pub open spec fn rfc_ack(ty: u64, b: Seq<u8>) -> Result<(SpecAck, nat), u64>`**, where `b` starts after the type.
    - It reads, in order: Largest, Delay, Range Count, First Range, Count × (Gap, Length), then three ECN counts iff `ty == 0x03`.
    - Any missing varint is FRAME_ENCODING_ERROR, and so is `!rfc_ack_ranges_valid`.
  - **`pub fn parse_ack(ty: u64, b: &[u8]) -> (r: Result<(AckFrame, usize), u64>)`**, which requires `ty == 0x02 || ty == 0x03` and is exec ≡ spec.
    - The range loop pushes one pair per iteration as it parses. It never reserves capacity from the count.
    - It tracks `smallest` in `u64`, checking `gap + 2 <= smallest` and `len <= largest'`.
  - **`pub fn serialize_ack(a: &AckFrame, out: &mut Vec<u8>)`** writes the whole frame, type included: 0x03 iff `ecn is Some`.
    - requires `rfc_ack_ranges_valid`, every field ≤ VARINT_MAX, and `ranges.len() <= VARINT_MAX`;
    - ensures `out@ == old(out)@ + spec_ack_bytes(a@)`.
  - **`theorem_ack_roundtrip`:** `rfc_ack(ty, spec_ack_bytes(a).skip(1) + rest) == Ok((a, len − 1))`.

- [ ] **Step 1: Failing tests:**
  - **`ack_basic`:** `parse_ack(2, [0x05, 0x00, 0x00, 0x02])` → `Ok(({largest 5, delay 0, first_range 2, ranges [], ecn None}, 4))`. That acknowledges 3..=5.
  - **`ack_ranges`:** `parse_ack(2, [0x0a, 0x00, 0x01, 0x01, 0x01, 0x02])` → `ranges [(1, 2)]`, consumed 6. The ranges are 9..=10 and 4..=6, so `ack_contains` holds for 4, 6, 9 and 10 and not for 7, 8 or 3. Assert this through a test-local mirror of the spec walk.
  - **`ack_ecn`:** `parse_ack(3, [0, 0, 0, 0, 1, 2, 3])` → `ecn Some((1, 2, 3))`, consumed 7.
  - **`ack_negative`:**
    - `[0x02, 0x00, 0x00, 0x03]` (first range > largest) → `Err(FRAME_ENCODING_ERROR)`;
    - `[0x05, 0x00, 0x01, 0x00, 0x04, 0x00]` → `Err(FRAME_ENCODING_ERROR)`: the gap gives 5−4−2 = −1;
    - `[0x05, 0x00, 0x01, 0x00, 0x03, 0x00]` → `Ok`, a range of 0..=0;
    - `[0x05, 0x00, 0x01, 0x00, 0x03, 0x01]` → `Err(FRAME_ENCODING_ERROR)`: the length goes below 0.
  - **`ack_count_exceeds_bytes`:** `[0x05, 0x00, 0xff ×8 (count 2⁶²−1), 0x00, 0x00, 0x00]` → `Err(FRAME_ENCODING_ERROR)`.
  - **`ack_roundtrip`:** `{largest 1000, delay 25, first_range 3, ranges [(0, 0), (10, 5)], ecn Some((7, 0, 1))}` serializes, then parses back from `bytes[1..]` with type `bytes[0] == 0x03`.
- [ ] **Step 2:** Run the tests and confirm they fail.
- [ ] **Step 3:** Implement with Duvet citations of §19.3 (both types "MUST properly handle"), §19.3.1 (the negative-PN MUST) and §19.3.2.
- [ ] **Step 4:** Run the four checks.
- [ ] **Step 5: Commit:** `feat(quic): verified ACK frame codec with range validation (RFC 9000 §19.3)`
- [ ] **Step 6: Matrix commit:** `✅ 3b: crates/quic/src/ack.rs` on §19.3 and §19.3.1.

---

### Task 5: Transport frame codec

**Files:**
- Create: `crates/quic/src/frame.rs`
- Modify: `TRUSTED.md` (extend the derived-impl row)
- Test: `crates/quic/tests/frame.rs`

**Interfaces:**
- Consumes: `AckFrame`, `parse_ack`, `serialize_ack`, `rfc_ack` (Task 4); `parse_varint`, `put_varint`, `varint_len` (Task 2); the codes.
- Produces (`quic::frame`):
  - **The `Frame` enum:**
    - `Padding`, `Ping`, `Ack(AckFrame)`;
    - `ResetStream { stream_id: u64, error_code: u64, final_size: u64 }`;
    - `StopSending { stream_id: u64, error_code: u64 }`;
    - `Crypto { offset: u64, data: Vec<u8> }`;
    - `Stream { stream_id: u64, offset: u64, data: Vec<u8>, fin: bool }`;
    - `MaxData(u64)`, `MaxStreamData { stream_id: u64, max: u64 }`, `MaxStreams { bidi: bool, max: u64 }`;
    - `DataBlocked(u64)`, `StreamDataBlocked { stream_id: u64, max: u64 }`, `StreamsBlocked { bidi: bool, max: u64 }`;
    - `NewConnectionId { seq: u64, retire_prior_to: u64, cid: Vec<u8>, reset_token: [u8; 16] }`;
    - `RetireConnectionId(u64)`;
    - `PathChallenge([u8; 8])`, `PathResponse([u8; 8])`;
    - `ConnectionClose { app: bool, error_code: u64, frame_type: u64, reason: Vec<u8> }`;
    - `HandshakeDone`.
    - There is no NEW_TOKEN variant (Global Constraints).
  - **`pub open spec fn rfc_frame_type(b: Seq<u8>) -> Result<(u64, nat), u64>`** and its exec twin **`pub fn parse_frame_type(b: &[u8]) -> (r: Result<(u64, usize), u64>)`** (exec ≡ spec):
    - `Ok((v, n))` iff `rfc_varint_decode(b) == Some((n, v))` and `n == rfc_varint_min_len(v)`;
    - a decodable but non-minimal type → `Err(PROTOCOL_VIOLATION)`;
    - an undecodable one → `Err(FRAME_ENCODING_ERROR)`.
    - Parse leniently, then compare with `varint_len`. `QuicVarInt<true>` alone can't tell non-minimal from truncated, and `theorem_matches_rfc` links the two.
  - **`pub open spec fn rfc_frame_body(ty: u64, b: Seq<u8>) -> Result<(SpecFrame, nat), u64>`.** Any truncation is FRAME_ENCODING_ERROR. Per type:
    - **0x00, 0x01:** consume 0 bytes.
    - **0x02/0x03:** `rfc_ack`.
    - **0x04, 0x05:** 3 and 2 varints.
    - **0x06:** Offset, Length, Data. Length > remaining, or Offset + Length > VARINT_MAX, is FRAME_ENCODING_ERROR.
    - **0x07:** PROTOCOL_VIOLATION, because the server received it (§19.7).
    - **0x08–0x0f:** Stream ID; Offset iff `ty & 0x04` (else 0); Length iff `ty & 0x02` (else the rest of `b`); `fin = ty & 0x01`. The same two checks as CRYPTO apply.
    - **0x10, 0x14, 0x19:** 1 varint.
    - **0x11, 0x15:** 2 varints.
    - **0x12/0x13 and 0x16/0x17:** 1 varint, and a value > `MAX_STREAMS_LIMIT` is FRAME_ENCODING_ERROR.
    - **0x18:** Seq and Retire Prior To (varints), then a 1-byte Length, the CID and a 16-byte token. Length ∉ 1..=20 is FRAME_ENCODING_ERROR, and so is `retire_prior_to > seq`.
    - **0x1a/0x1b:** 8 bytes.
    - **0x1c:** Error Code, Frame Type, Reason Length and the Reason.
    - **0x1d:** Error Code, Reason Length and the Reason, with `frame_type = 0`.
    - **0x1e:** PROTOCOL_VIOLATION, because the server received it (§19.20).
    - **Anything else:** FRAME_ENCODING_ERROR (§12.4).
  - **`pub open spec fn rfc_frame(b: Seq<u8>) -> Result<(SpecFrame, nat), u64>`**: `rfc_frame_type`, then `rfc_frame_body` on the rest, with the consumed counts added.
  - **`pub fn parse_frame_body(ty: u64, b: &[u8]) -> (r: Result<(Frame, usize), u64>)`** and **`pub fn parse_frame(b: &[u8]) -> (r: Result<(Frame, usize), u64>)`**. Each is exec ≡ its spec (`rfc_frame_body`, `rfc_frame`).
  - **`pub open spec fn frame_wf(f: SpecFrame) -> bool`:**
    - every u64 ≤ VARINT_MAX;
    - Stream/Crypto: `offset + data.len() <= VARINT_MAX`;
    - MaxStreams/StreamsBlocked: `max <= MAX_STREAMS_LIMIT`;
    - NewConnectionId: `1 <= cid.len() <= 20` and `retire_prior_to <= seq` (§19.15, sending);
    - ConnectionClose: `app ==> frame_type == 0`;
    - Ack: `rfc_ack_ranges_valid` and Task 4's field bounds.
  - **`pub fn frame_type_of(f: &Frame) -> u64`** returns the type byte `serialize_frame` writes. For STREAM that is `0x08 | (offset > 0 ? 0x04 : 0) | 0x02 | fin`: LEN is always set.
  - **`pub fn serialize_frame(f: &Frame, out: &mut Vec<u8>)`** requires `frame_wf(f@)`, and ensures `out@ == old(out)@ + spec_frame_bytes(f@)`. The type is written minimally, which is §12.4's sender half.
  - **`theorem_frame_roundtrip(f, rest)`:** if `frame_wf(f)` and `f !is HandshakeDone`, then `rfc_frame(spec_frame_bytes(f) + rest) == Ok((f, spec_frame_bytes(f).len()))`.

- [ ] **Step 1: Failing tests:**
  - **`frame_type_encoding`:**
    - `parse_frame_type([0x01]) == Ok((1, 1))`;
    - `[0x40, 0x01]` → `Err(PROTOCOL_VIOLATION)`;
    - `[]` and `[0x40]` → `Err(FRAME_ENCODING_ERROR)`;
    - `parse_frame([0x1f])` → `Err(FRAME_ENCODING_ERROR)`;
    - `parse_frame([0x7f, 0xff])` (type 0x3fff, minimal) → `Err(FRAME_ENCODING_ERROR)`.
  - **`stream_variants`:**
    - `[0x08, 0x04, 0x61, 0x62]` → `Stream{4, 0, "ab", false}`, consumed 4;
    - `[0x0f, 0x04, 0x05, 0x01, 0x61, 0x99]` → `Stream{4, 5, "a", true}`, consumed 5;
    - `[0x0a, 0x04, 0x05, 0x61]` → `Err(FRAME_ENCODING_ERROR)`.
  - **`offset_limit`:**
    - `[0x0e, 0x00, 0xff×8, 0x00]` → `Ok`, offset VARINT_MAX with length 0;
    - `[0x0e, 0x00, 0xff×8, 0x01, 0x61]` → `Err(FRAME_ENCODING_ERROR)`;
    - `[0x06, 0xff×8, 0x01, 0x61]` → `Err(FRAME_ENCODING_ERROR)`.
  - **`ncid_rules`:**
    - `[0x18, 0x01, 0x00, 0x08, 8×0x11, 16×0x22]` → `Ok(NewConnectionId{1, 0, 8×0x11, 16×0x22})`;
    - a Length byte of 0 → `Err(FRAME_ENCODING_ERROR)`;
    - a Length byte of 21 (with 21 bytes) → `Err(FRAME_ENCODING_ERROR)`;
    - `[0x18, 0x01, 0x02, …]` (retire_prior_to 2 > seq 1) → `Err(FRAME_ENCODING_ERROR)`.
  - **`stream_count_limit`:**
    - `[0x12, 0xd0, 0, 0, 0, 0, 0, 0, 0]` (2⁶⁰) → `Ok(MaxStreams{true, 1<<60})`;
    - `[0x12, 0xd0, 0, 0, 0, 0, 0, 0, 0x01]` → `Err(FRAME_ENCODING_ERROR)`;
    - the same two cases with type 0x17 → `StreamsBlocked{false, 1<<60}` and `Err(FRAME_ENCODING_ERROR)`.
  - **`server_receive_rules`:** `[0x07, 0x01, 0xaa]` → `Err(PROTOCOL_VIOLATION)`, and `[0x1e]` → `Err(PROTOCOL_VIOLATION)`.
  - **`close_frames`:**
    - `[0x1c, 0x0a, 0x06, 0x02, 0x68, 0x69]` → `ConnectionClose{false, 0x0a, 6, "hi"}`;
    - `[0x1d, 0x01, 0x00]` → `ConnectionClose{true, 1, 0, ""}`;
    - `[0x1c, 0x00, 0x00, 0x05, 0x68]` → `Err(FRAME_ENCODING_ERROR)`.
  - **`path_frames`:** `[0x1a, 1, 2, 3, 4, 5, 6, 7, 8]` → `PathChallenge([1..=8])`. The same with 7 data bytes → `Err(FRAME_ENCODING_ERROR)`.
  - **`frame_roundtrip`:**
    - one well-formed value of each variant except `HandshakeDone` serializes, then `parse_frame` gives it back with `consumed == bytes.len()`;
    - `serialize_frame(HandshakeDone)` writes `[0x1e]`;
    - `Stream{4, 0, "ab", false}` serializes to `[0x0a, 0x04, 0x02, 0x61, 0x62]`.
- [ ] **Step 2:** Run the tests and confirm they fail.
- [ ] **Step 3:** Implement with Duvet citations of:
  - §12.4: the shortest-encoding MUST and the unknown-type MUST;
  - §19.6 and §19.8: the 2⁶²−1 limit;
  - §19.7: "A server MUST treat receipt …";
  - §19.11 and §19.14: the 2⁶⁰ limit;
  - §19.15: Length, and the two Retire Prior To MUSTs;
  - §19.20: the receipt MUST.
  Allocate `data`, `cid` or `reason` only after their length has been checked against the remaining bytes.
- [ ] **Step 4:** Run the four checks.
- [ ] **Step 5: Commit:** `feat(quic): verified transport frame codec (RFC 9000 §12.4, §19)`
- [ ] **Step 6: Matrix commit:**
  - `✅ 3b: crates/quic/src/frame.rs` on §12.4 (req), §19.6, §19.7, §19.7 (req), §19.14 and the three §19.15 (req) rows;
  - "touched" notes on §19.8, §19.11 and §19.20.

---

### Task 6: Packet payloads and frame permissions

**Files:**
- Create: `crates/quic/src/payload.rs`
- Modify: `TRUSTED.md` (extend the derived-impl row)
- Test: `crates/quic/tests/payload.rs`

**Interfaces:**
- Consumes: `rfc_frame_type`/`parse_frame_type`, `rfc_frame_body`/`parse_frame_body`, `serialize_frame`, `frame_type_of`, `frame_wf`, `Frame` and `AckFrame`.
- Produces (`quic::payload`):
  - `pub enum PacketKind { Initial, Handshake, OneRtt }`. 0-RTT payloads are never parsed: 3d discards those packets.
  - **`pub open spec fn frame_permitted(ty: u64, k: PacketKind) -> bool`** transcribes the "Pkts" column of RFC 9000 Table 3 together with §12.5.
    - In Initial and Handshake, only `0x00, 0x01, 0x02, 0x03, 0x06, 0x1c` are allowed.
    - In OneRtt, every type `0x00..=0x1e` is allowed.
    - Plus the exec `frame_permitted`.
  - **`pub open spec fn ack_eliciting(ty: u64) -> bool`** transcribes the Table 3 "N" marking: not `0x00`, `0x02`, `0x03`, `0x1c` or `0x1d`. Plus `pub fn is_ack_eliciting(frames: &[Frame]) -> bool`.
  - **`pub open spec fn rfc_payload(b: Seq<u8>, k: PacketKind) -> Result<Seq<SpecFrame>, u64>`:**
    - `b.len() == 0` → PROTOCOL_VIOLATION (§12.4: no frames).
    - Otherwise, repeat until `b` is consumed:
      1. read `rfc_frame_type`, and stop with its error if it fails;
      2. a type > 0x1e → FRAME_ENCODING_ERROR;
      3. `!frame_permitted(ty, k)` → PROTOCOL_VIOLATION (§12.4, §17.2.4), *before* the body is read;
      4. otherwise `rfc_frame_body`, and stop with its error if it fails.
    - The first error wins. `Padding` is dropped from the result, so a payload of only padding is `Ok([])`.
  - **`pub fn parse_payload(b: &[u8], k: PacketKind) -> (r: Result<Vec<Frame>, u64>)`**, exec ≡ spec.
  - **`pub fn serialize_payload(frames: &[Frame], k: PacketKind, out: &mut Vec<u8>)`:**
    - requires `frames.len() >= 1` (§12.4: at least one frame), and for each frame `frame_wf` and `frame_permitted(frame_type_of(f), k)` (§12.5's sender MUSTs);
    - ensures `out` gains the concatenated `spec_frame_bytes`.
  - **Theorem:** if no frame is `HandshakeDone`, `rfc_payload(written, k) == Ok(frames without Padding)`.

- [ ] **Step 1: Failing tests:**
  - **`rfc9001_a3_payload`:** the 99-byte A.3 server Initial payload (`02000000000600405a0200…2b00020304`, copied from rfc9001.txt §A.3) parses as `Initial` to `[Ack{0, 0, 0, [], None}, Crypto{0, <the 90 bytes after 0x405a>}]`. `serialize_payload` of those two frames as `Initial` reproduces the 99 bytes exactly.
  - **`rfc9001_a2_payload`:** the A.2 CRYPTO frame (245 bytes, `060040f1010000ed…048000ffff`) followed by 917 zero bytes (1162 in total) parses as `Initial` to `[Crypto{0, 241 bytes starting 01 00 00 ed}]`.
  - **`permissions`:**
    - an Initial `[0x1d, 0x00, 0x00]` → `Err(PROTOCOL_VIOLATION)`;
    - an Initial `[0x1c, 0x00, 0x00, 0x00]` → `Ok`;
    - a Handshake `[0x10, 0x00]` → `Err(PROTOCOL_VIOLATION)`;
    - a OneRtt `[0x1a, 1, 2, 3, 4, 5, 6, 7, 8, 0x10, 0x05, 0x08, 0x00, 0x61]` → `Ok([PathChallenge, MaxData(5), Stream{0, 0, "a", false}])`.
  - **`permission_before_body`:** an Initial `[0x08]` → `Err(PROTOCOL_VIOLATION)`, not FRAME_ENCODING_ERROR. A OneRtt `[0x08]` → `Err(FRAME_ENCODING_ERROR)`, since the Stream ID is missing.
  - **`empty_and_padding`:**
    - `[]` → `Err(PROTOCOL_VIOLATION)`;
    - `[0x00, 0x00, 0x00]` → `Ok([])`;
    - `[0x01]` followed by 1000 zeros → `Ok([Ping])`.
  - **`server_receipt_any_space`:** a OneRtt `[0x07, 0x01, 0xaa]` → `Err(PROTOCOL_VIOLATION)`, and a OneRtt `[0x1e]` → `Err(PROTOCOL_VIOLATION)`.
  - **`ack_eliciting`:** `[Ack]` → false, `[Ack, Ping]` → true, `[ConnectionClose]` → false, `[Crypto]` → true.
- [ ] **Step 2:** Run the tests and confirm they fail.
- [ ] **Step 3:** Implement with Duvet citations of §12.4 (the no-frames MUST and the not-permitted MUST), §12.5 (both MUSTs), §17.2.4 and §13.2. Transcribe the Table 3 "Pkts" and "Spec" rows as one comment table above `frame_permitted`.
- [ ] **Step 4:** Run the four checks.
- [ ] **Step 5: Commit:** `feat(quic): verified packet payload codec + Table 3 frame permissions (RFC 9000 §12.4-12.5)`
- [ ] **Step 6: Matrix commit:** `✅ 3b: crates/quic/src/payload.rs` on §12.4, §12.5 and §17.2.4.

---

### Task 7: Transport parameters

**Files:**
- Create: `crates/quic/src/tp.rs`
- Modify: `TRUSTED.md` (extend the derived-impl row)
- Test: `crates/quic/tests/tp.rs`

**Interfaces:**
- Consumes: `parse_varint`, `put_varint`, `rfc_varint_decode`, the TP ids and the limits.
- Produces (`quic::tp`):
  - **`pub struct TransportParams`.** Absent parameters take the RFC defaults in brackets (§18.2):
    - `original_destination_connection_id: Option<Vec<u8>>`;
    - `max_idle_timeout: u64` [0];
    - `stateless_reset_token: Option<[u8; 16]>`;
    - `max_udp_payload_size: u64` [65527];
    - `initial_max_data`, `initial_max_stream_data_bidi_local`, `initial_max_stream_data_bidi_remote`, `initial_max_stream_data_uni`, `initial_max_streams_bidi`, `initial_max_streams_uni`: `u64` [0];
    - `ack_delay_exponent: u64` [3];
    - `max_ack_delay: u64` [25];
    - `disable_active_migration: bool` [false];
    - `active_connection_id_limit: u64` [2];
    - `initial_source_connection_id: Option<Vec<u8>>`.
    - Absence of `initial_source_connection_id` is an error (§7.3), but checking it is 3d's job.
  - **`pub fn default_transport_params() -> TransportParams`**, and the spec twin `spec_default_tp()`.
  - **`pub open spec fn rfc_transport_params(b: Seq<u8>, from_client: bool) -> Result<SpecTp, u64>`** (§7.4, §7.4.2, §18, §18.2, §4.6). The input is a sequence of (ID varint, Length varint, Value). Every error is TRANSPORT_PARAMETER_ERROR:
    - a truncated ID or Length, or `Length > remaining`;
    - a repeated *known* ID (0x00–0x10), tracked by a 17-bit seen-mask. `// ponytail: unknown-ID duplicates are not detected; add a seen-set if a peer abuses it.`
    - **Server-only IDs:** from a client, any of 0x00, 0x02, 0x0d, 0x10. With `from_client == false`, 0x0d and 0x10 are still errors, because we never send them and don't model them.
    - **Integer IDs** (0x01, 0x03–0x0b, 0x0e): the value must be exactly one varint, of any length.
    - **Value bounds:**
      - 0x03 < 1200;
      - 0x0a > 20;
      - 0x0b ≥ `MAX_ACK_DELAY_LIMIT`;
      - 0x0e < 2;
      - 0x08 or 0x09 > `MAX_STREAMS_LIMIT` (§4.6).
    - **Byte-valued IDs:**
      - 0x0c with a non-zero Length;
      - 0x02 with Length ≠ 16;
      - 0x00 or 0x0f with Length > 20.
    - **Any other ID is ignored**, including the reserved `31·N + 27` (§7.4.2, §18.1).
  - **`pub fn parse_transport_params(b: &[u8], from_client: bool) -> (r: Result<TransportParams, u64>)`**, exec ≡ spec. The server always calls it with `true`; `false` exists only for the round-trip theorem.
  - **`pub open spec fn server_tp_wf(p: SpecTp) -> bool`:**
    - `original_destination_connection_id`, `initial_source_connection_id` and `stateless_reset_token` are all `Some`, with CIDs ≤ 20 bytes;
    - every integer ≤ VARINT_MAX;
    - `max_udp_payload_size >= 1200`;
    - `ack_delay_exponent <= 20`;
    - `max_ack_delay < MAX_ACK_DELAY_LIMIT`;
    - `active_connection_id_limit >= 2` (§18.2: ours must be at least 2);
    - the two stream counts ≤ `MAX_STREAMS_LIMIT`.
  - **`pub fn serialize_server_params(p: &TransportParams, out: &mut Vec<u8>)`**, which requires `server_tp_wf(p@)`.
    - It writes each ID at most once (§7.4), in this fixed order: 0x00, 0x0f, 0x02, 0x01, 0x03–0x0b, then 0x0c only if `disable_active_migration`, then 0x0e.
    - Every integer is written even when it equals the default.
  - **Theorem:** if `server_tp_wf(p)`, then `rfc_transport_params(spec_server_tp_bytes(p), false) == Ok(p)`.

- [ ] **Step 1: Failing tests:**
  - **`rfc9001_a2_client_params`:** the 50-byte `quic_transport_parameters` value from the A.2 ClientHello is `0408ffffffffffffffff 05048000ffff 07048000ffff 080110 010480007530 090110 0f088394c8f03e515708 06048000ffff`. Parsed with `from_client = true` it gives:
    - `initial_max_data = 0x3fff_ffff_ffff_ffff`;
    - `initial_max_stream_data_bidi_local`, `_bidi_remote` and `_uni` each `0xffff`;
    - `initial_max_streams_bidi = 16` and `_uni = 16`;
    - `max_idle_timeout = 30000`;
    - `initial_source_connection_id = Some(8394c8f03e515708)`;
    - every other field at its default.
  - **`tp_errors`.** Each case returns `Err(TRANSPORT_PARAMETER_ERROR)`, parsed from the client:
    - `00 00` (odcid);
    - `02 10` + 16 bytes;
    - `0e 01 01`;
    - `03 02 44 af` (1199);
    - `0a 01 15` (21);
    - `0b 04 80 00 40 00` (2¹⁴);
    - `0c 01 00`;
    - `01 01 00 01 01 00` (a duplicate);
    - `01 05 00` (truncated);
    - `01 02 00 00` (a trailing byte);
    - `08 08 d0 00 00 00 00 00 00 01` (2⁶⁰+1);
    - `0f 15` + 21 bytes.
  - **`tp_accepts`:**
    - `03 02 44 b0` → `max_udp_payload_size 1200`;
    - `01 02 40 00` (non-minimal) → `max_idle_timeout 0`;
    - `1b 02 aa bb` (reserved 27) → defaults;
    - `40 ff 00` (unknown 255) → defaults;
    - `0c 00` → `disable_active_migration true`;
    - `[]` → defaults.
  - **`server_params_roundtrip`:** take odcid `8394c8f03e515708`, iscid `f067a5502a4262b5`, token `[0x11; 16]`, `max_idle_timeout 30000`, `initial_max_data 1048576`, the stream-data limits `65536`, `initial_max_streams_bidi 100` and `_uni 3`, `disable_active_migration true` and `active_connection_id_limit 4`.
    - It serializes to bytes starting `00 08 8394c8f03e515708 0f 08 f067a5502a4262b5 02 10 1111…`.
    - Parsing them with `false` gives `p` back.
    - Parsing them with `true` → `Err(TRANSPORT_PARAMETER_ERROR)`.
- [ ] **Step 2:** Run the tests and confirm they fail.
- [ ] **Step 3:** Implement with Duvet citations of §7.4 (the invalid-value and at-most-once MUSTs), §7.4.2, §18.1, §18.2 (the server-only, active_connection_id_limit and stateless_reset_token MUSTs, plus each value bound) and §4.6 (the 2⁶⁰ TRANSPORT_PARAMETER_ERROR clause).
- [ ] **Step 4:** Run the four checks.
- [ ] **Step 5: Commit:** `feat(quic): verified transport parameter codec (RFC 9000 §7.4, §18)`
- [ ] **Step 6: Matrix commit:**
  - `✅ 3b: crates/quic/src/tp.rs` on §7.4, §7.4.2, §18.2 and its four (req) rows;
  - a "touched" note on §4.6.

---

## Exit criteria (Phase 3b)

- All four checks pass on the merged tree, and every 2a/2b test still passes after Task 2's helper move.
- The 27 rows under "Matrix rows this plan closes" carry `✅ 3b: <file>`. The 8 touched rows carry their `3b codec: … (closed in 3x)` note.
- `phase-3b` is merged into `main`.

## Self-review (done while writing)

- **Spec coverage.** Design spec Phase 3 asks for: long/short headers (Task 2), all transport frames (Tasks 4–5), transport parameters (Task 7), packet-number encoding/decoding (Task 1), version negotiation and stateless reset (Task 3).
  - Codec obligations: exec ≡ spec and parse∘serialize in every task. The non-malleability waiver is stated in Global Constraints. Malformed input maps to the RFC's error code in every task, and there are no panics or overflow.
  - All the state-machine items in Phase 3 are in the 3c–3e outlines.
- **Type consistency.** These names are used identically everywhere: `parse_varint`/`put_varint`/`varint_len` (Task 2 → 5, 7); `AckFrame`/`parse_ack`/`serialize_ack` (Task 4 → 5); `Frame`/`frame_wf`/`frame_type_of`/`rfc_frame_type`/`rfc_frame_body`/`parse_frame_type`/`parse_frame_body` (Task 5 → 6); `PacketKind` (Task 6); `Header`/`LongType` (Task 2 → 3).
- **Row accounting.** The 27 closed rows plus the 3c/3d/3e outline lists account for all 139 Phase-3 rows exactly once. The check script is in `phase-3-outlines.md`.
- **Proportion.** Bodies appear only where the RFC's algorithm isn't determined by the signature: the A.3 transcription and the payload loop's error order. Everything else is signatures, vectors and citations.
