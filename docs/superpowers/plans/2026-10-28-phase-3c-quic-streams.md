# Phase 3c: QUIC Streams and Flow Control — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** A verified, sans-IO stream layer for the QUIC server. It covers:
- stream-ID accounting and stream limits;
- the per-stream receive state machine (Figure 3) and send state machine (Figure 2);
- stream-level and connection-level flow control;
- out-of-order reassembly for stream data and for CRYPTO data at each encryption level.

It consumes 3b `Frame` values. It emits exactly what `h3::conn` takes: in-order contiguous bytes plus FIN per stream, and resets.

**Architecture:**
- **New modules, all in `crates/quic`:**
  - `flow`: the credit counters;
  - `stream_id`;
  - `reassembly`;
  - `crypto_stream`;
  - `recv_stream`;
  - `send_stream`;
  - `streams`, the aggregate dispatcher used by 3d.
- **Receive spec style.** This follows the 2b style, but the input is QUIC frames instead of byte chunks.
  - Each receive part has a spec that is a total function of its *input trace*. The trace holds the STREAM and RESET_STREAM inputs received, plus markers for credit we sent and for a local STOP_SENDING.
  - The exec machine keeps that trace as ghost state. After every call, its cumulative events equal the spec of the trace.
  - Reassembly is specified over a byte map in which the first writer wins. The order-freedom theorem, with its exact premise, is in Task 2.
- **Send spec style:**
  - invariants over a ghost copy of every byte the application wrote;
  - a transition predicate transcribed edge-for-edge from Figure 2.
- **The aggregate uses 2b `h3::conn`'s approach:**
  - delegation lemmas, so per-stream events are exactly that stream's machine outputs;
  - error classification against a spec table;
  - connection-wide invariants for flow-control sums, buffer bounds and stream-ID monotonicity.

**Tech Stack:** Verus 0.2026.10.04.426d8b0, vstd `=0.0.0-2026-10-04-0306`, vest_lib `=0.2.2`, duvet 0.4.3.

**Spec:** `docs/superpowers/specs/2026-10-27-verified-http3-design.md`. See Phase 3 ("stream states, connection/stream flow control"); the state-machine proof obligations ("every transition the code takes is allowed by the RFC state diagram (RFC 9000 §3)", "flow-control limits are never exceeded", "every RFC-mandated connection/stream error is produced on the triggering input"); "Calls I made" (server only, sans-IO). Outline: `phase-3-outlines.md` §3c. Codecs: `2026-10-27-phase-3b-quic-codecs.md`, whose Interfaces blocks are this plan's contract.

## Controller rulings (2026-10-28, on the planner's open decisions)

- **Ack/loss ownership:** accepted. `Streams::on_frame_acked` / `on_frame_lost` are the interface, and the 3d plan must use them: 3d's sent-packet record calls them instead of requeuing raw frames, and it reports any polled-but-unsent frame as lost.
- **Receive limits are enforced against the limit actually sent** (peek/commit through `poll_frames`). This is the correct RFC 9000 §4.1 reading.
- **§2.2 MAY declined:** differing retransmitted bytes are never PROTOCOL_VIOLATION, and the first bytes received win. This is permitted, since it's a MAY.
- **`MAX_CRYPTO_BUFFER = 16384`** is accepted. It is ≥ the §7.5 floor of 4096, and it fits ClientHellos carrying post-quantum key shares.
- **`initial_max_streams_uni >= 3`** is a literal in `quic`, so `quic` doesn't depend on `h3`. 3d's adapter test asserts that it equals `h3::limits::MIN_PEER_UNI_STREAMS`.
- **Critical streams:** a peer STOP_SENDING on our control stream is handled by `h3::conn::on_stop_sending` → `H3_CLOSED_CRITICAL_STREAM`; this was added to the Phase 2b plan (b1dc2a0). The 3d adapter must forward STOP_SENDING to it. We open no QPACK streams.

## Global Constraints

- **3b's Global Constraints apply unchanged:**
  - the pins and Duvet citations (`//= https://www.rfc-editor.org/rfc/rfc9000#section-X` plus a contiguous `//#` quote);
  - the four checks with fresh-target evidence;
  - sans-IO, with no async, trait objects or closures in exec code;
  - no panics;
  - no allocation sized by an untrusted length before it is checked;
  - glob-only imports of spec items;
  - `Spec*` twins with a `View`;
  - zero escape tokens in `crates/quic`, and `scripts/verify.sh` unedited;
  - the shared TRUSTED.md row "Derived `Debug`/`PartialEq`/`Eq` on quic types", which each task extends with its new type names. The unit enums returned by value (`StreamKind`, `RecvState`, `SendState`) also derive `Clone`/`Copy`, and go in that row's `Clone`/`Copy` clause beside `PacketKind` (preflight);
  - **spec-mode accessors (preflight).** Some exec getters are both called by tests and used in a `requires`/`ensures`: `limit()`, `consumed()`, `pending()`, `available()`, `max()`, `peer_created`, `local_uni_created`, `local_uni_limit`, `pending_credit`, `pending_reset`, … Each keeps its exec name and gains a `pub closed spec fn <name>_spec`, linked by `#[verifier::when_used_as_spec(<name>_spec)]` (precedent: h3 `codes.rs` `is_grease`). The exec fn ensures `r == self.<name>_spec()`, so contracts can be written as the plan writes them. That attribute is not an escape: the verify.sh gate doesn't match it. The `state()`/`state_exec` and `base()`/`base_exec` pairs stay as written. Repo precedent covers only free fns with `open` twins. Task 1's first verify run confirms the attribute on one `&self` getter with a `closed` twin. If Verus rejects that, write contracts against `<name>_spec` directly;
  - matrix bookkeeping, written here as `✅ 3c: <file>`.
- **Base branch:** `phase-3c` branches from `main` *after* `phase-3b` merges.
- **Fresh evidence:** `(cd crates/quic && CARGO_TARGET_DIR=<scratch>/vt-3c-tN cargo verus verify)` prints `verification results:: … 0 errors`.
- **No new dependencies.** `crates/quic/Cargo.toml` is not edited, and in particular gets no `h3` dependency (see `Streams::new`'s `requires`).
- **Consumed from 3b**, with exact names. This is a list of names, not a `use` statement: inside the crate they come in by glob (`use crate::frame::*;`, `use crate::payload::*;`, `use crate::tp::*;`, `use crate::codes::*;`, `use wire::varint::*;`).
  - `quic::frame::{Frame, SpecFrame, frame_wf, frame_type_of, spec_frame_type, serialize_frame, spec_frame_bytes}` (`frame_type_of` is exec; spec positions use `spec_frame_type(f@)`);
  - `quic::payload::{PacketKind, frame_permitted}`;
  - `quic::tp::TransportParams`;
  - `quic::codes::*`, which includes FLOW_CONTROL_ERROR 0x03, STREAM_LIMIT_ERROR 0x04, STREAM_STATE_ERROR 0x05, FINAL_SIZE_ERROR 0x06, CRYPTO_BUFFER_EXCEEDED 0x0d and `MAX_STREAMS_LIMIT = 1 << 60`;
  - `wire::varint::*`, which includes `varint_len`, `rfc_varint_min_len` and `VARINT_MAX`.
- **The `Frame` variants used**, with 3b's field names verbatim:
  - `Stream { stream_id, offset, data, fin }`;
  - `ResetStream { stream_id, error_code, final_size }`;
  - `StopSending { stream_id, error_code }`;
  - `MaxData(u64)`, `MaxStreamData { stream_id, max }`, `MaxStreams { bidi, max }`;
  - `DataBlocked(u64)`, `StreamDataBlocked { stream_id, max }`, `StreamsBlocked { bidi, max }`;
  - `Crypto { offset, data }`.
- **What the 3b codec already guarantees** (it is not re-checked here). The vehicle is `parse_payload`'s `Ok(v)` ensures, `frames_received(frames_view(v@), k)`, which gives `frame_wf(v@[i]@)` and `frame_permitted(spec_frame_type(v@[i]@), k)` for each `i`. `Streams::on_frame` therefore **requires `frame_wf(f@)`** (preflight), and 3d discharges it from that ensures.
  - every received `offset + data.len() <= VARINT_MAX`, and `stream_id <= VARINT_MAX`;
  - `MaxStreams.max <= MAX_STREAMS_LIMIT`;
  - stream frames arrive only in 1-RTT packets (`frame_permitted`).
- **STREAM encoding** (3b `frame_type_of`): type `0x08 | (offset > 0 ? 0x04 : 0) | 0x02 | fin`. LEN is always set, and OFF is set only when offset > 0.
  - Anchor: `Stream{4, 0, "ab", false}` encodes as `0a 04 02 61 62`.
  - Every budget vector below follows this.
- **Direction mapping for transport parameters.** §18.2: "initial_max_stream_data_bidi_local … applies to newly created bidirectional streams opened by the endpoint that sends the transport parameter", and "…_bidi_remote … opened by the endpoint that receives the transport parameter". Here `local` is our TP and `peer` is the client's.

  | Stream (`id % 4`) | Our receive window | Our initial send limit |
  |---|---|---|
  | 0 client bidi | `local.initial_max_stream_data_bidi_remote` | `peer.initial_max_stream_data_bidi_local` |
  | 2 client uni | `local.initial_max_stream_data_uni` | — (receive-only) |
  | 3 server uni | — (send-only) | `peer.initial_max_stream_data_uni` |
  | 1 server bidi | never created | never created |

  Connection-level: we receive under `local.initial_max_data` and send under `peer.initial_max_data`. Peer stream limits: `local.initial_max_streams_bidi` and `_uni`. Our uni limit: `peer.initial_max_streams_uni`.
- **Rulings.** Each cites the RFC latitude it uses.
  - **The server never opens bidirectional streams** (RFC 9114 has no server-initiated bidi use). Any frame naming a server-bidi ID (`id % 4 == 1`) is STREAM_STATE_ERROR: such a stream is "a locally initiated stream that has not yet been created" (§19.5, §19.8, §19.10). That includes RESET_STREAM and STREAM_DATA_BLOCKED, where the RFC names no code.
  - **Receive limits are checked against the limit actually sent.**
    - Credit updates are *pending* until `poll_frames` emits them, and only then raise the enforced limit.
    - A frame beyond the sent limit is FLOW_CONTROL_ERROR, even if a larger value is pending (§4.1 "advertised").
    - Frames returned by `poll_frames` count as sent.
  - **Credit threshold** (`// ponytail: half-window threshold, fixed window; autotune per §4.2 if throughput needs it`):
    - an update is due when `2·(limit − consumed) < window`;
    - the new limit is `min(consumed + window, cap)`;
    - it is raised only if that is larger than the current limit.
    - The same rule drives MAX_DATA (cap VARINT_MAX), MAX_STREAM_DATA (cap VARINT_MAX) and MAX_STREAMS (cap MAX_STREAMS_LIMIT, with "consumed" = peer streams closed).
    - It depends on consumption only. No *_BLOCKED frame is ever an input (§4.2, §4.6).
  - **Eager delivery.** Contiguous bytes are delivered to the application inside the call that completes them.
    - So the receive part never rests in "Data Recvd" or "Reset Recvd". Each one is passed through within a single call, to "Data Read" or "Reset Read".
    - Exec states are `Recv, SizeKnown, DataRead, ResetRead`. The transition predicate allows exactly the Figure 3 edges, and the composition of those edges within one call.
  - **RESET_STREAM after all data was delivered is suppressed** (§3.2: "A RESET_STREAM signal might be suppressed or withheld if stream data is completely received").
  - **A STOP_SENDING from the peer resets the send part immediately**, in Ready, Send *and* Data Sent, with the peer's error code copied. §3.5 requires this in Ready/Send, allows deferring in Data Sent (we don't defer), and says SHOULD copy the code.
  - **No *_BLOCKED frames are sent.** They are all SHOULDs (§4.1, §19.12–§19.14). `// ponytail: add STREAM_DATA_BLOCKED/DATA_BLOCKED if peers stall waiting for them.` Received *_BLOCKED frames change nothing, except that STREAM_DATA_BLOCKED opens a peer stream (§3.2).
  - **FINAL_SIZE_ERROR (§4.5 SHOULDs) is enforced while the stream's state exists.** Once a stream's entry is removed (both parts terminal), later frames for it are ignored silently. §4.5 explicitly makes this optional ("not mandatory … significant state commitment").
  - **§2.2 MAY declined: retransmitted data that differs is never PROTOCOL_VIOLATION.** The first bytes received at an offset win, and later different bytes are discarded ("Data that has already been received can be discarded").
    - Complete detection would mean keeping every delivered byte, which is unbounded.
    - Partial detection (only against still-buffered bytes) would make the error depend on arrival order.
  - **No credit is raised after a local `stop_sending`.** The peer is expected to reset (§3.5 MUST on its side).
  - **A local `stop_sending` does not suppress events** (preflight R1). Bytes, the FIN and a peer reset are still delivered as `Data`/`Reset`. `h3::conn` ignores data on a stream it stopped (`on_stream_data`'s `!rx_open` arm). It forgets the stream only on that FIN or reset, and binding obligation 1 needs it to have forgotten the stream before we re-credit MAX_STREAMS.
- **Error precedence**, pinned by tests. The first applicable check wins. `RecvStream`, `SendStream`, `StreamIds` and `CryptoStream` leave themselves unchanged on `Err`. Any `Err` from `Streams::on_frame` is a connection error: 3d closes the connection, and `on_frame` requires `!failed()`, so state after an `Err` is never used again.
  1. direction/creation → STREAM_STATE_ERROR;
  2. peer stream limit → STREAM_LIMIT_ERROR;
  3. stream final size → FINAL_SIZE_ERROR;
  4. stream flow control → FLOW_CONTROL_ERROR;
  5. connection flow control → FLOW_CONTROL_ERROR.
- **Limits we choose:**
  - `MAX_CRYPTO_BUFFER: u64 = 16384`, in `crypto_stream.rs` (Task 2).
  - Stream entries live in a `Vec` with linear lookup: `// ponytail: linear scan over open streams, bounded by our advertised stream windows; HashMap if concurrency grows past ~100.`
- **The contract with `h3::conn`.** This is proven, and it is the `ensures` of every `Streams` method that pushes `StreamEvent`s:
  - **Scope:** E1–E3 cover the receive-side events, `Data` and `Reset`. `StopSending` is a send-side event: it can follow a receive-side terminal event on the same bidi ID, and at most one is emitted per stream (only when the send part is freshly reset).
  - **E1:** for each stream ID, the `Data`/`Reset` events form `Data* (Data{fin:true} | Reset)?`. The concatenated `Data` payloads are a prefix of the stream's bytes, with no gaps and no repeats.
  - **E2:** there is never a `Data{data: [], fin: false}`.
  - **E3:** no `Data`/`Reset` is emitted for a stream after its terminal event. A local `stop_sending` does not end the events (preflight R1).
  - **E4:** no `Data`/`Reset` is emitted on an ID with `id % 4` equal to 1 or 3.
  - **E5** (preflight R1, binding obligation 1): a peer-stream entry is removed, and `ids.on_peer_closed` is called, only after that stream's terminal receive event (`Data{fin: true}` or `Reset`) has been pushed. A RESET_STREAM suppressed after a delivered FIN is the one case with no `Reset`, because the FIN already went out. So every MAX_STREAMS re-credit follows the event on which 2b forgets the stream.

  E3 is load-bearing. 2b forgets a request stream once its FIN or reset is delivered and its sending side is done (`end_send` / `on_stream_data`). A later `Data` for that ID would then look like a new request.

## Matrix rows this plan closes

All RFC 9000. Labels are exactly as in `docs/requirements.md`.
- **Task 1:** §2.1, §4.6, §19.11.
- **Task 2:** §7.5.
- **Task 3:** none. It adds "touched" notes on §2.2 and §4.5.
- **Task 4:** §3.3.
- **Task 5:** §3.2, §4.5, §19.4, §19.5, §19.8, §19.13.
- **Task 6:** §2.2, §3.5, §4.1, §4.2, §4.4, §11.2, §19.9, §19.10.

That's 19 rows, the outline's list exactly.
- 3b's "touched … (closed in 3c)" notes on §4.6, §19.8 and §19.11 are **replaced** by the `✅ 3c` entry, not appended to.
- §19.14 (closed in 3b) is not touched.

**Rows touched but not closed:**

| Row | Touched by | 3c provides | Closed in |
|---|---|---|---|
| §13.3 | Task 6 | stream-family retransmission: RESET_STREAM resent unchanged, the current credit value resent, no STREAM after reset | 3d |

## Review Focus

1. **A retransmitted range whose bytes differ.** No error. The bytes delivered are the first ones received, and the differing bytes are dropped. This holds both below the delivered offset and inside the out-of-order buffer. Pinned in Task 2: `first_writer_wins`, and in Task 3: `conflicting_retransmit`.
2. **A FIN, or a RESET_STREAM, that changes a known final size**, or a FIN below data already received. Each is FINAL_SIZE_ERROR. A FIN-carrying duplicate with the same size is accepted silently. Pinned in Task 3: `final_size_rules`.
3. **Duplicate bytes counted twice against connection flow control.** The connection counts each stream's high-water mark, or its final size, exactly once. Pinned in Task 5: `conn_flow_counts_high_water` and `reset_final_size_counts`.
4. **MAX_STREAMS of exactly 2⁶⁰, and stream-ID arithmetic at 2⁶²−1.** Both are accepted with no overflow. A peer ID of `2⁶²−2` against a limit of 3 is STREAM_LIMIT_ERROR. Pinned in Task 1: `stream_limit_edges`, and in Task 5: `max_streams_2_60`.
5. **A STOP_SENDING for a stream we never opened.**
   - Our uni stream 3 before we opened it, or server-bidi 1, is STREAM_STATE_ERROR.
   - Client-bidi 0, which the peer may open with this frame, opens the stream and resets our send part with the code copied.
   - Pinned in Task 5: `stop_sending_unopened`, and in Task 6: `stop_sending_resets`.

---

### Task 1: Credit counters and stream IDs (`quic::flow`, `quic::stream_id`)

**Files:**
- Create: `crates/quic/src/flow.rs`, `crates/quic/src/stream_id.rs`
- Modify: `crates/quic/src/lib.rs` (`pub mod flow; pub mod stream_id;`), `TRUSTED.md` (extend the derived-impl row with `StreamKind`, `Opened`)
- Test: `crates/quic/tests/flow.rs`, `crates/quic/tests/stream_id.rs`

**Interfaces:**
- Consumes: `MAX_STREAMS_LIMIT`, `STREAM_LIMIT_ERROR` and `VARINT_MAX`.
- Produces (`quic::flow`):
  - **The threshold specs:**
    - `pub open spec fn credit_due(limit: u64, consumed: u64, window: u64) -> bool` = `2 * (limit - consumed) < window`;
    - `pub open spec fn credit_target(consumed: u64, window: u64, cap: u64) -> u64` = `min(consumed + window, cap)`.
  - **`pub struct RecvCredit`**, the receiver side. Fields are private: `limit` (sent), `consumed`, `window`, `cap`, `next: Option<u64>`.
    - `pub fn new(window: u64, cap: u64) -> RecvCredit`, which requires `window <= cap <= VARINT_MAX`, with `limit == window`.
    - `pub fn limit(&self) -> u64` and `pub fn consumed(&self) -> u64`.
    - `pub fn on_consumed(&mut self, n: u64)`, which requires `consumed + n <= limit`.
      - It ensures `next == Some(credit_target(..))` when `credit_due(limit, consumed', window)` holds and the target is greater than `limit`. Otherwise `next` is unchanged.
    - `pub fn pending(&self) -> Option<u64>`.
    - `pub fn commit(&mut self)`, which requires `pending() is Some(v)`, and ensures `limit == v` and `next is None`.
    - `pub fn on_lost(&mut self)`, which re-pends the current value: `next = Some(max(next.unwrap_or(0), limit))`.
    - Invariant: `consumed <= limit <= cap`, and `next is Some(v) ==> limit <= v <= cap`.
  - **`pub struct SendCredit`**, the sender side (§4.1). Fields: `max`, `used`.
    - `pub fn new(max: u64) -> SendCredit`;
    - `pub fn max(&self) -> u64` and `pub fn available(&self) -> u64` (`max − used`);
    - `pub fn on_max(&mut self, v: u64)`, which ensures `max' == max(max, v)`, so a non-increasing update is ignored;
    - `pub fn consume(&mut self, n: u64)`, which requires `n <= available()`.
    - Invariant: `used <= max`.
- Produces (`quic::stream_id`):
  - **`pub enum StreamKind { ClientBidi, ServerBidi, ClientUni, ServerUni }`**:
    - `pub open spec fn spec_stream_kind(id: u64) -> StreamKind`, by `id % 4` (Table 1);
    - `pub fn stream_kind(id: u64) -> StreamKind`, exec ≡ spec.
  - `pub open spec fn peer_id_allowed(id: u64, max_streams: u64) -> bool` = `id / 4 < max_streams`. This is §4.6's "stream ID less than max_streams * 4 + first_stream_id_of_type", for `id ≡ type (mod 4)`.
  - **`pub enum Opened { Existing, New { first: u64, count: u64 } }`.**
  - **`pub struct StreamIds`.** Fields: `peer_bidi_next`, `peer_uni_next` (counts opened), `peer_bidi: RecvCredit`, `peer_uni: RecvCredit` (cap `MAX_STREAMS_LIMIT`, consumed = closed), and `local_uni: SendCredit` (used = our uni streams opened).
    - **`pub fn new(local_max_bidi: u64, local_max_uni: u64, peer_max_uni: u64) -> StreamIds`**, which requires each ≤ `MAX_STREAMS_LIMIT`.
    - **`pub fn on_peer_stream(&mut self, id: u64) -> (r: Result<Opened, u64>)`**, which requires `id <= VARINT_MAX` and that `spec_stream_kind(id)` is `ClientBidi` or `ClientUni`.
      - `Err(STREAM_LIMIT_ERROR)` iff `!peer_id_allowed(id, limit)`, with the limit as *sent*; self is unchanged.
      - `Existing` iff `id / 4 < next`.
      - Otherwise `New { first: 4·next + (id % 4), count: id/4 + 1 − next }`, and `next' = id/4 + 1`. Every ID of that type in `[first, id]` is now opened (§3.2).
    - **`pub fn peer_created(&self, id: u64) -> bool`** = `id / 4 < next` for its type. Its spec twin is `peer_created_spec`, per the accessor rule in Global Constraints.
    - **`pub fn peer_limit(&self, bidi: bool) -> u64`**: the MAX_STREAMS value as *sent*, i.e. that credit's `limit()`, with spec twin `peer_limit_spec`. Task 5's `rfc_stream_frame_check` reads it (preflight: Task 5 consumes `StreamIds` through these spec twins, and no `SpecIds` type exists).
    - `pub closed spec fn wf(&self) -> bool`, required and ensured by every method. `RecvCredit` and `SendCredit` each get one too, holding the invariants below.
    - `pub fn on_peer_closed(&mut self, bidi: bool)`, which requires closed < opened. It calls `on_consumed(1)` on that credit.
    - `pub fn pending_max_streams(&self, bidi: bool) -> Option<u64>`, `pub fn commit_max_streams(&mut self, bidi: bool)` and `pub fn max_streams_lost(&mut self, bidi: bool)`. Every value is ≤ `MAX_STREAMS_LIMIT`.
    - **`pub fn open_local_uni(&mut self, id: u64) -> (ok: bool)`.**
      - `ok` iff `id == 4·used + 3 && available() > 0`, and then `used += 1`.
      - It ensures `ok ==> !old(self).local_uni_created(id) && self.local_uni_created(id)`, and the created set only grows. That gives §2.1: an ID is never reused.
    - `pub fn local_uni_created(&self, id: u64) -> bool` = `id % 4 == 3 && id / 4 < used`. Its spec twin is `local_uni_created_spec`, and both `open_local_uni`'s ensures and Task 5's dispatch use it.
    - `pub fn on_max_streams(&mut self, bidi: bool, max: u64)`.
      - uni → `local_uni.on_max(max)`.
      - bidi → no effect. We never open bidi streams, so the limit is ignored.
    - `pub fn local_uni_limit(&self) -> u64`.

- [ ] **Step 1: Failing tests** (`tests/flow.rs`):
  - **`recv_credit_half_window`:** `RecvCredit::new(100, VARINT_MAX)`:
    - `limit() == 100`;
    - `on_consumed(49)`, then `pending() == None`;
    - `on_consumed(2)`, then `pending() == Some(151)`;
    - `commit()`, then `limit() == 151` and `pending() == None`;
    - `on_lost()`, then `pending() == Some(151)`.
  - **`recv_credit_cap`:** `new(4, 6)`:
    - `on_consumed(3)`, then `pending() == Some(6)`;
    - `commit()`;
    - `on_consumed(3)`, then `pending() == None`, because the target of 6 is not > 6.
  - **`recv_credit_zero_window`:** `new(0, VARINT_MAX)`, then `on_consumed(0)`, then `pending() == None`.
  - **`send_credit`:** `SendCredit::new(10)`:
    - `on_max(5)`, then `max() == 10`;
    - `on_max(12)`, then `available() == 12`;
    - `consume(12)`, then `available() == 0`;
    - `on_max(12)`, then `max() == 12`.

  Failing tests (`tests/stream_id.rs`):
  - **`kinds`:** IDs 0, 1, 2, 3, 7 and `(1<<62)-1` give ClientBidi, ServerBidi, ClientUni, ServerUni, ServerUni and ServerUni.
  - **`peer_open_implicit`:** `new(10, 3, 1)`:
    - `on_peer_stream(8) == Ok(New{first: 0, count: 3})`;
    - `on_peer_stream(4) == Ok(Existing)`;
    - `on_peer_stream(12) == Ok(New{first: 12, count: 1})`.
  - **`peer_limit`:** `new(10, 3, 1)`:
    - `on_peer_stream(10) == Ok(New{first: 2, count: 3})`;
    - `on_peer_stream(14) == Err(STREAM_LIMIT_ERROR)`;
    - `on_peer_stream((1<<62) - 2) == Err(STREAM_LIMIT_ERROR)`.
  - **`max_streams_on_close`:** `new(4, 3, 1)`:
    - `on_peer_stream(12) == Ok(New{0, 4})`;
    - close bidi 2 times, then `pending_max_streams(true) == None`;
    - a 3rd close, then `pending_max_streams(true) == Some(7)`;
    - `on_peer_stream(16) == Err(STREAM_LIMIT_ERROR)`, since the value isn't committed yet;
    - `commit_max_streams(true)`;
    - `on_peer_stream(24) == Ok(New{first: 16, count: 3})`;
    - `on_peer_stream(28) == Err(STREAM_LIMIT_ERROR)`.
  - **`local_uni`:** `new(10, 3, 1)`:
    - `open_local_uni(7)` is false, then `open_local_uni(3)` is true;
    - `open_local_uni(3)` is false (no reuse), and `open_local_uni(7)` is false (limit 1);
    - `on_max_streams(false, 2)`, then `open_local_uni(7)` is true;
    - `on_max_streams(false, 1)`, then `local_uni_limit() == 2`;
    - `local_uni_created(3)` and `local_uni_created(7)` are true, and `local_uni_created(11)` is false.
  - **`stream_limit_edges`:** `new(1<<60, 1<<60, 0)`:
    - `on_peer_stream((1<<62) - 4) == Ok(New{first: 0, count: 1<<60})`;
    - `on_max_streams(false, 1<<60)`, then `local_uni_limit() == 1<<60` and `open_local_uni(3)` is true.
- [ ] **Step 2:** `cargo test -p quic --test flow --test stream_id`. Expected to fail: the modules don't exist yet.
- [ ] **Step 3: Implement both modules.** Duvet-cite:
  - §2.1: "A QUIC endpoint MUST NOT reuse a stream ID within a connection." At `open_local_uni`.
  - §4.6: "Endpoints MUST NOT exceed the limit set by their peer", the STREAM_LIMIT_ERROR sentence, "MAX_STREAMS frames that do not increase the stream limit MUST be ignored" and "MUST NOT wait to receive this signal before advertising additional credit".
  - §19.11: the "MUST be ignored", "MUST NOT open more streams" and STREAM_LIMIT_ERROR sentences.
  - §4.1: "A sender MUST ignore any MAX_STREAM_DATA or MAX_DATA frames that do not increase flow control limits." At `SendCredit::on_max`.

  Compare with `id / 4` or `id >> 2`, never `max * 4 + t`, so nothing overflows.
- [ ] **Step 4:** Run the four checks. `cargo test -p quic` passes 10 new tests.
- [ ] **Step 5: Commit:** `feat(quic): verified credit counters and stream-ID accounting (RFC 9000 §2.1, §4.6, §19.11)`
- [ ] **Step 6: Matrix commit:**
  - `✅ 3c: crates/quic/src/stream_id.rs` on §2.1, §4.6 (replacing 3b's touched note) and §19.11 (replacing 3b's touched note).
  - Commit: `docs: mark RFC 9000 §2.1, §4.6, §19.11 closed in 3c`.

---

### Task 2: Reassembly and CRYPTO streams (`quic::reassembly`, `quic::crypto_stream`)

**Files:**
- Create: `crates/quic/src/reassembly.rs`, `crates/quic/src/crypto_stream.rs`
- Modify: `crates/quic/src/lib.rs`
- Test: `crates/quic/tests/reassembly.rs`, `crates/quic/tests/crypto_stream.rs`

**Interfaces:**
- Consumes: `VARINT_MAX` and `CRYPTO_BUFFER_EXCEEDED`.
- Produces (`quic::reassembly`):
  - **`pub open spec fn rfc_received(ins: Seq<(nat, Seq<u8>)>) -> Map<nat, u8>`.** The first writer wins:
    - `rfc_received(ins.push((o, d)))` is `rfc_received(ins)`, plus `o + i ↦ d[i]` for each `i` where `o + i` is not already a key;
    - `rfc_received([])` is empty.
  - `pub open spec fn covered(ins, o: nat) -> bool`: some `(p, d)` in `ins` has `p <= o < p + d.len()`.
  - **`pub open spec fn rfc_contiguous(m: Map<nat, u8>) -> nat`**: the least offset that is not a key. It is total because the domain is finite (`lemma_contiguous_exists`).
  - `pub open spec fn rfc_prefix(m: Map<nat, u8>, n: nat) -> Seq<u8>` = `Seq::new(n, |i| m[i])`.
  - **`pub proof fn theorem_reassembly_order_free(ins: Seq<(nat, Seq<u8>)>, s: Seq<u8>)`.**
    - requires every `(o, d)` in `ins` to have `o + d.len() <= s.len()` and `d == s.subrange(o, o + d.len())`, i.e. consistent with `s`.
    - ensures `forall o. rfc_received(ins).contains_key(o) <==> covered(ins, o)`;
    - ensures `rfc_prefix(m, rfc_contiguous(m)) == s.take(rfc_contiguous(m))`.
    - So when the peer is consistent, the delivered bytes depend only on the *set* of ranges received, not on their order or duplication. When it is not consistent, the first-received bytes win (Global Constraints ruling), and no order-freedom is claimed.
  - **`pub struct Reassembly { base: u64, buf: Vec<u8>, have: Vec<bool> }`.** `buf[i]`/`have[i]` describe offset `base + i`.
    - Closed spec fns:
      - `inserted() -> Seq<(nat, Seq<u8>)>`;
      - `base() -> nat`;
      - `wf()`: `buf.len() == have.len()`; for every `i`, `have[i] <==> m.contains_key(base + i)` and then `buf[i] == m[base + i]` (with `m = rfc_received(inserted())`); `base <= rfc_contiguous(m)`; and no key of `m` is ≥ `base + buf.len()`.
    - `pub fn new() -> Reassembly`.
    - **`pub fn insert(&mut self, off: u64, data: &[u8])`**, which requires `off + data.len() <= VARINT_MAX`.
      - ensures `inserted() == old.inserted().push((off, data@))`;
      - ensures `self.base() + self.buf_len() <= max(old.base() + old.buf_len(), off + data.len())`. That is the high-water bound, which Task 3 turns into "≤ advertised window".
      - Bytes below `base` are skipped. Exec writes a byte only where `!have[idx]`.
    - **`pub fn pop(&mut self, out: &mut Vec<u8>)`:**
      - ensures `self.base() == rfc_contiguous(m)`;
      - ensures `out@ == old(out)@ + rfc_prefix(m, base').subrange(old.base(), base')`.
      - Then it rebuilds `buf`/`have` from the remaining tail. `// ponytail: O(buffered) copy per delivery; keep a start index with lazy compaction if profiling shows it.`
    - `pub fn base_exec(&self) -> u64` and `pub fn buf_len(&self) -> usize`.
- Produces (`quic::crypto_stream`):
  - **`pub const MAX_CRYPTO_BUFFER: u64 = 16384;`**
    - `// ponytail: fixed 16 KiB window past the read offset (§7.5 floor is 4096); grow during the handshake only if real ClientHellos need it.`
    - The window is an offset span: data ending within `read offset + MAX_CRYPTO_BUFFER` is always accepted.
  - **`pub struct CryptoStream { re: Reassembly }`**: one per encryption level, held by 3d. There is no flow control (§4).
    - `pub fn new() -> CryptoStream`.
    - **`pub fn on_crypto(&mut self, offset: u64, data: &[u8]) -> (r: Result<(), u64>)`**, which requires `offset + data.len() <= VARINT_MAX`. With `end = offset + data.len()`:
      - `end <= base` gives `Ok`, and nothing changes. The data was already consumed, and the packet is still acknowledged, since this isn't an error (§7.5).
      - `end > base + MAX_CRYPTO_BUFFER` gives `Err(CRYPTO_BUFFER_EXCEEDED)`, and nothing changes.
      - Otherwise `insert`, then `Ok`.
      - So `buf_len() <= MAX_CRYPTO_BUFFER` always holds.
    - **`pub fn read(&mut self, out: &mut Vec<u8>)`** = `pop`, and has `pop`'s ensures.

- [ ] **Step 1: Failing tests.** In `tests/reassembly.rs`, `"…"` stands for the ASCII bytes:
  - **`in_order`:**
    - `insert(0, "ab")`, then `pop` gives `"ab"`;
    - `insert(2, "cd")`, then `pop` gives `"cd"`, and `base_exec() == 4`.
  - **`out_of_order`:**
    - `insert(3, "de")`, then `pop` gives `""`;
    - `insert(0, "abc")`, then `pop` gives `"abcde"`.
  - **`first_writer_wins`:**
    - `insert(0, "abc")`, then `pop` gives `"abc"`;
    - `insert(1, "XYW")`, then `pop` gives `"W"`. X and Y lose to the delivered b and c, and W is new at offset 3. This was `"XYZW"`, which also writes offset 4 and pops `"ZW"`; fixed in preflight;
    - `insert(5, "pq")`;
    - `insert(4, "XYZ")`, then `pop` gives `"Xpq"`.
  - **`buffer_bound`:**
    - `insert(9, "z")`, then `buf_len() == 10`;
    - `insert(0, "abcdefghi")`, then `pop` gives `"abcdefghiz"`, and `buf_len() == 0`.
  - **`duplicate_below_base`:**
    - `insert(0, "abcde")`, then pop;
    - `insert(0, "abcde")`, then `pop` gives `""`, and `buf_len() == 0`;
    - `insert(2, "cdefg")`, then `pop` gives `"fg"`.

  In `tests/crypto_stream.rs`:
  - **`crypto_reorder_4096`:**
    - `on_crypto(1, [0x11; 4095]) == Ok(())`, then `read` gives `[]`;
    - `on_crypto(0, [0x10]) == Ok(())`, then `read` gives `[0x10] ++ [0x11; 4095]` (4096 bytes).
  - **`crypto_limit`:**
    - fresh: `on_crypto(16383, [1]) == Ok(())`;
    - fresh: `on_crypto(16384, [1]) == Err(CRYPTO_BUFFER_EXCEEDED)`;
    - fresh: `on_crypto(0, [0; 100])`, then read, then `on_crypto(16483, [1]) == Ok(())` and `on_crypto(16484, [1]) == Err(CRYPTO_BUFFER_EXCEEDED)`.
  - **`crypto_duplicate`:**
    - `on_crypto(0, [1..=10])`, then read 10 bytes;
    - `on_crypto(0, [1..=10]) == Ok(())`, then `read` gives `[]`;
    - `on_crypto(5, [6, 7, 8, 9, 10, 11]) == Ok(())`, then `read` gives `[11]`.
- [ ] **Step 2:** Run the tests and confirm they fail.
- [ ] **Step 3: Implement.** Duvet-cite:
  - §2.2: "Endpoints MUST be able to deliver stream data to an application as an ordered byte stream." Plus the "can be discarded" sentence and the MAY ruling as a comment.
  - §7.5: all three MUSTs. "MUST support buffering at least 4096 bytes" goes at `MAX_CRYPTO_BUFFER`, with a `const` assertion `MAX_CRYPTO_BUFFER >= 4096`. The CRYPTO_BUFFER_EXCEEDED MUST and the "MUST be acknowledged" MUST go at the `end <= base` branch.

  `insert` extends `buf`/`have` by pushing up to `end − base` (no `resize` from an untrusted length). The length was already checked against the caller's limit, which is the allocation rule.
- [ ] **Step 4:** Run the four checks.
- [ ] **Step 5: Commit:** `feat(quic): verified first-writer-wins reassembly and per-level CRYPTO buffers (RFC 9000 §2.2, §7.5)`
- [ ] **Step 6: Matrix commit:** `✅ 3c: crates/quic/src/crypto_stream.rs` on §7.5, and a touched note `3c: reassembly.rs ordered delivery (closed in Task 6)` on §2.2.

---

### Task 3: Receiving part (`quic::recv_stream`)

**Files:**
- Create: `crates/quic/src/recv_stream.rs`
- Modify: `crates/quic/src/lib.rs`, `TRUSTED.md` (extend the row with `StreamEvent`, `RecvState`)
- Test: `crates/quic/tests/recv_stream.rs`

**Interfaces:**
- Consumes: `Reassembly`, `rfc_received`, `rfc_contiguous`, `rfc_prefix` and `theorem_reassembly_order_free` (Task 2); `RecvCredit`, `credit_due` and `credit_target` (Task 1); FINAL_SIZE_ERROR and FLOW_CONTROL_ERROR.
- Produces:
  - **`pub enum StreamEvent { Data { id: u64, data: Vec<u8>, fin: bool }, Reset { id: u64, code: u64 }, StopSending { id: u64, code: u64 } }`**, plus `SpecStreamEvent` and its `View`. `StopSending` is produced only by Task 5.
  - **`pub enum RecvState { Recv, SizeKnown, DataRead, ResetRead }`.**
  - **`pub open spec fn recv_edge(a: RecvState, b: RecvState) -> bool`** lists the Figure 3 edges under the eager-delivery ruling. Data Recvd and Reset Recvd are each passed through within one call:
    - Recv→SizeKnown (Recv STREAM + FIN);
    - Recv→ResetRead and SizeKnown→ResetRead (Recv RESET_STREAM, then App Read Reset);
    - SizeKnown→DataRead (Recv All Data, then App Read All Data).

    **`pub open spec fn recv_step_ok(a, b)`** = `a == b || recv_edge(a, b) || exists|c| recv_edge(a, c) && recv_edge(c, b)`. Recv→DataRead is the one composed edge, for a frame that both carries the FIN and completes the data.
  - **`pub enum SpecRecvIn`:**
    - `Data { off: nat, data: Seq<u8>, fin: bool }`;
    - `Reset { code: u64, final_size: nat }`;
    - `Credit { limit: nat }`, a MAX_STREAM_DATA value we sent;
    - `Stop`, a local STOP_SENDING.
  - **`pub struct SpecRecv { state: RecvState, ins: Seq<(nat, Seq<u8>)>, delivered: nat, high: nat, final_size: Option<nat>, limit: nat, stopped: bool, events: Seq<SpecStreamEvent>, err: Option<u64> }`.**
  - **`pub open spec fn rfc_recv(id: u64, window: u64, t: Seq<SpecRecvIn>) -> SpecRecv`.** It is a left fold of `rfc_recv_step` from `{Recv, [], 0, 0, None, window, false, [], None}`, and once `err` is `Some` the state is frozen. `rfc_recv_step(id, s, i)` checks in this order; it is a body because the signature doesn't fix the order:
    ```
    Data{off, data, fin}:  end = off + |data|
      1. s.final_size == Some(F) && (end > F || (fin && end != F))   -> err FINAL_SIZE_ERROR
         s.final_size is None && fin && end < s.high                 -> err FINAL_SIZE_ERROR
      2. end > s.limit                                                -> err FLOW_CONTROL_ERROR
      3. s.state is DataRead | ResetRead                              -> s unchanged
      4. ins' = ins.push((off, data)); m = rfc_received(ins'); n = rfc_contiguous(m)
         high' = max(high, end); final' = if fin { Some(end) } else { final_size }
         state' = if final' == Some(n) { DataRead } else if final' is Some { SizeKnown } else { Recv }
         if n > delivered || state' is DataRead:                       // not gated on `stopped` (preflight R1)
             events' = events.push(Data{id, rfc_prefix(m, n).subrange(delivered, n), state' is DataRead})
         delivered' = n
    Reset{code, final}:
      1. (s.final_size == Some(F) && F != final) || final < s.high    -> err FINAL_SIZE_ERROR
      2. final > s.limit                                              -> err FLOW_CONTROL_ERROR
      3. s.state is DataRead | ResetRead                              -> s unchanged (suppressed)
      4. state' = ResetRead, final' = Some(final), high' = final; push Reset{id, code}   // also when stopped (R1)
    Credit{limit: v}: limit' = max(limit, v)        Stop: stopped' = true   // gates only credit and stop()
    ```
  - **`pub open spec fn counted(s: SpecRecv) -> nat`** = `s.final_size.unwrap_or(s.high)`. This is what the stream consumes from connection credit, counted once (§4.5).
  - **`pub open spec fn retired(s: SpecRecv) -> nat`** = `final` if ResetRead, else `delivered`. This is what is returned as connection credit.
  - **Lemmas:**
    - `lemma_counted_monotone`;
    - `lemma_retired_le_counted`;
    - every step satisfies `recv_step_ok(s.state, s'.state)`;
    - `events` satisfy E1/E2/E3 (Global Constraints) for `id`.
  - **`pub proof fn theorem_recv_order_free(id, window, t1, t2, s: Seq<u8>)`.**
    - requires:
      - `t1` and `t2` contain only `Data` inputs, and `t1.to_multiset() == t2.to_multiset()`;
      - each input is consistent with `s` (`d == s.subrange(o, o + |d|)`, `o + |d| <= s.len()`, and `fin ==> o + |d| == s.len()`);
      - neither fold has an `err`.
    - ensures the concatenated `Data` payloads of the two event sequences are equal, and so is whether a `fin: true` occurred.
    - Event chunking may differ, which matches 2b's Body-concatenation precedent.
  - **`pub struct RecvStream`.** Fields: `id`, `state`, `re: Option<Reassembly>` (None after reset), `high`, `final_size`, `credit: RecvCredit` (window, cap VARINT_MAX; `consumed == delivered`), `stopped`, `stop_pending`, and ghost `trace: Seq<SpecRecvIn>` and `emitted`.
    - Closed spec fns `trace()`, `emitted()` and `wf()`. `wf()` includes `rfc_recv(id, window, trace()).events == emitted()`, `.err is None`, and the buffer bound `buffered_len() <= limit − delivered`.
    - `pub fn new(id: u64, window: u64) -> RecvStream`, which requires `window <= VARINT_MAX`.
    - **`pub fn on_data(&mut self, off: u64, data: &[u8], fin: bool, conn_room: u64, ev: &mut Vec<StreamEvent>) -> (r: Result<u64, u64>)`**, which requires `wf()` and `off + data.len() <= VARINT_MAX`. With `t' = trace().push(Data{off, data@, fin})`:
      - if `rfc_recv(t').err == Some(c)`: `r == Err(c)`, and self and `ev` are unchanged;
      - else if `counted(t') − counted(t) > conn_room`: `r == Err(FLOW_CONTROL_ERROR)`, and self and `ev` are unchanged;
      - else `r == Ok(counted(t') − counted(t))`, `trace() == t'`, and `ev` gains exactly the new spec events.
      - Delivered bytes move the stream credit (`credit.on_consumed`).
    - **`pub fn on_reset(&mut self, code: u64, final_size: u64, conn_room: u64, ev: &mut Vec<StreamEvent>) -> (r: Result<u64, u64>)`.** The same shape, with `Reset{code, final_size}`. On success `re` becomes `None`, so `buffered_len() == 0`.
    - **`pub fn stop(&mut self, code: u64) -> (queued: bool)`**, which requires `code <= VARINT_MAX`. `queued` iff the state is Recv/SizeKnown and the stream isn't already stopped. Then it appends `Stop` and records `code` as the pending STOP_SENDING.
    - `pub fn pending_stop(&self) -> Option<u64>`, `pub fn commit_stop(&mut self)` and `pub fn stop_lost(&mut self)`. `stop_lost` re-pends the same code only while in Recv/SizeKnown.
    - `pub fn pending_credit(&self) -> Option<u64>` is `credit.pending()` when the state is Recv and the stream isn't stopped, else `None` (§3.3: "only sends MAX_STREAM_DATA frames in the 'Recv' state").
    - `pub fn commit_credit(&mut self)` appends `Credit{limit}`. `pub fn credit_lost(&mut self)`.
    - `pub fn state(&self) -> RecvState`, `pub fn counted_exec(&self) -> u64`, `pub fn retired_exec(&self) -> u64`, `pub fn buffered_len(&self) -> usize`, `pub fn is_terminal(&self) -> bool`.

- [ ] **Step 1: Failing tests** (`tests/recv_stream.rs`). Each case is `RecvStream::new(0, 100)` and `conn_room = 1000` unless stated. `D(d, f)` is `StreamEvent::Data{id: 0, data: d, fin: f}`.
  - **`ordered_delivery`:**
    - `on_data(3, "def", false)` returns `Ok(6)`, with no events;
    - `on_data(0, "abc", false)` returns `Ok(0)`, with events `[D("abcdef", false)]`;
    - `on_data(6, "", true)` returns `Ok(0)`, with events `[D("", true)]`, and the state is DataRead.
  - **`fin_out_of_order`:**
    - `on_data(3, "de", true)` leaves the state SizeKnown, with no events;
    - `on_data(0, "abc", false)` gives events `[D("abcde", true)]`, and the state is DataRead.
  - **`final_size_rules`.** Each case is fresh:
    - (a) `on_data(0, "abcdefghij", true)`, then `on_data(0, "abcdefghijkl", true)` → `Err(FINAL_SIZE_ERROR)`;
    - (b) `on_data(10, "", true)`, then `on_data(10, "x", false)` → `Err(FINAL_SIZE_ERROR)`;
    - (c) `on_data(0, [0; 8], false)`, then `on_data(5, "", true)` → `Err(FINAL_SIZE_ERROR)`;
    - (d) `on_data(10, "", true)`, then `on_reset(0, 9)` → `Err(FINAL_SIZE_ERROR)`;
    - (e) `on_data(10, "", true)`, then `on_reset(7, 10)` → `Ok(0)`, with events `[Reset{0, 7}]` and state ResetRead;
    - (f) `on_data(0, [0; 8], false)`, then `on_reset(0, 5)` → `Err(FINAL_SIZE_ERROR)`;
    - (g) `on_data(0, "abc", true)`, then:
      - `on_data(0, "abc", true)` → `Ok(0)`, with no new events;
      - `on_reset(0, 3)` → `Ok(0)`, with no new events;
      - `on_reset(0, 4)` → `Err(FINAL_SIZE_ERROR)`;
    - (h) `on_data(10, "", true)`, then `on_data(0, "abcde", true)` → `Err(FINAL_SIZE_ERROR)`.
  - **`flow_control`** (`new(0, 10)`):
    - `on_data(5, "abcde", false)` → `Ok(10)`;
    - `on_data(10, "x", false)` → `Err(FLOW_CONTROL_ERROR)`;
    - fresh: `on_reset(0, 11)` → `Err(FLOW_CONTROL_ERROR)`;
    - fresh: `on_data(0, "abcde", false, conn_room 4)` → `Err(FLOW_CONTROL_ERROR)` with no events, then `on_data(0, "abcd", false, conn_room 4)` → `Ok(4)` with `[D("abcd", false)]`.
  - **`error_precedence`** (`new(0, 10)`): `on_data(10, "", true)`, then `on_data(10, "x", false, conn_room 0)` → `Err(FINAL_SIZE_ERROR)`. The final size, the stream limit and the connection room are all exceeded, and the final-size check wins.
  - **`duplicates_not_recounted`:**
    - `on_data(0, "abcd")` → `Ok(4)`;
    - `on_data(0, "abcd")` → `Ok(0)`;
    - `on_data(2, "cdef")` → `Ok(2)`.
  - **`conflicting_retransmit`:**
    - `on_data(0, "abc")`;
    - `on_data(0, "xyz")` → `Ok(0)`, with no new events;
    - `on_data(2, "QR", true)` → events gain `[D("R", true)]`.
  - **`credit`** (`new(0, 10)`):
    - `on_data(0, [0; 6], false)`, then `pending_credit() == Some(16)`;
    - before committing, `on_data(6, [0; 5], false)` → `Err(FLOW_CONTROL_ERROR)`;
    - `commit_credit()`, then `pending_credit() == None`;
    - `on_data(6, [0; 10], true)` → `Ok(10)`, and the state is DataRead;
    - `pending_credit() == None`.
    - Separately: after a `commit_credit()`, `credit_lost()` gives `pending_credit() == Some(16)`.
  - **`stop_keeps_events`** (preflight R1; it was `stopped_suppresses_events`):
    - `on_data(0, "ab")` gives `[D("ab", false)]`;
    - `stop(0)` is true, `pending_stop() == Some(0)`, then `commit_stop()`;
    - `stop(0)` is false;
    - `on_data(2, "cd", true)` → `Ok(2)`, and the events gain `[D("cd", true)]`. The state is DataRead and `retired_exec() == 4`.
    - Fresh: `stop(0)`, then `on_reset(3, 0)` → `Ok(0)`, with events `[Reset{0, 3}]` and state ResetRead.
    - Fresh: `stop(0)`, then `on_data(0, [0; 60], false)` gives `pending_credit() == None`.
  - **`reset_counts`:** `on_data(0, "abc", false)`, then `on_reset(1, 10)` → `Ok(7)`, with `retired_exec() == 10` and `buffered_len() == 0`.
  - **`buffer_bound`** (`new(0, 10)`): `on_data(9, "z", false)` gives `buffered_len() <= 10`.
- [ ] **Step 2:** Run the tests and confirm they fail.
- [ ] **Step 3: Implement.** Duvet-cite:
  - §3.2: the Figure 3 paragraphs for each edge in `recv_edge`, and the "suppressed or withheld" sentence for step 3 of Reset;
  - §4.5: both FINAL_SIZE_ERROR SHOULDs;
  - §4.1 and §19.10: the receiver FLOW_CONTROL_ERROR MUSTs;
  - §3.5: "STREAM frames received after sending a STOP_SENDING frame are still counted toward connection and stream flow control".

  `on_data` computes every check before touching `re`. The `conn_room` comparison uses `counted` arithmetic in `u64`: every value is ≤ VARINT_MAX, so nothing overflows.
- [ ] **Step 4:** Run the four checks.
- [ ] **Step 5: Commit:** `feat(quic): verified receiving-part state machine with final-size and flow checks (RFC 9000 §3.2, §4.5)`
- [ ] **Step 6: Matrix commit:** touched notes `3c: recv_stream.rs (closed in Task 6)` on §2.2, appended to Task 2's note, and `3c: recv_stream.rs (closed in Task 5)` on §4.5. No row closes here. The `✅ 3c` entries in Tasks 5 and 6 replace these interim 3c notes.

---

### Task 4: Sending part (`quic::send_stream`)

**Files:**
- Create: `crates/quic/src/send_stream.rs`
- Modify: `crates/quic/src/lib.rs`, `TRUSTED.md` (extend the row with `SendState`, `Chunk`)
- Test: `crates/quic/tests/send_stream.rs`

**Interfaces:**
- Consumes: `SendCredit` (Task 1) and `VARINT_MAX`.
- Produces:
  - **`pub enum SendState { Ready, Send, DataSent, DataRecvd, ResetSent, ResetRecvd }`.**
  - **`pub open spec fn send_edge(a, b) -> bool`** lists exactly the Figure 2 edges:
    - Ready→Send;
    - Send→DataSent;
    - DataSent→DataRecvd;
    - Ready→ResetSent, Send→ResetSent and DataSent→ResetSent;
    - ResetSent→ResetRecvd.

    **`pub open spec fn send_step_ok(a, b)`** = `a == b || send_edge(a, b) || exists|c| send_edge(a, c) && send_edge(c, b)`. One emission may take Ready→Send→DataSent.
  - **`pub struct Chunk { pub off: u64, pub data: Vec<u8>, pub fin: bool, pub new_bytes: u64 }`.**
  - **`pub struct SendStream`.** Fields:
    - `state`;
    - `buf: Vec<u8>`, holding the bytes `[acked_base, written)`;
    - `acked_base`, `written`, `sent_end`, `fin_written`, `fin_acked`;
    - `acked: Vec<(u64, u64)>` and `lost: Vec<(u64, u64)>` (sorted, merged), plus `fin_lost`;
    - `credit: SendCredit`;
    - `reset: Option<(u64, u64)>` and `reset_pending`;
    - ghost `all_written: Seq<u8>`.

    `// ponytail: O(ranges) sorted-Vec range sets; interval tree if loss patterns make them long.`
    - Closed spec fns `all_written()`, `state()` and `wf()`. `wf()` holds:
      - `sent_end <= credit.max()`;
      - `sent_end <= written == all_written().len() <= VARINT_MAX`;
      - `state ∉ {ResetSent, ResetRecvd} ==> buf@ == all_written().subrange(acked_base, written)`. After a reset, `buf` is empty;
      - `reset is Some((_, f)) ==> f == sent_end`.
    - **`pub fn new(max: u64) -> SendStream`**, starting in Ready.
    - **`pub fn write(&mut self, data: &[u8], fin: bool) -> (r: Result<(), ()>)`.**
      - `Err(())` with no change iff the state ∉ {Ready, Send}, or `fin_written`, or `written + data.len() > VARINT_MAX`.
      - Otherwise `all_written' == all_written + data@`, and `fin_written' == fin`.
    - **`pub fn poll_data(&mut self, max_len: u64, conn_avail: u64) -> (r: Option<Chunk>)`:**
      - It returns `None` whenever the old state is ResetSent, ResetRecvd or DataRecvd (§3.3).
      - Retransmissions of `lost` ranges come first. They use no new credit, and are clipped to `acked_base`.
      - Then new data from `sent_end`: `len = min(max_len, written − sent_end, credit.available(), conn_avail)`.
      - `fin` is attached when the chunk ends at `written` and `fin_written` holds, or when a lost FIN is being resent.
      - A FIN-only chunk (`len == 0`) is emitted when nothing else is owed.
      - It never returns `len == 0 && !fin`.
      - Ensures:
        - `c.data@ == all_written().subrange(c.off, c.off + c.data.len())`, so the data at an offset never changes (§2.2);
        - `c.off + c.data.len() <= written`, so there is no data at or beyond the final size (§4.5);
        - `c.fin ==> c.off + c.data.len() == written && fin_written`;
        - `c.new_bytes <= conn_avail` and `sent_end' == sent_end + c.new_bytes`;
        - `send_step_ok(old.state, state)`, with any first emission leaving Ready.
    - **`pub fn reset(&mut self, code: u64) -> (fresh: bool)`**, which requires `code <= VARINT_MAX`.
      - `fresh` iff the state ∈ {Ready, Send, DataSent}.
      - Then the state is ResetSent, `reset = Some((code, sent_end))` and `reset_pending`, and `buf`, `lost` and `acked` are cleared.
    - **`pub fn on_stop_sending(&mut self, code: u64) -> bool`** = `reset(code)` (Global Constraints ruling).
    - `pub fn on_max_stream_data(&mut self, max: u64)` = `credit.on_max(max)`.
    - `pub fn pending_reset(&self) -> Option<(u64, u64)>`, `pub fn commit_reset(&mut self)`, `pub fn on_reset_lost(&mut self)` and `pub fn on_reset_acked(&mut self)`.
      - `on_reset_lost` re-pends the *same* `(code, final)` (§13.3, "unchanged").
      - `on_reset_acked` takes ResetSent→ResetRecvd.
    - `pub fn on_data_acked(&mut self, off: u64, len: u64, fin: bool)` and `pub fn on_data_lost(&mut self, off: u64, len: u64, fin: bool)`. These are no-ops in reset or terminal states.
      - An ack advances `acked_base` and frees the `buf` prefix.
      - DataSent→DataRecvd happens exactly when `acked_base == written && fin_acked`.
    - **`pub fn next_off(&self) -> (r: Option<u64>)`** (preflight: Task 6's fit rule and 3d's CRYPTO packing both need `off` before calling `poll_data`).
      - It returns `None` in ResetSent, ResetRecvd and DataRecvd.
      - Otherwise, if a lost range is pending, it returns that range's start clipped to `acked_base`; else `sent_end` when new data or a FIN is still owed; else `None`.
      - It ensures `r is Some(o) ==> o <= written`. `poll_data` ensures that `r is Some(c)` implies `old(self).next_off() == Some(c.off)`.
    - `pub fn state_exec(&self) -> SendState`, `pub fn sent_end(&self) -> u64`, `pub fn max(&self) -> u64`, `pub fn is_terminal(&self) -> bool`.
    - Every method ensures `wf()` and `send_step_ok(old.state, state)`.

- [ ] **Step 1: Failing tests** (`tests/send_stream.rs`). `C(off, data, fin, new)` is a `Chunk`.
  - **`send_flow`:** `new(5)`, then `write("abcdefgh", true)`, and the state is Ready.
    - `poll_data(100, 100) == Some(C(0, "abcde", false, 5))`, and the state is Send;
    - `poll_data(100, 100) == None`;
    - `on_max_stream_data(4)`, then `max() == 5`;
    - `on_max_stream_data(8)`, then `poll_data(100, 100) == Some(C(5, "fgh", true, 3))`;
    - the state is DataSent, and `sent_end() == 8`.
  - **`conn_limited`:** `new(100)`, then `write("abcdef", false)`:
    - `poll_data(100, 2) == Some(C(0, "ab", false, 2))`;
    - `poll_data(100, 0) == None`.
  - **`fin_only`:** `new(0)`, then `write("", true)`, then `poll_data(100, 0) == Some(C(0, "", true, 0))`, and the state is DataSent.
  - **`max_len_split`:** `new(100)`, then `write("abcdef", true)`:
    - `poll_data(4, 100) == Some(C(0, "abcd", false, 4))`;
    - `poll_data(4, 100) == Some(C(4, "ef", true, 2))`.
  - **`retransmit_same_bytes`:** `new(100)`, then `write("abcdef", true)`, then poll gives `C(0, "abcdef", true, 6)`.
    - `on_data_lost(2, 3, false)`, then `poll_data(100, 0) == Some(C(2, "cde", false, 0))`;
    - `on_data_lost(0, 6, true)`, then `poll_data(4, 0)` gives `C(0, "abcd", false, 0)` and then `C(4, "ef", true, 0)`;
    - `on_data_acked(0, 6, true)`, then the state is DataRecvd and `poll_data(100, 100) == None`.
  - **`all_acks_required`:** `new(100)`, then `write("abcd", true)`, then poll.
    - `on_data_acked(2, 2, true)`: the state is still DataSent;
    - `on_data_acked(0, 2, false)`: DataRecvd.
  - **`reset_stops_stream`:** `new(100)`, then `write("abcdef", false)`, then `poll_data(3, 100)`.
    - `reset(9)` is true, and the state is ResetSent;
    - `poll_data(100, 100) == None`;
    - `pending_reset() == Some((9, 3))`, then `commit_reset()`, then `pending_reset() == None`;
    - `on_data_lost(0, 3, false)`, then `poll_data(100, 100) == None`;
    - `write("x", false) == Err(())`;
    - `on_reset_lost()`, then `pending_reset() == Some((9, 3))`, then commit;
    - `on_reset_acked()`, then the state is ResetRecvd;
    - `reset(1)` is false.
  - **`stop_sending_forces_reset`.** Each case starts from a fresh `new(100)`:
    - in Ready: `on_stop_sending(5)` is true, and `pending_reset() == Some((5, 0))`;
    - in DataSent (after `write("ab", true)` and a poll): true, with `Some((6, 2))`;
    - in DataRecvd (that, plus `on_data_acked(0, 2, true)`): false, with `None`;
    - in ResetSent: false.
  - **`write_rules`:** `new(100)`, then `write("a", true)` is `Ok`, then `write("b", false) == Err(())` and `write("", true) == Err(())`.
  - **`next_off_tracks_poll`** (preflight): `new(100)`, then `write("abcdef", true)`:
    - `next_off() == Some(0)`;
    - `poll_data(4, 100)`, then `next_off() == Some(4)`;
    - `on_data_lost(1, 2, false)`, then `next_off() == Some(1)`;
    - `poll_data(100, 100)` gives `C(1, "bc", false, 0)` and then `C(4, "ef", true, 2)`, then `next_off() == None`;
    - `reset(0)`, then `next_off() == None`.
- [ ] **Step 2:** Run the tests and confirm they fail.
- [ ] **Step 3: Implement.** Duvet-cite:
  - §3.1: the Figure 2 paragraphs, one per `send_edge` arm;
  - §3.3: both sender MUSTs, at `poll_data`'s early return and at `pending_reset`'s terminal guard;
  - §3.5: "MUST send a RESET_STREAM frame if the stream is in the 'Ready' or 'Send' state", at `on_stop_sending`;
  - §4.5: "An endpoint MUST NOT send data on a stream at or beyond the final size.";
  - §2.2: "The data at a given offset MUST NOT change if it is sent multiple times".
- [ ] **Step 4:** Run the four checks.
- [ ] **Step 5: Commit:** `feat(quic): verified sending-part state machine with retransmission and reset (RFC 9000 §3.1, §3.3)`
- [ ] **Step 6: Matrix commit:** `✅ 3c: crates/quic/src/send_stream.rs` on §3.3.

---

### Task 5: `Streams` receive path and frame dispatch (`quic::streams`)

**Files:**
- Create: `crates/quic/src/streams.rs`
- Modify: `crates/quic/src/lib.rs`
- Test: `crates/quic/tests/streams_rx.rs`

**Interfaces:**
- Consumes: Tasks 1, 3 and 4; `Frame`; `TransportParams`; the codes.
- Produces (`quic::streams`):
  - **`pub struct Streams`.** Fields:
    - `ids: StreamIds`;
    - `entries: Vec<Entry>`, where `Entry { id: u64, recv: Option<RecvStream>, send: Option<SendStream> }`;
    - `conn_recv: RecvCredit` (window `local.initial_max_data`, cap VARINT_MAX), with consumed = Σ retired;
    - `conn_counted: u64`, Σ counted over *all* streams ever, removed ones included;
    - `conn_send: SendCredit` (`peer.initial_max_data`);
    - the per-direction windows from the Global Constraints table;
    - ghost per-ID traces.
  - **`pub fn new(local: &TransportParams, peer: &TransportParams) -> Streams`:**
    - requires `local.initial_max_streams_uni >= 3`. That is `h3::limits::MIN_PEER_UNI_STREAMS` (RFC 9114 §6.2), defined in `crates/h3/src/limits.rs`. It is written as a literal so `quic` doesn't depend on `h3`, and 3d's adapter test asserts the two are equal.
    - **requires `local.initial_max_streams_bidi <= MAX_LOCAL_STREAMS` and `local.initial_max_streams_uni <= MAX_LOCAL_STREAMS`** (preflight R3, binding obligation 1: "advertise bounded"). This uses `pub const MAX_LOCAL_STREAMS: u64 = 100;` in streams.rs, with `// ponytail: matches the linear-scan bound above; raise both together.` Every 3c, 3d and 3e vector uses at most 10.
    - **requires `stream_tp_ok(local@) && stream_tp_ok(peer@)`** (preflight; this replaces "3b's parser and `server_tp_wf` already ensure this", which held only for `local`).
      - `pub open spec fn stream_tp_ok(p: SpecTp) -> bool` says that `initial_max_data` and the three `initial_max_stream_data_*` are ≤ VARINT_MAX, and both `initial_max_streams_*` are ≤ `MAX_STREAMS_LIMIT`.
      - `server_tp_wf(p)` implies it for `local`.
      - For `peer`, 3b exports no lemma that a parsed TP is bounded: `parse_transport_params` ensures only `== rfc_transport_params(..)`. 3d must prove `rfc_transport_params(b, true) == Ok(t) ==> stream_tp_ok(t)` for its `peer_tp_wf`; see the cross-plan notes in `3c-preflight.md`.
  - **`pub open spec fn rfc_stream_frame_check(ids: StreamIds, f: SpecFrame) -> Option<u64>`.** It reads `ids` only through Task 1's `peer_limit` and `local_uni_created` (spec twins; preflight: `SpecIds` was never produced). This is the direction/creation/limit table, checked before anything else. With `k = spec_stream_kind(stream_id)`:
    - k is ServerBidi → STREAM_STATE_ERROR, for any of the five stream frames;
    - k is ServerUni with Stream, ResetStream or StreamDataBlocked → STREAM_STATE_ERROR (§19.4, §19.8, §19.13: send-only);
    - k is ClientUni with MaxStreamData or StopSending → STREAM_STATE_ERROR (§19.5, §19.10: receive-only);
    - k is ServerUni with MaxStreamData/StopSending and `!local_uni_created(id)` → STREAM_STATE_ERROR (§19.5, §19.10: not yet created);
    - k is ClientBidi/ClientUni with `!peer_id_allowed(id, ids.peer_limit(k is ClientBidi))` → STREAM_LIMIT_ERROR;
    - otherwise `None`.
  - **`pub fn on_frame(&mut self, f: &Frame, ev: &mut Vec<StreamEvent>) -> (r: Result<(), u64>)`:**
    - requires `wf()`, `!failed()`, `frame_wf(f@)` (preflight: the codec guarantee, from `parse_payload`'s `frames_received`), and that `f` is one of ResetStream, StopSending, Stream, MaxData, MaxStreamData, MaxStreams, DataBlocked, StreamDataBlocked or StreamsBlocked (types 0x04, 0x05, 0x08–0x17).
    - **`pub fn failed(&self) -> bool`**, with spec twin `failed_spec` (preflight: the Global Constraints name it, but nothing produced it). It is a latch, set on every `Err`: `r is Err ==> self.failed()`. It is needed because implicit opening may already have created entries when a later check fails.
    - **If `rfc_stream_frame_check` gives `Some(c)`**, the result is `Err(c)`, and nothing changes except the `failed` latch.
    - **Otherwise, for client streams:** `on_peer_stream`. A `New{first, count}` creates entries for every ID in `[first, id]` step 4: bidi entries get recv and send parts, uni entries get recv only (§3.2 MUST).
    - **An ID that is created but has no entry** belongs to a removed stream, so the result is `Ok` and nothing happens.
    - **Stream:** `recv.on_data(.., conn_room = conn_recv.limit() − conn_counted, ev)`. On `Ok(n)`: `conn_counted += n`, then `conn_recv.on_consumed(Δretired)`.
    - **ResetStream:** likewise, through `recv.on_reset`.
    - **StopSending:** if `send.on_stop_sending(code)` is fresh, push `StopSending{id, code}`.
    - **MaxStreamData:** `send.on_max_stream_data`.
    - **MaxData:** `conn_send.on_max`.
    - **MaxStreams:** `ids.on_max_streams`.
    - **DataBlocked, StreamsBlocked and StreamDataBlocked:** no state change beyond stream opening (§4.2).
    - After every delegated call, an entry whose parts are all terminal is removed (`fn gc(&mut self, i: usize)`). Removing a peer stream calls `ids.on_peer_closed`.
    - **Ensures:**
      - delegation: `ev`'s new events for `id` are exactly `rfc_recv` of that stream's extended trace;
      - E1–E5. E5 is binding obligation 1: `gc` removes a peer entry, and calls `on_peer_closed`, only once its receive part is DataRead or ResetRead. By delegation, that is only after the terminal event was pushed, because R1 means `stopped` no longer gates events;
      - `wf()`, which includes:
        - `conn_counted <= conn_recv.limit()`, so a violation is detected (§4.1, §19.9);
        - `conn_recv.consumed() <= conn_counted`;
        - Σ `buffered_len()` over entries ≤ `conn_counted − Σ retired` ≤ `conn_recv.limit()`, so no allocation goes beyond the advertised connection window;
        - every entry ID is created and unique, and the number of live peer-stream entries of each type is ≤ that type's *initial* `local.initial_max_streams_*`, so ≤ `MAX_LOCAL_STREAMS`. The re-credit target `closed + window` gives this, and it bounds both implicit-open allocation and `H3Conn`'s tables (binding obligation 1);
        - no RESET_STREAM is queued except by `StopSending` (for §11.2, finished in Task 6).
  - `pub fn peer_max_data(&self) -> u64`, `pub fn local_uni_limit(&self) -> u64` and `pub fn open_streams(&self) -> usize`, for tests and 3d.

- [ ] **Step 1: Failing tests** (`tests/streams_rx.rs`).
  - Helpers: `local()` is `default_transport_params()` with:
    - `initial_max_data = 1000`;
    - `initial_max_stream_data_bidi_remote = 100`, `_uni = 100`;
    - `initial_max_streams_bidi = 10`, `_uni = 3`.

    `peer()` is the default with:
    - `initial_max_data = 1000`;
    - `initial_max_stream_data_bidi_local = 100`, `_uni = 100`;
    - `initial_max_streams_uni = 3`.

    `S(id, off, d, fin)` is `Frame::Stream`. Each test starts from `Streams::new(&local(), &peer())` unless it says otherwise.
  - **`stream_data_to_events`:** `S(0, 0, "GET", true)` gives `ev == [Data{0, "GET", true}]`.
  - **`out_of_order_frames`:** `S(4, 3, "lo", true)`, then `S(4, 0, "hel", false)` gives `ev == [Data{4, "hello", true}]`.
  - **`state_errors`.** Each case is fresh and returns `Err(STREAM_STATE_ERROR)`:
    - `S(3, 0, "x", false)`;
    - `ResetStream{3, 0, 0}`;
    - `StreamDataBlocked{3, 0}`;
    - `MaxStreamData{2, 10}`;
    - `StopSending{2, 0}`;
    - `S(1, 0, "x", false)`;
    - `ResetStream{1, 0, 0}`;
    - `MaxStreamData{3, 10}`;
    - `StopSending{7, 0}`.
  - **`stream_limit`:**
    - `S(10, 0, "x", false)` is `Ok`;
    - `S(14, 0, "x", false)` → `Err(STREAM_LIMIT_ERROR)`;
    - fresh: `MaxStreamData{14, 5}` → `Err(STREAM_STATE_ERROR)`. The direction is checked before the limit;
    - fresh: `S(40, 0, "x", false)` → `Err(STREAM_LIMIT_ERROR)`.
  - **`implicit_open`:** `S(8, 0, "x", false)`, then `ResetStream{0, 5, 0}`, gives `ev == [Data{8, "x", false}, Reset{0, 5}]`.
  - **`closed_stream_ignored`:**
    - `S(2, 0, "a", true)` gives `[Data{2, "a", true}]`, and `open_streams() == 0`;
    - then `S(2, 0, "a", true)`, `S(2, 0, "ab", true)` and `ResetStream{2, 0, 9}` each return `Ok` and add no events.
  - **`conn_flow_counts_high_water`:** `local.initial_max_data = 10`:
    - `S(0, 0, [0; 8], false)` twice → `Ok`;
    - `S(0, 8, [0; 2], false)` → `Ok`;
    - `S(4, 0, [0], false)` → `Err(FLOW_CONTROL_ERROR)`. Nothing was polled, so the limit is still 10.
  - **`reset_final_size_counts`:** `local.initial_max_data = 10`:
    - `ResetStream{0, 1, 6}` gives `[Reset{0, 1}]`;
    - `S(4, 0, [0; 5], false)` → `Err(FLOW_CONTROL_ERROR)`;
    - fresh, the same reset, then `S(4, 0, [0; 4], false)` → `Ok`.
  - **`stop_sending_unopened`:**
    - fresh: `StopSending{3, 0}` → `Err(STREAM_STATE_ERROR)`;
    - fresh: `StopSending{1, 0}` → `Err(STREAM_STATE_ERROR)`;
    - fresh: `StopSending{0, 7}` → `Ok`, with `ev == [StopSending{0, 7}]`;
    - then `S(0, 0, "GET", true)` adds `Data{0, "GET", true}`. Our receive part is unaffected.
  - **`max_data_non_increasing`:** `peer.initial_max_data = 100`:
    - `MaxData(50)`, then `peer_max_data() == 100`;
    - `MaxData(200)`, then `peer_max_data() == 200`.
  - **`max_streams_2_60`:**
    - `MaxStreams{false, 1<<60}` → `Ok`, and `local_uni_limit() == 1<<60`;
    - `MaxStreams{false, 5}`: the limit is unchanged;
    - `MaxStreams{true, 7}` → `Ok`.
  - **`blocked_frames_ignored`:**
    - `DataBlocked(5)`, `StreamsBlocked{true, 3}` and `StreamsBlocked{false, 3}` each → `Ok`, with no events and `open_streams() == 0`;
    - `StreamDataBlocked{0, 5}` → `Ok`, with no events and `open_streams() == 1`.
  - **`tp_direction_mapping_rx`:** `local.initial_max_stream_data_bidi_remote = 5`, `_bidi_local = 1000`, `_uni = 7`. Each case is fresh:
    - `S(0, 0, [0; 6], false)` → `Err(FLOW_CONTROL_ERROR)`;
    - `S(0, 0, [0; 5], false)` → `Ok`;
    - `S(2, 0, [0; 7], false)` → `Ok`;
    - `S(6, 0, [0; 8], false)` → `Err(FLOW_CONTROL_ERROR)`.
- [ ] **Step 2:** Run the tests and confirm they fail.
- [ ] **Step 3: Implement.** Duvet-cite:
  - §3.2: "Before a stream is created, all streams of the same type with lower-numbered stream IDs MUST be created";
  - §4.5: "The receiver MUST use the final size of the stream to account for all bytes sent on the stream in its connection-level flow controller";
  - §19.4: the send-only MUST;
  - §19.5: both MUSTs;
  - §19.8: the STREAM_STATE_ERROR MUST, plus the 2⁶²−1 MUST, noting that 3b enforces it;
  - §19.10: both STREAM_STATE_ERROR MUSTs and the FLOW_CONTROL_ERROR MUST;
  - §19.13: the send-only MUST;
  - §19.9 and §4.1: the receiver FLOW_CONTROL_ERROR MUSTs;
  - RFC 9114 §6.2: "MUST allow the peer to create at least three unidirectional streams", at `Streams::new`'s `initial_max_streams_uni >= 3` requires (binding obligation 3).

  Transcribe the dispatch table as one comment block above `rfc_stream_frame_check`.
- [ ] **Step 4:** Run the four checks.
- [ ] **Step 5: Commit:** `feat(quic): verified stream frame dispatch, STREAM_STATE/STREAM_LIMIT errors, connection receive credit (RFC 9000 §3.2, §4.5, §19.4-19.13)`
- [ ] **Step 6: Matrix commit:** `✅ 3c: crates/quic/src/streams.rs` on §3.2, §4.5, §19.4, §19.5, §19.8 (replacing 3b's touched note) and §19.13.
  - On RFC 9114 §6.2, replace the tail "(open: transport parameter encoded in Phase 3)" with "(open: 3c `Streams::new` requires `initial_max_streams_uni >= 3`; encoded by 3d `local_tp_ok`, closed in 3d)".
  - This is not a 3c closing row. The 19-row count is unchanged.

---

### Task 6: `Streams` transmit path and application API

**Files:**
- Modify: `crates/quic/src/streams.rs`
- Test: `crates/quic/tests/streams_tx.rs`

**Interfaces:**
- Consumes:
  - Task 5's `Streams`, `gc` and `failed`;
  - Task 4's `poll_data`, `next_off` and `pending_reset`;
  - Task 3's `pending_stop` and `pending_credit`;
  - Task 1's `pending_max_streams`;
  - 3b's `serialize_frame`, `spec_frame_bytes`, `frame_wf`, `frame_permitted` and `parse_frame` (the last only for `emitted_frames_roundtrip`);
  - wire's `varint_len`, `spec_varint` and `theorem_serialize_matches_rfc` (`spec_varint(v).len() == rfc_varint_min_len(v)`, for `lemma_stream_frame_len`).
- Produces:
  - **`pub fn write(&mut self, id: u64, data: &[u8], fin: bool) -> (r: Result<(), ()>)`.**
    - It succeeds when `id` has an entry with a send part, and `SendStream::write` succeeds.
    - It also succeeds when `id` is ServerUni and `ids.open_local_uni(id)` holds: that creates an entry with a send part, `SendStream::new(peer.initial_max_stream_data_uni)`, and then writes.
    - Otherwise it returns `Err(())` with nothing changed. That covers: receive-only, server-bidi, a client stream the peer hasn't opened, a removed stream, a skipped local ID, and a local ID beyond the peer's limit.
  - **`pub fn reset(&mut self, id: u64, code: u64)`**, which requires `code <= VARINT_MAX`. It calls `send.reset(code)` if a send part exists, and otherwise does nothing. Together with Task 5's StopSending path, this is the *only* way a RESET_STREAM gets queued (§11.2).
  - **`pub fn stop_sending(&mut self, id: u64, code: u64)`**, which requires `code <= VARINT_MAX`. It calls `recv.stop(code)` if a receive part exists. Afterwards no MAX_STREAM_DATA is sent for `id`. Its `Data`/`Reset` events continue until the terminal one (E3, E5, preflight R1).
  - **`pub fn poll_frames(&mut self, budget: usize, out: &mut Vec<Frame>)`.**
    - It appends, in this order: every pending RESET_STREAM, STOP_SENDING, MAX_DATA, MAX_STREAM_DATA and MAX_STREAMS (bidi, then uni), then STREAM chunks in entry order.
    - Each control frame is serialized into a scratch `Vec` and appended only if it fits the remaining budget. It is then committed (`commit_*`); a frame that doesn't fit stays pending. `// ponytail: double serialization for control frames; compute lengths with varint_len if it shows in profiles.`
    - **STREAM fit rule.** This is a body, because the signature doesn't determine it. With `hdr = 1 + varint_len(id) + (off > 0 ? varint_len(off) : 0)`:
      ```
      for w in [1, 2, 4, 8]:  n_w = min(want, room - hdr - w)  if room >= hdr + w, and kept only if varint_len(n_w) <= w
      max_len = max n_w   (none if no w qualifies)
      ```
      Here `off` is `send.next_off()` (Task 4; skip the entry when it is `None`). `want` is `written − off` for new data, or the lost range for a retransmission. `poll_data(max_len, conn_send.available())` is called only if `max_len >= 1`, or for a FIN-only chunk with `room >= hdr + 1`. `conn_send.consume(new_bytes)` follows.
    - **Ensures:**
      - every appended frame satisfies `frame_wf(f@)` and `frame_permitted(spec_frame_type(f@), OneRtt)`;
      - Σ `spec_frame_bytes(f@).len()` over the appended frames is ≤ `budget`;
      - `conn_send.used <= peer max_data` and each `sent_end <= max` still hold (§2.2, §4.1, §19.9, §19.10);
      - MAX_STREAM_DATA appears only for a receive part in Recv;
      - no STREAM frame appears for a send part in ResetSent, ResetRecvd or DataRecvd;
      - every RESET_STREAM appended was queued by `reset` or by a peer STOP_SENDING.
    - **Binding for 3d:** frames returned here count as sent. 3d must report each one through `on_frame_acked` or `on_frame_lost`. If it never transmits a frame, it reports it lost at once.
  - **`pub fn on_frame_acked(&mut self, f: &Frame)` and `pub fn on_frame_lost(&mut self, f: &Frame)`.** They handle Stream, ResetStream, StopSending, MaxData, MaxStreamData and MaxStreams; any other variant, or a removed stream, is a no-op.
    - An ack calls `on_data_acked` or `on_reset_acked`, then `gc`.
    - A loss calls `on_data_lost`, `on_reset_lost` (unchanged), `stop_lost`, `credit_lost` or `max_streams_lost`, and resends the *current* value (§13.3).
  - **Binding note for the 3d h3 adapter.** The 2b obligations are carried here (preflight):
    - **`start()` first** (2b obligation 2). Call `H3Conn::start` before the first `StreamEvent` is delivered or `send_response` is called, so that SETTINGS opens stream 3 (RFC 9114 §6.2.1, §7.2.4.2). Draining `StreamEvent`s is gated on having started.
    - `Data` → `H3Conn::on_stream_data(id, &data, fin)`.
    - `Reset` → `on_stream_reset(id, code)`.
    - **Abort signal** (2b obligation 4). When a `Reset` hits a request stream whose `send_open` was already false, H3Conn emits nothing. The adapter must still tell the application that any `RequestBody` stream for that request was aborted. 3c delivers every `Reset`, including after a local stop (R1), so the signal is always available.
    - **`StopSending` → `H3Conn::on_stop_sending(id, code)` on every stream** (supersedes the earlier "ignore on other streams"; 3d already says so).
      - On stream 3, 2b answers H3_CLOSED_CRITICAL_STREAM (RFC 9114 §6.2.1: "the receiver MUST NOT request that the sender close the control stream"). We open no QPACK streams.
      - On a request stream, 2b drops the pending response, and later `write` calls return `Err(())`.
    - `Output::ResetStream` → `reset`, `Output::StopSending` → `stop_sending`, and `Output::StreamWrite` → `write`.
    - **Bounded streams** (2b obligation 1). 3c re-credits MAX_STREAMS only after the terminal event (E5) and bounds live peer streams by `MAX_LOCAL_STREAMS` (R3). The adapter must pass every `StreamEvent` to `H3Conn` in order, which 3d's proof obligation already states, so that `H3Conn` has forgotten the stream by then.
    - `initial_max_streams_uni >= 3` (2b obligation 3) is `Streams::new`'s requires (Task 5).

- [ ] **Step 1: Failing tests** (`tests/streams_tx.rs`). They use the same helpers as Task 5, and `S` as before.
  - **`write_and_poll`:** `S(0, 0, "GET", true)`, then `write(0, "hello", true) == Ok(())`, then `poll_frames(1200)` gives exactly `[S(0, 0, "hello", true)]`.
  - **`local_uni_open`:** `peer.initial_max_streams_uni = 1`:
    - `write(3, [0x00, 0x04, 0x00], false) == Ok(())`;
    - `write(7, "x", false)`, `write(2, ..)`, `write(1, ..)`, `write(4, ..)` and `write(11, ..)` are all `Err(())`;
    - `poll_frames(1200)` gives `[S(3, 0, [0, 4, 0], false)]`;
    - `MaxStreams{false, 3}`, then `write(11, ..)` is `Err(())` and `write(7, "x", false)` is `Ok(())`.
  - **`tp_direction_mapping_tx`:** `peer.initial_max_stream_data_bidi_local = 4`, `_bidi_remote = 1000`, `_uni = 6`:
    - `S(0, 0, "GET", true)`;
    - `write(0, "0123456789", true)` and `write(3, "abcdefghij", false)`;
    - poll gives `[S(0, 0, "0123", false), S(3, 0, "abcdef", false)]`;
    - `MaxStreamData{0, 10}`, then poll gives `[S(0, 4, "456789", true)]`.
  - **`conn_send_limit`:** `peer.initial_max_data = 5`. `S(0, 0, "GET", true)`, then `write(0, "0123456789", true)`:
    - poll gives `[S(0, 0, "01234", false)]`;
    - `MaxData(3)`, then poll gives `[]`;
    - `MaxData(8)`, then poll gives `[S(0, 5, "567", false)]`.
  - **`budget`:** `S(0, 0, "GET", true)`, then `write(0, (0..100) as bytes, false)`:
    - `poll_frames(20)` gives `[S(0, 0, bytes[0..17], false)]`, encoded `0a 00 11` + 17 bytes, 20 in all;
    - `poll_frames(20)` gives `[S(0, 17, bytes[17..33], false)]`, encoded `0e 00 11 10` + 16 bytes;
    - `poll_frames(4)` gives `[]`;
    - `poll_frames(70)` gives `[S(0, 33, bytes[33..98], false)]`. That is 65 bytes: a 2-byte length beats a 1-byte one, `1+1+1+2+65 = 70`;
    - `poll_frames(1200)` gives `[S(0, 98, bytes[98..100], false)]`.
  - **`control_frame_budget`:**
    - `S(0, 0, "GET", true)`, then `StopSending{0, 7}`;
    - `poll_frames(3)` gives `[]`;
    - `poll_frames(4)` gives `[ResetStream{0, 7, 0}]`.
  - **`credit_updates_emitted`:** `local.initial_max_data = 10` and `_bidi_remote = 10`:
    - `S(0, 0, [0; 6], false)`;
    - `poll_frames(1200)` gives exactly `[MaxData(16), MaxStreamData{0, 16}]`, and a second poll gives `[]`;
    - `S(0, 6, [0; 10], false)` → `Ok`;
    - `S(4, 0, [0], false)` → `Err(FLOW_CONTROL_ERROR)`. The update to 26 is pending, not sent.
  - **`lost_credit_resent`:** continue `credit_updates_emitted` up to its first poll. Then `on_frame_lost(&MaxData(16))`, and poll gives `[MaxData(16)]`.
  - **`stop_sending_resets`** (§3.5):
    - `S(0, 0, "GET", true)`;
    - `StopSending{0, 7}` makes `ev` end with `StopSending{0, 7}`;
    - poll gives `[ResetStream{0, 7, 0}]`;
    - `write(0, "x", true) == Err(())`.
  - **`stop_sending_after_partial`:**
    - `S(0, 0, "GET", true)`, then `write(0, "hello", false)`, then poll gives `[S(0, 0, "hello", false)]`;
    - `StopSending{0, 9}`, then poll gives `[ResetStream{0, 9, 5}]`;
    - `on_frame_lost(&S(0, 0, "hello", false))`, then poll gives `[]`.
  - **`app_reset_and_stop`:**
    - `S(0, 0, "GET", false)`;
    - `reset(0, 0x10c)` and `stop_sending(0, 0x10c)`;
    - poll gives `[ResetStream{0, 0x10c, 0}, StopSending{0, 0x10c}]`;
    - `S(0, 3, "x", true)` → `Ok`, and `ev == [Data{0, "GET", false}, Data{0, "x", true}]` (preflight R1: a stop doesn't suppress events, so h3 sees the FIN it forgets the stream on);
    - `open_streams() == 1`;
    - `on_frame_acked(&ResetStream{0, 0x10c, 0})`, then `open_streams() == 0` (E5: removed only after the terminal event).
  - **`reset_one_direction`** (§4.4):
    - `S(0, 0, "GET", false)`, then `ResetStream{0, 1, 3}`, gives `ev == [Data{0, "GET", false}, Reset{0, 1}]`;
    - `write(0, "resp", true) == Ok(())`;
    - `MaxStreamData{0, 200}` → `Ok`;
    - poll gives `[S(0, 0, "resp", true)]`.
  - **`max_streams_credit`:**
    - `S(2, 0, "a", true)` and `S(6, 0, "b", true)`, then poll gives `[MaxStreams{false, 5}]`;
    - `S(10, 0, "c", true)`, `S(14, 0, "d", true)` and `S(18, 0, "e", false)` are each `Ok`;
    - `S(22, 0, "f", false)` → `Err(STREAM_LIMIT_ERROR)`. The update to 7 is pending, not sent.
  - **`ack_frees_stream`:**
    - `S(0, 0, "GET", true)`, then `write(0, "ok", true)`, then poll gives `[f]`;
    - `on_frame_acked(&f)`, then `open_streams() == 0`;
    - `S(0, 0, "GET", true)` adds no event.
  - **`emitted_frames_roundtrip`:** after `credit_updates_emitted`, `stop_sending_after_partial` and `local_uni_open`, every polled frame goes through `serialize_frame`, and `parse_frame` gives it back, consuming its whole length.
- [ ] **Step 2:** Run the tests and confirm they fail.
- [ ] **Step 3: Implement.** Duvet-cite:
  - §2.2: "MUST NOT send data on any stream without ensuring that it is within the flow control limits";
  - §3.5: the RESET MUST, at the StopSending → `on_stop_sending` call site;
  - §4.1: "Senders MUST NOT send data in excess of either limit";
  - §4.2: "MUST NOT wait for a STREAM_DATA_BLOCKED or DATA_BLOCKED frame", at the pending-credit loop;
  - §4.4: "MUST maintain flow control state for the stream in the unterminated direction until that direction enters a terminal state", at `gc`;
  - §11.2: "RESET_STREAM MUST only be instigated by the application protocol", at `reset`;
  - §19.9: "The sum of the final sizes … MUST NOT exceed";
  - §19.10: "The data sent on a stream MUST NOT exceed the largest maximum stream data value".

  Write the binding note below into `streams.rs`'s module doc as a "Caller obligations (Phase 3d; stated here, not proven by this module)" block, mirroring `h3/src/conn.rs` l.9–22 (preflight). It lists `start()` first, the abort signal, forwarding every `StopSending`, and in-order delivery of every event, so that 2b obligations 2 and 4 live in code where the 3d implementer reads them.

  Add `pub open spec fn stream_frame_len(id, off, n) -> nat` and prove `lemma_stream_frame_len`: it equals `spec_frame_bytes(Stream{id, off, d, fin}).len()` for `|d| == n`. The budget ensures needs it.
- [ ] **Step 4:** Run the four checks. `cargo test` passes across the workspace, with every existing test unchanged: 2a, 2b, 3b, 4a, 5a, and Tasks 1–5.
- [ ] **Step 5: Commit:** `feat(quic): verified stream transmit path, app write/reset/stop API, credit emission (RFC 9000 §2.2, §4.1-4.4, §11.2)`
- [ ] **Step 6: Matrix commit:**
  - `✅ 3c: crates/quic/src/streams.rs` on §2.2, §3.5, §4.1, §4.2, §4.4, §11.2, §19.9 and §19.10;
  - the touched note on §13.3 (table above).

---

## Exit criteria (Phase 3c)

- All four checks pass on the merged tree.
- The 19 rows under "Matrix rows this plan closes" carry `✅ 3c: <file>`. 3b's touched notes on §4.6, §19.8 and §19.11 are replaced, and §13.3 has its touched note.
- `phase-3c` is merged into `main`.

## Self-review (done while writing)

- **Spec coverage.** The design spec's Phase 3 asks for "stream states" (Tasks 3–4, with Figure 2/3 edge predicates) and "connection/stream flow control" (Tasks 1, 3, 5, 6).
  - The state-machine obligations:
    - transitions are allowed: `recv_step_ok`/`send_step_ok` hold in every ensures;
    - limits are never exceeded: the `wf()` invariants in Tasks 4–6;
    - mandated errors: STREAM_STATE, STREAM_LIMIT, FINAL_SIZE, FLOW_CONTROL and CRYPTO_BUFFER_EXCEEDED each have a test on the triggering input.
  - Buffer bounds: `buffered_len <= limit − delivered` per stream, Σ ≤ the connection limit, and CRYPTO ≤ `MAX_CRYPTO_BUFFER`.
  - The outline's six tasks are kept. `reassembly` is folded into the CRYPTO task, and the aggregate is split into rx and tx, so a reviewer can reject `poll_frames` separately.
- **Type consistency.** These names are used identically everywhere:
  - `RecvCredit`/`SendCredit` (1 → 3, 4, 5) and `StreamIds`/`Opened`/`StreamKind` (1 → 5);
  - `Reassembly` (2 → 3);
  - `StreamEvent`/`RecvStream`/`RecvState`/`SpecRecvIn` (3 → 5, 6);
  - `SendStream`/`Chunk`/`SendState` (4 → 5, 6);
  - `pending_*`/`commit_*`/`*_lost` triples throughout.
  - 3b names (`Frame` fields, `frame_wf`, `spec_frame_bytes`, `frame_type_of`, `varint_len`, `TransportParams` fields) are copied from its Interfaces blocks.
- **Arithmetic re-checked:**
  - the half-window vectors (`49 → None`, `51 → 151`; `cap 6`; MAX_STREAMS `3 closes → 7`, `2 closes of 3 → 5`; `6 of 10 → 16`);
  - the STREAM encodings (`0a 00 11`, `0e 00 11 10`, and 65 bytes at budget 70).
- **Row accounting.** 3 + 1 + 0 + 1 + 6 + 8 = 19, matching the outline's list, and §19.14 is untouched.
- **Proportion.** Bodies appear only for the receive step's check order and the STREAM fit rule. Everything else is signatures, specs, vectors and citations.

## Binding obligations from the Phase 2b final review (2026-10-28)
- Advertise bounded `initial_max_streams_bidi`/`_uni`, and re-credit a stream only after `H3Conn` has forgotten it (its FIN or reset was delivered). H3Conn's stream tables are bounded only by this.
  - **Carried:** the R1 ruling in Global Constraints (a stop doesn't suppress events), with E3/E5 and Task 3's `rfc_recv_step`/`stop_keeps_events`.
  - Task 5: `Streams::new` requires `≤ MAX_LOCAL_STREAMS` (R3), and the ensures carry E5 and the live-entry bound.
  - Task 6: `app_reset_and_stop` and the binding note.
- Call `H3Conn::start()` before delivering any stream data, so SETTINGS goes first (RFC 9114 §6.2.1, §7.2.4.2).
  - **Carried:** Task 6 binding note, first bullet, and Task 6 Step 3's `streams.rs` "Caller obligations" module doc. The obligation is 3d's to execute.
- Encode `initial_max_streams_uni >= 3` (`h3::limits::MIN_PEER_UNI_STREAMS`). This closes the open tail on row 6.2.
  - **Carried:** Task 5, through `Streams::new`'s requires, the Step 3 citation and the Step 6 tail update. 3d's `local_tp_ok` encodes the value and closes the row.
- When a peer reset ends a request whose response already went out (`send_open == false`), H3Conn emits nothing. The QUIC adapter must tell the application that the request was aborted.
  - **Carried:** Task 6 binding note ("Abort signal"), and Task 6 Step 3's `streams.rs` "Caller obligations" module doc. The obligation is 3d's to execute.
