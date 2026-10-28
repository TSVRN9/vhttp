# Phase 3c–3e outlines (to be planned in full later)

Each outline is meant to become a full writing-plans document with the same house style as `2026-10-27-phase-3b-quic-codecs.md`:
- Global Constraints;
- the four checks, with fresh-`CARGO_TARGET_DIR` evidence;
- Duvet citations;
- per-task `✅ 3x: <file>` matrix commits;
- a Review Focus section.

Every one of them consumes the 3b codecs and adds none of its own.

**Row accounting.** These are the 139 RFC 9000 rows whose Phase is 3. Each one is owned by exactly one plan: 3b 27, 3c 19, 3d 88, 3e 5. RFC 9001 and RFC 9002 have no Phase-3 rows.
- How it was checked: `python3 -I <scratch>/chk3b/rows.py <scratch>/p3rows.txt` printed `139 27 19 88 5`, and asserted that every row appears exactly once.
- Rows are named by `§` plus the matrix's own `(req)` label.
- Mixed rows that 3b touches carry a `3b codec: … (closed in 3x)` note, and are listed once, under their owner here.

---

## 3c — Streams and flow control (RFC 9000 §2–§4, §7.5, §19.4–§19.14 semantics)

**Goal:** A verified, sans-IO stream layer:
- stream-ID accounting and limits;
- per-stream send and receive state machines;
- connection-level and stream-level flow control;
- per-level CRYPTO reassembly.

It consumes 3b `Frame` values and emits exactly the events `h3::conn` takes: `on_stream_data(id, data, fin)` and `on_stream_reset(id, code)`.

**Spec style:** the same as 2b. Each stream's spec is a total function of the frames received so far. The exec machine is fed arbitrary frame orders and duplicates. After each call, its cumulative events must equal the spec, so retransmission and reordering can't change behaviour.

**Tasks:**
1. **`quic::stream_id`** (§2.1, §3.2, §4.6):
   - the initiator and direction come from `id % 4`;
   - opening stream N implicitly opens every lower peer stream of that type;
   - a peer exceeding our limit is STREAM_LIMIT_ERROR;
   - a MAX_STREAMS that doesn't increase the limit is ignored;
   - local stream IDs are never reused;
   - we advertise at least `h3::limits::MIN_PEER_UNI_STREAMS` (3).
2. **`quic::recv_stream`** (§3.2, §2.2, §4.5):
   - the states Recv, Size Known, Data Recvd, Data Read, Reset Recvd and Reset Read;
   - a reassembly buffer bounded by the advertised stream window;
   - ordered delivery, and the same bytes at the same offset;
   - FINAL_SIZE_ERROR when the final size changes or data lands beyond it.
3. **`quic::send_stream`** (§3.1, §3.3, §3.5, §4.4):
   - the states Ready, Send, Data Sent, Data Recvd, Reset Sent and Reset Recvd;
   - no STREAM or STREAM_DATA_BLOCKED after RESET_STREAM;
   - STOP_SENDING forces RESET_STREAM;
   - flow-control state is kept until the stream is terminal.
4. **`quic::flow`** (§4.1, §4.2, §19.9, §19.10, §19.13):
   - connection and stream credit, with FLOW_CONTROL_ERROR when it is exceeded;
   - we never exceed the peer's limits;
   - a non-increasing MAX_DATA or MAX_STREAM_DATA is ignored;
   - credit is raised without waiting for *_BLOCKED (`// ponytail:` half-window threshold);
   - the final size counts toward connection credit exactly once.
5. **`quic::crypto_stream`** (§7.5, §19.6): one reassembly buffer per encryption level, with no flow control.
   - It accepts out-of-order data up to at least 4096 bytes ahead, and anything beyond is CRYPTO_BUFFER_EXCEEDED.
   - Data that was already consumed is still acknowledged.
6. **`quic::streams`** (§19.4, §19.5, §19.8, §19.11, §11.2): the aggregate dispatcher.
   - STREAM_STATE_ERROR for a send-only stream, a receive-only stream, or a locally initiated stream that has not been created yet;
   - only the application starts RESET_STREAM;
   - plus the application write/reset/stop API.

**Key interfaces** (names fixed now; types refined in the full plan):
- `Streams::new(local: &TransportParams, peer: &TransportParams) -> Streams`.
- `fn on_frame(&mut self, f: &Frame, ev: &mut Vec<StreamEvent>) -> Result<(), u64>`. It is called for frame types 0x04, 0x05, 0x08–0x15 and 0x16/0x17.
- `enum StreamEvent { Data { id: u64, data: Vec<u8>, fin: bool }, Reset { id: u64, code: u64 }, StopSending { id: u64, code: u64 } }`.
- `fn write(&mut self, id: u64, data: &[u8], fin: bool) -> Result<(), ()>`, `fn reset(&mut self, id: u64, code: u64)` and `fn stop_sending(&mut self, id: u64, code: u64)`.
- `fn poll_frames(&mut self, budget: usize, out: &mut Vec<Frame>)`. It emits STREAM, MAX_DATA, MAX_STREAM_DATA, MAX_STREAMS and RESET_STREAM frames that are `frame_wf`, for 3d's packetizer.
- `CryptoStream::on_crypto(&mut self, offset: u64, data: &[u8]) -> Result<(), u64>` and `fn read(&mut self, out: &mut Vec<u8>)`.

**Review Focus seeds:**
- a retransmitted range whose bytes differ;
- a FIN after the final size is known, with a different size;
- duplicate bytes counted twice against flow control;
- a MAX_STREAMS of exactly 2⁶⁰;
- a STOP_SENDING for a stream we never opened.

**Matrix rows it closes (19):** §2.1, §2.2, §3.2, §3.3, §3.5, §4.1, §4.2, §4.4, §4.5, §4.6, §7.5, §11.2, §19.4, §19.5, §19.8, §19.9, §19.10, §19.11, §19.13.

---

## 3d — Connection (RFC 9000 §5, §7–§14 behaviour, §19.15–§19.20 semantics, §21.11)

**Goal:** A verified, sans-IO server `Connection` over **plaintext** packets: header fields, the decoded PN and the parsed frames.
- **Inputs:** decoded packets, datagram lengths, time and random bytes.
- **Outputs:** plaintext packets to protect, plus the next timer deadline.

3d's tests never touch crypto; 3e wraps it. TLS is a stub here: it consumes CRYPTO and produces nothing. Phase 4 replaces it behind `crypto_in`/`crypto_out`.

**Tasks:**
1. **PN spaces and ACKs** (§12.3, §13.1, §13.2.1, §13.2.3, §13.2.5, §13.2.6, §17.2.3):
   - one space each for Initial, Handshake and Application;
   - PNs are monotonic and never reused, and the connection closes silently at 2⁶²−1;
   - duplicates are suppressed after decryption;
   - ACKs are sent only after the whole packet has been processed;
   - Initial and Handshake are ACKed immediately, and `max_ack_delay` applies otherwise;
   - an ACK goes in the same space, and a 1-RTT ACK only in 1-RTT;
   - ECN rows (§13.4.x) are recorded as vacuous unless the shell supplies ECN.
2. **Sent-packet record** (§13.3):
   - it records which frames each PN carried, and offers `on_packet_lost(space, pn)` to requeue them. Phase 6 drives it;
   - RESET_STREAM is resent unchanged, HANDSHAKE_DONE is retransmitted, and outdated frames are accepted.
3. **Connection IDs** (§5.1, §5.1.1, §5.1.2, §19.15, §19.16, §9.5):
   - CIDs come from shell randomness, so they are unlinkable and never reissued;
   - sequence numbers increase by 1, and we stay within the peer's `active_connection_id_limit`;
   - more active peer CIDs than our limit is CONNECTION_ID_LIMIT_ERROR;
   - Retire Prior To handling, plus the RETIRE_CONNECTION_ID rules;
   - a fresh CID for each new peer address.
4. **Handshake CIDs and transport-parameter semantics** (§7, §7.2, §7.3, §7.4.1, §8.1.3):
   - our DCID comes from the first Initial;
   - a later Initial with a different SCID is dropped;
   - we send `original_destination_connection_id` and `initial_source_connection_id`, and check the client's `initial_source_connection_id` (absent or mismatched is TRANSPORT_PARAMETER_ERROR);
   - 0-RTT is always refused and 0-RTT packets are discarded;
   - a token in an Initial never validates, so the address stays unvalidated.
5. **Address validation and datagrams** (§8, §8.1, §14.1, §14.2, §12.2, §5.2, §5.2.2, §5.2.3):
   - the 3× anti-amplification budget is counted over whole datagrams;
   - an Initial in a datagram under 1200 bytes is discarded without closing the connection;
   - datagrams carrying an ack-eliciting Initial are padded to 1200;
   - every coalesced packet in a datagram is processed, with the same DCID throughout;
   - unmatched packets are routed to: new connection, VN, or drop.
6. **Path validation and peer address change** (§8.2.1, §8.2.2, §8.2.3, §9, §9.3, §9.3.2, §9.3.3, §9.4, §19.17):
   - PATH_RESPONSE echoes the challenge, at most once per challenge, on the arrival path, padded to 1200 within the amplification limit;
   - any peer address change is validated, NAT rebinding included;
   - on failure we fall back to the last validated path;
   - a `// ponytail:` reset hook is left for Phase 6's congestion/RTT state.
7. **Idle, close, draining and stateless reset** (§10.1, §10.2.1, §10.2.2, §10.2.3, §10.3, §10.3.1, §10.3.2, §11, §11.1, §19.20, §21.11):
   - the idle timeout is at least 3×PTO;
   - closing-state sends are capped at 3× received bytes, and nothing is sent while draining;
   - 0x1d is replaced by 0x1c before the handshake is confirmed;
   - stateless-reset tokens are random per CID;
   - an incoming reset is detected only for active CIDs. Constant-time comparison is a known gap (spec non-goal);
   - no reset is sent while connection state exists;
   - HANDSHAKE_DONE is sent once the handshake completes, and receiving one is already rejected by 3b.
8. **`Connection` integration:**
   - frame dispatch to 3c `Streams` and to Tasks 1–7;
   - packetization only through `serialize_payload` (§12.5 precondition) and `pn_encode_len`;
   - every send is gated by the amplification budget;
   - the h3 adapter (`StreamEvent` → `H3Conn::on_stream_data`, `Output` → `Streams::write`).

**Key interfaces:**
- `struct PlainPacket { kind: PacketKind, dcid: Vec<u8>, scid: Vec<u8>, token: Vec<u8>, pn: u64, frames: Vec<Frame> }`.
- `Connection::accept(first: &PlainPacket, datagram_len: usize, path: PathId, now: u64, rand: &[u8], local_tp: &TransportParams) -> Option<Connection>`.
- `fn on_datagram(&mut self, path: PathId, datagram_len: usize, packets: Vec<PlainPacket>, now: u64, rand: &[u8])`.
- `fn poll_transmit(&mut self, now: u64) -> Option<OutDatagram { path: PathId, packets: Vec<PlainPacket>, pad_to: usize }>`.
- `fn next_timeout(&self) -> Option<u64>` and `fn on_timeout(&mut self, now: u64)`.
- `fn route(datagram: &[u8], table: &CidTable) -> Route { Existing(ConnId), NewInitial, VersionNegotiation(Vec<u8>), Drop }`.

**Proof obligations:**
- bytes sent ≤ 3 × bytes received until the address is validated;
- no output while draining;
- PNs are strictly increasing in each space;
- active issued CIDs ≤ the peer's limit;
- every sent datagram that carries an ack-eliciting Initial is at least 1200 bytes.

**Binding note for 3e:** `reserved_bits_zero == false` becomes PROTOCOL_VIOLATION only after AEAD succeeds (§17.2, §17.3.1, RFC 9001 §9.5).

**Matrix rows it closes (88):**
- §5.1, plus §5.1 (req) "Same CID not issued twice";
- §5.1.1, plus its 4 (req) rows: "Sequence number increases by 1", "Accept issued CID until retired", "Do not exceed peer's active_connection_id_limit", "CONNECTION_ID_LIMIT_ERROR on excess active CIDs";
- §5.1.2, §5.2, §5.2.2, §5.2.3;
- §7, §7.2, plus 2 (req): "Server sets DCID from first received Initial", "Discard later Initial with different SCID";
- §7.3, plus (req) "Validate/send initial_source_connection_id; …";
- §7.4.1, plus (req) "Server MUST reject 0-RTT if restored values unsupported";
- §8, §8.1, plus 2 (req): "Anti-amplification …", "Count payload bytes …";
- §8.1.3, plus (req) "Server MUST attempt to validate a token in Initial";
- §8.2.1 plus its 4 (req) rows; §8.2.2 plus its 7 (req) rows; §8.2.3;
- §9, plus 2 (req): "Peer violating disable_active_migration …", "Path validation on any peer address change …";
- §9.3, §9.3.2, §9.3.3, §9.4, §9.5, plus (req) "Do not reuse CID when sending to more than one destination address";
- §10.1, §10.2.1, §10.2.2, §10.2.3, §10.3, §10.3.1, §10.3.2, §11, §11.1;
- §12.2, §12.3, §13.1, §13.2.1, §13.2.3, §13.2.5, §13.2.6, §13.3, §13.4.1, §13.4.2.1, §13.4.2.2;
- §14.1, plus 3 (req): "Server expands ack-eliciting Initial datagrams to 1200", "Server discards Initial in datagram < 1200 bytes", "Server limits bytes sent before address validation";
- §14.2;
- §17.2.3, plus (req) "ACK for a 1-RTT packet MUST be in a 1-RTT packet";
- §19.15, plus its 5 remaining (req) rows: "MUST NOT send if peer requires zero-length DCID", "Zero-length-DCID sender receiving NEW_CONNECTION_ID …", "Duplicate frame not a connection error", "Ignore non-increasing Retire Prior To", "Send RETIRE_CONNECTION_ID for sequence below earlier Retire Prior To";
- §19.16, plus its 3 (req) rows;
- §19.17, §19.20, §21.11.

8 tasks is the top of the 5–8 range. If the full plan runs over, split Task 6 (paths, about 22 rows) into its own sub-plan.

---

## 3e — Packet protection, pipelines, shell and harness (RFC 9001 §5 against the 3a crypto specs)

**Goal:**
- Protect and unprotect packets with proofs against `spec_aes128_encrypt`, `spec_gcm_seal` and `spec_gcm_open` (Phase 3a).
- Glue 3b and 3d into receive and send pipelines.
- Ship the unverified `crates/server` shell.
- Meet the design spec's Phase 3 exit: "the `server` shell exchanges Initial packets with a test harness".

`crates/quic` gains `crypto = { path = "../crypto" }` here, and only here.

**Initial secrets stay in Phase 4** (RFC 9001 §5.2 is a Phase-4 row; HKDF-Expand-Label belongs to the key schedule).
- 3e's functions take `PacketKeys { key: [u8; 16], iv: [u8; 12], hp: [u8; 16] }` as inputs.
- The shell's `initial_keys(dcid)` returns RFC 9001 A.1's published client and server keys only when `dcid == 8394c8f03e515708`. For any other DCID it returns `None`, and the packet is dropped.
- `// ponytail: A.1 keys only until Phase 4 derives Initial secrets.`

**Tasks:**
1. **Header protection** (RFC 9001 §5.4.1–§5.4.3):
   - `hp_mask(hp: &[u8], sample: &[u8]) -> [u8; 5]` ensures it is the first 5 bytes of `spec_aes128_encrypt(hp, sample)`;
   - `remove_hp` / `apply_hp` take the sample at `pn_offset + 4`;
   - a packet too short for a sample is dropped (§5.4.2);
   - tests: A.2's sample `d1b1c98d…` gives mask `437b9aec36`, and A.3's sample `2cd0991c…` gives mask `2ec0d8356a`.
2. **AEAD packet protection** (RFC 9001 §5.3):
   - the nonce is `iv XOR pn`, left-padded;
   - the AAD is the unprotected header;
   - `seal_packet` / `open_packet` are proven against the GCM specs;
   - tests: the A.2 client Initial (1200 bytes) and the A.3 server Initial both reproduce byte-for-byte from their 3b-built headers and payloads.
3. **Receive pipeline:**
   1. the datagram goes to `version_negotiation`, then `route`;
   2. coalesced packets are split on `packet_end`;
   3. header protection is removed;
   4. `first_byte_pn_len`, `read_pn` and `decode_pn`;
   5. `open_packet`;
   6. `reserved_bits_zero`, where false is PROTOCOL_VIOLATION;
   7. `parse_payload`;
   8. 3d's `PlainPacket`.

   0-RTT packets and packets that fail to decrypt are dropped silently.
4. **Send pipeline:** 3d's `OutDatagram` goes to `pn_encode_len`, then the header and payload serializers, then `seal_packet`, then `apply_hp`, and the packets are coalesced. Padding goes to `pad_to` (PADDING frames inside the last packet).
5. **`crates/server` shell** (unverified, TRUSTED.md rows):
   - a blocking `std::net::UdpSocket` loop, `Instant` for the clock, and getrandom;
   - `version_negotiation` is called exactly once per datagram (§17.2.1);
   - DF is set (`IP_MTU_DISCOVER=IP_PMTUDISC_DO` / `IPV6_DONTFRAG`) (§14);
   - the IPv6 flow label is left at the kernel default (§9.7);
   - no ICMP is processed, so §14.2.1 is vacuous.
6. **Harness** `crates/server/tests/initial_exchange.rs`, over loopback:
   - **A.2's protected Initial:** exactly one reply datagram of at most 3600 bytes (3× the 1200 received). Decrypted with the A.1 *server* keys, it is a server Initial whose ACK acknowledges PN 2.
   - **A valid Initial in a 1199-byte datagram:** no reply, and no connection state. Build it with 3e's own `protect` and the A.1 *client* keys: the A.2 CRYPTO frame padded so that Length fits a 1199-byte datagram. Truncating A.2's packet won't do, because Length = 1182 would exceed the remaining bytes and `rfc_long_header` would drop it before §14.1 is ever reached.
   - **Version `0x1a2a3a4a`:** one VN listing `00000001`.

**Key interfaces:**
- `fn unprotect(datagram: &[u8], off: usize, keys: &PacketKeys, largest: Option<u64>, dcid_len: usize) -> Result<Option<(PlainPacket, usize)>, u64>`, where `Ok(None)` means drop.
- `fn protect(p: &PlainPacket, keys: &PacketKeys, largest_acked: Option<u64>, out: &mut Vec<u8>)`.

**Matrix rows it closes (5):** §9.7, §14, §14.2.1, §17.2, §17.3.1.

**Touches, Phase 4 rows:** RFC 9001 §5.3, §5.4.1, §5.4.2 and §5.5. Decide when planning whether to re-tag §5.4.1 and §5.4.2 as Phase 3, since the code lands here.

**Also required (no repo edit by this outline):** the Phase 3a plan says "Phase 3b" in three places where it means packet protection: the Goal paragraph, "no Expand-Label, which is Phase 3b/4", and "Phase 3b can `use crypto::{…}`". All three should read 3e.
