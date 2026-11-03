# Phase 3e: Packet Protection, Pipelines, Shell and Harness — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Put QUIC packets on the wire:
- RFC 9001 §5 header protection and AEAD packet protection, proven against `spec_aes128_encrypt`, `spec_gcm_seal` and `spec_gcm_open`, which since 5b are met by verified code (no shim);
- packet- and datagram-level `protect`/`unprotect`, with the theorem that `unprotect` inverts `protect`;
- verified glue (`pipeline`) between those and 3d2's `Connection`;
- the unverified `crates/server` shell;
- a loopback harness that meets the design spec's Phase 3 exit: "the `server` shell exchanges Initial packets with a test harness".

**Architecture:**
- **Four verified modules in `crates/quic`:**
  - `hp`: RFC 9001 Figure 6 over a 5-byte AES-ECB mask (§5.4.1, §5.4.3);
  - `aead`: the §5.3 nonce and AAD over AES-128-GCM;
  - `protect`: `protect`/`protect_datagram`, `unprotect`/`open_datagram`, and `theorem_unprotect_protect`;
  - `pipeline`: `accept_datagram`, `receive` and `transmit`, which compose the above with `Connection` inside verified code (Decision 3), plus the RFC 9001 §5.7 gate (no 1-RTT decryption before the handshake completes).
- **The trust boundary.** The shell calls only `quic` functions whose `requires` is at most the receiver's `wf()` (`Connection`, `CidTable`). Verus never checks a `requires` at an unverified call site; `wf()` is an invariant every constructor (`accept_datagram`, `CidTable::new`) and every pub method ensures, over private fields, so the shell cannot break it. Every other obligation (3d2 P7 ⇒ `protect`'s precondition, `plain_wf` for `on_datagram`, `code <= VARINT_MAX` for `close`) is discharged by Verus inside `pipeline`. TRUSTED.md states this (Task 6).
- **The keys are inputs.** `PacketKeys { key, iv, hp }` is passed per space as `[Option<KeyPair>; 3]`, indexed by 3d2's `space_idx` (Initial 0, Handshake 1, OneRtt 2). Phase 4 derives keys; until then the shell's `initial_keys(dcid)` returns RFC 9001 A.1's keys for DCID `8394c8f03e515708` only (outline §3e: Initial secrets stay in Phase 4).
  - `// ponytail: A.1 keys only until Phase 4 derives Initial secrets (RFC 9001 §5.2).`
- **The shell is a socket-free `Server` plus a thin `run` loop** (Decision 17), so the 3d2 ordering bindings are unit-tested without sockets.

**Tech Stack:** Verus 0.2026.10.04.426d8b0 (rustc 1.98.1, `rust-toolchain.toml`), vstd `=0.0.0-2026-10-04-0306`, vest_lib `=0.2.2`, duvet 0.4.3. `crypto` is verified (5a–5e); verify.sh's escape count on `main` is 0. The shell alone adds `libc =0.2.191`, already in `Cargo.lock` through test-only dependencies; it becomes a normal dependency of `server` only.

**Spec:** `docs/superpowers/specs/2026-10-27-verified-http3-design.md`:
- Phase 3: its exit, and "upper layers prove against the specs from day one";
- "Sans-IO core": a thin, unverified shell with a blocking `std::net::UdpSocket` loop, clock, getrandom and timers;
- "Trusted base": the shell, the clock and getrandom;
- the anti-goal: no "proven" claim for anything that isn't.

Also read (their Interfaces blocks and binding notes are this plan's contract):
- `2026-10-28-phase-3-outlines.md` §3e (the starting point; its `protect`/`unprotect` signatures are stale);
- `2026-10-29-phase-3d-quic-connection.md`: Task 6 (`datagram.rs`: `PlainPacket`, `OutPacket` with `spin`, `OutDatagram`, `PathId`, `out_packet_len`, `out_packet_sized`, `out_packet_wf`), Task 6/8 routing (`route.rs`: `Route`, `CidTable`, `CidUpdate`, `ConnId`, `MAX_CONNS`), Task 8 (`path.rs`, `MAX_PATHS`), "Binding notes → 3e";
- `2026-10-29-phase-3d2-quic-connection-integration.md`: Tasks 1a-i–3 (`Connection`), E9, and "Binding notes for later phases" (every 3e and Phase 4 item; mapped in the preflight table `<scratch>/vt-3e-evidence/preflight.md`);
- `2026-10-27-phase-3b-quic-codecs.md` (header, pn, payload);
- `2026-11-03-phase-7a-binary-ct-gate.md` and `docs/crypto-binary-audit.md` "Gate" (the dependents' tripwire Tasks 1 and 2 trip).

`<scratch>` is `/home/tavern/Projects/rust/web-server/.worktrees` (git-excluded; the 3d2 recovery note).

## Global Constraints

- **3d's and 3d2's Global Constraints apply unchanged** (`2026-10-29-phase-3d-quic-connection.md` "Global Constraints"; 3d2's "Proof structure" applies to the one `conn.rs` edit in Task 5):
  - Duvet citations: `//= https://www.rfc-editor.org/rfc/rfc9001#section-X` or `…/rfc9000#…` plus a contiguous `//#` quote copied verbatim from `.duvet/specifications/www.rfc-editor.org/rfc/`; vacuous MUSTs use the `type=exception` / `reason=` form;
  - every function verifies at `--rlimit 4` (`#[verifier::spinoff_prover]` where needed, split lemmas, never raise the rlimit); no `let … else` in proof fns; loops restate every fact they need;
  - sans-IO in `quic`, no async, trait objects or closures in verified exec code; no panics; no allocation sized by an untrusted length before it is checked (every 3e allocation is bounded by the received datagram, itself `<= MAX_UDP_PAYLOAD`, or by `out_packet_len < 16384 + 63`);
  - glob-only imports of spec items (`use crypto::gcm::*;`, `#[allow(unused_imports)]` where spec-only); `Spec*` twins with a `View` for every new pub struct with array or `Vec` fields;
  - each task extends the TRUSTED.md row "Derived `Debug`/`PartialEq`/`Eq` on `quic::…`" with its new types (and its `Clone`/`Copy` clause where derived);
  - matrix bookkeeping `✅ 3e: <file>`; a row's earlier touched note is *replaced*, not appended to.
- **The four checks, every task** (3d's list): `scripts/verify.sh` ends `verify.sh: all crates verified, duvet ok, ct ok (10 declassify), cost 19/36, escapes accounted (0), binary ok (<n> fns)` (n is 49 on `main`; Tasks 1–2 change only the `U` block, not n); `cargo build && cargo test` with 0 warnings; the escape grep contributes 0 lines from `crates/quic` **and `crates/server`** (line grep and `grep -Pz`; in the shell not even in comments, and the grep also matches the bare word `axiom`); `duvet report` exits 0.
- **Evidence, every task** (the 3d2 final recipe, `<scratch>/vt-3d2-final-evidence/checks.sh`): with `CARGO_TARGET_DIR=<scratch>/vt-3e-tN/target` and `CT_TARGET_DIR=$CARGO_TARGET_DIR/ct`, run build, test, `verify.sh`, `duvet report`; then, on that warm target (a fresh target at rlimit 4 fails inside vstd), `cargo clean -p quic` plus `rm -rf $CARGO_TARGET_DIR/verus-partial/*/.fingerprint/quic-*` and `(cd crates/quic && cargo verus verify -- --rlimit 4)`, printing quic `… 0 errors`. `crypto`'s code does not change in 3e, so its rlimit-4 result (5e) stands.
- **Quote and MUST checks.** `<scratch>/qchk/check_quotes.py` and `<scratch>/duvet_q.py` did not survive the /tmp wipe. Task 1 rewrites both (stdlib only, run with `python3 -I`): the first checks every `//#` block against the RFC text and prints `N citations, 0 bad`; the second reads `duvet report --json` and prints every uncited, unexcepted MUST of the given sections. Every task with citations runs the first on the files it touched; every task with rows runs the second on its sections.
- **Mutations, every task** (3d rule): each listed mutation, applied alone, fails verification on a named postcondition, invariant or assertion, not on rlimit.
- **Base branch:** `phase-3e` from `main` at 7e95f7f (3a–3d2, 5a–5e, 7a, 8a, 8b merged). Phase 8c runs in parallel in `wt-8c` and also edits `Cargo.toml`/`Cargo.lock` (a `ctmir` crate); the second to merge resolves the lock and the `[profile.release.package.*]` list. `crates/server` gets no profile entry: it keeps overflow checks, being unverified.
- **Dependencies:**
  - Task 1 adds `crypto = { path = "../crypto" }` to `crates/quic/Cargo.toml` (quic → crypto → vstd: acyclic, and crypto's normal deps stay exactly vstd, which verify.sh checks). The only edit to quic's manifest.
  - Task 6 creates `crates/server/Cargo.toml` with `quic = { path = "../quic" }` and `libc = "=0.2.191"`, and **no** `[package.metadata.verus]`. The workspace's `members = ["crates/*"]` picks it up.
- **`scripts/verify.sh` stays unedited** (Decision 8; Task 6 re-probes it). 3d2's note M21 (merge 3e's and 8a's success-line edits) is moot: 8a has landed and 3e does not edit the line.
- **Consumed from crypto** (verbatim from `crates/crypto/src`):
  - `aes::aes128_encrypt_block(key: &[u8], block: &[u8]) -> (r: [u8; 16])`: requires both lengths 16; ensures `r@ == spec_aes128_encrypt(key@, block@)`.
  - `gcm::aes128_gcm_seal(key, nonce, aad, pt) -> (r: Vec<u8>)`: requires `key@.len() == 16`, `nonce@.len() == 12`, `aad@.len() <= MAX_INPUT_LEN`, `pt@.len() <= GCM_MAX_PT_LEN`; ensures `r@ == spec_gcm_seal(..)`.
  - `gcm::aes128_gcm_open(key, nonce, aad, ct) -> (r: Option<Vec<u8>>)`: the same, with `ct@.len() <= GCM_MAX_PT_LEN + 16`; ensures `r.deep_view() == spec_gcm_open(..)`.
  - spec fns `gctr`, `inc32`, `gcm_j0`, `gcm_tag`, **the existing `pub proof fn lemma_gctr_len`** (gcm.rs:504), and `bytes::{xor_bytes, i2osp, lemma_i2osp_len, MAX_INPUT_LEN}`.
  - Pass array fields as `k.key.as_slice()`. `u64::to_be_bytes` is unsupported by this Verus: use `(pn >> (56 - 8·i)) as u8`.
- **Consumed from 3b** (exact names): `parse_header`/`rfc_header` (requires `1 <= dcid_len <= MAX_CID_LEN`), `parse_long_header`/`rfc_long_header`, `Header`/`SpecHeader`, `LongType`; `serialize_long_header` (its `payload_len` counts the tag) / `spec_long_header_bytes`, `serialize_short_header(dcid, key_phase, spin, pn, pn_len, out)` / `spec_short_header_bytes`, `theorem_long_header_roundtrip`, `theorem_short_header_roundtrip` (requires `1 <= |dcid|`), `first_byte_pn_len`/`spec_pn_len`, `reserved_bits_zero`/`spec_reserved_bits_zero`; `put_pn`/`pn_be`, `read_pn`/`be_val`, `lemma_be_val_bound`, `decode_pn` (requires `largest < PN_MAX`)/`rfc_decode_pn`, `expected_pn`, `theorem_decode_pn_recovers`; `serialize_payload`, `parse_payload` (ensures `frames_received` and errors in {FRAME_ENCODING_ERROR, PROTOCOL_VIOLATION}), `rfc_payload`, `spec_frames_bytes`, `non_padding`, `frames_sendable`, `frames_view`, `theorem_payload_roundtrip`, `theorem_payload_padded` (frames then n zero bytes), `theorem_payload_error_codes`, `ack_eliciting`, `PacketKind`; `codes::{MAX_CID_LEN, MIN_SHORT_PACKET, MIN_INITIAL_DATAGRAM, PN_MAX, PROTOCOL_VIOLATION, RESET_TOKEN_LEN}`, `VARINT_MAX`.
- **Consumed from 3d/3d2** (exact names):
  - `datagram::{PlainPacket, SpecPlain, plain_wf, OutPacket, SpecOutPacket, OutDatagram, SpecOutDatagram, PathId, plaintext_len, length_field, out_packet_len, out_datagram_len, out_packet_sized, out_packet_wf, AEAD_TAG_LEN, MAX_DATAGRAM, MIN_PN_AND_PAYLOAD}`;
  - `cid::LOCAL_CID_LEN`; `route::{route, Route, CidTable, CidUpdate, ConnId, MAX_CONNS}`; `tp::{TransportParams, default_transport_params}`; `lifecycle::Phase`;
  - `conn::{RAND_LEN, space_idx, transmit_ok, has_eliciting_initial, later}` and `Connection::{accept, on_datagram, poll_transmit, next_timeout, on_timeout, on_reset_candidate, poll_cid_updates, close, largest_pn, handshake_complete, is_closed, phase, path_state, now, on_peer_params, on_handshake_complete}` and the closed specs `out_log`, `timers_later`, `acks_later`, `keeps_later`, `lemma_keeps_elim`, `live`, `recv`, `phase_spec`.
  - What `poll_transmit` gives (3d2 binding note, preflight I6): `out_log()` pushed with exactly the returned datagram (unchanged on None); `transmit_ok` (P16 `out_datagram_len <= MAX_DATAGRAM`, P7 `out_packet_wf(p, c.sent(kind).largest_acked_spec())` per packet, P4, P5, P9); P2 `initial_padded`; `timers_later(now)` kept; `r is None ==> acks_later(now)`. The draft's Decision 14 fallbacks for these and for 3b's header-byte specs are therefore not needed.
- **One new constant:** `aead::MAX_UDP_PAYLOAD: usize = 65535`, the shell's receive-buffer size and the bound below which datagrams are opened.
- **Shell rules:**
  - `now` is µs since a start `Instant`, read once per event and passed to every call that event makes;
  - a fresh `[u8; RAND_LEN]` (`RAND_LEN` 129) from `libc::getrandom` for each `accept_datagram`, `receive` and `on_timeout` call;
  - `version_negotiation` is reached only through `route`, once per datagram (§17.2.1, 3d binding);
  - the 3d2 order binding (I1): after `Route::NewInitial`, `accept_datagram`, then apply every `poll_cid_updates` update to the `CidTable`, in order, before the next datagram is routed; the same after every `receive`, `on_reset_candidate` and `on_timeout`; `remove_conn` when a connection is dropped.
- **Vector tests run the verified code.** They check our specs and code against RFC 9001 Appendix A; the proofs tie the code to the specs.
- **Shared test data:** `crates/quic/tests/common/mod.rs`, loaded with `mod common;`:
  - `hex(&str) -> Vec<u8>`; the A.1 keys `CLIENT`, `SERVER` (`PacketKeys`, consts);
  - `A2` (1200 bytes) and `A3` (135 bytes), the protected packets copied from rfc9001.txt §A.2 and §A.3;
  - `A2_CRYPTO` (the 241 CRYPTO data bytes after `060040f1`) and `A3_PAYLOAD` (99 bytes);
  - `build(header, pn_offset, pn, pt, k)` = `header ++ seal_packet(k, pn, header, pt)`, then `apply_hp(_, 0, pn_offset, &k.hp)` (Task 2);
  - from 3d2's `tests/conn_rx.rs`: `rnd(n)`, `S1`, `C1`, `L0`, `ltp()`, `ptp()`.

  A.1 keys: client key `1f369613dd76d5467730efcbe3b1a22d`, iv `fa044b2f42a3fd3b46fb255c`, hp `9f50449e04a0e810283a1e9933adedd2`; server key `cf3a5331653c364c88f0f379b6067e37`, iv `0ac1493ca1905853b0bba03e`, hp `c206b8d9b9f0f37644430b490eeaa314`. `crates/server/tests/` carries its own copies (test crates of different packages share no modules).
- **Literal `OutPacket`s** are written `OutPacket{kind, dcid, scid, pn, pn_len, frames, padding, spin}`; every vector below has `spin: false` unless it says otherwise.

## Matrix rows this plan closes (7)

- **RFC 9000 (the outline's 5):** §9.7, §14, §14.2.1 (Task 6); §17.2, §17.3.1 (Task 5). They are the only RFC 9000 Phase-3 rows without `✅` on `main`. After Task 6, `awk '/^## RFC 9000/,/^## RFC 9001/' docs/requirements.md | awk -F'|' 'NF>6 && $6 ~ /^ *3 *$/ && $0 !~ /✅/'` prints nothing (it prints exactly those 5 on `main`; the draft's `rows.py` is gone).
- **RFC 9001, retagged Phase 4 → 3 (Decision 7):** §5.4.1 (Task 1), §5.4.2 (Task 4). Task 1 amends the outline's "RFC 9001 and RFC 9002 have no Phase-3 rows" and extends the Legend's Phase 3 row.
- **Touched, not closed (Phase 4 keeps them):** §5.3 (Task 2); §5.5, §4.6.2, §9.5 (Task 4); §5.7 (Task 5).

## Review Focus

1. **A reserved bit flipped on the wire** is covered by the AAD, so AEAD fails and the packet is dropped silently, never PROTOCOL_VIOLATION, which comes only after both protections are removed (§17.2). Task 4: `reserved_flip_on_wire_drops`.
2. **A coalesced datagram with an unkeyed Handshake packet between two Initials:** the Handshake packet is skipped by its Length and the second Initial still processed. Task 4: `coalesced_skip_unkeyed`.
3. **A connection error before Handshake keys exist:** 3d's closing state builds CONNECTION_CLOSE in Initial and Handshake; only the Initial one can be protected, and it goes out within 3× the bytes received. Task 5: `first_packet_error_closes`.
4. **A browser-sized client Initial** (1350 bytes, padded inside the packet) is accepted and acknowledged like A.2. Task 5: `accept_1350`.
5. **A 1-RTT packet before the handshake completes is never decrypted** (RFC 9001 §5.7), even with 1-RTT keys supplied, which `Connection`'s own gate cannot show. Task 5: `one_rtt_gated_until_complete` (a reserved-bit 1-RTT packet closes the connection only after completion).
6. **Spoofed garbage from new addresses takes no shell path slot** (3d2 E9 carried into the shell's address table). Task 6: `spoofed_addresses_take_no_slot`.
7. **A past deadline cannot spin the loop:** the shell's wake sequence is proved settled (`pipeline::settled_later`), polls are capped, and the read timeout has a 1 ms floor (`set_read_timeout(Some(Duration::ZERO))` is an error). Tasks 5–6: `timeout_settles`, `read_timeout_floor`.

---

### Task 1: Header protection (`quic::hp`) — suggested model: opus

**Files:**
- Create: `crates/quic/src/hp.rs`, `crates/quic/tests/hp.rs`, `crates/quic/tests/common/mod.rs` (`hex`, keys, `A2`, `A3`, `A2_CRYPTO`, `A3_PAYLOAD`, the 3d2 helpers; Task 2 adds `build`); `<scratch>/qchk/check_quotes.py`, `<scratch>/duvet_q.py` (scratch, not committed)
- Modify:
  - `crates/quic/Cargo.toml` (`crypto = { path = "../crypto" }`), `Cargo.lock`, `crates/quic/src/lib.rs` (module doc line and `pub mod hp;`);
  - `docs/crypto-binary-digests.txt` and `docs/crypto-binary-audit.md` ("Gate records"), per Step 4;
  - `docs/superpowers/plans/2026-10-27-phase-3a-crypto-specs.md`: its three "Phase 3b" mentions that mean packet protection (line 9, line 199 "Phase 3b/4", line 541) become "Phase 3e";
  - `docs/superpowers/plans/2026-10-28-phase-3-outlines.md` line 12: "RFC 9002 has no Phase-3 rows; RFC 9001 §5.4.1–§5.4.2 were retagged to Phase 3 by the 3e plan".

**Interfaces:**
- Consumes: `crypto::aes::{spec_aes128_encrypt, aes128_encrypt_block}`.
- Produces (`quic::hp`). Specs, literal from RFC 9001:
  - **`pub open spec fn rfc_sample(pkt: Seq<u8>, pn_offset: nat) -> Seq<u8>`** = `pkt.subrange(pn_offset + 4, pn_offset + 20)` (§5.4.2 pseudocode, sample_length 16 per §5.4.3).
  - **`pub open spec fn rfc_hp_mask(hp: Seq<u8>, sample: Seq<u8>) -> Seq<u8>`** = `spec_aes128_encrypt(hp, sample).take(5)` (§5.4.3 `AES-ECB(hp_key, sample)`, §5.4.1's 5-byte mask).
  - **`pub open spec fn rfc_hp_apply(pkt: Seq<u8>, pn_offset: nat, mask: Seq<u8>) -> Seq<u8>`**, Figure 6: `pn_length = (pkt[0] & 0x03) + 1` read before masking; byte 0 `^= mask[0] & 0x0f` if `pkt[0] & 0x80 == 0x80`, else `^= mask[0] & 0x1f`; `pkt[pn_offset + i] ^= mask[1 + i]` for `i < pn_length`; every other byte unchanged.
  - **`pub open spec fn rfc_hp_remove(pkt, pn_offset, mask) -> Seq<u8>`**: the same, but `pn_length` is read from byte 0 after it is unmasked (§5.4.1).
- Exec:
  - `pub fn hp_mask(hp: &[u8; 16], sample: &[u8]) -> (m: [u8; 5])`: requires `sample@.len() == 16`; ensures `m@ == rfc_hp_mask(hp@, sample@)`.
  - **`pub fn apply_hp(buf: &mut Vec<u8>, start: usize, pn_offset: usize, hp: &[u8; 16])`**: requires `pn_offset >= 1`, `start + pn_offset + 20 <= old(buf)@.len()`; with `w = old(buf)@.skip(start)`, ensures `final(buf)@ == old(buf)@.take(start) + rfc_hp_apply(w, pn_offset, rfc_hp_mask(hp@, rfc_sample(w, pn_offset)))`. In place at `start`, because `protect` appends to a datagram buffer.
  - **`pub fn remove_hp(pkt: &[u8], pn_offset: usize, hp: &[u8; 16]) -> (u: Vec<u8>)`**: requires `pn_offset >= 1`, `pn_offset + 20 <= pkt@.len()`; ensures `u@ == rfc_hp_remove(pkt@, pn_offset, rfc_hp_mask(hp@, rfc_sample(pkt@, pn_offset)))`. A copy, at most `MAX_UDP_PAYLOAD` bytes in its callers.
- Lemmas (for Task 4), each requiring `pn_offset >= 1`, `pn_offset + 4 <= pkt.len()`, `mask.len() == 5`:
  - **`lemma_hp_roundtrip`:** `rfc_hp_remove(rfc_hp_apply(pkt, o, m), o, m) == pkt` (`by (bit_vector)` for `(b ^ (m & 0x0f)) & 0x03` and the involution).
  - **`lemma_hp_frame`:** `rfc_hp_apply` keeps the length, keeps `pkt[0] & 0xf0` (long) or `pkt[0] & 0xe0` (short), and keeps every byte outside `{0} ∪ [o, o + 4)`, so it keeps `rfc_sample(_, o)` and every byte `rfc_header` reads.

- [ ] **Step 1: Failing tests** in `tests/hp.rs`:
  - **`a2_mask`:** `hp_mask(CLIENT.hp, d1b1c98dd7689fb8ec11d242b123dc9b) == 437b9aec36`.
  - **`a3_mask`:** `hp_mask(SERVER.hp, 2cd0991cd25b0aac406a5816b6394100) == 2ec0d8356a`.
  - **`a2_apply`:** from `c300000001088394c8f03e5157080000449e00000002 ++ A2[22..38]`, `apply_hp(_, 0, 18, &CLIENT.hp)` makes the first 22 bytes `c000000001088394c8f03e5157080000449e7b9aec34` and leaves the last 16; `remove_hp` of the result gives the input back.
  - **`a3_apply`:** from `c1000000010008f067a5502a4262b50040750001 ++ A3[20..38]`, `apply_hp(_, 0, 18, &SERVER.hp)` makes the first 20 bytes `cf000000010008f067a5502a4262b5004075c0d9`.
  - **`apply_at_offset`:** `[0xee; 7] ++ <a3_apply input>` with `start = 7` leaves bytes 0..7 and gives `a3_apply`'s result at 7..27.
  - **`short_header_bits`:** `[0x41] ++ [0x11; 8] ++ [0xa0, 0xa1] ++ [0; 2] ++ <A.2 sample> ++ [0; 3]`, `pn_offset = 9`: byte 0 becomes `0x42` (`0x41 ^ (0x43 & 0x1f)`), bytes 9..11 `0xdb 0x3b`, byte 11 and bytes 13.. unchanged (pn_len 2).
- [ ] **Step 2:** `cargo test -p quic --test hp` fails to compile.
- [ ] **Step 3: Implement.** Duvet-cite RFC 9001 §5.4.1 "a header protection algorithm MUST be specified for the AEAD used with that cipher suite" at `rfc_hp_mask` (AES-128 HP, §5.4.3, for our only AEAD); the Figure 6 lines at `rfc_hp_apply`/`rfc_hp_remove`; the §5.4.2 pseudocode at `rfc_sample`. Doc comment: `hp_mask`/`apply_hp` have no secret-dependent branch over key or mask, but branch on the unmasked pn length (RFC 9001 §9.5, known gap; Task 4 notes it). Write the two scratch scripts. Make the two plan-doc edits.
- [ ] **Step 4: Binary gate (7a dependents' tripwire).** quic's rlib now references `crypto::aes::aes128_encrypt_block`, so `scripts/ct-binary.sh` fails with one added `U quic crypto::aes::aes128_encrypt_block` line and no digest change. Per the audit's update protocol step 2: confirm the line is `U` (a call) and that no `D quic crypto::…` line exists (nothing inlined); no crypto symbol changed, so no symbol read is due. Record it in "Gate records" (date, "this commit on base 7e95f7f", toolchain, "dependent added: quic, 1 `U` line, no `D` line, digests unchanged"), then `scripts/ct-binary.sh --update`. The digests file and the record ride in Step 6's feat commit, never before it: a tracked `U` line with no code behind it fails verify.sh at that commit. Any digest change or `D` line instead is a stop: report it.
- [ ] **Step 5:** The four checks, plus `scripts/ct-check.sh` passing with quic now depending on crypto (the parsers' selftest and cost runs build quic, and so crypto, under the driver), plus the rlimit-4 run of quic. If ct-check fails while building crypto under the driver, stop and report; do not patch `tools/ct-driver` (Phase 8c is editing it in parallel). **Mutations:** `& 0x0f` → `& 0x1f` in the long branch of `apply_hp`; read `pn_length` after masking in `apply_hp`.
- [ ] **Step 6: Commit:** `feat(quic): verified RFC 9001 header protection over the AES spec (§5.4.1, §5.4.3); crypto dependency`
- [ ] **Step 7: Matrix commit.** RFC 9001 §5.4.1: Phase 4 → 3, `✅ 3e: crates/quic/src/hp.rs (AES-128 HP per §5.4.3, the HP of our only AEAD)`. Legend Phase 3 row: append `; RFC 9001 §5.4.1–§5.4.2 header protection (3e)`. Commit: `docs: retag RFC 9001 §5.4.1 to Phase 3 and close it in 3e` (§5.4.2 is retagged when it closes, Task 4).

---

### Task 2: AEAD packet protection (`quic::aead`) — suggested model: opus

**Files:**
- Create: `crates/quic/src/aead.rs`, `crates/quic/tests/aead.rs`
- Modify: `crates/quic/src/lib.rs`, `crates/quic/tests/common/mod.rs` (add `build`), `TRUSTED.md` (derived-impl row: `PacketKeys`, `KeyPair`, with `Clone`/`Copy`), `docs/crypto-binary-digests.txt` and `docs/crypto-binary-audit.md` (Step 4)

**Interfaces:**
- Consumes: `crypto::gcm::*`, `crypto::bytes::*`, `PN_MAX`.
- Produces (`quic::aead`):
  - `pub const MAX_UDP_PAYLOAD: usize = 65535;`
  - **`pub struct PacketKeys { pub key: [u8; 16], pub iv: [u8; 12], pub hp: [u8; 16] }`** and **`pub struct KeyPair { pub rx: PacketKeys, pub tx: PacketKeys }`**, derived `Clone, Copy, Debug, PartialEq, Eq` (Copy so `pipeline` can mask a key slot by value), with spec twins `SpecKeys`, `SpecKeyPair`.
  - **`pub open spec fn rfc_nonce(iv: Seq<u8>, pn: u64) -> Seq<u8>`** = `xor_bytes(iv, i2osp(pn as nat, 12))` (§5.3).
  - `pub fn nonce(iv: &[u8; 12], pn: u64) -> (n: [u8; 12])`: ensures `n@ == rfc_nonce(iv@, pn)`; XORs `iv[4 + i]` with `(pn >> (56 − 8i)) as u8`, equal to `i2osp` by `bit_vector`.
  - **`pub fn seal_packet(k: &PacketKeys, pn: u64, header: &[u8], payload: &[u8]) -> (c: Vec<u8>)`**: requires `header@.len() <= MAX_UDP_PAYLOAD`, `payload@.len() <= MAX_UDP_PAYLOAD`; ensures `c@ == spec_gcm_seal(k.key@, rfc_nonce(k.iv@, pn), header@, payload@)` and `c@.len() == payload@.len() + 16`. `header` is the AAD (§5.3).
  - **`pub fn open_packet(k: &PacketKeys, pn: u64, header: &[u8], ct: &[u8]) -> (r: Option<Vec<u8>>)`**: same requires; ensures `r.deep_view() == spec_gcm_open(k.key@, rfc_nonce(k.iv@, pn), header@, ct@)`.
- Lemmas over the crypto specs (key-length agnostic), using crypto's `lemma_gctr_len`:
  - `lemma_gctr_involution(key, icb, x)`: `gctr(key, icb, gctr(key, icb, x)) == x`, by induction on `x.len()` (`xor_bytes(xor_bytes(a, b), b) == a`);
  - **`lemma_gcm_open_seal(key, nonce, aad, pt)`:** `spec_gcm_open(key, nonce, aad, spec_gcm_seal(key, nonce, aad, pt)) == Some(pt)` and `spec_gcm_seal(..).len() == pt.len() + 16` (`gcm_tag` is 16 bytes through `lemma_gctr_len` and `lemma_i2osp_len`).

- [ ] **Step 1: Failing tests** in `tests/aead.rs`:
  - **`nonce_vectors`:** `nonce(CLIENT.iv, 2) == fa044b2f42a3fd3b46fb255e`; `nonce(SERVER.iv, 1) == 0ac1493ca1905853b0bba03f`; `nonce([0; 12], PN_MAX) == 000000003fffffffffffffff`.
  - **`a3_seal`:** `seal_packet(&SERVER, 1, c1000000010008f067a5502a4262b50040750001, A3_PAYLOAD) == A3[20..135]` (HP changes only byte 0 and the packet-number bytes, all inside the 20-byte header, so the ciphertext appears verbatim in A.3).
  - **`a2_seal`:** `seal_packet(&CLIENT, 2, c300000001088394c8f03e5157080000449e00000002, A2_CRYPTO frame ++ [0; 917]) == A2[22..1200]`.
  - **`a3_open`:** `open_packet(&SERVER, 1, <A.3 header>, A3[20..135]) == Some(A3_PAYLOAD)`; last byte XOR 1 → `None`; pn 2 → `None`; header byte 0 `0xc3` → `None`.
- [ ] **Step 2:** The tests fail.
- [ ] **Step 3: Implement.** Duvet-cite the §5.3 nonce paragraph at `rfc_nonce`, the AAD paragraph at `seal_packet`, and "the AEAD function is applied prior to applying header protection" at `seal_packet`'s doc comment.
- [ ] **Step 4: Binary gate.** Two more `U quic crypto::gcm::{aes128_gcm_open, aes128_gcm_seal}` lines; same procedure and stop conditions as Task 1 Step 4, and the digests file and record ride in Step 6's feat commit.
- [ ] **Step 5:** The four checks and the rlimit-4 run. **Mutations:** `56 − 8i` → `48 − 8i` in `nonce`; drop the tag-length half of `lemma_gcm_open_seal`'s proof step.
- [ ] **Step 6: Commit:** `feat(quic): verified RFC 9001 §5.3 AEAD packet protection over the GCM spec; open∘seal lemma`
- [ ] **Step 7: Matrix commit.** RFC 9001 §5.3 touched note: `3e: nonce and AAD construction proven in crates/quic/src/aead.rs; the three MUSTs (suite/HP negotiation, unsupported-suite ClientHello, AEAD-limit key update) close in 4`.

---

### Task 3: Send side: `protect` and `protect_datagram` (`quic::protect`) — suggested model: opus

**Files:**
- Create: `crates/quic/src/protect.rs`, `crates/quic/tests/protect.rs`
- Modify: `crates/quic/src/lib.rs`

**Interfaces:**
- Consumes: Tasks 1–2; `out_packet_sized`, `out_packet_wf`, `plaintext_len`, `length_field`, `out_packet_len`, `out_datagram_len`, `AEAD_TAG_LEN`, `MIN_PN_AND_PAYLOAD`; `serialize_long_header`/`spec_long_header_bytes`, `serialize_short_header`/`spec_short_header_bytes`, `serialize_payload`, `spec_frames_bytes`, `ack_eliciting`, `has_eliciting_initial`, `space_idx`.
- Produces:
  - **`pub open spec fn protect_ok(p: SpecOutPacket) -> bool`** (Decision 1) = `out_packet_sized(p) && p.pn_len + plaintext_len(p) >= MIN_PN_AND_PAYLOAD && (p.kind is OneRtt ==> p.scid.len() == 0)`: `out_packet_wf` without the `pn_len_ok` minimality clauses.
  - `pub proof fn lemma_wf_protect_ok(p, la)`: `out_packet_wf(p, la) ==> protect_ok(p)`.
  - **`pub open spec fn spec_header_bytes(p) -> Seq<u8>`**: `spec_long_header_bytes(ty(p.kind), p.dcid, p.scid, p.pn, p.pn_len, plaintext_len(p) + AEAD_TAG_LEN)` for Initial/Handshake; `spec_short_header_bytes(p.dcid, false, p.spin, p.pn, p.pn_len)` for OneRtt (key phase 0 until Phase 4; **`p.spin` is written**, 3d binding).
  - **`pub open spec fn spec_plaintext(p) -> Seq<u8>`** = `spec_frames_bytes(p.frames) + Seq::new(p.padding, |i| 0u8)`.
  - **`pub open spec fn rfc_protect(p: SpecOutPacket, k: SpecKeys) -> Seq<u8>`**, AEAD first, then HP (§5.3, §5.4.1):
    ```
    h = spec_header_bytes(p); o = h.len() - p.pn_len
    w = h + spec_gcm_seal(k.key, rfc_nonce(k.iv, p.pn), h, spec_plaintext(p))
    rfc_hp_apply(w, o, rfc_hp_mask(k.hp, rfc_sample(w, o)))
    ```
  - **`pub fn protect(p: &OutPacket, k: &PacketKeys, out: &mut Vec<u8>)`** (3d binding, minus `largest_acked`): requires `protect_ok(p@)`; ensures `final(out)@ == old(out)@ + rfc_protect(p@, k@)` and `rfc_protect(p@, k@).len() == out_packet_len(p@)`. Body: header into a scratch `Vec`; payload into another, then `padding` zeros; `seal_packet`; append header then ciphertext to `out`; `apply_hp(out, old_len, o, &k.hp)`.
  - **`pub open spec fn rfc_protect_datagram(d: SpecOutDatagram, keys: Seq<Option<SpecKeyPair>>) -> Seq<u8>`** (Decision 4). With `kept` the packets whose `keys[space_idx(kind)]` is `Some`: every packet kept → the concatenation, **in `packets` order**, of `rfc_protect(p, keys[..].tx)`; else `has_eliciting_initial(d.packets)` → empty (skipping a packet would undercut §14.1's 1200); else the concatenation over `kept`, in order.
  - **`pub fn protect_datagram(d: &OutDatagram, keys: &[Option<KeyPair>; 3], out: &mut Vec<u8>)`**: requires `forall p in d.packets: protect_ok(p@)`; ensures `final(out)@ == old(out)@ + rfc_protect_datagram(d@, keys@)`, the written length `<= out_datagram_len(d@)` and `==` when every packet is kept.
  - 3d2's §12.2 note (a 1-RTT packet is always alone) is not needed as a proof fact here: no datagram-level inverse theorem is stated, and order is fixed by the ensures.

- [ ] **Step 1: Failing tests** in `tests/protect.rs`:
  - **`a2_protect`:** `OutPacket{Initial, 8394c8f03e515708, [], 2, 4, [Crypto{0, A2_CRYPTO}], 917}` with `CLIENT` writes exactly `A2` (1200 bytes).
  - **`a3_protect`:** `OutPacket{Initial, [], f067a5502a4262b5, 1, 2, [Ack(AckFrame{0, 0, 0, [], None}), Crypto{0, A3_PAYLOAD[9..]}], 0}` with `SERVER` writes exactly `A3`.
  - **`protect_appends`:** with `out = [0xee; 5]`, `a3_protect` leaves `out[0..5]` and makes `out[5..] == A3`.
  - **`short_len`:** `OutPacket{OneRtt, [0x11; 8], [], 0, 1, [Ping], 2}` writes 29 bytes (3d's `short_sample_padding`), `out[0] & 0xe0 == 0x40`.
  - **`spin_written`:** the same with `spin: true` gives `out[0] & 0xe0 == 0x60` (HP masks only the low 5 bits); `unprotect` (Task 4) is not needed for this.
  - **`datagram_all_keyed`:** `OutDatagram{0, [a3 packet, OutPacket{Handshake, [], [0x5a; 8], 0, 1, [Crypto{0, [7; 30]}], 0}]}` with Initial and Handshake keyed (`SERVER`, then `CLIENT` as a stand-in) writes `A3 ++ <that packet alone>`, length `datagram_len`.
  - **`datagram_skip_unkeyed`:** the same with only Initial keyed writes exactly `A3`.
  - **`datagram_eliciting_initial_unkeyed_peer`:** `[a3 packet, Handshake{.., [Ping], 0}]` with only Initial keyed writes nothing (A.3's Initial carries CRYPTO).
- [ ] **Step 2:** The tests fail.
- [ ] **Step 3: Implement.** Prove the length from 3b's header lengths, `lemma_gcm_open_seal`'s length half and `lemma_hp_frame`. Duvet-cite RFC 9001 §5.4.2 "packets are padded so that the combined lengths … is at least 4 bytes longer than the sample" at `protect_ok`'s `MIN_PN_AND_PAYLOAD` clause, and RFC 9000 §14.1 "MUST expand the payload of all UDP datagrams carrying ack-eliciting Initial packets" at the write-nothing branch (extra citation; 3d closed the row).
- [ ] **Step 4:** The four checks and the rlimit-4 run. **Mutations:** pass `false` for `spin`; drop the `has_eliciting_initial` branch of `protect_datagram` (consistent: spec and exec together must fail `protect_datagram`'s length ensures or its §14.1 test).
- [ ] **Step 5: Commit:** `feat(quic): verified packet and datagram protection, exact out_packet_len (RFC 9001 §5.3-§5.4)`. No matrix commit.

---

### Task 4: Receive side: `unprotect`, `open_datagram` and the inverse theorem — suggested model: opus

**Files:**
- Modify: `crates/quic/src/protect.rs`, `TRUSTED.md` (derived-impl row: `Rx`; the "CT check scope" row gains `quic::hp`, `quic::aead`, `quic::protect`: key, nonce and mask handling outside crypto, not CT-checked, branching on the unmasked pn length)
- Test: `crates/quic/tests/unprotect.rs`

**Interfaces:**
- Consumes: Tasks 1–3; `parse_header`/`rfc_header` with `LOCAL_CID_LEN`; `first_byte_pn_len`, `reserved_bits_zero`, `read_pn`, `decode_pn`/`rfc_decode_pn`, `theorem_decode_pn_recovers`; `parse_payload`/`rfc_payload`, `theorem_payload_padded`, `theorem_payload_error_codes`; `PlainPacket`, `plain_wf`, `MIN_SHORT_PACKET`, `PN_MAX`, `PROTOCOL_VIOLATION`, `RESET_TOKEN_LEN`.
- Produces:
  - **`pub open spec fn rfc_unprotect(b: Seq<u8>, keys: Seq<Option<SpecKeyPair>>, largest: Seq<Option<u64>>) -> Result<(Option<SpecPlain>, nat), (u64, SpecPlain)>`.** `b` starts at a packet; the `nat` is the bytes consumed, also on a drop, so the next coalesced packet is still reached (Decision 2). First rule that applies:
    ```
    b.len() > MAX_UDP_PAYLOAD                                  => Ok((None, b.len()))
    rfc_header(b, LOCAL_CID_LEN) is None or UnsupportedVersion => Ok((None, b.len()))   // rest unparseable
    Long{ty: ZeroRtt, packet_end, ..}                           => Ok((None, packet_end)) // RFC 9001 §4.6.2
    let (kind, o, end) = Long: (Initial|Handshake, pn_offset, packet_end) | Short: (OneRtt, pn_offset, b.len())
    keys[space_idx(kind)] is None                               => Ok((None, end))
    end < o + 20                                                => Ok((None, end))       // RFC 9001 §5.4.2
    largest[space_idx(kind)] == Some(PN_MAX)                   => Ok((None, end))       // decode_pn's domain
    let k = keys[..].rx; pkt = b.take(end)
    let u = rfc_hp_remove(pkt, o, rfc_hp_mask(k.hp, rfc_sample(pkt, o)))
    let n = spec_pn_len(u[0]); pn = rfc_decode_pn(largest[..], be_val(u.subrange(o, o + n)), 8n)
    match spec_gcm_open(k.key, rfc_nonce(k.iv, pn), u.take(o + n), u.subrange(o + n, end)):
      None                                                     => Ok((None, end))       // RFC 9001 §5.5
      Some(pt):
        let hdr = SpecPlain{kind, dcid, scid, token, pn, frames: []}
        !spec_reserved_bits_zero(u[0], kind != OneRtt)         => Err((PROTOCOL_VIOLATION, hdr))  // §17.2, §17.3.1
        rfc_payload(pt, kind) is Err(c)                        => Err((c, hdr))
        Ok(fs)                                                 => Ok((Some(hdr with frames fs), end))
    ```
  - **`pub fn unprotect(b: &[u8], keys: &[Option<KeyPair>; 3], largest: &[Option<u64>; 3]) -> (r: Result<(Option<PlainPacket>, usize), (u64, PlainPacket)>)`:** no `requires`; ensures `r.deep_view() == rfc_unprotect(b@, keys@, largest@)`; `b.len() > 0 && r is Ok((_, n)) ==> 0 < n <= b.len()`; `Ok((Some(p), _)) ==> plain_wf(p@)`; `Err((c, h)) ==> c <= VARINT_MAX && plain_wf(h@)` (`theorem_payload_error_codes`; `Connection::accept` and `close` require these); `Ok((Some(p), n)) && p.kind is OneRtt ==> n == b.len()`.
  - **`pub struct Rx { pub packets: Vec<PlainPacket>, pub error: Option<(u64, PlainPacket)>, pub reset_tail: Option<[u8; 16]> }`** + `SpecRx`.
  - **`pub open spec fn rfc_open_datagram(d, keys, largest) -> SpecRx`**: `rfc_unprotect` from offset 0, advancing by the consumed count; collects each `Some` packet in order; stops at the first `Err` (into `error`); `reset_tail = Some(d.take_last(16))` iff the **first** call returned `Ok((None, _))` and `d.len() >= MIN_SHORT_PACKET` (RFC 9000 §10.3.1, Decision 6).
  - **`pub fn open_datagram(d: &[u8], keys: &[Option<KeyPair>; 3], largest: &[Option<u64>; 3]) -> (r: Rx)`**: no `requires`; ensures `r@ == rfc_open_datagram(d@, keys@, largest@)`, `forall i: plain_wf(r.packets[i]@)`, the `error` facts above, and **at most one 1-RTT packet, last** (`r.packets[i].kind is OneRtt ==> i == r.packets.len() - 1`; 3d2 binding: a short header runs to the end of the datagram). `vstd::slice::slice_subrange` for the tail.
    - `// ponytail: one largest per space for the whole datagram; coalesced same-space packets decode against it.`
  - **`pub proof fn theorem_unprotect_protect(p: SpecOutPacket, k: SpecKeyPair, keys, largest, rest: Seq<u8>)`:** requires `protect_ok(p)`; `keys[space_idx(p.kind)] == Some(k)` (the packet was protected with `k.rx`); no frame of `p` is `HandshakeDone`; OneRtt ⇒ `p.dcid.len() == LOCAL_CID_LEN && rest == []`; `largest[space_idx(p.kind)]` is `None` or `< PN_MAX`, and `p.pn` lies in `theorem_decode_pn_recovers`'s window for `p.pn_len`. Ensures `rfc_unprotect(rfc_protect(p, k.rx) + rest, keys, largest) == Ok((Some(SpecPlain{p.kind, p.dcid, p.scid, [], p.pn, non_padding(p.frames)}), out_packet_len(p)))`. Ingredients: `lemma_hp_frame` (the protected header parses as 3b's round-trip theorems say), `lemma_hp_roundtrip`, `lemma_gcm_open_seal`, `theorem_decode_pn_recovers`, `theorem_payload_padded`.

- [ ] **Step 1: Failing tests** in `tests/unprotect.rs`. `KR = [Some(KeyPair{rx: CLIENT, tx: SERVER}), None, None]` (server view); `KC` the client view (rx `SERVER`).
  - **`a2_unprotect`:** `unprotect(A2, KR, [None; 3]) == Ok((Some(PlainPacket{Initial, 8394c8f03e515708, [], [], 2, [Crypto{0, A2_CRYPTO}]}), 1200))`.
  - **`a3_unprotect_coalesced`:** `unprotect(A3 ++ [0xaa; 30], KC, [None; 3]) == Ok((Some({Initial, [], f067a5502a4262b5, [], 1, [Ack(..{0, 0, 0, [], None}), Crypto{0, ..}]}), 135))`.
  - **`drops`:** each `Ok((None, n))`: `A2` with its last byte XOR 1 (1200); `A2` with `[None; 3]` (1200); `A2` with largest `[Some(PN_MAX), None, None]` (1200); `[0x40] ++ [0x11; 8] ++ [0; 19]` with OneRtt keyed (28 < 9 + 20); `[0x00; 30]` (30).
  - **`reserved_bits_violation`:** `build(cb00000001088394c8f03e5157080000449e00000002, 18, 2, A2_CRYPTO frame ++ [0; 917], CLIENT)` → `Err((0x0a, PlainPacket{Initial, 8394…, [], [], 2, []}))`.
  - **`reserved_flip_on_wire_drops`** (Review Focus 1): `A2` with `A2[0] ^= 0x08` → `Ok((None, 1200))`.
  - **`payload_error`:** `build(<A.2 header>, 18, 2, [0x10, 0x00] ++ [0; 1160], CLIENT)` → `Err((0x0a, _))` (MAX_DATA not permitted in Initial).
  - **`decode_with_largest`:** protect `OutPacket{OneRtt, [0x11; 8], [], 0x1_0000_0002, 1, [Ping], 2}` with `CLIENT`, unprotect with keys `[None, None, Some(KR[0])]` and largest `[None, None, Some(0x1_0000_0001)]` → pn `0x1_0000_0002`.
  - **`coalesced_skip_unkeyed`** (Review Focus 2): `open_datagram(I1 ++ H ++ I2, KR, [None; 3])`, `I1`/`I2` = `protect(OutPacket{Initial, S1, [], 3/4, 1, [Ping], 40}, CLIENT)`, `H` a Handshake packet protected with `SERVER` → `packets` = the two Initials (pn 3, 4), `error == None`, `reset_tail == None`.
  - **`short_takes_rest`:** two 1-RTT packets protected back to back under the same keys → `open_datagram` yields `packets == []` (the first short header claims both, so AEAD fails) and `reset_tail == Some(last 16)`.
  - **`zero_rtt_skipped`:** `d0 00000001 08 8394c8f03e515708 00 1e ++ [0; 30] ++ A2` → `packets == [<a2 plain>]`.
  - **`error_stops`:** `I1 ++ <reserved_bits_violation packet> ++ I2` → `packets == [I1 plain]`, `error` is `Some((0x0a, _))`.
  - **`reset_tail`:** `[0x40] ++ [0x11; 8] ++ [0x33; 15] ++ [0x77; 16]` with `[None; 3]` → `packets == []`, `reset_tail == Some([0x77; 16])`; `open_datagram(A2, KR, ..)` → `reset_tail == None`.
  - **`oversized`:** `[0; 65536]` → `Rx{[], None, None}`.
- [ ] **Step 2:** The tests fail.
- [ ] **Step 3: Implement.** Duvet-cite: RFC 9001 §5.4.2 "MUST discard packets that are not long enough to contain a complete sample" at the `o + 20` check; RFC 9000 §17.2 and §17.3.1 "MUST treat receipt of a packet that has a non-zero value for these bits after removing both packet and header protection as a connection error of type PROTOCOL_VIOLATION" at the `reserved_bits_zero` check after `open_packet` (extra citations; 3b cited them at `reserved_bits_zero`); RFC 9000 §10.3.1 "the comparison MUST be performed when the first packet in an incoming datagram … cannot be decrypted" at `reset_tail`; comment-cite RFC 9001 §5.5 at the AEAD-failure drop and §4.6.2 at the 0-RTT drop.
- [ ] **Step 4:** The four checks and the rlimit-4 run. **Mutations:** check `reserved_bits_zero` before `open_packet` (fails `reserved_flip_on_wire_drops` and the spec equality); compute `reset_tail` from the last packet instead of the first.
- [ ] **Step 5: Commit:** `feat(quic): verified unprotect and datagram opening; theorem unprotect∘protect = id (RFC 9001 §5.3-§5.5)`
- [ ] **Step 6: Matrix commit.** RFC 9001 §5.4.2: Phase 4 → 3, `✅ 3e: crates/quic/src/protect.rs`. Touched notes: §5.5 `3e: every packet that fails AEAD is discarded (protect.rs); key-update half closes in 4`; §4.6.2 `3e: 0-RTT packets dropped unprocessed (protect.rs)`; §9.5 `3e: HP removal, PN decoding and AEAD are applied together in protect.rs; not constant time (branches on the unmasked pn length), known gap`. Commit: `docs: close RFC 9001 §5.4.2 in 3e`.

---

### Task 5: Connection glue (`quic::pipeline`) — suggested model: opus

**Files:**
- Create: `crates/quic/src/pipeline.rs`, `crates/quic/tests/pipeline.rs`
- Modify: `crates/quic/src/lib.rs`; `crates/quic/src/conn.rs`, **spec only**: `poll_cid_updates` gains `final(self).keeps_later(*old(self))`, proved like `poll_stream_events` with a `lemma_keeps_streams`-style frame lemma (it writes only `cid_updates` and `tokens_registered`, which no timer reads) (Decision 14, revised)

**Interfaces:**
- Consumes: `Connection::{accept, on_datagram, poll_transmit, close, on_reset_candidate, largest_pn, handshake_complete, now, on_timeout, poll_cid_updates, next_timeout}`; `transmit_ok` (P7, P16), `lemma_wf_protect_ok`, `out_log`, `timers_later`, `acks_later`, `keeps_later`, `lemma_keeps_elim`, `later`; `rfc_long_header`/`parse_long_header`, `TransportParams`, `RAND_LEN`, `PathId`.
- Produces. Each `requires` at most `old(c).wf()`; each ensures `final(c).wf()`.
  - **`pub open spec fn rx_keys(keys: Seq<Option<SpecKeyPair>>, complete: bool) -> Seq<Option<SpecKeyPair>>`** = `if complete { keys } else { keys.update(2, None) }`, with exec `fn gate_keys(keys: &[Option<KeyPair>; 3], complete: bool) -> [Option<KeyPair>; 3]`. RFC 9001 §5.7: no 1-RTT packet is decrypted before the handshake completes, whatever keys the caller holds (3d2 binding note; 3d2 final re-review's related finding).
  - **`pub fn initial_dcid(d: &[u8]) -> (r: Option<Vec<u8>>)`**: `r` is `Some(c)` iff `rfc_long_header(d@)` is `Long{ty: Initial, dcid: c, ..}`. The shell's key-lookup input for `Route::NewInitial`.
  - **`pub fn accept_datagram(d: &[u8], path: PathId, now: u64, rand: &[u8; RAND_LEN], local_tp: &TransportParams, keys: &[Option<KeyPair>; 3]) -> (r: Option<Connection>)`**: ensures `r matches Some(c) ==> c.wf()`. Body order:
    ```
    rx = open_datagram(d, &gate_keys(keys, false), &[None; 3])
    first = rx.packets[0], else rx.error's packet (frames []), else return None   // nothing decrypted: no state
    c = Connection::accept(&first, d.len(), path, now, rand, local_tp)?              // §14.1 sub-1200 → None
    c.on_datagram(path, d.len(), rx.packets, now, rand)                              // bytes counted before close (§8.1)
    if let Some((code, _)) = rx.error { c.close(code, false, &[], c.now()) }         // connection error (Decision 5)
    Some(c)
    ```
  - **`pub fn receive(c: &mut Connection, d: &[u8], path: PathId, now: u64, rand: &[u8; RAND_LEN], keys: &[Option<KeyPair>; 3])`**: ensures `final(c).out_log() == old(c).out_log()`. Body order:
    ```
    rx = open_datagram(d, &gate_keys(keys, c.handshake_complete()),
                       &[c.largest_pn(Initial), c.largest_pn(Handshake), c.largest_pn(OneRtt)])
    c.on_datagram(path, d.len(), rx.packets, now, rand)        // always, even with no packet (3d2 binding)
    if let Some((code, _)) = rx.error { c.close(code, false, &[], c.now()) }
    if let Some(t) = rx.reset_tail { c.on_reset_candidate(&t, now) }
    ```
  - **`pub fn transmit(c: &mut Connection, now: u64, keys: &[Option<KeyPair>; 3], out: &mut Vec<u8>) -> (r: Option<PathId>)`**: `out.clear()`, `d = c.poll_transmit(now)?`, `protect_datagram(&d, keys, out)`, `Some(d.path)`. Ensures:
    - `r is Some(q) ==> final(c).out_log() == old(c).out_log().push(L)` with `L = final(c).out_log().last()`, `L.path == q`, `out@ == rfc_protect_datagram(L, keys@)`, `out@.len() <= out_datagram_len(L) <= MAX_DATAGRAM`, `transmit_ok(*old(c), *final(c), L)`;
    - `r is None ==> out@ == [] && final(c).out_log() == old(c).out_log() && final(c).acks_later(now)`;
    - `now < u64::MAX && old(c).timers_later(now) ==> final(c).timers_later(now)` (forwarded from `poll_transmit`).
    - A `Some` with an empty `out` means every packet was unkeyed: the shell sends nothing and polls again. With 3d2 P1 (`wf_amp`), the bytes the shell sends are bounded by what the amplification trace counted.
  - **`fn settled_later(c: &mut Connection, now: u64, rand: &[u8; RAND_LEN], keys: &[Option<KeyPair>; 3], out: &mut Vec<u8>, cap: usize) -> (r: Option<Option<u64>>)`**, never called, `#[allow(dead_code)]` (the 3d2 `Connection::settled_later` pattern): requires `old(c).wf()`, `now < u64::MAX`; ensures `r matches Some(t) ==> later(t, now)`. Body: the shell's wake sequence exactly: `c.on_timeout(now, rand)`; `c.poll_cid_updates(&mut v)`; `transmit` until `None`, at most `cap` times (`None` at the cap); `Some(c.next_timeout())`. This is the 3d2 note "sleeping on `next_timeout`" proved for the calls the shell makes.

- [ ] **Step 1: Failing tests** in `tests/pipeline.rs`. `K = [Some(KeyPair{rx: CLIENT, tx: SERVER}), None, None]`, `KC` the client view; `T` arbitrary test `PacketKeys`, `K1 = [K[0], None, Some(KeyPair{rx: T, tx: T})]`; `ini_c1(pn, frames, padding)` = `protect(OutPacket{Initial, S1, C1, pn, 4, frames, padding}, CLIENT)` (1200 bytes with `[Crypto{0, A2_CRYPTO}]` and padding 909), for tests that need `ptp()`'s `initial_source_connection_id C1`.
  - **`accept_transmit_a2`:** `accept_datagram(A2, 0, 0, &rnd(1), &ltp(), &K)` is `Some(c)`; `transmit(&mut c, 0, &K, &mut out) == Some(0)`, `out.len() == 39` (3d2's 47-byte `harness_mirror` ACK-only Initial without its 8-byte DCID: A.2's SCID is empty); `unprotect(&out, &KC, &[None; 3]) == Ok((Some(PlainPacket{Initial, [], rnd(1)[0..8], [], 0, [Ack(AckFrame{2, 0, 0, [], None})]}), 39))`; the next `transmit` is `None`.
  - **`accept_rejects`:** `None` for the 1199-byte Initial `protect(OutPacket{Initial, S1, [], 2, 4, [Crypto{0, A2_CRYPTO}], 916}, CLIENT)`; `A2` with keys `[None; 3]`; `A2` with its last byte flipped.
  - **`accept_1350`** (Review Focus 4): the same packet with `padding = 1067` (1350 bytes) → `Some`; its reply ACKs pn 2.
  - **`first_packet_error_closes`** (Review Focus 3): `accept_datagram(<the reserved_bits_violation packet>, ..)` is `Some(c)`; `transmit` gives one Initial datagram which, decrypted with `KC`, is `[ConnectionClose{false, 0x0a, 0, []}]` (the Handshake CC is unkeyed and skipped); `out.len() <= 3 · 1200`; `c.phase()` is Closing.
  - **`receive_then_error`:** after `accept_transmit_a2`, `receive(&mut c, I3 ++ <reserved-bit packet, pn 4>, 0, 5, ..)`, `I3` pn 3 `[Ping]` padded to 1200 in total → `largest_pn(Initial) == Some(3)`, next `transmit` carries `ConnectionClose{false, 0x0a, ..}`.
  - **`receive_counts_undecryptable`:** after accept and a drained `transmit`, `receive` of 1200 bytes `[0xc0, 0, 0, 0, 1, 8, S1.., 0, 0x44, 0x9e] ++ zeros` (AEAD fails): `largest_pn(Initial)` stays `Some(2)`, `phase()` Open, and `path_budget(0)` (3d2's doc-hidden getter) grows by 3600 (§8.1: counted although nothing decrypted).
  - **`one_rtt_gated_until_complete`** (Review Focus 5): `c = accept_datagram(ini_c1(2, [Crypto{0, A2_CRYPTO}], 909), 0, 0, &rnd(1), &ltp(), &K1)`; `bad = build(<short header 0x48 ++ L0 ++ pn byte 00>, 9, 0, [Ping] ++ [0; 3], T)` (reserved bit 0x08 set, valid AEAD). `receive(&mut c, bad, 0, 10, &rnd(2), &K1)` leaves `phase()` Open (not decrypted). Then `c.on_peer_params(&ptp(), 10)`, `c.on_handshake_complete(b"h3", 10, &rnd(3))`, and the same `receive` → `phase()` Closing with code 0x0a.
  - **`timeout_settles`:** after `accept_transmit_a2`, with `t = c.next_timeout().unwrap()`: `on_timeout(t, ..)`, `poll_cid_updates`, `transmit` to `None` within 1024 calls, then `c.next_timeout().map_or(true, |u| u > t)`.
- [ ] **Step 2:** The tests fail.
- [ ] **Step 3: Implement.** Duvet-cite RFC 9000 §14 "an endpoint MUST NOT close a connection when it receives a datagram that does not meet size constraints" at `accept_datagram`/`receive` (sizes only drop packets here; the only `close` is on an authenticated packet's error), and RFC 9001 §5.7 "Endpoints in either role MUST NOT decrypt 1-RTT packets from their peer prior to completing the handshake" at `gate_keys` (conn.rs already cites the "MUST NOT process" sentence). **Check every MUST of §17.2 (7) and §17.3.1 (3)** with `duvet_q.py`: all are cited in 3b's `header.rs` or Task 4's check; add any missing citation where its behaviour lives.
- [ ] **Step 4:** The four checks, and the rlimit-4 run, which re-verifies `conn.rs` for the one ensures. **Mutations:** `gate_keys(keys, true)` in `receive`; call `on_datagram` only when `rx.packets` is non-empty; drop `poll_cid_updates`' new ensures (must fail `settled_later`).
- [ ] **Step 5: Commit:** `feat(quic): verified receive/send pipelines over Connection (RFC 9000 §17.2, §17.3.1 reserved bits; §14 no close on size; RFC 9001 §5.7 decrypt gate)`
- [ ] **Step 6: Matrix commit.** §17.2, §17.3.1: `✅ 3e: crates/quic/src/protect.rs + pipeline.rs (reserved bits after AEAD); other MUSTs in header.rs (3b)`, replacing 3b's touched notes. RFC 9001 §5.7 touched note: `3e: 1-RTT keys masked until handshake_complete in crates/quic/src/pipeline.rs; the re-feed of a 1-RTT packet coalesced with the client Finished is Phase 4`. Commit: `docs: mark RFC 9000 §17.2, §17.3.1 closed in 3e`.

---

### Task 6: `crates/server` shell (unverified) — suggested model: sonnet

**Files:**
- Create: `crates/server/Cargo.toml`, `crates/server/src/lib.rs`, `crates/server/src/main.rs`, `crates/server/tests/shell.rs`
- Modify: `Cargo.lock`, `TRUSTED.md`, `docs/requirements.md`, `docs/crypto-binary-audit.md` ("What it does not check": "a linked binary (none exists)" becomes "a linked binary (`crates/server`'s, since 3e)")

**Interfaces:**
- Consumes: `quic::pipeline::{initial_dcid, accept_datagram, receive, transmit}`; `quic::aead::{PacketKeys, KeyPair, MAX_UDP_PAYLOAD}`; `quic::route::{route, Route, CidTable, ConnId}`; `quic::conn::{Connection, RAND_LEN}` (`next_timeout`, `on_timeout`, `on_reset_candidate`, `poll_cid_updates`, `is_closed`, `path_state`); `quic::tp::{TransportParams, default_transport_params}`. Every callee's `requires` is at most the receiver's `wf()` (Architecture); Step 3 checks the list.
- Produces (`server`):
  - **`pub fn bind(addr: SocketAddr) -> io::Result<UdpSocket>`**, DF set before returning (Decision 9): IPv4 `IP_MTU_DISCOVER = IP_PMTUDISC_PROBE`; IPv6 `IPV6_MTU_DISCOVER = IPV6_PMTUDISC_PROBE` and `IPV6_DONTFRAG = 1`; any `setsockopt` failure is an `Err`. `// ponytail: a dual-stack [::] socket's v4-mapped traffic gets no IPv4 DF; bind v4 and v6 separately if both are needed.`
  - **`pub fn initial_keys(dcid: &[u8]) -> Option<KeyPair>`**: `Some(KeyPair{rx: <A.1 client>, tx: <A.1 server>})` iff `dcid == 8394c8f03e515708`, with the Architecture ponytail.
  - **`pub fn local_params() -> TransportParams`** = `default_transport_params()` with 3d2's `ltp()` values (`max_idle_timeout 30000`, `initial_max_data 1000`, `initial_max_stream_data_bidi_remote 100`, `_uni 100`, `initial_max_streams_bidi 10`, `_uni 3`, `active_connection_id_limit 2`, `disable_active_migration true`).
  - **`pub fn read_timeout(now: u64, deadline: Option<u64>) -> Option<Duration>`**: `None` without a deadline, else `Some(Duration::from_micros(max(deadline.saturating_sub(now), 1000)))`. The 1 ms floor is defence in depth only (Decision 18); the guarantee is `pipeline::settled_later`.
  - **`pub fn fresh_rand() -> io::Result<[u8; RAND_LEN]>`** via `libc::getrandom`, looping on partial reads and EINTR.
  - `pub const MAX_POLLS: usize = 1024;`
  - **`pub struct Server`** (Decision 17), state `table: CidTable`, `conns: Vec<Conn>`, `next_id: ConnId`, `rng: fn() -> io::Result<[u8; RAND_LEN]>`, `out: Vec<u8>`; private `struct Conn { id: ConnId, conn: Connection, keys: [Option<KeyPair>; 3], addrs: Vec<SocketAddr> }` (`PathId` = index into `addrs`).
    - `pub fn new(rng: fn() -> io::Result<[u8; RAND_LEN]>) -> Server`
    - **`pub fn on_datagram(&mut self, d: &[u8], from: SocketAddr, now: u64, send: &mut Vec<(Vec<u8>, SocketAddr)>) -> io::Result<()>`**:
      ```
      match route(d, &self.table):                         // sole version_negotiation call site (§17.2.1)
        VersionNegotiation(v) => send.push((v, from))
        Reset(id)             => conn(id).on_reset_candidate(&last16(d), now); service(id)
        Existing(id)          => p = index of from in addrs, else addrs.push(from) and p = new index (tentative)
                                 receive(&mut conn, d, p, now, &rng()?, &keys)
                                 if conn.path_state(p) is None { addrs.truncate(p) }   // 3d2 E9: no slot for an unaccepted path
                                 service(id)
        NewInitial            => if let Some(kp) = initial_dcid(d).and_then(|x| initial_keys(&x)):
                                   keys = [Some(kp), None, None]
                                   if let Some(conn) = accept_datagram(d, 0, now, &rng()?, &local_params(), &keys):
                                     push Conn{next_id, conn, keys, vec![from]}; next_id += 1; service(new)   // I1
        Drop                  => {}
      ```
    - **`pub fn on_wake(&mut self, now: u64, send: &mut ..) -> io::Result<()>`**: for each connection with `matches!(conn.next_timeout(), Some(t) if t <= now)` (a `None` deadline is never due): `on_timeout(now, &rng()?)`; then `service` every connection.
    - `service(i, now, send)`, in `settled_later`'s order: `poll_cid_updates`, each update `table.apply(id, &u)` in order (a `false` is ignored: a key collision, `issue_cids`' ponytail); then `transmit` at most `MAX_POLLS` times until `None`, pushing `(out.clone(), addrs[p])` when `out` is non-empty and `p < addrs.len()`; reaching `MAX_POLLS` is a bug: one line to stderr, then stop; then, if `is_closed()`, `table.remove_conn(id)` and drop the connection.
    - **`pub fn deadline(&self) -> Option<u64>`**: the minimum `next_timeout()` over connections, re-read on every call, so after every receive and every `on_timeout`.
    - `#[doc(hidden)] pub fn conn_count(&self) -> usize`, `#[doc(hidden)] pub fn addr_count(&self, i: usize) -> usize` (tests).
    - `// ponytail: linear scans over conns and route's CID/token lists (≤ MAX_CONNS = 102 connections; route costs ≤ 512 CID and 816 CT token comparisons per datagram); a random-keyed SipHash index before production, never a sorted Vec (it leaks token order, §10.3.1).` Connections are capped by `route`'s `has_room` (`MAX_CONNS`), counted at the first applied `Add`, which `service` applies before the next datagram; nothing is evicted, and RFC 9000 §10.1's 3·PTO floor lets a peer hold a slot up to 55.6 min (3d2 note), which admission must assume. A.1-only keys admit one connection in 3e.
  - **`pub fn run(sock: UdpSocket) -> io::Result<()>`**, returning only on a fatal socket or RNG error:
    ```
    start = Instant::now(); srv = Server::new(fresh_rand); buf = vec![0; MAX_UDP_PAYLOAD]
    loop:
      now = µs since start; srv.on_wake(now, &mut send)?; send_all
      sock.set_read_timeout(read_timeout(now, srv.deadline()))?
      match sock.recv_from(&mut buf):
        Ok((n, from)) => srv.on_datagram(&buf[..n], from, µs since start, &mut send)?; send_all
        Err WouldBlock | TimedOut | Interrupted => {}
        Err e => return Err(e)
    send_all: send_to each, errors ignored (UDP); drain the queue
    ```
  - **`main.rs`:** `server [ADDR]`, default `127.0.0.1:4433`; `bind`, then `run`; on `Err`, the error to stderr and exit 1.

- [ ] **Step 1: Failing tests** in `tests/shell.rs` (a deterministic `rng` returning `rnd(1)`; A.1 keys, `A2` and `hex` copied in):
  - **`df_set_v4`:** `bind("127.0.0.1:0")`, then `getsockopt(IPPROTO_IP, IP_MTU_DISCOVER) == IP_PMTUDISC_PROBE` via `libc`.
  - **`df_set_v6`:** `bind("[::1]:0")`, returning early on `AddrNotAvailable`; `IPV6_MTU_DISCOVER == IPV6_PMTUDISC_PROBE`, `IPV6_DONTFRAG == 1`.
  - **`a1_keys_only`:** `initial_keys(8394c8f03e515708)` has `rx.key == 1f369613…a22d` and `tx.hp == c206b8d9…a314`; `initial_keys([0x83; 8])` and `initial_keys(&[])` are `None`.
  - **`read_timeout_floor`** (Review Focus 7): `read_timeout(10, Some(5)) == Some(1 ms)`; `read_timeout(10, Some(10)) == Some(1 ms)`; `read_timeout(0, Some(2500)) == Some(2500 µs)`; `read_timeout(0, None) == None`.
  - **`a2_registered_before_next`** (3d2 I1): `on_datagram(A2, a0, 0, ..)` sends one 39-byte datagram to `a0`; a second `on_datagram(A2, a0, 1, ..)` leaves `conn_count() == 1` (routed `Existing`: the `Add(odcid)` was applied before it).
  - **`spoofed_addresses_take_no_slot`** (Review Focus 6): after A2 from `a0`, four 1200-byte undecryptable datagrams with A.2's header (DCID `S1`) from `a1`..`a4` leave `addr_count(0) == 1`.
  - **`idle_close_frees_slot`:** after A2, `on_wake(60_000_000, ..)` (past the 30 s idle timeout) leaves `conn_count() == 0`, and A2 again creates a connection (`remove_conn` freed the table).
- [ ] **Step 2:** The tests fail.
- [ ] **Step 3: Implement.** Duvet-cite, in `lib.rs`:
  - RFC 9000 §14 "UDP datagrams MUST NOT be fragmented at the IP layer" and "the Don't Fragment (DF) bit MUST be set if possible" at `bind`. "QUIC MUST NOT be used if the network path cannot support … 1200 bytes" as an exception whose reason points at 3d2's P17 gate (`Paths::mtu_failed`, conn.rs; the §14.2 row): every datagram is ≤ `MAX_DATAGRAM`, and a path that fails the 1200-byte probe gets only probes and CONNECTION_CLOSE.
  - RFC 9000 §9.7 "The flow label generation MUST be designed…" at `bind`, as an exception: the shell never sets a flow label; any label is the kernel's (the OS UDP stack, trusted base).
  - RFC 9000 §14.2.1's three MUSTs at `bind`, as exceptions: no ICMP is read (no `IP_RECVERR`), and `PMTUDISC_PROBE` makes the kernel ignore ICMP PMTU for our sends.
  - **Call check:** list every `quic` function and method `crates/server/src` calls with its `requires` (expected: none, or the receiver's `wf()` only) in the task report.
- [ ] **Step 4:** The four checks. Before relying on Decision 8, re-probe: `(cd crates/server && cargo verus verify)` type-checks the shell, reuses the cached verification of quic, crypto, h3 and wire, and exits 0 (the 2026-10-28 probe was lost with /tmp). If it fails, stop and report: the fallback is a one-line `verify.sh` skip for crates without `[package.metadata.verus]`, which needs a ruling. `scripts/verify.sh` still ends `escapes accounted (0)` and `binary ok (<n> fns)` (`libserver.rlib` should reference no `crypto::` symbol; if a `U server crypto::…` or `D server …` line appears, follow Task 1 Step 4's procedure and stop conditions); `cargo build -p server` gives 0 warnings.
- [ ] **Step 5: TRUSTED.md.**
  - "Pinned versions": `libc =0.2.191 (crates/server only: setsockopt, getsockopt in tests, getrandom)`.
  - Trusted base bullet: getrandom is also used for PATH_CHALLENGE data and the spin bit (3d2 Task 2b review).
  - Rows:
    - `| crates/server (whole crate): unverified IO shell — UDP loop, DF setsockopt, libc getrandom, Instant clock, per-connection address table (an address is kept only once Connection accepts its path), dispatch on quic::route, CidTable updates applied in order before the next datagram; scripts/verify.sh's cargo verus verify only type-checks it. It calls only quic fns whose requires is the receiver's wf(), which Verus does not check at an unverified call site; every constructor and pub method ensures wf() over private fields | crates/server/src/lib.rs, crates/server/src/main.rs | design-spec trusted base (IO shell) | never |`
    - `| RFC 9001 A.1 Initial keys hard-coded in server::initial_keys (DCID 8394c8f03e515708 only) | crates/server/src/lib.rs | RFC constants stand in for Initial secret derivation (RFC 9001 §5.2) | 4 |`
- [ ] **Step 6: Commit:** `feat(server): unverified UDP shell over the verified pipelines (DF set, A.1 Initial keys)`
- [ ] **Step 7: Matrix commit.** §14: `✅ 3e: crates/server/src/lib.rs (bind: DF via PMTUDISC_PROBE) + quic/src/pipeline.rs (no close on size); 1200-byte path via 3d2 P17`. §9.7: `✅ 3e: crates/server/src/lib.rs (flow label never set; kernel default)`. §14.2.1: `✅ 3e: crates/server/src/lib.rs (no ICMP read; PMTUDISC_PROBE ignores kernel PMTU; vacuous)`. Commit: `docs: mark RFC 9000 §9.7, §14, §14.2.1 closed in 3e`.

---

### Task 7: Loopback harness (`crates/server/tests/initial_exchange.rs`) — suggested model: sonnet

**Files:**
- Create: `crates/server/tests/initial_exchange.rs`

**Interfaces:**
- Consumes: `server::{bind, run}`; `quic::protect::{protect, unprotect}`, `quic::aead::{PacketKeys, KeyPair}`, `quic::datagram::{OutPacket, PlainPacket}`, `quic::frame::Frame`, `quic::ack::AckFrame`, `quic::payload::PacketKind`. The A.1 keys, `A2` and `A2_CRYPTO` are copied in from rfc9001.txt.
- Helpers:
  - `start() -> SocketAddr`: `s = bind("127.0.0.1:0")`, its address, `thread::spawn(move || run(s))`.
  - `client()`: a `UdpSocket` on `127.0.0.1:0` with a 500 ms read timeout.
  - `KC = [Some(KeyPair{rx: SERVER, tx: CLIENT}), None, None]`.
  - `assert_a2_reply(sock)`: one `recv` of `n <= 3600` bytes (3d2: the 39-byte ACK-only Initial); `unprotect(&buf[..n], &KC, &[None; 3])` is `Ok((Some(p), n))` with `p.kind == Initial`, `p.dcid == []`, `p.scid.len() == 8`, `p.pn == 0`, `p.frames == [Ack(a)]`, `a.largest == 2`, `a.first_range == 0`, `a.ranges == []`, `a.ecn == None`; then `recv` times out.

- [ ] **Step 1: Write the tests**, each against a fresh `start()`:
  - **`a2_gets_one_ack`:** send `A2`, then `assert_a2_reply`.
  - **`initial_1199_ignored`:** send `protect(OutPacket{Initial, 8394c8f03e515708, [], 2, 4, [Crypto{0, A2_CRYPTO}], 916}, CLIENT)` (assert its length is 1199); `recv` times out; then send `A2`, and `assert_a2_reply` holds with pn 0. (Had the 1199-byte datagram created state, A.2's pn 2 would be a duplicate.)
  - **`unknown_version_gets_vn`:** send `c0 1a2a3a4a 08 8394c8f03e515708 00` zero-padded to 1200; the one reply is `c0 00000000 00 08 8394c8f03e515708 00000001`; then `recv` times out.
  - **`small_unknown_version_dropped`:** the same truncated to 1199 bytes gets no reply (§5.2.2).
- [ ] **Step 2:** `cargo test -p server --test initial_exchange`: all 4 pass. Tasks 1–6 are in place, so this is a check, not a red step; on a failure, debug the shell, not the test.
- [ ] **Step 3:** The four checks.
- [ ] **Step 4: Commit:** `test(server): loopback Initial exchange harness (RFC 9001 A.2 → ACK, sub-1200 Initial dropped, VN) — Phase 3 exit`

---

## Exit criteria (Phase 3e, and Phase 3)

- All four checks pass on the merged tree; quic verifies at `--rlimit 4` (the evidence recipe).
- The 7 rows carry `✅ 3e: <file>`; the RFC 9000 awk above prints nothing; RFC 9001 §5.4.1 and §5.4.2 are Phase 3; §5.3, §5.5, §4.6.2, §9.5 and §5.7 carry 3e touched notes.
- `duvet_q.py` prints nothing for RFC 9000 §9.7, §14, §14.2.1, §17.2, §17.3.1 and RFC 9001 §5.4.1, §5.4.2.
- `docs/crypto-binary-digests.txt` has the three `U quic crypto::…` lines, each recorded in the audit's Gate records.
- `cargo test -p server --test initial_exchange` passes 4 tests: the design spec's Phase 3 exit.
- `phase-3e` is merged into `main`.

## Binding notes for later phases

- **Phase 4 (TLS):**
  - replace `initial_keys` with RFC 9001 §5.2 derivation for any DCID (tls's `hkdf_expand_label` exists) and drop its TRUSTED.md row; fill the Handshake and 1-RTT `KeyPair` slots as keys are installed;
  - add `crypto_read`/`crypto_write` to the shell's `service`, inside the proven wake order: anything called between `on_timeout` and the `next_timeout` read must ensure `keeps_later` (3d2 note; `crypto_read` does not today);
  - switch the shell from `Connection` to `H3Server` plus `pump` (Decision 11, 3d2 note): `H3Server::settled_later` covers `on_timeout` → `pump` → `poll_transmit` loop via `conn_mut` → `conn().next_timeout()`; give `pipeline` an `H3Server` twin of `settled_later`. `H3Server::pump` also discharges the 3d2 obligation to drain `poll_stream_events` after every `on_datagram`, which 3e meets vacuously (no `Streams` before `on_peer_params`);
  - **re-feed the 1-RTT packet coalesced with the client Finished** (3d2 final review M5): `receive` keeps it protected (Task 5's gate); Phase 4 hands its bytes back, and after `on_handshake_complete` unprotects it and calls `on_datagram(path, 0, vec![p], now, rand)` on the same path, only if `p` matched the original datagram's first DCID (§12.2), then pumps (pinned at the `Connection` level by `early_one_rtt_refed`). Decision 20;
  - key phase and key update in `rfc_unprotect` (RFC 9001 §5.5, §6); the key-phase bit is ignored today, with one 1-RTT key;
  - with any DCID keyed, `MAX_CONNS` (102) becomes reachable: admission must assume §10.1's 3·PTO floor (a slot held up to 55.6 min, 196 s for a dead peer with defaults), and `route`'s linear scan (≤ 512 CID + 816 CT token comparisons per datagram) needs the random-keyed SipHash index before production (3d final review I3, carried by 3d2);
  - **keep "no keyless ack-eliciting packet":** every space that can carry CRYPTO, ACK or PING has its keys first, so `protect_datagram`'s write-nothing branch stays unreachable outside a misconfiguration; alternatively gate 3d's `close_spaces` on key availability (RFC 9000 §10.2.3).
- **Phase 5:** done; `hp`/`aead` already prove against the verified primitives' specs.
- **Phase 7:** the shipped `server` binary is a linked build the binary gate does not check (audit "What it does not check").

## Self-review (done while writing)

- **Spec coverage.** Protection proven against the crypto specs: Tasks 1–3 (`rfc_protect`), Task 4 (`rfc_unprotect`, inverse theorem). Pipelines: Tasks 3–5. Shell (UDP loop, clock, getrandom, DF): Task 6. Phase 3 exit: Task 7. The outline's "receive pipeline" and "send pipeline" are split per side (Tasks 3–4) plus the `Connection` glue (Task 5).
- **3d/3d2 bindings honoured** (each mapped in the preflight table): `protect` writes exactly `out_packet_len` including padding and spin; `accept` then `on_datagram` with the full length, always; `largest_pn` feeds `decode_pn`; `dcid_len = LOCAL_CID_LEN`; `on_reset_candidate` on an undecryptable first packet and on `Route::Reset`; one 1-RTT packet per datagram; `plain_wf` discharged by Verus; `version_negotiation` only via `route`; the I1 order; the no-spin wake; §5.7.
- **Type consistency:** `PacketKeys`, `KeyPair`, `MAX_UDP_PAYLOAD` (2 → 3–7); `rfc_hp_*`/`apply_hp`/`remove_hp` (1 → 3, 4); `protect_ok`/`rfc_protect`/`protect`/`protect_datagram`/`rfc_protect_datagram` (3 → 4, 5, 7); `unprotect`/`open_datagram`/`Rx` (4 → 5, 7); `gate_keys`/`initial_dcid`/`accept_datagram`/`receive`/`transmit` (5 → 6); `bind`/`run`/`Server` (6 → 7). 3b/3d/3d2 names are as on `main` at 7e95f7f.
- **Arithmetic:** A.2: 22 + 245 + 917 + 16 = 1200; padding 916 → 1199 (Length 1181, still 2 bytes); padding 1067 → 1350. With SCID `C1`, the header is 30 bytes, so padding 909 gives 1200. A.3: 20 + 99 + 16 = 135. ACK-only reply: 1 + 4 + 1 + 0 + 1 + 8 + 1 (token length) + 1 (Length 22) + 1 (pn) + 5 (ACK) + 16 = 39 (3d2's `harness_mirror` is 47 with an 8-byte DCID). Short packet 1 + 8 + 1 + 3 + 16 = 29. Nonce XORs `5c^02 = 5e`, `3e^01 = 3f`. `short_header_bits`: `0x41 ^ 0x03 = 0x42`, `a0^7b = db`, `a1^9a = 3b`.
- **Proportion.** Bodies only where order is the requirement: `rfc_protect`, `rfc_unprotect`, `accept_datagram`/`receive`, `settled_later`, `Server::on_datagram`/`service`, `run`.

## Decisions (controller rulings; recommendation given)

1. **`protect` requires `protect_ok`, not `out_packet_wf(p, _)`:** `out_packet_sized` plus the sample room and OneRtt-no-SCID, without the `pn_len_ok` minimality clauses, which A.2 (pn 2, length 4), A.3 (pn 1, length 2) and the 1199-byte builder can't satisfy. `lemma_wf_protect_ok` keeps 3d's binding. *Accept.*
2. **`unprotect(b, keys: &[Option<KeyPair>; 3], largest: &[Option<u64>; 3]) -> Result<(Option<PlainPacket>, usize), (u64, PlainPacket)>`**, replacing the outline's single-key form: keys chosen by parsed kind; the consumed length survives a drop (skip unkeyed and 0-RTT packets inside a coalesced datagram); the error carries header fields so a first-packet error can still create the connection that closes; `dcid_len` fixed at `LOCAL_CID_LEN`. *Accept.*
3. **The pipelines are verified glue**, so 3d2 P7 ⇒ `protect`'s precondition, `plain_wf` and `close`'s code bound are checked by Verus, and the shell calls only fns whose `requires` is the receiver's `wf()`. *Accept.*
4. **Packets in unkeyed spaces are skipped by `protect_datagram`**; written length `<= out_datagram_len` (`==` when all keyed); a datagram with an ack-eliciting Initial is withheld whole if anything is skipped (§14.1 on the wire). In 3e it fires only for a closing CONNECTION_CLOSE in the Handshake space. *Accept, with the Phase 4 note.*
5. **A reserved-bit or payload error on the packet that would create the connection is a connection error** (accept from its header, count the bytes, close): pinned by `first_packet_error_closes`. *Accept.*
6. **The reset-check trigger is "the first packet yielded no packet and no error"** (no keys, too short, 0-RTT, AEAD failure), datagram ≥ 21 bytes: a superset of §10.3.1's "cannot be decrypted". *Accept.*
7. **Retag RFC 9001 §5.4.1 and §5.4.2 to Phase 3 and close both in 3e**; §5.3, §5.5, §4.6.2, §9.5, §5.7 stay Phase 4 with touched notes. *Accept.*
8. **`scripts/verify.sh` stays unedited**: `cargo verus verify` in `crates/server` type-checks only (re-probed in Task 6), the escape grep covers the shell, TRUSTED.md records it as unverified. The success line's "all crates verified" slightly overstates for `server`. *Accept.*
9. **DF via `IP_PMTUDISC_PROBE` / `IPV6_PMTUDISC_PROBE` + `IPV6_DONTFRAG`**, not the outline's `_DO`: DF set and kernel ICMP PMTU ignored, so §14.2.1 holds in fact. *Accept.*
10. **Randomness from `libc::getrandom`**, no `getrandom` crate; libc is the shell's only new direct dependency. *Accept.*
11. **The shell drives `Connection`, not `H3Server`**: nothing reaches HTTP/3 before Phase 4 completes a handshake. *Accept; Phase 4 switches.*
12. *(Replaced by 21.)*
13. **`theorem_unprotect_protect` is in Task 4's scope** (`gctr` involution, HP round trip, header-ignores-masked-bits; trailing padding is 3b's `theorem_payload_padded`). *Keep; drop only if Task 4 overruns.*
14. **Earlier-crate additions:** none of the draft's fallbacks is needed (3b exports `spec_long_header_bytes`/`spec_short_header_bytes`; 3d2 exports `out_log`, P7 and P16). One spec-only addition remains: `poll_cid_updates` ensures `keeps_later`, so the shell's wake order (I1 needs the updates applied after `on_timeout`) is inside the no-spin proof. No behaviour change. *Accept.*
15. **`largest == Some(PN_MAX)` drops that space's packets** (outside `decode_pn`'s domain); coalesced same-space packets decode against one pre-datagram `largest`. *Accept (ponytail).*
16. **The doc fixes ride in Task 1** (3a plan's three "Phase 3b" → 3e; outline row-accounting line). *Accept.*
17. **The shell is `Server` (socket-free: `on_datagram`, `on_wake`, `deadline`) plus `run`**, replacing the draft's monolithic loop, so the I1 order, the address-slot rule and idle removal are unit-tested. *Accept.*
18. **`read_timeout` floor 1 ms** (draft: 1 µs, which avoids `Duration::ZERO` but is no minimum sleep): defence in depth against a past deadline, at RFC 9002's 1 ms timer granularity. *Accept.*
19. **`crypto_read` is not called in 3e** (YAGNI: no TLS reads it, the CRYPTO receive buffer is bounded, and it would sit between `on_timeout` and the deadline read without `keeps_later`). *Accept; Phase 4 adds it.*
20. **The §5.7 re-feed is Phase 4**: 3e guarantees the "MUST NOT decrypt" half (`gate_keys`, Duvet-cited, tested) but does not hold the protected bytes, since nothing in 3e can complete a handshake to re-feed them. *Recommend Phase 4; the 3d2 note's heading says "carried out by the 3e shell", so this needs a ruling.*
21. **The shell's address table follows `Connection`'s paths** (replaces Decision 12): an unknown address gets the next `PathId` tentatively and is kept only if `path_state(p)` is `Some` after `receive`. No `MAX_PATHS` cap in the shell: `Connection` caps paths. The draft's push-on-any-datagram would let spoofed garbage fill the slots, undoing 3d2 E9. *Accept.*
