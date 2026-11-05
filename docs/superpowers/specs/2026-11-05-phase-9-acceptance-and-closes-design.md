# Phase 9: acceptance clauses and proved closes — design

**User request (2026-11-05):** "Start using acceptance clauses and proving closes."

**Why.** Most review findings so far got past Verus for the same reason: the specs said "must reject X" and never "must accept Y". For example, a legal empty CRYPTO frame closed the connection with a false PROTOCOL_VIOLATION (fixed in 753ec2d, pinned only by tests). Closes were pinned by tests too, never proved: no `Connection` ensures names the code a connection closes with.

**Input:** `docs/superpowers/specs/2026-11-05-phase-9-inventory.md` (the inventory). It lists 98 error-site rows, the vest_lib finding, close paths C1–C12, two pilots with draft clauses (§4.1, §4.2) and the task order P0–P7 with rlimit notes (§4.3). Its file:line claims were checked against `main` at 73cc244: no crate source changed since the inventory's base `ecd54a2`. §5 below lists the claims this design corrects.

---

## 1. The rule (binding from Phase 9 on)

1. **Acceptance clause.** Every verified fn that can return an error carries
   `Err(code) ==> allowed_err(state, input, code)`.
   - `allowed_err` is one spec fn per handler, cited to the RFC with a duvet `//=` block. It is a disjunction of:
     - errors the RFC requires (MUST);
     - errors the RFC permits (MAY, or SHOULD "treat as a connection error") where we chose to raise them;
     - our own named limits (Busy, full tables), each as a visible named predicate.
   - Codecs: `spec_parse(b) is Some ==> res is Ok`.
   - A fn that signals a close with a bool instead of an `Err` (the quictls steps' `cont`/`ok`) is covered the same way: `!ok && old Open ==> allowed_x(..)`.
2. **Proved close.**
   - (a) The error path leaves the connection Closing with that exact code: `final.close_spec() == Some((app, code, reason))` (`Connection::close_spec`).
   - (b) In Closing, **if** a datagram is emitted, it contains CONNECTION_CLOSE with that code at the right key level (RFC 9000 §10.2.3). The clause says "if emitted" because amplification limits and pacing can block sends.
3. **Forward rule.** The Global Constraints of every future plan carry rules 1 and 2. An error path without an acceptance clause, or a close without a proved code, is an **Important** review finding.

A clause stated over an implementation number does not meet rule 1. The 753ec2d bug sat behind `crypto_end > init_end`, where `crypto_end` was a window end and not "the end of received data" (RFC 9001 §4.1.3). Each `allowed_*` names the RFC's own quantity (bytes received, bytes TLS has not consumed), or a named own-limit.

## 2. What vest already gives

`vest_lib 0.2.2`'s `Parser` trait ensures an iff against the combinator's `spec_parse` (`parse_matches_spec`). In this project only one leaf inherits it: `wire::varint::QuicVarInt` and everything built on `parse_varint`. Every other codec (quic frames, ACK, payload, headers, transport parameters, `open_one`; h3 frames, QPACK, request validation; the tls ClientHello, extensions, Finished, `HsReader`) is hand-written and proved **exact ≡** a hand-written `rfc_*` spec: `match r { Ok(..) => rfc_x(b) == Ok(..), Err(e) => rfc_x(b) == Err(e) }`.

**Consequence.** The codec half of rule 1 (`spec Some ==> Ok`) already holds everywhere, relative to each `rfc_*`. What is left is **spec fidelity**: does each `rfc_x` reject only what the RFC allows? That is a spec-only audit plus one lemma per spec, `rfc_x(..) == Err(c) ==> allowed_x(.., c)`. No exec codec ensures changes, and the lemmas add nothing to any exec fn's VC (9b).

## 3. Phase split

| Sub-phase | Inventory steps | Proves |
|---|---|---|
| **9a** (plan: `docs/superpowers/plans/2026-11-05-phase-9a-acceptance-pilot.md`) | P0, P1, P2 | Rule 2(a) at the `Connection` boundary and in quictls's close sinks; rule 1 on the CRYPTO path end to end (the pilot); the measured rlimit of every touched fn |
| **9b** | P3, P4 | Rule 1 for every exact ≡ codec and h3/tls spec (spec-only lemmas); rule 2(b) through `poll_transmit` |
| **9c** | P5, P6, P7 | Rule 1 and 2(a) for frame errors inside packets, h3 → quic closes, and the tls own-limit escapes |

### 3.1 9a: what it proves

**P0: close code at the `Connection` boundary** (quic/src/conn.rs).
- New `pub closed spec fn close_spec(&self) -> Option<(bool, u64, Seq<u8>)>` (`self.lc.close_spec()`) and `pub open spec fn reason_cap(r: Seq<u8>) -> Seq<u8>` (the 64-byte cap that `Lifecycle::enter_closing` applies).
- `close`, `close_internal` and `on_tls_alert` ensure:
  - `old Open ==> Closing` with `close_spec() == Some((app, code, reason_cap(reason@)))`;
  - `!old Open ==>` phase and `close_spec` unchanged (the first error wins, RFC 9000 §11.1).
- `on_peer_params` (close path C4) ensures the same, with its acceptance: it closes only if `tp@.initial_source_connection_id != Some(client_scid_spec())` (RFC 9000 §7.3), and the code is TRANSPORT_PARAMETER_ERROR. `pub closed spec fn client_scid_spec(&self) -> Seq<u8>` is new.
  - The inventory's P0 omits it, but quictls `on_params`'s acceptance (P2) needs it.

**P1: quictls close sinks** (quictls/src/server.rs).
- `shut` ensures `Closing` with `close_spec == Some((false, code, []))`. Today it proves only `!Open`.
- `report` ensures the same, with `report_code(code)`: `code` if `code <= VARINT_MAX`, else INTERNAL_ERROR. The alert branch round-trips `CRYPTO_ERROR_BASE + ((code - CRYPTO_ERROR_BASE) as u8) == code`.
- The comment at server.rs:120-125 drops "not an ensures". `tampered_finished_0x133`, `error_ranges` and `a2_closes_0x178` become regression checks, no longer the only evidence.
- Acceptance for `report`'s code belongs at its caller `feed` and needs `allowed_tls_err` over `spec_on_crypto`, so it goes in 9c (P7).

**P2: Pilot A, the CRYPTO path.**
- **Tight end, in `CryptoStream`, not `Reassembly`.**
  - New `closed spec fn tight(&self)` on `CryptoStream`: the last window slot is a received byte (`buf_len > 0 ==> rfc_received(inserted).contains_key(base + buf_len - 1)`).
  - It is a conjunct of `CryptoStream::wf` (open), so `Connection` sees it as opaque.
  - It is proved in crypto_stream.rs from `insert`'s and `pop`'s **existing** ensures plus `lemma_wf` and `lemma_received_push`. reassembly.rs is not edited, so no new conjunct reaches `RecvStream::on_data` (11.79M), which also calls `insert`.
- **Acceptance for `on_crypto`.** `crypto_allowed_err(s, offset, len, c)`: `c == CRYPTO_BUFFER_EXCEEDED && len > 0 && offset + len > s.base + MAX_CRYPTO_BUFFER`. RFC 9000 §7.5 MUST, with the window as a named own-limit at least the 4096-byte floor.
  - The `len > 0` conjunct is new. It is a **bug the pilot finds** (§5, item 1), fixed by checking for empty data before the window check.
- **`Connection` exports.** `pub closed spec fn crypto_inserted(&self, k) -> Seq<(nat, Seq<u8>)>` and `pub proof fn lemma_crypto_end_received(&self, k)`, which says `crypto_end_spec(k) > 0 ==>` byte `crypto_end_spec(k) - 1` is received.
- **quictls acceptance and close code.** Two new spec fns:
  - `past_received(c, k, end)`: some received byte at offset `>= end`;
  - `tls_unconsumed(l, k)`: TLS's reader is non-empty, or `past_received(c, k, crypto_base(k))`.

  With them:
  - `superseded`: `!cont && old Open ==>` not at Initial, `past_received(conn, Initial, init_end)`, Closing with `(false, PROTOCOL_VIOLATION, [])`. RFC 9001 §4.1.3 bullet 1.
  - `key_changes`: `!ok && old Open ==>` the batch moves past Initial with `tls_unconsumed(Initial)`, or completes with `tls_unconsumed(Handshake)`; Closing with `(false, PROTOCOL_VIOLATION, [])`. RFC 9001 §4.1.3, the "not consumed" sentence. `key_events` gains ensures over `ev.deep_view()`.
  - `on_params`: `!ok && old Open ==>` `rfc_transport_params(b@, true) is Err` (RFC 9000 §7.4, §18), or the §7.3 SCID mismatch; Closing with `(false, TRANSPORT_PARAMETER_ERROR, [])`. Whether `rfc_transport_params` rejects only what the RFC allows is P3 (9b).
- **Removed: `superseded`'s second close** (server.rs:607-613: "newly contiguous Initial bytes", read through `crypto_read`).
  - It is unreachable. At the key change `key_changes` closes unless nothing is unread, so `crypto_base(Initial) == crypto_end(Initial) == init_end`. Any later received byte is then at an offset `>= init_end`, which pushes `crypto_end` past `init_end` and takes the first branch.
  - It cannot carry an acceptance clause. Bytes that are newly contiguous below `init_end` do not "extend past the end of previously received data", so §4.1.3 does not justify the close. Proving the branch dead needs `crypto_base(Initial)` monotone across every `Connection` entry quictls calls, `poll_transmit` included (§5, item 2).
  - Removing it loses no MUST. With the tight end, the first branch is exactly §4.1.3 bullet 1 in both directions.
- **Audit item, no fix:** `RecvStream::on_data` inserts empty STREAM data too (recv_stream.rs:1336). Flow control reads `high`/`counted`, not the window end, so no false error follows. The window still grows with unreceived slots, which costs memory up to the window. `on_data` is not to be touched. 9c records the item in its plan.

**9a pilot result.** The measured rlimit of every touched fn, before and after, goes in §4. That table is the pilot's result: it says whether rules 1 and 2 cost anything near the tight fns.

### 3.2 9b: spec-only lemmas and part (b)

- **P3: one `allowed_x` and one lemma per `rfc_*`** (the inventory's "spec-relative" rows). The lemma is `rfc_x(..) == Err(c) ==> allowed_x(.., c)`, a disjunction of MUST / MAY-chosen / named own-limit predicates, each re-derived from the RFC text (the inventory's labels are provisional).
  - First, name a predicate for each of the 5 "chosen (no clause)" rows: streams.rs server-bidi RESET_STREAM/STREAM_DATA_BLOCKED; the client_hello cookie; tls `step` :1317; h3 conn.rs:2916; h3_server `pump` :1032.
  - Recursive specs (`rfc_frames`, `rfc_recv`, `rfc_request_stream`, `rfc_control`, `rfc_uni_stream`) need inductive lemmas.
  - **rlimit:** none on exec fns. Budget each lemma at rlimit 4 on its own. `RecvStream::on_data`'s acceptance comes only from a lemma on `rfc_recv`/`recv_data`.
  - Spec-fidelity item from 9a: `crypto_allowed_err` uses a span window (`offset + len > base + 16384`). Whether a span limit meets §7.5's "4096 bytes of data" floor for sparse frames is a P3 question.
- **P4: part (b).**
  - Strengthen `close_built` with `frames[0] == close_frame_spec(app, code, reason, k)`. Today it keeps only `is ConnectionClose` and drops `close_frame`'s ensures.
  - Add a closed `close_dgram_ok(o, d)`: every packet's kind is in `close_spaces(o.complete, o.live_i, o.live_h, o.complete)`, and its frame is `close_frame_spec` of `o.close_spec()` at that kind. `build_close` ensures it.
  - In `poll_transmit`'s Closing conjunct, replace `only_close(d@)` with `close_dgram_ok(*old(self), d@)`, plus `lemma_close_dgram_only_close` for existing users.
  - Then a pure `lemma_close_dgram_rfc` gives the §10.2.3 statement: app closes outside 1-RTT become APPLICATION_ERROR with an empty reason.
  - **rlimit: `poll_transmit` (7.13M) is the one tight fn 9b touches.**
    - The change is a closed-predicate swap only: the conjunct count stays equal, and nothing is added outside the existing `phase is Closing ==>` guard.
    - The early `return r` in the Closing arm is the only path that proves it.
  - The wire-level lift to `pipeline::transmit`/`QuicServer::transmit` needs `live(k) ==> keys[k] is Some` for close spaces (the converse of quictls `keys_ok`). The alternative is to state (b) on `out_log` only. 9b's plan decides.

### 3.3 9c: frame errors, h3 → quic, tls own-limits

- **P5: rule 1 and 2(a) for frame errors.**
  - `on_frame`/`on_ack_frame`/`on_crypto_frame`/`on_cid_frame` gain `Err(c) ==> allowed_frame_err(*old(self), k, f@, c)`, a closed disjunction over the sub-handlers' `allowed_*`.
  - `on_stream_frame` gains `Err(c) ==> final.close_spec() == Some((false, c, []))`.
  - `on_packet` and `on_frames` lift this to "some frame of p".
  - `on_counted`/`on_datagram` gain `old Open && final Closing ==> close_spec matches Some((false, c, _)) && allowed_datagram_err(..)`.
  - The rest of C3 and C5:
    - `close_on_error`;
    - `on_handshake_complete`'s INTERNAL_ERROR, named `internal_unreachable` or proved unreachable, and its 0x178.
  - **rlimit: medium/high.** `on_counted` and `on_frame` are large dispatch fns, spun off and unmeasured.
    - Hide `allowed_frame_err` as `closed`, and reveal it per arm in per-frame-kind proof fns.
    - Keep `on_counted`'s loop invariant as is, and prove the close fact only at the two `return`s after `close_internal`/`close_on_error`.
- **P6: h3 → quic.**
  - h3 `step`/`one_call` prove `CloseConnection{code} ==> code <= VARINT_MAX`, so `wire_code` is the identity.
  - `H3Server::apply`/`pump` ensure `close_spec == Some((true, code, []))`.
  - (b) at application level uses the §10.2.3 conversion, or proves app ⇒ `complete`.
  - **rlimit: medium.** `H3Server::pump`'s ensures is large (h3_server.rs:149-175), so the new clause goes behind a closed predicate.
- **P7: tls own-limit escapes.**
  - Name `signing_unavailable(cfg, chain)` for the INTERNAL_ERROR-where-the-spec-says-Ok branches (tls server.rs:1252, :1433), so that `allowed_tls_err` is total.
  - Then `feed` gains `Err(code) ==> allowed_tls_err(..)`. P1's `report_code` INTERNAL_ERROR branch is then dead.
  - **rlimit: medium.** `spec_drain` is sensitive in tls at rlimit 4 (4c plan). Keep the lemma in a module that does not import quic, so vest_lib's broadcast lemmas stay out of tls.
- **Must not be touched in any sub-phase:** `RecvStream::on_data` (11.79M), `datagram::pick` (12.10M), `Paths::on_timeout` (11.04M). Their acceptance comes from P3 lemmas only.

## 4. 9a pilot result (filled by the 9a plan's last task)

rlimit as reported by `--output-json --time-expanded` at `--rlimit 4`, ranked with `vt-4c-evidence/t3/rl.py`. "Before" is measured on 73cc244 in Task 1.

| fn | before | after | task |
|---|---|---|---|
| `quic::conn::Connection::close` | | | 1 |
| `quic::conn::Connection::close_internal` | | | 1 |
| `quic::conn::Connection::on_tls_alert` | | | 1 |
| `quic::conn::Connection::on_peer_params` | | | 1 |
| `quic::conn::Connection::close_on_error` (caller) | | | 1 |
| `quic::conn::Connection::on_counted` (caller) | | | 1 |
| `quic::conn::Connection::on_handshake_complete` (caller) | | | 1 |
| `quic::h3_server::H3Server::apply` (caller) | | | 1 |
| `quic::h3_server::H3Server::pump` (caller) | | | 1 |
| `quictls::server::shut` | | | 2 |
| `quictls::server::report` | | | 2 |
| `quic::crypto_stream::CryptoStream::on_crypto` | | | 3 |
| `quic::crypto_stream::CryptoStream::read` | | | 3 |
| `quic::crypto_stream::lemma_insert_tight` (new) | — | | 3 |
| `quic::conn::Connection::crypto_read` (caller) | | | 3 |
| `quic::conn::Connection::on_crypto_frame` (caller) | | | 3 |
| `quic::conn::Connection::discard` (caller) | | | 3 |
| `quictls::server::QuicServer::superseded` | | | 4 |
| `quictls::server::QuicServer::key_changes` | | | 4 |
| `quictls::server::QuicServer::on_params` | | | 4 |
| `quictls::server::key_events` | | | 4 |
| `quictls::server::QuicServer::{tls_step, feed, apply}` (callers) | | | 4 |
| `quic::conn::Connection::poll_transmit` (must not move) | | | all |
| `quic::recv_stream::RecvStream::on_data` (must not move) | | | all |

## 5. Inventory claims corrected

1. **§4.1 "on_crypto never returned PROTOCOL_VIOLATION … its ensures is already an iff"** is true, but the iff is over-strict, and rule 1 flags it.
   - `on_crypto` checks the window (`offset + len > base + MAX_CRYPTO_BUFFER`) *before* the empty-data filter. So an empty CRYPTO frame at offset > `base + 16384` closes with CRYPTO_BUFFER_EXCEEDED.
   - `on_crypto_frame` (conn.rs:1381-1395) passes empty frames straight through, so a client can trigger this. `CryptoStream::new().on_crypto(16385, &[])` returns `Err(0x0d)` on main.
   - An empty frame buffers nothing, and §7.5's MUST applies only when the buffer is exceeded. This is a sibling of 753ec2d. The inventory's draft `crypto_allowed_err` (no `len > 0`) would have proved the bug allowed.
2. **§4.1 "Add it to `core_ok` first"** (`!(level is Initial) ==> crypto_base(Initial) >= init_end`) is not a local change.
   - `core_ok` is re-proved after every `Connection` call quictls makes: `pipeline::receive` (`on_datagram`), `refeed_one_rtt`, `pipeline::transmit` (`poll_transmit`), `H3Server::{pump, on_timeout, send_response}`, `poll_cid_updates`, `on_reset_candidate`, `crypto_read`, `crypto_write`, `on_peer_params`, `on_handshake_complete`, `close`.
   - None of them ensures anything about `crypto_base`. `tx_kept` (conn.rs:3601), which frames `crx_i`, is private to `poll_transmit`'s helpers.
   - `poll_transmit` may get only a closed-predicate swap (9b), so the invariant cannot be proved in 9a or 9b. 9a removes the dead branch it was for (§3.1, P2).
3. **§4.1 "`insert` ensures `old.tight_end() && data@.len() > 0 ==> final.tight_end()`; `pop` preserves it".** Any new `insert` ensures is a new conjunct in `RecvStream::on_data`'s VC, because `on_data` calls `insert`. 9a defines and proves the tight end in crypto_stream.rs from `insert`'s and `pop`'s existing ensures instead.
4. **§4.1's `key_changes` draft** uses the exec fn `key_events(ev)` inside an ensures, and `key_events` has no ensures. 9a adds a spec over `ev.deep_view()` and a loop invariant.
5. **§4.2 / §4.3 P0** omit `on_peer_params` (C4), which `on_params`'s acceptance needs.
6. **§4.3 P0, "`close` is called from ~8 sites".** There are 5 direct callers: conn.rs:828 (`close_on_error`) and :3020 (`close_internal`), h3_server.rs:751 (`apply`) and :1032 (`pump`), and quictls server.rs:96 (`shut`). `close_internal` has 5 more: conn.rs:764 (`on_counted`), :3175, :3205, :3209, :3232. The rlimit watch list omits `H3Server::pump` (:1032), whose ensures is large; 9a adds it.
7. Minor: `superseded`'s §4.1.3 ensures is at server.rs:595-596 (the inventory says :594-595). The 753ec2d tests are at server.rs:339-353 (the inventory says :336-353).

## 6. Fidelity notes (trusted-base items, unchanged by 9a)

- `past_received` reads `crypto_inserted(k)`. After an Initial discard, `crx_i` is `CryptoStream::new_at(end)`, whose ghost record is `end` zero bytes at offset 0. So "received" after the discard means "below the end that was tight before the discard". The offsets are right; the byte values are not. No clause reads the values.
- `allowed_*` predicates are hand-written readings of RFC text, like every `rfc_*` spec (TRUSTED.md, "hand-written formalization"). Rule 1 makes the reading explicit and reviewable per handler. It does not remove the trust.
