# Phase 9: acceptance clauses and proved closes — design

**User request (2026-11-05):** "Start using acceptance clauses and proving closes."

**Why.** Most review findings so far got past Verus for the same reason: the specs said "must reject X" and never "must accept Y". For example, a legal empty CRYPTO frame closed the connection with a false PROTOCOL_VIOLATION (fixed in 753ec2d, pinned only by tests). Closes were pinned by tests too, never proved: no `Connection` ensures names the code a connection closes with.

**Input:** `docs/superpowers/specs/2026-11-05-phase-9-inventory.md` (the inventory). It lists 98 error-site rows, the vest_lib finding, close paths C1–C12, two pilots with draft clauses (§4.1, §4.2) and the task order P0–P7 with rlimit notes (§4.3). Its file:line claims were checked against `main` at 73cc244: no crate source changed since the inventory's base `ecd54a2`. §5 below lists the claims this design corrects.

**Amended 2026-11-05** after the 9a preflight (`.superpowers/sdd/2026-11-05-phase-9a-acceptance-pilot/preflight.md`) and the user directive below. Each change carries its finding id:
- **[UD]** the user directive;
- **[C1]**, **[I1]**–**[I6]**, **[m1]**–**[m11]** preflight findings, under the controller rulings in that directory's `progress.md`.

---

## 1. The rule (binding from Phase 9 on)

0. **[UD] User directive (binding, 2026-11-05):** "The entire point of this project is to try and prove as much as possible st it only assumes the same things as verus, ie rustc llvm z3 correctness. Do not take shortcuts. If it means rewriting proofs with lemmas, do it."
   - **Consequences:**
     - Near-cap fns may be restructured (split, lemma extraction, closed/opaque predicates, proof fns) to stay under `--rlimit 4`.
     - rlimit stays 4.
     - No clause is dropped, weakened or deferred to save budget.
     - Anything this design states as trusted that a phase can prove becomes proved in that phase.
     - What stays trusted is listed in §7 with the reason it cannot be proved in Verus.
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
3. **Forward rule.** The Global Constraints of every future plan carry rules 0, 1 and 2. An error path without an acceptance clause, or a close without a proved code, is an **Important** review finding.

A clause stated over an implementation number does not meet rule 1. The 753ec2d bug sat behind `crypto_end > init_end`, where `crypto_end` was a window end and not "the end of received data" (RFC 9001 §4.1.3). Each `allowed_*` names the RFC's own quantity (bytes received, bytes TLS has not consumed), or a named own-limit.

## 2. What vest already gives

`vest_lib 0.2.2`'s `Parser` trait ensures an iff against the combinator's `spec_parse` (`parse_matches_spec`). In this project only one leaf inherits it: `wire::varint::QuicVarInt` and everything built on `parse_varint`. Every other codec (quic frames, ACK, payload, headers, transport parameters, `open_one`; h3 frames, QPACK, request validation; the tls ClientHello, extensions, Finished, `HsReader`) is hand-written and proved **exact ≡** a hand-written `rfc_*` spec: `match r { Ok(..) => rfc_x(b) == Ok(..), Err(e) => rfc_x(b) == Err(e) }`.

**Consequence.** The codec half of rule 1 (`spec Some ==> Ok`) already holds everywhere, relative to each `rfc_*`. What is left is **spec fidelity**: does each `rfc_x` reject only what the RFC allows? That is a spec-only audit plus one lemma per spec, `rfc_x(..) == Err(c) ==> allowed_x(.., c)`. No exec codec ensures changes, and the lemmas add nothing to any exec fn's VC. 9a does the transport-parameter lemma, because `on_params` needs it [I6]; 9b does the rest.

## 3. Phase split

| Sub-phase | Contents | Proves |
|---|---|---|
| **9a** (plan: `docs/superpowers/plans/2026-11-05-phase-9a-acceptance-pilot.md`) | rlimit headroom [C1]; P0; P1; P2; the `core_ok` invariant [I1]; the transport-parameter lemma [I6]; the empty STREAM insert [I3] | Rule 2(a) at the `Connection` boundary and in quictls's close sinks. Rule 1 on `CryptoStream`, `on_crypto_frame` and the quictls CRYPTO steps. `superseded`'s second close proved unreachable, then removed. The measured rlimit of every touched fn, with no quic fn above 8M |
| **9b** | P3, P4 | Rule 1 for every other exact ≡ codec and h3/tls spec (spec-only lemmas); rule 2(b) through `poll_transmit` |
| **9c** | P5, P6, P7, and the quictls `apply`/`feed`/`tls_step` lift | Rule 1 and 2(a) for frame errors inside packets, h3 → quic closes, the tls own-limit escapes, and the quictls steps above `key_changes`/`on_params` |

### 3.1 9a: what it proves

**Headroom first [C1].**
- At 73cc244 four quic fns sit near the cap: `RecvStream::on_data` 11.79M, `datagram::pick` 12.10M, `Paths::on_timeout` 11.04M, and `Reassembly::insert` 6.85M, which measured up to 11.54M after unrelated conn.rs edits.
- The preflight's prototype showed cross-module Z3 perturbation: `on_data` failed at rlimit 4 after Task 3's conn.rs edits, with its own code untouched.
- 9a therefore restructures every quic fn above 8M (two-thirds of the cap), measured per query, before any clause lands. The tools are lemma extraction, helper fns per half, and closed or opaque predicates.
- From then on, "no quic fn above 8M" is every task's stop rule. A fn that cannot reach 8M without weakening a clause stops the phase with its measurements.

**P0: close code at the `Connection` boundary** (quic/src/conn.rs).
- New `pub closed spec fn close_spec(&self) -> Option<(bool, u64, Seq<u8>)>` (`self.lc.close_spec()`) and `pub open spec fn reason_cap(r: Seq<u8>) -> Seq<u8>` (the 64-byte cap that `Lifecycle::enter_closing` applies).
- `close`, `close_internal` and `on_tls_alert` ensure:
  - `old Open ==> Closing` with `close_spec() == Some((app, code, reason_cap(reason@)))`;
  - `!old Open ==>` phase and `close_spec` unchanged (the first error wins, RFC 9000 §11.1).
- `on_peer_params` (close path C4) ensures the same, with its acceptance: while the parameters are not yet known (`peer_tp_known_spec`), it closes if and only if `tp@.initial_source_connection_id != Some(client_scid_spec())` (RFC 9000 §7.3: both directions, since a mismatch or an absence is a MUST), and the code is TRANSPORT_PARAMETER_ERROR. `pub closed spec fn client_scid_spec(&self) -> Seq<u8>` and `pub closed spec fn peer_tp_known_spec(&self) -> bool` are new.

**P1: quictls close sinks** (quictls/src/server.rs).
- `shut` ensures `Closing` with `close_spec == Some((false, code, []))`. Today it proves only `!Open`.
- `report` ensures the same, with `report_code(code)`: `code` if `code <= VARINT_MAX`, else INTERNAL_ERROR.
- The comment at server.rs:120-125 drops "not an ensures".
- Acceptance for `report`'s code belongs at its caller `feed`. It needs `allowed_tls_err` over `spec_on_crypto`, including the tls own-limit predicate `signing_unavailable`, so it is **scheduled in 9c (P7)**: phasing, not a dropped clause.

**P2: Pilot A, the CRYPTO path.**
- **Tight end.**
  - `Reassembly` gets `pub closed spec fn tight(&self)` (the last window slot is a received byte) and the proof fns `lemma_insert_tight`, `lemma_pop_tight` and `lemma_end_received`. These are proof fns only: no new `insert`/`pop` ensures, and `tight` is not in `Reassembly::wf`.
  - `CryptoStream::wf` carries `reassembly().tight()`. RecvStream's does too, after the [I3] fix.
- **Opaque CRYPTO wf in `Connection` [I2].**
  - The tight atoms alone cost `poll_transmit` +17.9% (7.13M → 8.41M).
  - `wf_parts`' three `crx_*.wf()` conjuncts become one `#[verifier::opaque] spec fn crx_ok(i, h, o)` over the three fields, revealed only in the fns that touch a CRYPTO stream. Measured: `poll_transmit` 5.76M.
- **Acceptance for `on_crypto`.** `crypto_allowed_err(s, offset, len, c)`: `c == CRYPTO_BUFFER_EXCEEDED && len > 0 && offset + len > s.base + MAX_CRYPTO_BUFFER`.
  - RFC 9000 §7.5: a MUST during the handshake, and a MAY after it [m7]. The window is a named own-limit.
  - A spec lemma proves the §7.5 floor: data ending within `base + 4096` is never refused [m9].
  - The `len > 0` conjunct is a **bug the pilot finds** (§5, item 1), fixed by checking for empty data before the window check.
- **`on_crypto_frame` acceptance [I4].** `r matches Err(c) ==> c == CRYPTO_BUFFER_EXCEEDED && crypto_window_exceeded(old.crypto_base_spec(k), offset, len)`. The lift through `on_frame`/`on_counted` is **scheduled in 9c (P5)**, with the other frame errors.
- **`Connection` exports [C1].**
  - `pub closed spec fn crypto_received(&self, k, p: nat) -> bool`.
  - `crypto_end`'s ensures adds `crypto_base_spec(k) <= r` and `r > 0 ==> crypto_received(k, r - 1)`.
  - A `pub proof fn` on `Connection` was measured to tip `on_data` over the cap. The ensures on the exec accessor did not.
- **The `core_ok` invariant [I1]** (reverses the first draft's ruling, which removed the branch on an unproved argument).
  - `QuicServer::core_ok` gains `!(level is Initial) ==> conn.crypto_base_spec(Initial) >= init_end`.
  - **Establishment:**
    - `key_changes` ensures `ok && moves past Initial ==> unread(Initial) == 0`;
    - `apply`'s loop carries `crypto_end(Initial) <= crypto_base(Initial)` until `on_secrets(Handshake)`;
    - `on_peer_params`, `crypto_write` and `on_handshake_complete` ensure the Initial end unchanged and the base not lowered.
  - **Preservation:** a new `pub closed spec fn crypto_kept(&self, o: Connection) -> bool` (the Initial base does not decrease), with refl/trans lemmas as for `keeps_later`. It is ensured by every `Connection` and `H3Server` entry quictls reaches:
    - `on_datagram`, `refeed_one_rtt` and `poll_transmit`, each through one closed atom;
    - `pump`, `on_timeout`, `send_response`, `poll_cid_updates`, `on_reset_candidate`;
    - `crypto_read`, `crypto_write`, `on_peer_params`, `on_handshake_complete`, `close`.
  - `discard` gains its missing base ensures.
  - **Proved unreachable, then removed:** `superseded`'s second close (server.rs:607-613, "newly contiguous Initial bytes"). `crypto_read` gains `end <= base ==> out unchanged`. With `e <= init_end <= base`, the read returns nothing. An `assert(b@.len() == 0)` proves the branch dead before it is deleted.
  - This also proves the link that §6 of the first draft left trusted: `init_end` is the end of the Initial data received before the key change.
- **Real Initial history across the discard [m10, reworked].**
  - `discard(Initial)` restarts `crx_i` with `new_at(end)`, whose ghost record is `end` fabricated zero bytes.
  - The preflight's fix, keeping the old ghost `inserted` in the restarted `Reassembly`, breaks `Reassembly::wf` (`base <= rfc_contiguous`) whenever the window has a gap at the discard. That can happen: Initial data past `init_end` and the first Handshake packet can arrive in one datagram.
  - Instead, `CryptoStream` keeps a ghost `hist` of its real insertions. A new `restart(&mut self)` keeps `hist`, and `crypto_received` reads `hist`. The tight end is stated as `end > 0 ==> received(hist)(end - 1)`, which `restart` preserves because it keeps `end`.
- **quictls acceptance and close code.** Two spec fns:
  - `past_received(c, k, end)`: some `crypto_received(k, p)` with `p >= end`;
  - `tls_unconsumed(l, k)`: TLS's reader is non-empty, or `past_received(c, k, crypto_base(k))`.

  With them:
  - `superseded`: `!cont && old Open ==>` not at Initial, `past_received(conn, Initial, init_end)`, Closing with `(false, PROTOCOL_VIOLATION, [])`. RFC 9001 §4.1.3 bullet 1.
  - `key_changes`: `!ok && old Open ==>` the batch moves past Initial with `tls_unconsumed(Initial)`, or completes with `tls_unconsumed(Handshake)`; Closing with `(false, PROTOCOL_VIOLATION, [])`. RFC 9001 §4.1.3, the "not consumed" sentence. `unconsumed` ensures `r ==> tls_unconsumed(l, k)` [I5]. `key_events` gains ensures over `ev.deep_view()`.
  - `on_params`: `!ok && old Open ==>` `tp_allowed_err(conn, b@)`; Closing with `(false, TRANSPORT_PARAMETER_ERROR, [])`.
- **The transport-parameter lemma [I6].**
  - `tp_allowed_err`'s parse-error half is `allowed_tp_err(b)`, an RFC-side predicate over the parameter list. Some parameter at a position where the list so far parsed is one of:
    - badly formatted (§18, §20.1);
    - a duplicate (§7.4 SHOULD, chosen);
    - server-only from a client (§18.2 MUST);
    - an invalid value under §18.2's per-parameter rules (§7.4 MUST).
  - It comes with a spec-only lemma `rfc_transport_params(b, true) is Err ==> allowed_tp_err(b)`. Without it, the clause would accept any parse error.
- **The empty STREAM insert, fixed and proved [I3].**
  - `RecvStream::on_data` inserted empty data (recv_stream.rs:1336), which grows the window with unreceived slots.
  - After the Task 0 split, `on_data` skips `insert` when `data.len() == 0`, after the final-size checks: an empty FIN still sets the final size.
  - `RecvStream::wf` carries the same `Reassembly::tight()`.

**9a pilot result.** The measured rlimit of every touched fn, before and after, and each task's quic top 8, go in §4.

### 3.2 9b: spec-only lemmas and part (b)

- **P3: one `allowed_x` and one lemma per `rfc_*`** (the inventory's "spec-relative" rows, less 9a's transport parameters). The lemma is `rfc_x(..) == Err(c) ==> allowed_x(.., c)`, a disjunction of MUST / MAY-chosen / named own-limit predicates, each re-derived from the RFC text.
  - First, name a predicate for each of the 5 "chosen (no clause)" rows.
  - Recursive specs need inductive lemmas.
  - **rlimit:** none on exec fns. Each lemma is budgeted at rlimit 4 on its own. `RecvStream::on_data`'s acceptance is a lemma on `rfc_recv`/`recv_data`.
- **P4: part (b).**
  - Strengthen `close_built` with `frames[0] == close_frame_spec(app, code, reason, k)`.
  - Add a closed `close_dgram_ok(o, d)`, ensured by `build_close`. Thread it through `poll_transmit`'s Closing conjunct in place of `only_close(d@)`, then prove the pure `lemma_close_dgram_rfc` (RFC 9000 §10.2.3).
  - **rlimit [UD]:** `poll_transmit` may be restructured (split, lemma extraction, closed/opaque predicates, proof fns) to stay under `--rlimit 4`. rlimit stays 4, and no clause is dropped, weakened or deferred to save budget. 9a's `crx_ok` restructure already brought it from 7.13M to about 5.8M.
  - The wire-level lift to `pipeline::transmit`/`QuicServer::transmit` needs `live(k) ==> keys[k] is Some` for close spaces (the converse of quictls `keys_ok`). It is proved, not traded for an `out_log`-only statement [UD].

### 3.3 9c: frame errors, h3 → quic, tls own-limits, the quictls lift

- **P5: rule 1 and 2(a) for frame errors.**
  - `on_frame`/`on_ack_frame`/`on_cid_frame` gain `Err(c) ==> allowed_frame_err(..)`. `on_crypto_frame`'s clause is 9a's.
  - `on_stream_frame` gains its close triple. `on_packet`/`on_frames` lift to "some frame of p".
  - `on_counted`/`on_datagram` gain `old Open && final Closing ==> close_spec matches Some((false, c, _)) && allowed_datagram_err(..)`.
  - `close_on_error`, and `on_handshake_complete`'s INTERNAL_ERROR (named `internal_unreachable`, or proved unreachable) and 0x178.
  - **rlimit:** `on_counted`/`on_frame` are large dispatch fns. Per-arm proof fns and a closed `allowed_frame_err` keep them under 8M.
- **P6: h3 → quic.**
  - h3 `step`/`one_call` prove `CloseConnection{code} ==> code <= VARINT_MAX`, so `wire_code` is the identity.
  - `H3Server::apply_one`/`pump` ensure `close_spec == Some((true, code, []))`.
  - (b) at application level uses the §10.2.3 conversion, or proves app ⇒ `complete`.
- **P7: tls own-limit escapes.** Name `signing_unavailable(cfg, chain)` for the INTERNAL_ERROR-where-the-spec-says-Ok branches (tls server.rs:1252, :1433), so that `allowed_tls_err` is total. Keep the lemma in a module that does not import quic.
- **The quictls `apply`/`feed`/`tls_step` acceptance is scheduled here, not deferred [I4].**
  - `feed`'s clause needs P7's `allowed_tls_err`.
  - `apply`'s clause is a disjunction over `key_changes`' reason (9a), `PeerParams`' `tp_allowed_err` (9a) and `on_complete`'s reason, which comes from P5's `on_handshake_complete` clause.
  - `tls_step` composes them.
  - 9c's plan carries all three as tasks.

## 4. 9a pilot result (filled by the 9a plan's tasks)

rlimit as reported by `--output-json --time-expanded` at `--rlimit 4`. The per-fn number from `vt-4c-evidence/t3/rl.py` is a sum over that fn's queries. Headroom is read per query (`--profile`), as the preflight measured it. "Before" is 73cc244, measured in Task 0. Every task also records the quic top 8 by rlimit. **Stop rule: no quic fn above 8M after any task.**

| fn | before | after | task |
|---|---|---|---|
| `quic::recv_stream::RecvStream::on_data` | 11790727 | 2202435 (T0) | 0, 6 |
| `quic::datagram::pick` | 12095817 | 2730524 (T0) | 0 |
| `quic::path::Paths::on_timeout` | 11043766 | 1573567 (T0) | 0 |
| `quic::reassembly::Reassembly::insert` | 6848875 | 2077934 (T0) | 0 |
| `quic::conn::Connection::poll_transmit` | 7133799 | 5762297 (T3) | 3, 3b |
| `quic::conn::Connection::on_datagram` | 1717635 | 2823844 (T3) | 3, 3b |
| `quic::conn::Connection::close` | 743986 | 688163 (T1) | 1 |
| `quic::conn::Connection::close_internal` | 45734 | 86724 (T1) | 1 |
| `quic::conn::Connection::on_tls_alert` | 226738 | 193172 (T1) | 1 |
| `quic::conn::Connection::on_peer_params` | 671420 | 616702 (T1) | 1, 3b |
| `quic::conn::Connection::close_on_error` (caller) | 414859 | 423068 (T1) | 1 |
| `quic::conn::Connection::on_counted` (caller) | 1078483 | 1399145 (T1) | 1 |
| `quic::conn::Connection::on_handshake_complete` | 1328880 | 1153238 (T1) | 1, 3b |
| `quic::h3_server::H3Server::apply_one` (caller) [m2] | 313607 | 203717 (T1) | 1 |
| `quic::h3_server::H3Server::pump` | 183852 | 184389 (T1) | 1, 3b |
| `quictls::server::shut` | 4171 | 7833 (T2) | 2 |
| `quictls::server::report` | 6447 | 15511 (T2) | 2 |
| `quic::crypto_stream::CryptoStream::on_crypto` | 42037 | 57284 (T3) | 3 |
| `quic::crypto_stream::CryptoStream::read` | 14538 | 15576 (T3) | 3 |
| `quic::reassembly::Reassembly::lemma_insert_tight` (new) | — | 266316 (T3) | 3 |
| `quic::conn::Connection::crypto_read` | 1407354 | 1404386 (T3) | 3, 3b |
| `quic::conn::Connection::crypto_end` | 42704 | 65508 (T3) | 3 |
| `quic::conn::Connection::on_crypto_frame` | 356795 | 375682 (T3) | 3 |
| `quic::conn::Connection::discard` | 464457 | 537731 (T3) | 3, 3b |
| `quic::conn::Connection::crypto_write` | 261459 | | 3b |
| `quic::pipeline::{receive, transmit, refeed_one_rtt}` | 37596, 124540, 44385 | | 3b |
| `quic::h3_server::H3Server::{on_timeout, send_response}` | 31317, 203780 | | 3b |
| `quictls::server::QuicServer::{receive, transmit, accept, tls_step, feed, apply, on_secrets}` | 327717, 271997, 3631736, 214332, 681625, 93837, 1153995 | | 3b |
| `quic::tp::lemma_tp_err_allowed` (new) | — | | 4 |
| `quictls::server::QuicServer::superseded` | 88699 | | 3b, 5 |
| `quictls::server::QuicServer::key_changes` | 103831 | | 3b, 5 |
| `quictls::server::QuicServer::on_params` | 80863 | | 5 |
| `quictls::server::QuicServer::unconsumed` | 31707 | | 5 |
| `quictls::server::key_events` | 77403 | | 3b |

Task 0 (rlimit headroom) evidence: `vt-9a-evidence/t0` (before: 423878b, whose code is 73cc244's; 73cc244..423878b changes docs only) and `vt-9a-evidence/t0b` (after). quic top 8 before (1201 verified, 0 errors): `datagram::pick` 12095817, `RecvStream::on_data` 11790727, `Paths::on_timeout` 11043766, `frame::lemma_body_roundtrip_a` 9825619, `Streams::poll_max_streams` 8623542, `Connection::send_path_datagram` 8323049, `Reassembly::pop` 8184809, `streams::poll_stream` 7820849; the first seven are above 8M. Each of the seven was split into private helpers (requires/ensures of every existing pub/crate fn unchanged); the new helpers after T0: `RecvStream::data_gate` 152269, `RecvStream::data_buffer` 6321936, `datagram::pick_step` 877778, `Paths::abandon_at` 4220291, `Paths::lemma_lowest_expired` 165595, `frame::lemma_body_roundtrip_{a,r,s}` 496237/158707/550740, `Reassembly::fill` 6116767, `Reassembly::run_end` 45616, `Reassembly::pop` 748360 (was 8184809), `streams::lemma_max_streams_kept` 1448086, `Streams::poll_max_streams` 3352955, `Connection::lemma_idle_timers` 67165, `Connection::send_path_datagram` 5070344.

quic top 8 after Task 0 (`--rlimit 4`, 1212 verified, 0 errors): `Connection::add_space_packet` 7595647, `Streams::poll_max_data` 7553000, `streams::poll_stream` 7402168, `Connection::poll_transmit` 7133799, `Streams::recv_op_at` 6812261, `recv_stream::lemma_same_ranges` 6750564, `header::serialize_long_header` 6542112, `RecvStream::data_buffer` 6321936. `lemma_same_ranges` is untouched and its query text is byte-identical, but it rose from 212497: replayed alone, both the before and the after query cost 7454847, so the 212497 came from the state the `recv_stream` module's solver had reached by then, which the `on_data` split changed. Spinning off `on_data` raised it to 7437501; it cannot be spun off itself (Verus panics on `hide(rfc_recv_step)` in a spun-off fn).

Task 1 (close code at the `Connection` boundary) evidence: `vt-9a-evidence/t1` (before: `t1/base` at bbb5d1d, identical to T0's after; after: `t1/after`). quic top 8 after Task 1 (`--rlimit 4`, 1212 verified, 0 errors; quictls 43 verified, 0 errors): `Connection::add_space_packet` 7595647, `Streams::poll_max_data` 7553000, `streams::poll_stream` 7402168, `Connection::poll_transmit` 7133799, `Streams::recv_op_at` 6812261, `recv_stream::lemma_same_ranges` 6750564, `header::serialize_long_header` 6542112, `RecvStream::data_buffer` 6321936 (unchanged from T0). `on_counted` rose 1078483 → 1399145, as the preflight measured. T0 review m1: without the `forall|q2|` ensures of `Paths::lemma_lowest_expired` (and its `assert forall`), `abandon_at` rises 4220291 → 5033281 (`lemma_lowest_expired` 165595 → 34993, `on_timeout` 1573567 → 1228638), so the conjunct stays: it carries `abandon_at`'s rlimit, not its provability (`t1/m1-noforall`). T1 fix round (review I1): `on_peer_params` gained the converse (`old Open && !peer_tp_known ==> (!final Open <==> isci != Some(client_scid))`) and the §7.3 absence clause; quic top 8 unchanged (`t1/fix1`).

Task 2 (close sinks `shut` and `report`) evidence: `vt-9a-evidence/t2` (`run1`). quictls 43 verified, 0 errors; top 8: `QuicServer::accept` 3631736, `on_secrets` 1153995, `feed` 608838, `receive` 341945, `lemma_fed` 327287, `transmit` 274321, `send_response` 255725, `lemma_push` 252882; `shut` 7833, `report` 15511. quic re-run (1212 verified, 0 errors): top 8 unchanged from T1.

Task 3 (tight CRYPTO end, `crypto_allowed_err`, the empty-CRYPTO fix, opaque `crx_ok`) evidence: `vt-9a-evidence/t3` (`final`). quic 1219 verified, 0 errors; quictls 43 verified, 0 errors. quic top 8 after Task 3: `Streams::poll_max_data` 7553000, `streams::poll_stream` 7402168, `Connection::add_space_packet` 7185031, `Streams::recv_op_at` 6812261, `recv_stream::lemma_same_ranges` 6750564, `header::serialize_long_header` 6542112, `RecvStream::data_buffer` 6321936, `Reassembly::fill` 6116767. `poll_transmit` falls 7133799 → 5762297 and `on_datagram` rises 1717635 → 2823844, both as the preflight's `opaque` run measured; `Reassembly::insert` 2077934 → 1816357, `RecvStream::on_data` 2202435 (unchanged), `Connection::accept` 368325 → 334867. New proof fns: `Reassembly::{lemma_new_tight, lemma_pop_tight, lemma_end_received}` 6532/9923/9490, `CryptoStream::lemma_end_received` 4914, `crypto_stream::lemma_crypto_floor` 4893, `crypto_stream::lemma_crypto_allowed_err_rejects` 4294. `lemma_insert_tight` needs `hide(Reassembly::wf)`, `hide(rfc_received)` and `hide(rfc_contiguous)`: with none it exceeds rlimit 4 (`t3/try1`), and so it does with only the `wf` hide (`t3/try3`).

## 5. Inventory claims corrected

1. **§4.1 "on_crypto never returned PROTOCOL_VIOLATION … its ensures is already an iff"** is true, but the iff is over-strict, and rule 1 flags it.
   - `on_crypto` checks the window (`offset + len > base + MAX_CRYPTO_BUFFER`) *before* the empty-data filter. So an empty CRYPTO frame at offset > `base + 16384` closes with CRYPTO_BUFFER_EXCEEDED.
   - `on_crypto_frame` (conn.rs:1381-1395) passes empty frames straight through, so a client can trigger this.
   - An empty frame buffers nothing, and §7.5's MUST applies only when the buffer is exceeded. §19.6's offset bound stays in frame decoding. This is a sibling of 753ec2d.
2. **§4.1 "Add it to `core_ok` first"** is not a local change.
   - `core_ok` is re-proved after every `Connection` call quictls makes, and none of those calls ensures anything about `crypto_base` today. `discard` does not even ensure its own base.
   - 9a proves the invariant anyway (§3.1, [I1]) with a `crypto_kept` frame on each entry.
3. **§4.1 "`insert` ensures `old.tight_end() && data@.len() > 0 ==> final.tight_end()`".** Any new `insert` ensures is a new conjunct in `RecvStream::on_data`'s VC. 9a states the tight end as `Reassembly` proof fns over `insert`'s and `pop`'s existing ensures.
4. **§4.1's `key_changes` draft** uses the exec fn `key_events(ev)` inside an ensures, and `key_events` has no ensures. 9a adds a spec over `ev.deep_view()` and a loop invariant.
5. **§4.2 / §4.3 P0** omit `on_peer_params` (C4), which `on_params`'s acceptance needs.
6. **§4.3 P0, "`close` is called from ~8 sites".** There are 5 direct callers:
   - conn.rs:828 (`close_on_error`) and :3020 (`close_internal`);
   - h3_server.rs:751, in `apply_one` (:670) [m2], and :1032 (`pump`);
   - quictls server.rs:96 (`shut`).

   `close_internal` has 5 more: conn.rs:764, :3175, :3205, :3209 and :3232.
7. Minor: `superseded`'s §4.1.3 ensures is at server.rs:595-596 (the inventory says :594-595). The 753ec2d tests are at server.rs:339-353 (the inventory says :336-353).
8. **[C1] §4.3's rlimit notes treat each fn's budget as local.** It is not. Adding one `pub proof fn` to conn.rs pushed `RecvStream::on_data` (recv_stream.rs, unedited) past 12M. `Reassembly::insert` (unedited) read anywhere from 6.85M to 11.54M depending on conn.rs content. Headroom must be made (Task 0), not assumed.

## 6. Fidelity notes

- **[I1] Proved in 9a, no longer trusted:** `init_end` is the end of the Initial data received before the key change. `superseded`'s clause is then exact about the RFC's "end of previously received data".
- **[m10] Proved in 9a, no longer trusted:** after an Initial discard, `crypto_received` reads the real insertion history (`hist`), not `new_at`'s fabricated record.
- **Trusted, unchanged:** `allowed_*` predicates are hand-written readings of RFC text, like every `rfc_*` spec (TRUSTED.md, "hand-written formalization"). No tool can prove that a formula means what an English sentence means. Rule 1 makes each reading explicit and reviewable per handler.

## 7. Trust-base follow-ups [UD]

**Scheduled after 9c,** each as its own sub-phase with a plan:
1. **`decode_crate` functional:** prove the CT front end's JSON/schema decoder (`crates/ctmir/src/schema.rs`) a function of its input with a stated inverse against `json::print`. It then leaves TRUSTED's "CT front end: the JSON and schema specs" row.
2. **`mir_run` fuel monotonicity:** prove that more fuel never changes a Done/Panic result (`ctmir::sem`'s `mir_run`, used by 8d's evaluator gate). This is proved about `sem.rs` from outside it; `sem.rs` itself is not edited.
3. **quic packet protection and tls key-schedule glue as CT roots** (RFC 9001 §9.5, today "not met" in TRUSTED): add `quic::{hp, aead, protect, pn}` and tls's `hkdf_expand_label` assembly, transcript and Finished paths to the CT manifest, and prove them through `theorem_ct_mir`.
4. **Cost bounds for network-driven fns:** 8b's unmet DoS aim. Every frame, payload and field-section decoder is `none` in `cost 19/36`. Bound each, so that one datagram's work has a proved step bound.
5. **`respond`'s Busy ordering proved:** today the stop-at-first-`Busy` path of `Conn::respond` is untested and unproved (4c plan, Note). Prove it in verified code, or move the ordering out of the shell into verified code.
6. **never-Stuck for bounded roots via their cost proofs:** 8d gives executable evidence only on exercised inputs. For roots with a cost bound, a proof that `mir_run` reaches Done or Panic within the bound for every `wt_args` input gives never-Stuck outright.

**Stays trusted, with why it cannot be proved in Verus:**
- **Timing below MIR.** Verus reasons about the semantics of Rust code, not about the instructions LLVM emits or the cycles a CPU spends. A MIR-level constant-time proof cannot see codegen turning a masked select into a branch (7a's `ct_mask` case). The binary gate and the dudect tests are checks, not proofs.
- **Memory zeroisation.** Rust's and Verus's semantics have no notion of the bytes a value leaves in memory after it is dropped or moved, and the compiler may remove stores to dead memory. "The secret is gone from RAM" cannot be stated, let alone proved.
- **The MIR semantics and leakage model** (`ctmir::sem`, `sem_subset`). They are the definition the CT theorem is relative to. Proving them would need a formal semantics of rustc's MIR to relate them to, and Verus has none: it trusts rustc rather than modelling it.
- **The dumper** (`ct-dump`, tools/ct-driver). It runs inside rustc (`rustc_private`) to read rustc's internal MIR, which no Verus spec describes. It is the same kind of trust as rustc itself: an unverified bridge out of the compiler, kept decision-free.
