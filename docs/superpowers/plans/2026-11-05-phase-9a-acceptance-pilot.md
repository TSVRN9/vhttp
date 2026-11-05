# Phase 9a: Acceptance Clauses and Proved Closes, Pilot — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:**
- Make rlimit headroom in quic.
- Prove the close code at the `Connection` boundary and in quictls's close sinks.
- Put RFC-cited acceptance clauses on `CryptoStream`, `on_crypto_frame`, the transport-parameter spec and the quictls CRYPTO steps.
- Prove the Initial-CRYPTO invariant behind `superseded`.
- Fix and prove the two empty-frame bugs.
- Measure what all of this costs.

The lift through `on_frame`/`on_counted` and quictls `apply`/`feed`/`tls_step` is scheduled in 9c (design §3.3) [I4].

**Architecture:**
- **Task 0** splits every quic fn above 8M so that later clauses have room [C1].
- **Tasks 1–2:** new closed specs on `Connection` (`close_spec`, `client_scid_spec`) give the exact close triple through `close`/`close_internal`/`on_tls_alert`/`on_peer_params` and quictls `shut`/`report`.
- **Task 3:** a tight-end predicate on `Reassembly` (proof fns only) enters `CryptoStream::wf`, behind an opaque `crx_ok` in `Connection` [I2]. `Connection::crypto_end` exports `crypto_received` [C1].
- **Task 3b** proves `core_ok`'s Initial-base invariant with a `crypto_kept` frame on every entry quictls reaches. It then deletes `superseded`'s second close as proved unreachable [I1].
- **Tasks 4–5** state the quictls clauses over RFC quantities, with an RFC-side transport-parameter predicate and lemma [I6].
- **Task 6** fixes the empty STREAM insert [I3].

**Tech Stack:** Verus 0.2026.10.04.426d8b0 (rustc 1.98.1), vstd `=0.0.0-2026-10-04-0306`, vest_lib `=0.2.2`, duvet 0.4.3. No new dependency.

**Spec:** `docs/superpowers/specs/2026-11-05-phase-9-acceptance-and-closes-design.md`: §1 the rule (with the user directive), §3.1 what 9a proves, §4 the result table these tasks fill, §5 inventory corrections, §7 trust-base follow-ups. Its input, `docs/superpowers/specs/2026-11-05-phase-9-inventory.md`, gives the error-site rows and the close paths C1–C12. The preflight (`.superpowers/sdd/2026-11-05-phase-9a-acceptance-pilot/preflight.md`, prototype evidence in `<scratch>/vt-9a-evidence/preflight/`) measured Tasks 1–3 and part of Task 5.

`<scratch>` is `/home/tavern/Projects/rust/web-server/.worktrees`. Evidence goes in `<scratch>/vt-9a-evidence/tN/` (never /tmp). Branch `phase-9a` in `<scratch>/wt-9a`, from `main` at 73cc244.

**Amended 2026-11-05.** Each change carries its id:
- **[UD]** the user directive;
- **[C1]**, **[I1]**–**[I6]**, **[m1]**–**[m11]** the preflight findings, under the controller rulings in `progress.md` next to the preflight.

## Global Constraints

- **[UD] User directive (binding):** "The entire point of this project is to try and prove as much as possible st it only assumes the same things as verus, ie rustc llvm z3 correctness. Do not take shortcuts. If it means rewriting proofs with lemmas, do it."
- **Rule 1, acceptance (design §1):** every verified fn that can return an error carries `Err(code) ==> allowed_err(state, input, code)`.
  - `allowed_err` is one spec fn per handler, RFC-cited, and a disjunction of: errors the RFC requires (MUST); errors it permits (MAY/SHOULD "treat as a connection error") where we chose to raise them; our own named limits (Busy, full tables) as visible named predicates.
  - Codecs: `spec_parse(b) is Some ==> res is Ok`.
  - A bool-signalling step (`cont`/`ok`) carries `!ok && old Open ==> allowed_x(..)`.
- **Rule 2, proved close:**
  - (a) the error path leaves the connection Closing with that exact code (`close_spec`);
  - (b) in Closing, if a datagram is emitted, it contains CONNECTION_CLOSE with that code at the right key level (RFC 9000 §10.2.3). The words are "if emitted" because amplification and pacing can block sends. (b) is 9b's.
- **Rule 3, forward:** every future plan's Global Constraints carry the directive and rules 1 and 2. An error path without an acceptance clause, or a close without a proved code, is an **Important** review finding.
- Verify everything at `--rlimit 4`; a fresh target fails in vstd at rlimit 4, so run a default verify first. Force a real re-run by deleting the crate's fingerprint, deps and verus-partial dirs under target. Record the measured rlimit of every touched fn.
  - Recipe, per crate `<c>`, with `CARGO_TARGET_DIR=<scratch>/vt-9a-evidence/tN/target`:
    ```bash
    (cd crates/<c> && cargo verus verify)                     # default rlimit, warms vstd (first run on a target only)
    cargo clean -p <c>; rm -rf $CARGO_TARGET_DIR/verus-partial/*/.fingerprint/<c>-*
    (cd crates/<c> && cargo verus verify -- --rlimit 4 --output-json --time-expanded) > $E/<c>.json 2> $E/<c>.err
    python3 -I <scratch>/vt-4c-evidence/t3/rl.py $E/<c>.json <qualified fn names…>   # verification-results, top 6, the named fns, FAIL rows
    ```
  - Pass qualified names (`H3Server::apply_one`, not `apply`): rl.py matches by `endswith('::'+name)` (preflight, Global Constraints note).
  - rl.py's per-fn number is a sum over that fn's queries. Read headroom per query with `--profile`, as the preflight did, in Task 0 and wherever a fn is near 8M [I2].
  - quictls depends on quic: after any quic edit, run the recipe for quic and then for quictls.
  - Use `hide(rfc_received)`/`hide(rfc_contiguous)` in a new proof context only where it lowers the measured rlimit [m1]. The preflight measured `hide` raising one lemma from 71.7K to 4.48M.
- **[UD] replaces the first draft's "Must not be touched" list and the "poll_transmit closed-predicate swap only" rule:** near-cap fns may be restructured (split, lemma extraction, closed/opaque predicates, proof fns) to stay under --rlimit 4; rlimit stays 4; no clause is dropped, weakened or deferred to save budget.
  - **Stop rule [I2]:** after every task, record the quic top 8 by rlimit (rl.py) in design §4's evidence and in the task's evidence directory. **No quic fn may be above 8M after a task.** If one is, restructure it in that task. If it cannot reach 8M without weakening a clause, stop and report the per-query measurements.
  - A restructure keeps every `requires`/`ensures` of the restructured pub or crate-visible fn textually unchanged (diff the signatures), unless a task here adds to it.
- Never edit crates/crypto/src, crates/ctcore/src, crates/ctmir/src/sem.rs.
- No `assume(`, `external_body`, `verifier::external`, `axiom` anywhere under crates/ outside crates/crypto/src, in code or comments.
  - Check: the line grep `grep -rnE 'assume[[:space:]]*\(|external_body|verifier[[:space:]]*(::|\()[[:space:]]*external|\baxiom\b' crates --include='*.rs' | grep -v '^crates/crypto/src/'` and the multi-line `grep -rlPz '\bassume\s*\(' crates --include='*.rs' | grep -v '^crates/crypto/src/'` both print nothing. Both print nothing on 73cc244 (checked 2026-11-05).
- vest_lib's default broadcast lemmas leak into any crate importing quic; tls stays free of quic.
  - 9a edits no tls file.
- verify.sh's final line stays byte-identical: `verify.sh: all crates verified, duvet ok, ct ok (10 declassify), cost 19/36, escapes accounted (0), binary ok (49 fns)`.
- cargo test --workspace stays green (902 tests at main 73cc244).
  - Plus this plan's new tests: 904 after Task 1, 907 after Task 3, 909 after Task 5, 910 after Task 6. 0 warnings in `cargo build` and `cargo test`.
- No attribution lines in commits.
- **Duvet:** every new spec fn and ensures that states an RFC condition carries `//= https://www.rfc-editor.org/rfc/rfcNNNN#section-X` plus a contiguous `//#` quote copied verbatim from `.duvet/specifications/www.rfc-editor.org/rfc/`.
  - `.duvet/specifications` and `.duvet/requirements` are git-ignored and missing in wt-9a. Copy both once from `/home/tavern/Projects/rust/web-server/.duvet/`.
  - Per task: `python3 -I <scratch>/qchk/check_quotes.py --spec-dir .duvet/specifications/www.rfc-editor.org/rfc <touched files>` prints `N citations, 0 bad` (run it explicitly on line-split quotes [m8]), and `duvet report` exits 0.
- **Mutations:** each listed mutation, applied alone to the committed tree, must fail on the named postcondition, precondition, assertion or test, not on rlimit. Restore with `git checkout -- <file>`, then re-run the default verify of that crate.
- **Spec fns on `Connection` are `closed`** (as `phase_spec`, `out_log`). quictls sees them through ensures on exec fns.
  - Prefer a fact on an exec accessor's ensures over a `pub proof fn` in conn.rs [C1]. A `pub proof fn` requiring `Connection::wf` was measured to push `RecvStream::on_data` over the cap.
  - Any proof fn a task adds to conn.rs is measured against the stop rule in that task.

## Review Focus

1. **An empty CRYPTO or STREAM frame at any offset** never closes the connection and never grows a buffer. For CRYPTO that covers below the read offset, inside the window, past the window, and after the key change. Task 3: `crypto_empty_past_window_ok`, `crypto_empty_keeps_end`, `empty_initial_past_window_ok`. Task 6: `empty_stream_frame_keeps_window`. Already pinned: `empty_gapped_initial_ok`, `empty_initial_after_switch_ok`.
2. **An Initial frame straddling `init_end` by one byte** after the key change closes with 0x0a; one ending exactly at `init_end` does not (already pinned by `initial_retransmit_after_switch_ok`). Task 5: `initial_straddle_after_switch_pv` [m4].
3. **Two errors in one flight:** the first error's code is the one sent. Task 5: `trailing_bytes_before_bad_tp_pv` (0x0a, not 0x08), with mutation T5-M5 [m11]. Task 1: `alert_after_close_keeps_code`.
4. **TLS alert 0xff** closes with 0x1ff, the top of the CRYPTO_ERROR range (RFC 9001 §4.8). Task 1: `tls_alert_top_of_range`.
5. **A CRYPTO frame ending exactly at `base + 16384`** is accepted; one byte more closes with 0x0d. Pinned by `crypto_limit`, which must stay green after Task 3's reorder. The `base + 4096` floor is proved (Task 3, [m9]).

---

## File Structure

- `crates/quic/src/{recv_stream.rs, datagram.rs, path.rs, reassembly.rs}` (Task 0): restructure only. reassembly.rs also gets the tight-end proof fns (Task 3). recv_stream.rs also gets the empty-insert fix (Task 6).
- `crates/quic/src/conn.rs` (Tasks 1, 3, 3b): the close specs and ensures; `crx_ok`, `crypto_received`, the `crypto_end` ensures, `on_crypto_frame`'s clause; `crypto_kept` and its frames.
- `crates/quic/src/crypto_stream.rs` (Tasks 3, 3b): `tight` in `wf`, `crypto_window_exceeded`, `crypto_allowed_err`, the floor lemma, the empty-first reorder; ghost `hist` and `restart`.
- `crates/quic/src/{h3_server.rs, pipeline.rs}` (Task 3b): `crypto_kept` ensures.
- `crates/quic/src/tp.rs` (Task 4): `allowed_tp_err` and its lemma (spec-only).
- `crates/quictls/src/server.rs` (Tasks 2, 3b, 5).
- Tests: `crates/quic/tests/{conn_rx.rs, crypto_stream.rs, recv_stream.rs}`, `crates/quictls/tests/server.rs`.
- `docs/superpowers/specs/2026-11-05-phase-9-acceptance-and-closes-design.md` §4 (every task fills its rows).

---

### Task 0: rlimit headroom in quic [C1]

**Files:**
- Modify (restructure only; no `requires`/`ensures` text change):
  - `crates/quic/src/recv_stream.rs` (`on_data` :1214);
  - `crates/quic/src/datagram.rs` (`pick` :523);
  - `crates/quic/src/path.rs` (`Paths::on_timeout` :1147);
  - `crates/quic/src/reassembly.rs` (`insert` :333);
  - any other quic fn the baseline shows above 8M.
- Modify: design doc §4 ("before" column).

**Interfaces:**
- Consumes: nothing new.
- Produces: the same pub/crate API with every quic fn at or below 8M at rlimit 4. Task 6 relies on `on_data` being split into a flow-control/final-size half and a buffering half (private helper fns, names the implementer's).

- [ ] **Step 1: Baseline.**
  - Run the recipe for `quic` and `quictls` on 73cc244 (`E=…/t0`).
  - Record design §4's "before" column and the quic top 8.
  - Expected: 0 errors. `on_data` 11790727, `pick` about 12.10M, `on_timeout` about 11.04M, `insert` 6848875; the preflight reproduced the first and last exactly.
- [ ] **Step 2: Per-query profile** of each fn above 8M and of `insert`. Run `--profile` on the fn's module. Note the costliest query and what it instantiates. Keep the output in `t0/profile-<fn>.txt`.
- [ ] **Step 3: Restructure.**
  - Use lemma extraction: move loop-body maintenance and the closing assertions into `proof fn`s with explicit `requires`/`ensures`.
  - Split `on_data` into a flow-control/final-size half and a buffering half, and `pick` and `on_timeout` per phase of their loops.
  - Spin each new helper off (`#[verifier::spinoff_prover]`).
  - Do not weaken or drop any clause. Do not raise the rlimit.
- [ ] **Step 4: Verify.**
  - Run the recipe for `quic` and `quictls` (`E=…/t0b`).
  - Expected: 0 errors; every quic fn ≤ 8M (rl.py top 8), and the costliest query of each restructured fn ≤ 8M (`--profile`).
  - If a fn cannot reach 8M: stop, and report the per-query table.
- [ ] **Step 5: Full checks, then commit.**
  - Checks: `cargo build && cargo test --workspace`, 902 passed, 0 warnings; `verify.sh`'s exact line; escape grep 0; `duvet report` exit 0.
  - If a moved `//=` block's file changed, run the quote check on it.
  ```bash
  git add crates/quic/src docs/superpowers/specs/2026-11-05-phase-9-acceptance-and-closes-design.md
  git commit -m "refactor(quic, 9a T0): split RecvStream::on_data, datagram::pick, Paths::on_timeout and Reassembly::insert below 8M at rlimit 4 (no clause changed)"
  ```
- [ ] **Step 6: Mutation.** **T0-M1:** in one extracted proof fn, drop one `ensures` conjunct that its caller uses. Expected: the caller's postcondition or a later assertion fails, which shows that the extraction carries the proof.

### Task 1: Close code at the `Connection` boundary (P0)

**Files:**
- Modify: `crates/quic/src/conn.rs`:
  - new spec fns next to `phase_spec` (:285);
  - `close_internal` :3009-3021, `close` :3025-3053, `on_peer_params` :3160-3184, `on_tls_alert` :3222-3233 (line numbers as at 73cc244; Task 0 may have moved them).
- Test: `crates/quic/tests/conn_rx.rs`.
- Modify: design doc §4 (Task 1 rows).

**Interfaces:**
- Consumes: `Lifecycle::close_spec` and `enter_closing`'s ensures (lifecycle.rs:333, :412-454); `HandshakeIds::check_peer_tp`'s iff (handshake.rs:364-367).
- Produces (`quic::conn`):
  - `pub open spec fn reason_cap(r: Seq<u8>) -> Seq<u8>` = `r.take(if r.len() > 64 { 64int } else { r.len() as int })`. This is a free fn.
  - `impl Connection`:
    - `pub closed spec fn close_spec(&self) -> Option<(bool, u64, Seq<u8>)>` = `self.lc.close_spec()`;
    - `pub closed spec fn client_scid_spec(&self) -> Seq<u8>` = `self.ids@.client_scid`.
  - `close(&mut self, code: u64, app: bool, reason: &[u8], now: u64)` adds:
    ```
    old(self).phase_spec() is Open ==> final(self).close_spec() == Some((app, code, reason_cap(reason@))),
    !(old(self).phase_spec() is Open) ==> final(self).close_spec() == old(self).close_spec(),
    ```
  - `close_internal(&mut self, code: u64)` and `on_tls_alert(&mut self, alert: u8, now: u64)` add the block below, with `C` = `code` and `(CRYPTO_ERROR_BASE + alert as u64) as u64` respectively:
    ```
    old(self).phase_spec() is Open ==> final(self).phase_spec() is Closing
        && final(self).close_spec() == Some((false, C, Seq::<u8>::empty())),
    !(old(self).phase_spec() is Open) ==> final(self).phase_spec() == old(self).phase_spec()
        && final(self).close_spec() == old(self).close_spec(),
    ```
  - `on_peer_params(&mut self, tp: &TransportParams, now: u64)` adds:
    ```
    old(self).phase_spec() is Open && !(final(self).phase_spec() is Open) ==> {
        &&& final(self).phase_spec() is Closing
        &&& final(self).close_spec() == Some((false, TRANSPORT_PARAMETER_ERROR, Seq::<u8>::empty()))
        &&& tp@.initial_source_connection_id != Some(old(self).client_scid_spec())
    },
    !(old(self).phase_spec() is Open) ==> final(self).phase_spec() == old(self).phase_spec()
        && final(self).close_spec() == old(self).close_spec(),
    ```

- [ ] **Step 1: Add the regression tests** to `crates/quic/tests/conn_rx.rs`, using its `conn()` and `peer_params_failed()`:
  ```rust
  #[test]
  fn alert_after_close_keeps_code() {
      let mut c = peer_params_failed();
      c.on_tls_alert(0x28, 2);
      assert_eq!(c.phase(), Phase::Closing);
      assert_eq!(c.close_info(), &Some((false, 0x08, vec![])));
  }

  #[test]
  fn tls_alert_top_of_range() {
      let mut c = conn();
      c.on_tls_alert(0xff, 1);
      assert_eq!(c.close_info(), &Some((false, 0x1ff, vec![])));
  }
  ```
  - Run `cargo test -p quic --test conn_rx`. Expected: PASS. These pin what the new ensures prove.
- [ ] **Step 2: Add the Interfaces items.**
  - On `close`: `//= https://www.rfc-editor.org/rfc/rfc9000#section-10.2.1` with `//# An endpoint enters the closing state after initiating an immediate` / `//# close.`.
  - On `on_tls_alert`: RFC 9001 §4.8, `//# A TLS alert is converted into a QUIC connection error.  The` through `//# [QUIC-TRANSPORT].` (rfc9001.txt:883-886).
  - On `on_peer_params`: RFC 9000 §7.3, the "TRANSPORT_PARAMETER_ERROR or PROTOCOL_VIOLATION:" block as at handshake.rs:354-360.
- [ ] **Step 3: Verify.**
  - Run the recipe for `quic` then `quictls` (`E=…/t1`). Expected: 0 errors.
  - Record `close`, `close_internal`, `on_tls_alert`, `on_peer_params`, `close_on_error`, `on_counted`, `on_handshake_complete`, `H3Server::apply_one` [m2], `H3Server::pump`, and the quic top 8.
  - The preflight measured `on_counted` going from 1.08M to 1.40M.
  - The stop rule applies.
- [ ] **Step 4: Full checks, then commit.**
  - Checks: tests 904, 0 warnings; `verify.sh`'s exact line; escape grep 0; quote check on conn.rs; `duvet report` exit 0.
  ```bash
  git add crates/quic/src/conn.rs crates/quic/tests/conn_rx.rs docs/superpowers/specs/2026-11-05-phase-9-acceptance-and-closes-design.md
  git commit -m "feat(quic, 9a T1): Connection::close_spec; close, close_internal, on_tls_alert and on_peer_params prove the close code (RFC 9000 §10.2.1, §7.3; RFC 9001 §4.8)"
  ```
- [ ] **Step 5: Mutations.** Each alone, then `git checkout -- crates/quic/src/conn.rs`.
  - **T1-M1:** `on_tls_alert` calls `self.close_internal(alert as u64)`. Expected: its `close_spec` postcondition fails, and so does `tls_alert_closes`.
  - **T1-M2:** `close` passes `!app` to `enter_closing`. Expected: `close`'s `close_spec` postcondition fails.
  - **T1-M3:** `on_peer_params` calls `self.close_internal(PROTOCOL_VIOLATION)`. Expected: its `close_spec` postcondition fails.

### Task 2: quictls close sinks `shut` and `report` (P1)

**Files:**
- Modify: `crates/quictls/src/server.rs:84-153`.
- Modify: design doc §4 (Task 2 rows).

**Interfaces:**
- Consumes: Task 1's `close_spec`, and the `close` and `on_tls_alert` ensures.
- Produces (`quictls::server`, private):
  - `spec fn report_code(code: u64) -> u64` = `if code <= 0x3fff_ffff_ffff_ffff { code } else { INTERNAL_ERROR }`.
  - `fn shut(c: &mut Connection, code: u64, now: u64)`: **replace** `old(c).phase_spec() is Open ==> !(final(c).phase_spec() is Open)` (:93) with:
    ```
    old(c).phase_spec() is Open ==> final(c).phase_spec() is Closing
        && final(c).close_spec() == Some((false, code, Seq::<u8>::empty())),
    !(old(c).phase_spec() is Open) ==> final(c).phase_spec() == old(c).phase_spec()
        && final(c).close_spec() == old(c).close_spec(),
    ```
  - `fn report(c: &mut Connection, code: u64, now: u64)`: add the same two clauses with `report_code(code)` in place of `code`.

- [ ] **Step 1: Write the ensures and `report_code`.**
  - The alert branch's round trip verified without `bit_vector` in the preflight (qt2).
  - Above `report`, cite RFC 9001 §4.8 as in Task 1.
  - Replace the comment at :120-125. Its first sentence becomes: `// Every TLS error is passed to a close, and the ensures pins its code: the alert as CRYPTO_ERROR_BASE + alert, which is how QUIC sends alert X; a transport code (0x0a, 0x0d) as it is; anything past VARINT_MAX as INTERNAL_ERROR. tampered_finished_0x133, error_ranges and a2_closes_0x178 are regression checks.` Keep the rest of the comment.
- [ ] **Step 2: Verify.**
  - Run the recipe for `quictls` (`E=…/t2`). Expected: 0 errors. The preflight measured `shut` at 7833 and `report` at 15511.
  - The callers' `!(final … is Open)` ensures (tls_step :546-547, superseded :595-596) still verify.
- [ ] **Step 3: Full checks, then commit.**
  - Checks: tests 904, `tampered_finished_0x133`/`error_ranges`/`a2_closes_0x178` included; `verify.sh`'s line; escape grep 0; quote check; `duvet report`.
  ```bash
  git add crates/quictls/src/server.rs docs/superpowers/specs/2026-11-05-phase-9-acceptance-and-closes-design.md
  git commit -m "feat(quictls, 9a T2): shut and report prove Closing with the exact close code (RFC 9001 §4.8)"
  ```
- [ ] **Step 4: Mutations.** Each alone, then `git checkout -- crates/quictls/src/server.rs`.
  - **T2-M1:** in `report`'s last branch, `shut(c, PROTOCOL_VIOLATION, now)`. Expected: `report`'s postcondition fails.
  - **T2-M2:** in `report`'s alert branch, `c.on_tls_alert(((code - CRYPTO_ERROR_BASE) as u8) ^ 1, now)`. Expected: `report`'s postcondition fails.
  - **T2-M3:** in `shut`, `c.close(code, true, …)`. Expected: `shut`'s postcondition fails.

### Task 3: Tight CRYPTO end, `crypto_allowed_err`, `on_crypto_frame`'s clause (P2, quic)

**Files:**
- Modify: `crates/quic/src/reassembly.rs` (new proof fns only; no `insert`/`pop`/`wf` text change).
- Modify: `crates/quic/src/crypto_stream.rs` (`wf` :29-32, `on_crypto` :56-101, `read` :104-128).
- Modify: `crates/quic/src/conn.rs`:
  - `wf_parts` :321-323;
  - `crypto_end` :8046;
  - `on_crypto_frame` :1381;
  - new `crypto_received` next to `crypto_base_spec` :272;
  - `reveal(crx_ok)` sites.
- Test: `crates/quic/tests/crypto_stream.rs`, `crates/quictls/tests/server.rs`.
- Modify: design doc §4 (Task 3 rows).

**Interfaces:**
- Consumes: Task 0's headroom; `Reassembly`'s existing ensures, `lemma_wf`, `lemma_received_push`, `lemma_contiguous_exists`.
- Produces (`quic::reassembly`, `impl Reassembly`; serves CRYPTO now and STREAM in Task 6 [I3]):
  - `pub closed spec fn tight(&self) -> bool` = `self.buf_len() > 0 ==> rfc_received(self.inserted()).contains_key((self.base() + self.buf_len() - 1) as nat)`. Not a conjunct of `wf`.
  - `pub proof fn lemma_new_tight(&self)`: requires `self.wf()`, `self.buf_len() == 0`; ensures `self.tight()`.
  - `pub proof fn lemma_insert_tight(a: Reassembly, b: Reassembly, off: u64, d: Seq<u8>)`:
    - requires `a.wf()`, `a.tight()`, `b.wf()`, `d.len() > 0`, `off + d.len() > a.base()`, `b.inserted() == a.inserted().push((off as nat, d))`, `b.base() == a.base()`, and `insert`'s end bound;
    - ensures `b.tight()`.
    - The new end is `max(old end, off + len)`: `lemma_received_push` puts both candidates' last bytes in the new map, and `lemma_wf` on `b` puts every received key below the new end.
  - `pub proof fn lemma_pop_tight(a: Reassembly, b: Reassembly)`: requires `a.wf()`, `a.tight()`, `b.wf()`, `b.inserted() == a.inserted()`, `b.base() + b.buf_len() == a.base() + a.buf_len()`, `b.base() >= a.base()`; ensures `b.tight()`.
  - `pub proof fn lemma_end_received(&self)`: requires `self.wf()`, `self.tight()`; ensures `self.base() + self.buf_len() > 0 ==> rfc_received(self.inserted()).contains_key((self.base() + self.buf_len() - 1) as nat)`. For `buf_len == 0`, the key is `base - 1`, received because `base <= rfc_contiguous`.
- Produces (`quic::crypto_stream`):
  - `pub open spec fn crypto_window_exceeded(base: nat, offset: u64, len: nat) -> bool` = `len > 0 && offset + len > base + MAX_CRYPTO_BUFFER`. This is the named own-limit.
  - `pub open spec fn crypto_allowed_err(s: CryptoStream, offset: u64, len: nat, c: u64) -> bool` = `c == CRYPTO_BUFFER_EXCEEDED && crypto_window_exceeded(s.reassembly().base(), offset, len)`. Cite §7.5's handshake MUST (crypto_stream.rs:90-92) and its post-handshake MAY [m7]: `//# Once the handshake completes, if an endpoint is unable to buffer all` … `//# CONNECTION_CLOSE … CRYPTO_BUFFER_EXCEEDED error code.`, copied exactly from rfc9000.txt §7.5.
  - `pub proof fn lemma_crypto_floor(base: nat, offset: u64, len: nat)` [m9]: requires `offset + len <= base + 4096`; ensures `!crypto_window_exceeded(base, offset, len)`. Cite §7.5's "MUST support buffering at least 4096 bytes" (crypto_stream.rs:12-14).
  - `CryptoStream::wf` adds `&&& self.reassembly().tight()`.
  - `on_crypto`'s body order: `end <= base` → `Ok`; `data.len() == 0` → `Ok`; `end > base + MAX_CRYPTO_BUFFER` → `Err(CRYPTO_BUFFER_EXCEEDED)`; `insert`, then `proof { Reassembly::lemma_insert_tight(old(self).re, self.re, offset, data@) }`. The ensures (the iff changes; the rest as today):
    ```
    final(self).wf(),
    r is Err <==> crypto_window_exceeded(old(self).reassembly().base(), offset, data@.len()),
    r is Err ==> r == Err::<(), u64>(CRYPTO_BUFFER_EXCEEDED),
    r matches Err(c) ==> crypto_allowed_err(*old(self), offset, data@.len(), c),
    (r is Err || offset + data@.len() <= old(self).reassembly().base() || data@.len() == 0) ==> *final(self) == *old(self),
    (r is Ok && offset + data@.len() > old(self).reassembly().base() && data@.len() > 0) ==> { …unchanged… },
    ```
  - `read` calls `lemma_pop_tight`. `new`/`new_at` call `lemma_new_tight`.
  - `pub proof fn lemma_end_received(&self)` on `CryptoStream` forwards `Reassembly::lemma_end_received`.
- Produces (`quic::conn`, `impl Connection`) [C1][I2][I4]:
  - `#[verifier::opaque] spec fn crx_ok(i: CryptoStream, h: CryptoStream, o: CryptoStream) -> bool` = `i.wf() && h.wf() && o.wf()`. It replaces the three `crx_*.wf()` conjuncts in `wf_parts` with `&&& crx_ok(self.crx_i, self.crx_h, self.crx_1)`.
    - It takes the three fields, not `&self`, so field-frame congruence still proves it in every fn that does not touch a CRYPTO stream.
    - `reveal(crx_ok)` only in the Connection constructor(s), `on_crypto_frame`, `discard`, `crypto_read` (after its `hide`s), `crypto_end` and `crypto_base`.
  - `pub closed spec fn crypto_received(&self, k: PacketKind, p: nat) -> bool` = `rfc_received(s.reassembly().inserted()).contains_key(p)`, with `s` the `crx_*` of `k`. Cite RFC 9001 §4.1.3 bullet 1 (as at quictls server.rs:572-575).
  - `crypto_end(&self, k) -> (r: u64)` adds `self.crypto_base_spec(k) <= r` and `r > 0 ==> self.crypto_received(k, (r - 1) as nat)` (proof: `crx_k.lemma_end_received()`).
  - `on_crypto_frame` adds `r matches Err(c) ==> c == CRYPTO_BUFFER_EXCEEDED && crypto_window_exceeded(old(self).crypto_base_spec(k), offset, data@.len())`.

- [ ] **Step 1: Failing tests.**
  - In `crates/quic/tests/crypto_stream.rs`:
    ```rust
    #[test]
    fn crypto_empty_past_window_ok() {
        let mut c = CryptoStream::new();
        assert_eq!(c.on_crypto(16385, &[]), Ok(()));
        assert_eq!(c.on_crypto(1 << 40, &[]), Ok(()));
        assert_eq!(c.end(), 0);
        assert_eq!(c.on_crypto(16384, &[1]), Err(CRYPTO_BUFFER_EXCEEDED));
    }

    #[test]
    fn crypto_empty_keeps_end() {
        let mut c = CryptoStream::new();
        assert_eq!(c.on_crypto(0, &[1; 10]), Ok(()));
        assert_eq!(c.on_crypto(100, &[]), Ok(()));
        assert_eq!(c.end(), 10);
        assert_eq!(read(&mut c), [1; 10]);
        assert_eq!(c.end(), 10);
    }
    ```
  - In `crates/quictls/tests/server.rs`:
    ```rust
    /// An empty CRYPTO frame past the 16 KiB window buffers nothing: not CRYPTO_BUFFER_EXCEEDED (RFC 9000 §7.5).
    #[test]
    fn empty_initial_past_window_ok() {
        let ch = h3ch(id);
        let s = accept(&ini(&qc::S1, 0, || vec![cr(0, &ch), cr(20000, &[])]));
        assert_eq!(s.conn().phase(), Phase::Open);
        assert_eq!(s.key_slots(), [true, true, true]);
    }
    ```
  - Run them. Expected:
    - `crypto_empty_past_window_ok` FAILS with `Err(13)` at 16385;
    - `empty_initial_past_window_ok` FAILS, Closing through on_counted:764;
    - `crypto_empty_keeps_end` PASSES (the pre-753ec2d pin; M1 shows it failing).
- [ ] **Step 2: Implement the Interfaces items.** Order: the reassembly proof fns, then crypto_stream.rs, then `crx_ok`, then `crypto_received`/`crypto_end`/`on_crypto_frame`.
- [ ] **Step 3: Run the tests.** Expected: PASS, `crypto_limit` included.
- [ ] **Step 4: Verify.**
  - Run the recipe for `quic` then `quictls` (`E=…/t3`). Expected: 0 errors.
  - Record `on_crypto`, `read`, `lemma_insert_tight`, `crypto_read`, `crypto_end`, `on_crypto_frame`, `discard`, `poll_transmit`, `on_datagram`, `on_data`, `insert`, and the quic top 8.
  - Preflight's measurements for this shape: `poll_transmit` 5.76M with `crx_ok` (8.41M without); `on_datagram` 2.82M; `insert` 11.54M before Task 0's split.
  - The stop rule applies.
- [ ] **Step 5: Full checks, then commit.**
  - Checks: tests 907, 0 warnings; `verify.sh`'s line; escape grep 0; quote check on reassembly.rs, crypto_stream.rs, conn.rs; `duvet report`.
  ```bash
  git add crates/quic/src crates/quic/tests/crypto_stream.rs crates/quictls/tests/server.rs docs/superpowers/specs/2026-11-05-phase-9-acceptance-and-closes-design.md
  git commit -m "fix(quic, 9a T3): CRYPTO window ends at a received byte; an empty CRYPTO frame past the window is not CRYPTO_BUFFER_EXCEEDED; on_crypto and on_crypto_frame acceptance clauses; opaque crx_ok (RFC 9000 §7.5, RFC 9001 §4.1.3)"
  ```
- [ ] **Step 6: Mutations.** Each alone, then `git checkout -- crates/quic/src/crypto_stream.rs`.
  - **M1, the 753ec2d revert [m3].** It must fail on the tight end itself:
    1. Delete the `if data.len() == 0 { … return Ok(()); }` block.
    2. Guard the lemma call as `if data.len() > 0 { proof { … lemma_insert_tight(..) } }`.
    3. Replace the two frame clauses with their pre-753ec2d forms: `(r is Err || offset + data@.len() <= old(self).reassembly().base()) ==> *final(self) == *old(self),` and `(r is Ok && offset + data@.len() > old(self).reassembly().base()) ==> { … }`.
    4. Make the iff `r is Err <==> offset + data@.len() > old(self).reassembly().base() + MAX_CRYPTO_BUFFER`.
    5. Delete the `crypto_allowed_err` line.
    - Expected: `on_crypto`'s `final(self).wf()` postcondition fails (the `tight` conjunct). `cargo test` also fails `crypto_empty_keeps_end`, `empty_gapped_initial_ok` and `empty_initial_after_switch_ok`.
  - **M2:** move the `data.len() == 0` block after the window check. Expected: the iff and `crypto_allowed_err` postconditions fail, and so does `crypto_empty_past_window_ok`.
  - **M3:** in conn.rs, remove `reveal(crx_ok)` from `crypto_end`. Expected: `crypto_end`'s `crypto_received` postcondition fails. This shows the opaque wrapper actually hides the conjunct.

### Task 3b: the Initial CRYPTO invariant across the `Connection` boundary [I1]

**Files:**
- Modify: `crates/quic/src/conn.rs`:
  - `crypto_kept` with its lemmas;
  - `discard` :2941;
  - `crypto_read` :3098, `crypto_write` :3136, `on_peer_params`, `on_handshake_complete`, `close`;
  - `on_datagram`, `poll_transmit` :6614, `poll_cid_updates`, `on_reset_candidate`, and the private `rx_kept` (:541) / `tx_kept` (:3601).
- Modify: `crates/quic/src/crypto_stream.rs` (ghost `hist`, `restart`) [m10].
- Modify: `crates/quic/src/pipeline.rs` (`receive`, `transmit`, `refeed_one_rtt`).
- Modify: `crates/quic/src/h3_server.rs` (`pump`, `on_timeout`, `send_response`).
- Modify: `crates/quictls/src/server.rs`: `core_ok` :204-216, `key_events` :155-171, `key_changes`, `apply`'s loop invariant, `on_secrets`, `superseded` :586-616, and every method that re-proves `core_ok`.
- Modify: design doc §4 (Task 3b rows), §6 (confirm both "proved in 9a" bullets).

**Interfaces:**
- Consumes: Task 3's `crypto_received`, `crypto_end` ensures, `crx_ok`; Task 2's `shut`.
- Produces (`quic::crypto_stream`) [m10, reworked; design §3.1]:
  - Field `hist: Ghost<Seq<(nat, Seq<u8>)>>`. `on_crypto` pushes what it inserts.
  - `pub closed spec fn received(&self, p: nat) -> bool` = `rfc_received(self.hist@).contains_key(p)`.
  - `wf` adds:
    - `self.end_spec() > 0 ==> self.received(self.end_spec() - 1)`, where `end_spec = base + buf_len`;
    - `forall p. self.received(p) ==> rfc_received(re.inserted()).contains_key(p)`.
  - `pub fn restart(&mut self)`: ensures `wf`, base == old end, `buf_len == 0`, `hist` unchanged, end unchanged. It replaces `discard`'s `CryptoStream::new_at(self.crx_i.end())`.
  - `Connection::crypto_received(k, p)` is redefined as `crx_k.received(p)`. It stays closed, so callers are unaffected.
  - Not adopted: the preflight's "keep the old ghost `inserted`". It breaks `Reassembly::wf`'s `base <= rfc_contiguous` when the window has a gap at the discard.
- Produces (`quic::conn`, `impl Connection`):
  - `pub closed spec fn crypto_kept(&self, o: Connection) -> bool` = `self.crypto_base_spec(PacketKind::Initial) >= o.crypto_base_spec(PacketKind::Initial)`.
  - Its lemmas, following `keeps_later`'s pattern (conn.rs:7171-7230). Neither requires `wf`:
    - `pub proof fn lemma_crypto_kept_refl(c: Connection)`: ensures `c.crypto_kept(c)`;
    - `pub proof fn lemma_crypto_kept_trans(a: Connection, b: Connection, c: Connection)`: requires `b.crypto_kept(a)`, `c.crypto_kept(b)`; ensures `c.crypto_kept(a)`.
  - Measure `on_data` after adding them [C1]. If it moves past the stop rule, fold them into `keeps_later`'s existing lemma fns.
  - `final(self).crypto_kept(*old(self))` is ensured by:
    - `close`, `crypto_read`, `crypto_write`, `on_peer_params`, `on_handshake_complete`;
    - `on_datagram`, `poll_transmit`, `poll_cid_updates`, `on_reset_candidate`;
    - `discard`, and `discard` also ensures `final.crypto_end_spec(Initial) == old.crypto_end_spec(Initial)` as today.
    - Inside the receive path, carry it through `rx_kept`/`frames_kept` where they hold, and through an explicit conjunct where `discard` is reached (`validate_hs_path`).
    - `poll_transmit` gets it from `tx_kept` (`crx_i == o.crx_i`) as one closed atom, never as an unfolded comparison.
  - `crypto_write`, `on_peer_params` and `on_handshake_complete` also ensure `final(self).crypto_end_spec(PacketKind::Initial) == old(self).crypto_end_spec(PacketKind::Initial)`.
  - `crypto_read` also ensures `old(self).crypto_end_spec(level) <= old(self).crypto_base_spec(level) ==> final(out)@ == old(out)@`.
- Produces (`quic::pipeline`, `quic::h3_server`): `receive`, `transmit`, `refeed_one_rtt`, `H3Server::{pump, on_timeout, send_response}` ensure `final….crypto_kept(old…)` on their connection.
- Produces (`quictls::server`):
  - `core_ok` adds `&&& !(self.level is Initial) ==> self.h3.conn_spec().crypto_base_spec(PacketKind::Initial) >= self.init_end`.
  - `spec fn spec_key_events(ev: Seq<SpecTlsEvent>) -> (bool, bool)` = `(exists|i: int| 0 <= i < ev.len() && #[trigger] spec_secrets_level(ev[i], Level::Handshake), exists|i: int| #![trigger ev[i]] 0 <= i < ev.len() && ev[i] is Complete)`.
  - `key_events` ensures `r == spec_key_events(ev.deep_view())`, with a loop invariant linking `ev.deep_view()[j] == ev@[j].deep_view()`, as `apply` does at :704.
  - `key_changes` adds `ok ==> final(self).h3 == old(self).h3` and `ok && spec_key_events(ev.deep_view()).0 ==> old(self).unread(Level::Initial, PacketKind::Initial) == 0`.
  - `apply`'s loop invariant adds `spec_key_events(ev.deep_view()).0 && self.level is Initial ==> self.conn_spec().crypto_end_spec(PacketKind::Initial) <= self.conn_spec().crypto_base_spec(PacketKind::Initial)`.
  - `superseded`:
    - First add `assert(b@.len() == 0)` after `crypto_read` and verify it. This is the proof that the branch is dead.
    - Then delete the `crypto_read` and the close (:607-613), and drop "or newly contiguous" and the `crypto_read` sentence from the comment at :580-584.

- [ ] **Step 1: Implement `hist`/`restart` and `crypto_kept`** in quic, with the ensures above, through pipeline and h3_server.
- [ ] **Step 2: Verify quic.**
  - Run the recipe (`E=…/t3b`). Expected: 0 errors.
  - Record `poll_transmit`, `on_datagram`, `discard`, `crypto_read`, `pump`, `on_data`, `insert`, and the top 8. The stop rule applies.
- [ ] **Step 3: Implement the quictls items** up to and including the `assert(b@.len() == 0)`, with the branch still present.
  - Verify quictls. Expected: 0 errors, the assertion included.
  - Save the JSON as `t3b/dead-branch.json`: it is the evidence.
- [ ] **Step 4: Delete the branch.**
  - Verify quictls again. Expected: 0 errors, and the existing `superseded`/`tls_step` ensures still hold.
  - Run `cargo test --workspace`. Expected: 907 passed, `initial_data_after_switch_pv` and `initial_retransmit_after_switch_ok` included.
- [ ] **Step 5: Full checks, then commit.**
  - Checks: `verify.sh`'s line; escape grep 0; quote check; `duvet report`.
  ```bash
  git add crates/quic/src crates/quictls/src/server.rs docs/superpowers/specs/2026-11-05-phase-9-acceptance-and-closes-design.md
  git commit -m "feat(quic, quictls, 9a T3b): the Initial CRYPTO base never decreases (crypto_kept on every Connection entry), so core_ok proves init_end <= base after the key change; superseded's newly-contiguous close proved unreachable and removed; the Initial history survives its discard (RFC 9001 §4.1.3)"
  ```
- [ ] **Step 6: Mutations.** Each alone, then `git checkout` the file.
  - **T3b-M1:** drop `crypto_kept` from `crypto_read`'s ensures. Expected: a quictls `core_ok` postcondition fails (in `superseded` or `feed`).
  - **T3b-M2:** `restart` sets base to 0. Expected: `restart`'s or `discard`'s postcondition fails (`crypto_kept`).
  - **T3b-M3:** restore the deleted block with the `assert(b@.len() == 0)` before it, using `git show 73cc244:crates/quictls/src/server.rs | sed -n 607,613p` from main's numbering. Expected: verification **passes**, which shows the branch is proved dead.
  - **T3b-M4:** drop the `apply` loop-invariant conjunct. Expected: `on_secrets`' `core_ok` postcondition fails.

### Task 4: transport-parameter acceptance lemma (spec-only) [I6]

**Files:**
- Modify: `crates/quic/src/tp.rs` (new spec fns and one proof fn; no exec change).
- Modify: design doc §4 (Task 4 row).

**Interfaces:**
- Consumes: `rfc_tp_from`, `rfc_tp_apply`, `rfc_tp_value`, `tp_bit`, `rfc_vint`, `rfc_bytes` (tp.rs:211-357).
- Produces (`quic::tp`), each disjunct cited:
  - `pub open spec fn tp_value_invalid(id: u64, v: Seq<u8>) -> bool`: §18.2's per-parameter rules, written from the RFC text:
    - an integer parameter whose value is not one varint filling `v`;
    - `max_udp_payload_size < 1200`;
    - `ack_delay_exponent > 20`;
    - `max_ack_delay >= 2^14`;
    - `active_connection_id_limit < 2`;
    - `initial_max_streams_* > 2^60`;
    - a connection ID over 20 bytes;
    - `stateless_reset_token` not 16 bytes;
    - `disable_active_migration` non-empty.
  - `pub open spec fn tp_server_only(id: u64) -> bool`: odcid, preferred_address, retry_scid, stateless_reset_token (§18.2: "A client MUST NOT include any server-only transport parameter … A server MUST treat receipt …").
  - `pub open spec fn allowed_tp_err(b: Seq<u8>) -> bool`: there is a position `p` reached by a successful parse of `b[..p]`, with state `(t, seen)`, such that one of these holds:
    - the TLV at `p` is badly formatted: `rfc_vint` or `rfc_bytes` fails (§18, §20.1 "badly formatted");
    - `id <= TP_RETRY_SOURCE_CONNECTION_ID && seen & tp_bit(id) != 0` (duplicate, §7.4 SHOULD, chosen);
    - `tp_server_only(id)` (§18.2 MUST);
    - `id <= TP_RETRY_SOURCE_CONNECTION_ID && tp_value_invalid(id, v)` (§7.4 MUST).
    - Define it with a recursive `allowed_tp_err_from(b, p, t, seen)` mirroring `rfc_tp_from`'s shape (same `decreases_by`).
  - `pub proof fn lemma_tp_err_allowed(b: Seq<u8>)`: ensures `rfc_transport_params(b, true) is Err ==> allowed_tp_err(b)`. Induction on `rfc_tp_from`. Its sub-lemma `rfc_tp_value(id, v, t) is None && id <= TP_RETRY_SOURCE_CONNECTION_ID && !tp_server_only(id) ==> tp_value_invalid(id, v)` is where a spec stricter than §18.2 would show up. If it does not prove, report the parameter. Do not widen `tp_value_invalid`.

- [ ] **Step 1: Write the spec fns and the lemma.** Spin the lemma off. It is a proof fn, so it adds no exec VC.
- [ ] **Step 2: Verify.** Run the recipe for `quic` then `quictls` (`E=…/t4`). Expected: 0 errors. Record the lemma and the top 8. The stop rule applies.
- [ ] **Step 3: Full checks, then commit.**
  - Checks: tests 907; `verify.sh`'s line; escape grep 0; quote check on tp.rs; `duvet report`.
  ```bash
  git add crates/quic/src/tp.rs docs/superpowers/specs/2026-11-05-phase-9-acceptance-and-closes-design.md
  git commit -m "feat(quic, 9a T4): allowed_tp_err and lemma_tp_err_allowed: a client's transport parameters are refused only as RFC 9000 §7.4, §18, §18.2 and §20.1 allow"
  ```
- [ ] **Step 4: Mutations.** Each alone, then `git checkout -- crates/quic/src/tp.rs`.
  - **T4-M1:** in `tp_value_invalid`, make `ack_delay_exponent > 21`. Expected: `lemma_tp_err_allowed` fails, because `rfc_tp_value` rejects 21.
  - **T4-M2:** drop the duplicate disjunct. Expected: the lemma fails.

### Task 5: quictls acceptance and close code on the CRYPTO path (P2, quictls)

**Files:**
- Modify: `crates/quictls/src/server.rs`: `superseded`; `unconsumed` :755-763; `key_changes`; `on_params`; new spec fns after `level_rank` (:54) and in `impl QuicServer` after `unread`.
- Test: `crates/quictls/tests/server.rs`.
- Modify: design doc §4 (Task 5 rows; check every row has both columns).

**Interfaces:**
- Consumes:
  - Task 1: `close_spec`, `client_scid_spec`, `on_peer_params`' ensures;
  - Task 2: `shut`;
  - Task 3: `crypto_received`, `crypto_end`'s ensures;
  - Task 3b: `core_ok`, `spec_key_events` and `key_events`' ensures;
  - Task 4: `allowed_tp_err`, `lemma_tp_err_allowed`;
  - `quic::tp::rfc_transport_params`, `tls::server::{spec_reader, spec_secrets_level}`, `tls::flight::SpecTlsEvent`.
- Produces (`quictls::server`, private):
  - `spec fn past_received(c: Connection, k: PacketKind, end: nat) -> bool` = `exists|p: nat| p >= end && #[trigger] c.crypto_received(k, p)` [C1]. Cite RFC 9001 §4.1.3 bullet 1 and its PROTOCOL_VIOLATION sentence (server.rs:572-579).
  - `spec fn tp_allowed_err(c: Connection, b: Seq<u8>) -> bool` = `match rfc_transport_params(b, true) { Err(_) => allowed_tp_err(b), Ok(t) => t.initial_source_connection_id != Some(c.client_scid_spec()) }` [I6]. Cite RFC 9000 §7.4 (rfc9000.txt:2016-2018) and §7.3.
  - `spec fn tls_unconsumed(&self, l: Level, k: PacketKind) -> bool` = `spec_reader(self.hs@, l).len() > 0 || past_received(self.h3.conn_spec(), k, self.h3.conn_spec().crypto_base_spec(k))`. Cite RFC 9001 §4.1.3's "When TLS provides keys … PROTOCOL_VIOLATION." (server.rs:724-728).
  - `unconsumed` adds `r ==> self.tls_unconsumed(l, k)` [I5]. The witness is `crypto_end(k) - 1` from Task 3's `crypto_end` ensures; no lemma needs `conn_spec().wf()`.
  - `superseded(&mut self, now: u64) -> (cont: bool)` adds [m5: T5-M1 fails both]:
    ```
    !cont ==> !(old(self).level is Initial)
        && old(self).conn_spec().crypto_end_spec(PacketKind::Initial) > old(self).init_end,
    !cont && old(self).conn_spec().phase_spec() is Open ==> {
        &&& past_received(old(self).conn_spec(), PacketKind::Initial, old(self).init_end as nat)
        &&& final(self).conn_spec().phase_spec() is Closing
        &&& final(self).conn_spec().close_spec() == Some((false, PROTOCOL_VIOLATION, Seq::<u8>::empty()))
    },
    ```
  - `key_changes(&mut self, ev: &Vec<TlsEvent>, now: u64) -> (ok: bool)` adds:
    ```
    !ok && old(self).conn_spec().phase_spec() is Open ==> {
        &&& (spec_key_events(ev.deep_view()).0 && old(self).tls_unconsumed(Level::Initial, PacketKind::Initial))
            || (spec_key_events(ev.deep_view()).1 && old(self).tls_unconsumed(Level::Handshake, PacketKind::Handshake))
        &&& final(self).conn_spec().phase_spec() is Closing
        &&& final(self).conn_spec().close_spec() == Some((false, PROTOCOL_VIOLATION, Seq::<u8>::empty()))
    },
    ```
  - `on_params(&mut self, b: &Vec<u8>, now: u64) -> (ok: bool)` adds the following; the `Err` arm calls `lemma_tp_err_allowed(b@)`:
    ```
    !ok && old(self).conn_spec().phase_spec() is Open ==> {
        &&& tp_allowed_err(old(self).conn_spec(), b@)
        &&& final(self).conn_spec().phase_spec() is Closing
        &&& final(self).conn_spec().close_spec() == Some((false, TRANSPORT_PARAMETER_ERROR, Seq::<u8>::empty()))
    },
    ```
  - Scheduled in 9c, not here: `apply`/`feed`/`tls_step` acceptance (design §3.3) [I4].

- [ ] **Step 1: Tests** in `crates/quictls/tests/server.rs`:
  ```rust
  /// One byte past the ClientHello's end after the key change: past the end of previously received data (RFC 9001 §4.1.3).
  #[test]
  fn initial_straddle_after_switch_pv() {
      let mut ch = h3ch(id);
      let l = ch.len();
      ch.push(7);
      let mut s = flight();
      receive(&mut s, &ini(&qc::S1, 1, || vec![cr(l - 10, &ch[l - 10..])]), 2);
      assert_eq!(close_code(&mut s), 0x0a);
  }

  /// Bytes TLS has not consumed at the key change (0x0a) are checked before the peer's transport
  /// parameters (a duplicate active_connection_id_limit, 0x08): the first error is the one sent.
  #[test]
  fn trailing_bytes_before_bad_tp_pv() {
      let mut ch = h3ch(|e| {
          for (t, d) in e.iter_mut() {
              if *t == 0x39 {
                  *d = qc::hex("0f08c1c1c1c1c1c1c1c1 0e0104 0e0104");
              }
          }
      });
      ch.push(0x01);
      let mut s = accept(&ini(&qc::S1, 0, || vec![cr(0, &ch)]));
      assert_eq!(close_code(&mut s), 0x0a);
  }
  ```
  - Run `cargo test -p quictls --test server`. Expected: PASS on the Task 4 tree.
  - Both pin behaviour the new ensures prove; T5-M1 and T5-M5 show them failing.
  - The TP is `ctp()`'s bytes plus a duplicated `0e0104`, so its only fault is the duplicate [m6].
- [ ] **Step 2: Implement the Interfaces items.** `superseded`'s witness is one `assert(old(self).conn_spec().crypto_received(PacketKind::Initial, (e - 1) as nat))`, as in the preflight (qt2, 73802).
- [ ] **Step 3: Verify.**
  - Run the recipe for `quictls` (`E=…/t5`). Expected: 0 errors.
  - Record `superseded`, `key_changes`, `on_params`, `unconsumed`, `tls_step`, `apply`, `feed`.
- [ ] **Step 4: Full checks, then commit.**
  - Checks: tests 909, 0 warnings; `verify.sh`'s line; escape grep 0; quote check on server.rs; `duvet report`.
  ```bash
  git add crates/quictls/src/server.rs crates/quictls/tests/server.rs docs/superpowers/specs/2026-11-05-phase-9-acceptance-and-closes-design.md
  git commit -m "feat(quictls, 9a T5): superseded, key_changes and on_params prove an RFC-allowed reason and the exact close code (RFC 9001 §4.1.3, RFC 9000 §7.3, §7.4)"
  ```
- [ ] **Step 5: Mutations.** Each alone, then `git checkout -- crates/quictls/src/server.rs`.
  - **T5-M1:** `superseded` uses `if e >= self.init_end`. Expected: both new clauses fail (`crypto_end > init_end` and `past_received`), and so does `initial_retransmit_after_switch_ok` [m4, m5].
  - **T5-M2:** `key_changes`' first check becomes `self.h3.conn().crypto_end(PacketKind::Initial) > 0`. Expected: the `tls_unconsumed` postcondition fails. It may also fail `lemma_push`'s `unread == 0` precondition; both belong to this mutation.
  - **T5-M3:** `on_params`' `Err` arm calls `shut(…, PROTOCOL_VIOLATION, now)`. Expected: the `close_spec` postcondition fails.
  - **T5-M4:** delete the `lemma_tp_err_allowed(b@)` call. Expected: the `tp_allowed_err` postcondition fails.
  - **T5-M5 [m11]:** in `apply`, move the `key_changes` call after the event loop. Expected: `trailing_bytes_before_bad_tp_pv` reads 0x08 and fails.

### Task 6: the empty STREAM insert, fixed and proved [I3]

**Files:**
- Modify: `crates/quic/src/recv_stream.rs` (Task 0's buffering half of `on_data`; `RecvStream::wf`; `new`), plus `#[doc(hidden)] pub fn capacities(&self) -> (usize, usize)` outside `verus!`, as `CryptoStream::capacities`.
- Test: `crates/quic/tests/recv_stream.rs`.
- Modify: design doc §4 (`on_data`'s final row).

**Interfaces:**
- Consumes: Task 0's split; Task 3's `Reassembly::{tight, lemma_new_tight, lemma_insert_tight, lemma_pop_tight}`.
- Produces:
  - The buffering half skips `insert` when `data.len() == 0`. This comes after the final-size and flow-control checks, so an empty FIN still sets the final size.
  - `RecvStream::wf` adds `&&& self.re.tight()` (or the field's accessor), proved at each insert and pop with the Task 3 lemmas.
  - No `on_data` `requires`/`ensures` text changes, except where the empty case is stated today. Its existing exact three-way ensures against `rfc_recv` must still hold; if `rfc_recv` models the empty insert, the empty case is a no-op on the buffer but not on `high`/final size.

- [ ] **Step 1: Failing test** in `crates/quic/tests/recv_stream.rs`, using its `data` helper:
  ```rust
  /// An empty STREAM frame inside the window buffers nothing (no unreceived slots).
  #[test]
  fn empty_stream_frame_keeps_window() {
      let mut s = RecvStream::new(0, 100);
      data(&mut s, 0, &[1; 10], false, 1000);
      assert_eq!(s.capacities(), (0, 0));
      data(&mut s, 90, &[], false, 1000);
      assert_eq!(s.capacities(), (0, 0));
  }
  ```
  - Expected: FAIL. On main, the empty insert at 90 grows the window to 90 slots.
  - If `data`'s 10 bytes are not delivered and drained by `on_data` itself, replace the first `capacities` assertion with a saved value and compare against it.
- [ ] **Step 2: Implement.**
- [ ] **Step 3: Run the tests.** Expected: PASS, the `final_size_rules` and FIN tests included.
- [ ] **Step 4: Verify.**
  - Run the recipe for `quic` then `quictls` (`E=…/t6`). Expected: 0 errors.
  - Record `on_data` (and its halves), `insert`, and the top 8. The stop rule applies.
- [ ] **Step 5: Full checks, then commit.**
  - Checks: tests 910, 0 warnings; `verify.sh`'s line; escape grep 0; quote check; `duvet report`.
  ```bash
  git add crates/quic/src/recv_stream.rs crates/quic/tests/recv_stream.rs docs/superpowers/specs/2026-11-05-phase-9-acceptance-and-closes-design.md
  git commit -m "fix(quic, 9a T6): an empty STREAM frame does not grow the receive window; RecvStream's reassembly ends at a received byte (RFC 9000 §2.2)"
  ```
- [ ] **Step 6: Mutation.** **T6-M1:** remove the empty-data guard. Expected: the `tight` conjunct of `RecvStream::wf` fails at the insert, and so does `empty_stream_frame_keeps_window`.

---

## Self-review notes

- **Spec coverage:**
  - design §3.1 headroom → Task 0; P0 → Task 1; P1 → Task 2;
  - tight end, `crypto_allowed_err`, `on_crypto_frame`, `crx_ok`, `crypto_received`, the floor lemma → Task 3;
  - `core_ok` invariant, `hist`/`restart`, the branch proved dead → Task 3b;
  - `allowed_tp_err` → Task 4; the quictls clauses → Task 5; the empty STREAM insert → Task 6;
  - §4 → every task.
  - Scheduled in 9c (design §3.3): `on_frame`/`on_counted` and `apply`/`feed`/`tls_step`.
- **Names used across tasks:**
  - `close_spec`, `reason_cap`, `client_scid_spec` (T1) → T2, T5;
  - `crypto_received`, `crypto_end`'s ensures, `Reassembly::tight` and its lemmas (T3) → T3b, T5, T6;
  - `crypto_kept`, `spec_key_events` (T3b) → T5;
  - `allowed_tp_err`, `lemma_tp_err_allowed` (T4) → T5.
- **Test counts:** 902 → 902 (T0) → 904 (T1) → 904 (T2) → 907 (T3) → 907 (T3b, T4) → 909 (T5) → 910 (T6).
