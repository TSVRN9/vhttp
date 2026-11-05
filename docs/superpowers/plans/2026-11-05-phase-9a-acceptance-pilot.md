# Phase 9a: Acceptance Clauses and Proved Closes, Pilot — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** prove the close code at the `Connection` boundary and in quictls's close sinks, and put RFC-cited acceptance clauses on the whole CRYPTO error path. Measure what that costs in rlimit.

**Architecture:**
- New closed specs on `Connection`: `close_spec`, `client_scid_spec` and `crypto_inserted`, with `close`/`close_internal`/`on_tls_alert`/`on_peer_params` ensuring the exact close triple.
- quictls `shut`/`report` forward it.
- The CRYPTO pilot adds a tight-end conjunct to `CryptoStream::wf`, proved in crypto_stream.rs from `Reassembly`'s existing ensures (reassembly.rs is not edited). On it rest:
  - `crypto_allowed_err`, which also fixes a sibling of 753ec2d (design §5.1);
  - quictls's `past_received` / `tls_unconsumed` / `tp_allowed_err` clauses on `superseded`, `key_changes` and `on_params`.
- `superseded`'s unreachable second close is removed (design §3.1 P2, §5.2).

**Tech Stack:** Verus 0.2026.10.04.426d8b0 (rustc 1.98.1), vstd `=0.0.0-2026-10-04-0306`, vest_lib `=0.2.2`, duvet 0.4.3. No new dependency.

**Spec:** `docs/superpowers/specs/2026-11-05-phase-9-acceptance-and-closes-design.md` (§1 the rule, §3.1 what 9a proves, §4 the result table this plan fills, §5 inventory corrections). Its input, `docs/superpowers/specs/2026-11-05-phase-9-inventory.md`, gives the error-site rows and the close paths C1–C12.

`<scratch>` is `/home/tavern/Projects/rust/web-server/.worktrees`. Evidence goes in `<scratch>/vt-9a-evidence/tN/` (never /tmp). Branch `phase-9a` in `<scratch>/wt-9a`, from `main` at 73cc244.

## Global Constraints

- **Rule 1, acceptance (design §1):** every verified fn that can return an error carries `Err(code) ==> allowed_err(state, input, code)`.
  - `allowed_err` is one spec fn per handler, RFC-cited, and a disjunction of: errors the RFC requires (MUST); errors it permits (MAY/SHOULD "treat as a connection error") where we chose to raise them; our own named limits (Busy, full tables) as visible named predicates.
  - Codecs: `spec_parse(b) is Some ==> res is Ok`.
  - A bool-signalling step (`cont`/`ok`) carries `!ok && old Open ==> allowed_x(..)`.
- **Rule 2, proved close:**
  - (a) the error path leaves the connection Closing with that exact code (`close_spec`);
  - (b) in Closing, if a datagram is emitted, it contains CONNECTION_CLOSE with that code at the right key level (RFC 9000 §10.2.3). The words are "if emitted" because amplification and pacing can block sends. (b) is 9b's; 9a does not touch it.
- **Rule 3, forward:** every future plan's Global Constraints carry rules 1 and 2. An error path without an acceptance clause, or a close without a proved code, is an **Important** review finding.
- **rlimit:**
  - Verify everything at `--rlimit 4`. A fresh target fails in vstd at rlimit 4, so run a default verify first.
  - Force a real re-run by deleting the crate's fingerprint, deps and verus-partial dirs under target.
  - Record the measured rlimit of every touched fn.
  - Recipe, per crate `<c>`, with `CARGO_TARGET_DIR=<scratch>/vt-9a-evidence/tN/target`:
    ```bash
    (cd crates/<c> && cargo verus verify)                     # default rlimit, warms vstd (first run on a target only)
    cargo clean -p <c>; rm -rf $CARGO_TARGET_DIR/verus-partial/*/.fingerprint/<c>-*
    (cd crates/<c> && cargo verus verify -- --rlimit 4 --output-json --time-expanded) > $E/<c>.json 2> $E/<c>.err
    python3 -I <scratch>/vt-4c-evidence/t3/rl.py $E/<c>.json <fn names…>   # prints verification-results, top 6, the named fns, FAIL rows
    ```
  - quictls depends on quic: after any quic edit, run the recipe for quic and then for quictls.
  - Use `#[verifier::spinoff_prover]` and split lemmas; never raise the rlimit.
- **Must not be touched:** `RecvStream::on_data` (11.79M), `datagram::pick` (12.10M), `Paths::on_timeout` (11.04M). Any change to `poll_transmit` (7.13M) is a closed-predicate swap only (9b), and 9a makes none.
  - reassembly.rs is not edited, so `on_data`, which calls `insert`, sees no new conjunct.
  - Every task prints `on_data` and `poll_transmit` from `rl.py`. Each must stay within ±5% of Task 1's "before" value. A larger move is a stop: report it.
- Never edit `crates/crypto/src`, `crates/ctcore/src` or `crates/ctmir/src/sem.rs`.
- No `assume(`, `external_body`, `verifier::external` or `axiom` anywhere under `crates/` outside `crates/crypto/src`, in code or comments.
  - Check with the line grep and `grep -Pz` from `<scratch>/vt-4c-evidence/t3/final.sh` (its `escape` loop), run over every crate directory except `crypto`. It must report 0.
- vest_lib's default broadcast lemmas leak into any crate importing quic; tls stays free of quic. 9a edits no tls file.
- `scripts/verify.sh`'s final line stays byte-identical: `verify.sh: all crates verified, duvet ok, ct ok (10 declassify), cost 19/36, escapes accounted (0), binary ok (49 fns)`.
- `cargo test --workspace` stays green: 902 tests at main 73cc244, plus this plan's new tests (909 after Task 4). 0 warnings in `cargo build` and `cargo test`.
- No attribution lines in commits.
- **Duvet:** every new spec fn and ensures that states an RFC condition carries `//= https://www.rfc-editor.org/rfc/rfcNNNN#section-X` plus a contiguous `//#` quote copied verbatim from `.duvet/specifications/www.rfc-editor.org/rfc/`.
  - `.duvet/specifications` and `.duvet/requirements` are git-ignored and missing in wt-9a. Copy both once from `/home/tavern/Projects/rust/web-server/.duvet/`.
  - Per task: `python3 -I <scratch>/qchk/check_quotes.py --spec-dir .duvet/specifications/www.rfc-editor.org/rfc <touched files>` prints `N citations, 0 bad`, and `duvet report` exits 0.
- **Mutations:** each listed mutation, applied alone to the committed tree, must fail verification on the named postcondition, precondition or assertion, not on rlimit. Restore with `git checkout -- <file>`, then re-run the default verify of that crate.
- **Spec fns on `Connection` are `closed`** (as `phase_spec`, `out_log`); quictls sees them through ensures and `pub proof fn` lemmas only.

## Review Focus

1. **An empty CRYPTO frame at any offset** never closes the connection: below the read offset, inside the window, past the window, or after the key change. Task 3: `crypto_empty_past_window_ok`, `crypto_empty_keeps_end`, `empty_initial_past_window_ok`. Already pinned: `empty_gapped_initial_ok`, `empty_initial_after_switch_ok`.
2. **An Initial retransmission ending exactly at `init_end`** after the key change leaves the connection Open. This is the boundary of `superseded`'s only remaining close. Task 4: `initial_tail_retransmit_after_switch_ok`.
3. **Two errors in one flight:** the first error's code is the one sent. Task 4: `trailing_bytes_before_bad_tp_pv` (0x0a, not 0x08). Task 1: `alert_after_close_keeps_code`.
4. **TLS alert 0xff** closes with 0x1ff, the top of the CRYPTO_ERROR range (RFC 9001 §4.8). Task 1: `tls_alert_top_of_range`.
5. **A CRYPTO frame ending exactly at `base + 16384`** is accepted; one byte more closes with 0x0d. Already pinned by `crypto_limit`, which must stay green after Task 3's reorder.

---

## File Structure

- `crates/quic/src/conn.rs` (Tasks 1, 3): `close_spec`, `reason_cap`, `client_scid_spec`, `crypto_inserted`, `lemma_crypto_end_received`; ensures on `close`, `close_internal`, `on_tls_alert`, `on_peer_params`.
- `crates/quic/src/crypto_stream.rs` (Task 3): `tight`, `crypto_window_exceeded`, `crypto_allowed_err`, `lemma_end_received`, private tight-end lemmas; `on_crypto` checks empty data before the window.
- `crates/quictls/src/server.rs` (Tasks 2, 4): `shut`/`report` ensures and `report_code`; `past_received`, `tls_unconsumed`, `tp_allowed_err`, `spec_key_events`; ensures on `superseded`, `key_changes`, `on_params`, `key_events`; `superseded`'s second close removed.
- Tests: `crates/quic/tests/{conn_rx.rs, crypto_stream.rs}`, `crates/quictls/tests/server.rs`.
- `docs/superpowers/specs/2026-11-05-phase-9-acceptance-and-closes-design.md` §4 (every task fills its rows).

---

### Task 1: Close code at the `Connection` boundary (P0)

**Files:**
- Modify: `crates/quic/src/conn.rs`:
  - new spec fns next to `phase_spec` (:285);
  - `close_internal` :3009-3021, `close` :3025-3053, `on_peer_params` :3160-3184, `on_tls_alert` :3222-3233.
- Test: `crates/quic/tests/conn_rx.rs`.
- Modify: design doc §4 (the "before" column of every row, and Task 1's "after").

**Interfaces:**
- Consumes: `Lifecycle::close_spec` and `enter_closing`'s ensures (lifecycle.rs:333, :412-454); `HandshakeIds::check_peer_tp`'s iff (handshake.rs:364-367).
- Produces (`quic::conn`):
  - `pub open spec fn reason_cap(r: Seq<u8>) -> Seq<u8>` = `r.take(if r.len() > 64 { 64int } else { r.len() as int })`. This is a free fn, the cap `enter_closing` applies.
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

- [ ] **Step 1: Baseline rlimit on the unedited tree.**
  - Run the Global Constraints recipe for `quic` and then `quictls`, with `E=<scratch>/vt-9a-evidence/t0`.
  - Name every fn in design §4's table to `rl.py`.
  - Expected: `verification-results` with 0 errors for both crates.
  - Copy each fn's rlimit into §4's "before" column. Keep `t0/*.json` as the evidence.
- [ ] **Step 2: Add the regression tests** to `crates/quic/tests/conn_rx.rs`, using its `conn()` and `peer_params_failed()`:
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
  - Run `cargo test -p quic --test conn_rx`. Expected: PASS. The behaviour is already right; these tests pin what the new ensures prove.
- [ ] **Step 3: Add the Interfaces items** to conn.rs.
  - On `close`, add above the fn:
    ```
    //= https://www.rfc-editor.org/rfc/rfc9000#section-10.2.1
    //# An endpoint enters the closing state after initiating an immediate
    //# close.
    ```
  - On `on_tls_alert`, cite RFC 9001 §4.8 with `//# A TLS alert is converted into a QUIC connection error.  The` through `//# [QUIC-TRANSPORT].` (rfc9001.txt:883-886).
  - On `on_peer_params`, cite RFC 9000 §7.3 with the same "MUST treat the following as a connection error of type TRANSPORT_PARAMETER_ERROR or PROTOCOL_VIOLATION:" block as handshake.rs:354-360.
  - `close_internal`'s empty reason needs `reason_cap(Seq::<u8>::empty()) =~= Seq::<u8>::empty()` at most.
- [ ] **Step 4: Verify.**
  - Run the recipe for `quic` then `quictls` (`E=…/t1`).
  - Expected: 0 errors in both.
  - Record "after" in §4 for `close`, `close_internal`, `on_tls_alert`, `on_peer_params` and the callers `close_on_error`, `on_counted`, `on_handshake_complete`, `H3Server::apply`, `H3Server::pump`, plus `on_data` and `poll_transmit` (the ±5% check).
  - If a caller trips rlimit 4, put `#[verifier::spinoff_prover]` on it (`close_on_error`, `on_counted`), or hide the new conjuncts there with a closed wrapper predicate. Never raise the rlimit.
- [ ] **Step 5: Full checks.**
  - `cargo build && cargo test --workspace`: 904 passed, 0 warnings.
  - `scripts/verify.sh`: the exact final line.
  - The escape grep: 0.
  - The quote check on conn.rs: `N citations, 0 bad`.
  - `duvet report`: exit 0.
- [ ] **Step 6: Commit.**
  ```bash
  git add crates/quic/src/conn.rs crates/quic/tests/conn_rx.rs docs/superpowers/specs/2026-11-05-phase-9-acceptance-and-closes-design.md
  git commit -m "feat(quic, 9a T1): Connection::close_spec; close, close_internal, on_tls_alert and on_peer_params prove the close code (RFC 9000 §10.2.1, §7.3; RFC 9001 §4.8)"
  ```
- [ ] **Step 7: Mutations.** Each one alone, then restore with `git checkout -- crates/quic/src/conn.rs`.
  - **T1-M1:** in `on_tls_alert`, `self.close_internal(alert as u64)`. Expected: `on_tls_alert`'s `close_spec` postcondition fails.
  - **T1-M2:** in `close`, pass `!app` to `enter_closing`. Expected: `close`'s `close_spec` postcondition fails.
  - **T1-M3:** in `on_peer_params`, `self.close_internal(PROTOCOL_VIOLATION)`. Expected: `on_peer_params`'s `close_spec` postcondition fails.

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
  - The alert branch needs `(CRYPTO_ERROR_BASE + ((code - CRYPTO_ERROR_BASE) as u8) as u64) as u64 == code` under `CRYPTO_ERROR_BASE <= code <= CRYPTO_ERROR_BASE + 0xff`. Use one `assert`; if Z3 does not close it, add `by (bit_vector)` with the range as its `requires`.
  - Above `report`, cite RFC 9001 §4.8 with the quote from Task 1 Step 3.
  - Replace the comment at :120-125. Its first sentence becomes: `// Every TLS error is passed to a close, and the ensures pins its code: the alert as CRYPTO_ERROR_BASE + alert, which is how QUIC sends alert X; a transport code (0x0a, 0x0d) as it is; anything past VARINT_MAX as INTERNAL_ERROR. tampered_finished_0x133, error_ranges and a2_closes_0x178 are regression checks.` Keep the rest of the comment (the closing state, the draining sentence).
- [ ] **Step 2: Verify.**
  - Run the recipe for `quictls` (`E=…/t2`). Expected: 0 errors.
  - Record `shut`, `report`, and every caller `rl.py` lists in its top 6.
  - The callers' existing `!(final … is Open)` ensures (tls_step :546-547, superseded :595-596) must still verify: `Closing` implies not `Open`.
- [ ] **Step 3: Full checks.**
  - `cargo test --workspace`: 904, including `tampered_finished_0x133`, `error_ranges` and `a2_closes_0x178`.
  - `verify.sh`: the exact line.
  - The escape grep: 0.
  - The quote check on server.rs: `N citations, 0 bad`.
  - `duvet report`: exit 0.
- [ ] **Step 4: Commit.**
  ```bash
  git add crates/quictls/src/server.rs docs/superpowers/specs/2026-11-05-phase-9-acceptance-and-closes-design.md
  git commit -m "feat(quictls, 9a T2): shut and report prove Closing with the exact close code (RFC 9001 §4.8)"
  ```
- [ ] **Step 5: Mutations.** Each alone, then `git checkout -- crates/quictls/src/server.rs`.
  - **T2-M1:** in `report`'s last branch, `shut(c, PROTOCOL_VIOLATION, now)`. Expected: `report`'s `close_spec` postcondition fails.
  - **T2-M2:** in `report`'s alert branch, `c.on_tls_alert(((code - CRYPTO_ERROR_BASE) as u8) ^ 1, now)`. Expected: `report`'s `close_spec` postcondition fails.
  - **T2-M3:** in `shut`, `c.close(code, true, …)`. Expected: `shut`'s postcondition fails.

### Task 3: Tight CRYPTO end and `crypto_allowed_err` (P2, quic half)

**Files:**
- Modify: `crates/quic/src/crypto_stream.rs` (`wf` :29-32, `on_crypto` :56-101, `read` :104-128; new spec and proof fns).
- Modify: `crates/quic/src/conn.rs` (new `crypto_inserted` next to `crypto_base_spec` :272, and `lemma_crypto_end_received`).
- Test: `crates/quic/tests/crypto_stream.rs`, `crates/quictls/tests/server.rs`.
- Modify: design doc §4 (Task 3 rows).

**Interfaces:**
- Consumes: `Reassembly::{insert, pop, new, new_at}`'s existing ensures, `lemma_wf`, `lemma_received_push`, `lemma_contiguous_exists`. Do not change reassembly.rs.
- Produces (`quic::crypto_stream`):
  - `pub open spec fn crypto_window_exceeded(base: nat, offset: u64, len: nat) -> bool` = `len > 0 && offset + len > base + MAX_CRYPTO_BUFFER`. This is the named own-limit, a window of at least §7.5's 4096 floor. Cite §7.5's 4096 sentence (crypto_stream.rs:12-14).
  - `pub open spec fn crypto_allowed_err(s: CryptoStream, offset: u64, len: nat, c: u64) -> bool` = `c == CRYPTO_BUFFER_EXCEEDED && crypto_window_exceeded(s.reassembly().base(), offset, len)`. Cite §7.5 "If an endpoint does not expand its buffer, it MUST close …" (crypto_stream.rs:90-92).
  - `impl CryptoStream`:
    - `pub closed spec fn tight(&self) -> bool` = `self.reassembly().buf_len() > 0 ==> rfc_received(self.reassembly().inserted()).contains_key((self.reassembly().base() + self.reassembly().buf_len() - 1) as nat)`. Cite RFC 9001 §4.1.3's "MUST NOT contain data that extends past the end of previously received data" (as at quictls server.rs:572-575): this is what makes the window end "the end of received data".
    - `wf` becomes `reassembly().wf() && buf_len() <= MAX_CRYPTO_BUFFER && self.tight()`.
    - `pub proof fn lemma_end_received(&self)`: requires `self.wf()`; ensures `self.reassembly().base() + self.reassembly().buf_len() > 0 ==> rfc_received(self.reassembly().inserted()).contains_key((self.reassembly().base() + self.reassembly().buf_len() - 1) as nat)`.
      - When `buf_len == 0`, this is `base - 1`, received because `base <= rfc_contiguous` (from `lemma_wf` and `lemma_contiguous_exists`).
  - Private `proof fn lemma_insert_tight(a: CryptoStream, b: CryptoStream, off: u64, d: Seq<u8>)`:
    - requires `a.wf()`, `b.reassembly().wf()`, `d.len() > 0`, `off + d.len() > a.reassembly().base()`, `b.reassembly().inserted() == a.reassembly().inserted().push((off as nat, d))`, `b.reassembly().base() == a.reassembly().base()`, and insert's end bound;
    - ensures `b.tight()`.
    - The proof: `lemma_received_push` puts `off+len-1` and the old last slot in the new map, and `lemma_wf` on `b` puts every received key below the new end. So the new end is `max(old end, off+len)`, and its last slot is received.
  - `read` gets the same argument privately: end and `inserted` are unchanged, and base does not decrease.
  - `on_crypto(&mut self, offset: u64, data: &[u8]) -> (r: Result<(), u64>)`. The body order becomes: `end <= base` → `Ok`; `data.len() == 0` → `Ok`; `end > base + MAX_CRYPTO_BUFFER` → `Err(CRYPTO_BUFFER_EXCEEDED)`; then `insert`, then `proof { lemma_insert_tight(*old(self), *self, offset, data@) }`. Ensures (the iff changes; the other clauses stay as today):
    ```
    final(self).wf(),
    r is Err <==> crypto_window_exceeded(old(self).reassembly().base(), offset, data@.len()),
    r is Err ==> r == Err::<(), u64>(CRYPTO_BUFFER_EXCEEDED),
    r matches Err(c) ==> crypto_allowed_err(*old(self), offset, data@.len(), c),
    (r is Err || offset + data@.len() <= old(self).reassembly().base() || data@.len() == 0) ==> *final(self) == *old(self),
    (r is Ok && offset + data@.len() > old(self).reassembly().base() && data@.len() > 0) ==> { …unchanged… },
    ```
- Produces (`quic::conn`, `impl Connection`):
  - `pub closed spec fn crypto_inserted(&self, k: PacketKind) -> Seq<(nat, Seq<u8>)>` = `crx_i`/`crx_h`/`crx_1` `.reassembly().inserted()`, by `k`, as in `crypto_base_spec`.
  - `pub proof fn lemma_crypto_end_received(&self, k: PacketKind)`: requires `self.wf()`; ensures `self.crypto_base_spec(k) <= self.crypto_end_spec(k)` and `self.crypto_end_spec(k) > 0 ==> rfc_received(self.crypto_inserted(k)).contains_key((self.crypto_end_spec(k) - 1) as nat)`.

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
  - In `crates/quictls/tests/server.rs`, next to `empty_gapped_initial_ok`:
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
  - Run `cargo test -p quic --test crypto_stream` and `cargo test -p quictls --test server empty_initial_past_window_ok`.
  - Expected: `crypto_empty_past_window_ok` FAILS (`Err(13)` at offset 16385); `empty_initial_past_window_ok` FAILS (phase Closing); `crypto_empty_keeps_end` PASSES. The last one is the pre-753ec2d pin, which Step 6's M1 shows failing.
- [ ] **Step 2: Implement the Interfaces items.**
  - `CryptoStream::new` and `new_at` get `tight` from `buf_len == 0`.
  - `Connection`'s `discard` (`CryptoStream::new_at(self.crx_i.end())`), `crypto_read` and `on_crypto_frame` need no edit: they already prove `crx_*.wf()` through CryptoStream's ensures.
  - Keep `tight` closed so that no conn.rs VC unfolds it.
- [ ] **Step 3: Run the tests.** `cargo test -p quic --test crypto_stream` and `cargo test -p quictls --test server`. Expected: PASS, `crypto_limit` included.
- [ ] **Step 4: Verify.**
  - Run the recipe for `quic` then `quictls` (`E=…/t3`). Expected: 0 errors.
  - Record `on_crypto`, `read`, `lemma_insert_tight`, `crypto_read`, `on_crypto_frame`, `discard`, `on_data`, `poll_transmit`.
- [ ] **Step 5: Full checks, then commit.**
  - Checks: tests 907, 0 warnings; `verify.sh`'s exact line; escape grep 0; quote check on crypto_stream.rs and conn.rs; `duvet report` exit 0.
  ```bash
  git add crates/quic/src/crypto_stream.rs crates/quic/src/conn.rs crates/quic/tests/crypto_stream.rs crates/quictls/tests/server.rs docs/superpowers/specs/2026-11-05-phase-9-acceptance-and-closes-design.md
  git commit -m "fix(quic, 9a T3): CRYPTO window ends at a received byte (tight end in CryptoStream::wf); an empty CRYPTO frame past the window is not CRYPTO_BUFFER_EXCEEDED; on_crypto's acceptance clause (RFC 9000 §7.5, RFC 9001 §4.1.3)"
  ```
- [ ] **Step 6: Mutations.** Each alone on the committed tree, then `git checkout -- crates/quic/src/crypto_stream.rs`.
  - **M1, the 753ec2d revert.** It must fail on the tight end alone, so it also reverts the clauses 753ec2d and this task added:
    1. Delete the `if data.len() == 0 { … return Ok(()); }` block.
    2. Replace the two frame clauses with their pre-753ec2d forms: `(r is Err || offset + data@.len() <= old(self).reassembly().base()) ==> *final(self) == *old(self),` and `(r is Ok && offset + data@.len() > old(self).reassembly().base()) ==> { … }`.
    3. Make the iff `r is Err <==> offset + data@.len() > old(self).reassembly().base() + MAX_CRYPTO_BUFFER`.
    4. Delete the `r matches Err(c) ==> crypto_allowed_err(..)` line.
    - Expected: `quic` fails only on `lemma_insert_tight`'s `d.len() > 0` precondition at its call in `on_crypto`: an empty insert past the end leaves an unreceived last slot. `cargo test` also fails `crypto_empty_keeps_end`, `empty_gapped_initial_ok` and `empty_initial_after_switch_ok`.
  - **M2, the window check before the empty check** (main's order, with this task's ensures kept). Move the `data.len() == 0` block after the `end > base + MAX_CRYPTO_BUFFER` block. Expected: the `r is Err <==> crypto_window_exceeded(..)` and `crypto_allowed_err` postconditions fail.

### Task 4: quictls acceptance and close code on the CRYPTO path (P2, quictls half)

**Files:**
- Modify: `crates/quictls/src/server.rs`:
  - `key_events` :155-171;
  - `superseded` :572-616, removing :607-613;
  - `key_changes` :765-802, `on_params` :804-834;
  - new spec fns after `level_rank` (:54) and in `impl QuicServer` after `unread` (:746).
- Test: `crates/quictls/tests/server.rs`.
- Modify: design doc §4 (Task 4 rows; check that every row has both columns).

**Interfaces:**
- Consumes:
  - Task 1: `close_spec`, `client_scid_spec`, `on_peer_params`'s ensures;
  - Task 2: `shut`'s ensures;
  - Task 3: `crypto_inserted`, `lemma_crypto_end_received`;
  - `quic::reassembly::rfc_received`, `quic::tp::rfc_transport_params`, `tls::server::{spec_reader, spec_secrets_level}`, `tls::flight::SpecTlsEvent`.
- Produces (`quictls::server`, all private):
  - `spec fn past_received(c: Connection, k: PacketKind, end: nat) -> bool` = `exists|p: nat| p >= end && #[trigger] rfc_received(c.crypto_inserted(k)).contains_key(p)`. Cite RFC 9001 §4.1.3 bullet 1 and its PROTOCOL_VIOLATION sentence (server.rs:572-579's two blocks).
  - `spec fn tp_allowed_err(c: Connection, b: Seq<u8>) -> bool` = `match rfc_transport_params(b, true) { Err(_) => true, Ok(t) => t.initial_source_connection_id != Some(c.client_scid_spec()) }`.
    - Cite RFC 9000 §7.4 `//# An endpoint MUST treat receipt of a transport parameter with an` … `//# TRANSPORT_PARAMETER_ERROR.` (rfc9000.txt:2016-2018), and §7.3 as in Task 1.
    - Whether `rfc_transport_params` rejects only what the RFC allows is 9b's P3.
  - `spec fn spec_key_events(ev: Seq<SpecTlsEvent>) -> (bool, bool)` = `(exists|i: int| 0 <= i < ev.len() && #[trigger] spec_secrets_level(ev[i], Level::Handshake), exists|i: int| #![trigger ev[i]] 0 <= i < ev.len() && ev[i] is Complete)`.
  - `fn key_events(ev: &Vec<TlsEvent>) -> (r: (bool, bool))`: ensures `r == spec_key_events(ev.deep_view())`. The loop invariant states the two exists over `j < i`, and links `ev.deep_view()[j] == ev@[j].deep_view()`, as `apply` does at :704.
  - `impl QuicServer`:
    - `spec fn tls_unconsumed(&self, l: Level, k: PacketKind) -> bool` = `spec_reader(self.hs@, l).len() > 0 || past_received(self.h3.conn_spec(), k, self.h3.conn_spec().crypto_base_spec(k))`.
    - Cite RFC 9001 §4.1.3's "When TLS provides keys for a higher encryption level … PROTOCOL_VIOLATION." (server.rs:724-728).
    - `unread` stays; it is the log's number. A short lemma gives `self.unread(l, k) > 0 ==> self.tls_unconsumed(l, k)`, from `lemma_crypto_end_received`.
  - `superseded(&mut self, now: u64) -> (cont: bool)`:
    - Delete :607-613, the `crypto_read(Initial)` and its close (design §3.1 P2: unreachable, and no §4.1.3 basis).
    - In the comment at :580-584, drop "or newly contiguous" and the `crypto_read` sentence.
    - Keep every existing ensures, and add:
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
  - `on_params(&mut self, b: &Vec<u8>, now: u64) -> (ok: bool)` adds:
    ```
    !ok && old(self).conn_spec().phase_spec() is Open ==> {
        &&& tp_allowed_err(old(self).conn_spec(), b@)
        &&& final(self).conn_spec().phase_spec() is Closing
        &&& final(self).conn_spec().close_spec() == Some((false, TRANSPORT_PARAMETER_ERROR, Seq::<u8>::empty()))
    },
    ```
  - Not added in 9a: the `core_ok` invariant `crypto_base(Initial) >= init_end` (design §5.2). The lift of these clauses to `apply`/`feed`/`tls_step` is 9c, with P7's `allowed_tls_err`.

- [ ] **Step 1: Regression tests** in `crates/quictls/tests/server.rs`:
  ```rust
  /// The ClientHello's tail again, ending exactly at init_end: not past the end (RFC 9001 §4.1.3).
  #[test]
  fn initial_tail_retransmit_after_switch_ok() {
      let ch = h3ch(id);
      let l = ch.len();
      let mut s = flight();
      receive(&mut s, &ini(&qc::S1, 1, || vec![cr(l - 10, &ch[l - 10..])]), 2);
      assert_eq!(s.conn().phase(), Phase::Open);
  }

  /// Bytes TLS has not consumed at the key change (0x0a) are checked before the peer's transport
  /// parameters (a duplicate, 0x08): the first error is the one sent.
  #[test]
  fn trailing_bytes_before_bad_tp_pv() {
      let mut ch = h3ch(|e| {
          for (t, d) in e.iter_mut() {
              if *t == 0x39 {
                  *d = qc::hex("010105 010105");
              }
          }
      });
      ch.push(0x01);
      let mut s = accept(&ini(&qc::S1, 0, || vec![cr(0, &ch)]));
      assert_eq!(close_code(&mut s), 0x0a);
  }
  ```
  - Run `cargo test -p quictls --test server`. Expected: PASS on the Task 3 tree. Both pin behaviour that the new ensures prove; M1 and M4 below show the first failing.
- [ ] **Step 2: Implement the Interfaces items.**
  - `superseded`'s `!cont` path proves `past_received` with the witness `crypto_end(Initial) - 1`. Get it from `lemma_crypto_end_received(PacketKind::Initial)` on `old(self).conn_spec()`, whose `wf` comes from `self.h3.conn()`'s ensures.
  - `key_changes` uses `unconsumed`'s `r == (unread > 0)` and the `unread ==> tls_unconsumed` lemma.
  - `on_params`' Ok arm uses `parse_transport_params`'s `rfc_transport_params(b@, true) == Ok(t@)` and Task 1's `on_peer_params` ensures.
- [ ] **Step 3: Verify.**
  - Run the recipe for `quictls` (`E=…/t4`). Expected: 0 errors.
  - Record `superseded`, `key_changes`, `on_params`, `key_events`, `tls_step`, `apply`, `feed`, and the quic rows `on_data`/`poll_transmit` from the Task 3 run.
- [ ] **Step 4: Fill design §4 and the pilot result.**
  - Every row has before and after.
  - Under the table, add one line per fn whose rlimit rose by more than 20%, naming the cause, or the line "no touched fn rose by more than 20%".
- [ ] **Step 5: Full checks, then commit.**
  - Checks: `cargo build && cargo test --workspace`, 909 passed, 0 warnings; `verify.sh`'s exact line; escape grep 0; quote check on server.rs; `duvet report` exit 0.
  ```bash
  git add crates/quictls/src/server.rs crates/quictls/tests/server.rs docs/superpowers/specs/2026-11-05-phase-9-acceptance-and-closes-design.md
  git commit -m "feat(quictls, 9a T4): superseded, key_changes and on_params prove an RFC-allowed reason and the exact close code; superseded's unreachable newly-contiguous close removed (RFC 9001 §4.1.3, RFC 9000 §7.3, §7.4)"
  ```
- [ ] **Step 6: Mutations.** Each alone, then `git checkout -- crates/quictls/src/server.rs`.
  - **T4-M1:** in `superseded`, `if e >= self.init_end`. Expected: the `past_received` postcondition fails (`e - 1 < init_end`), and `cargo test` fails `initial_tail_retransmit_after_switch_ok`.
  - **T4-M2:** in `key_changes`' first check, replace `self.unconsumed(Level::Initial, PacketKind::Initial)` with `self.h3.conn().crypto_end(PacketKind::Initial) > 0`. Expected: the `tls_unconsumed` postcondition fails.
  - **T4-M3:** in `on_params`' `Err` arm, `shut(…, PROTOCOL_VIOLATION, now)`. Expected: the `close_spec` postcondition fails.
  - **T4-M4:** restore the deleted block verbatim, from main's numbering (Task 2 shifted the file): `git show 73cc244:crates/quictls/src/server.rs | sed -n 607,613p`, pasted back between `superseded`'s `e > init_end` block and its final `sync_keys()`. Expected: the `!cont ==> … crypto_end_spec(Initial) > init_end` postcondition fails. This is the evidence for design §5.2: the old close cannot carry an acceptance clause without the invariant.

---

## Self-review notes

- **Spec coverage:** design §3.1 P0 → Task 1; P1 → Task 2; P2 (tight end, `crypto_allowed_err`, `crypto_inserted`, the empty-before-window fix) → Task 3; P2 (quictls clauses, the branch removal) → Task 4; §4 table → every task, closed in Task 4 Step 4. The RecvStream empty-insert audit item has no task by design (§3.1: no fix; 9c records it).
- **Names used across tasks:** `close_spec`, `reason_cap`, `client_scid_spec` (T1) → T2, T4. `crypto_inserted`, `lemma_crypto_end_received` (T3) → T4. `shut`'s new ensures (T2) → T4.
- **Test counts:** 902 → 904 (T1) → 904 (T2) → 907 (T3) → 909 (T4).
