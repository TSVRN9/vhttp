# RCAs from Phase 9a, 2026-11-06 (fixes on branch `phase-9a`, not yet on main)

## 1. on_peer_params proved only "close ==> mismatch" (9a T1 review I1)
- **Defect:** `Connection::on_peer_params` proved that a close implies an initial_source_connection_id mismatch, but not that a mismatch closes (the RFC 9000 §7.3 MUST). Deleting the `close_internal` call still verified. Fixed on phase-9a in 87c3561.
- **Escape:** the design's rule 1 is one-way (`Err ==> allowed`). Nothing required the converse for a MUST-close trigger, and no planned mutation deleted a close call.
- **Class:** C7, required close missing.
- **Catch:** plan rule 1b. Where the RFC says MUST close on a trigger, the site proves `old Open && trigger ==> Closing with that code`. Every touched close site gets a delete-the-close mutation that must fail on a postcondition.
- **Evidence:** mutations T1-M4..T1-M7 (delete each of the four closes) fail on postconditions (`.worktrees/vt-9a-evidence/t1`). Task 3's D3 is the same check for on_crypto_frame. Since 9r2 T2 these are registry rows T1-M4..T1-M7 and T3-D3, re-run by `scripts/mutants.sh run` before every merge (`.worktrees/vt-9r2-evidence/r2/mutants-run.log`).
- **Open:** the remaining close sites (on_handshake_complete in 9a Task 5; close_on_error and on_counted in 9c).

## 2. CRYPTO window anchored at the read offset (9a T3 review I2; a real bug, already on main)
- **Defect:** RFC 9000 §7.5: "Implementations MUST support buffering at least 4096 bytes of data received in out-of-order CRYPTO frames". The window was `read offset + 16384`. One datagram with CRYPTO[0,13000) and then CRYPTO[16000,16500) closed with 0x0d while holding 500 out-of-order bytes. Fixed on phase-9a in fcf9ff0 (anchored at the contiguous end) and e5a85ae.
- **Escape:** `crypto_window_exceeded` and the floor lemma were transcribed from the code's own base-relative notion, not from the RFC sentence, so the proof only checked the code against itself. No test mixed in-order and out-of-order CRYPTO data in one datagram.
- **Class:** C8, spec written from code instead of the RFC.
- **Catch:** plan rule 1d. Every RFC "MUST support at least N" floor is a lemma over RFC-defined quantities (here `rfc_contiguous` and out-of-order bytes), with the boundary counterexample as a test.
- **Evidence:** mutation M4 (re-anchor at the read offset) fails the floor lemma. The test `crypto_in_and_out_of_order_one_datagram_ok` (conn_rx.rs) failed on fcb43a7 and passes after the fix (`.worktrees/vt-9a-evidence/t3`).

## 3. Open: the CRYPTO limit is an offset span, not a byte count
- **Status:** OPEN conformance item under the strict reading of RFC 9000 §7.5. A 1-byte frame at the contiguous end + 20000 closes with 0x0d while almost nothing is held.
- **Why it is not fixed yet:** `Reassembly` stores one byte and one flag per offset from base to the highest end, so memory follows the span. A held-bytes limit needs a sparse fragment store or a range-set Reassembly with a proved memory bound. That is multi-session work, scheduled as its own task.
- **Rejected alternatives:**
  - A large span cap still closes on far frames.
  - Recording it as an accepted deviation would be a shortcut.
- **Interpretation question for the user:** does "at least 4096 bytes of data received in out-of-order CRYPTO frames" count bytes held, or does an offset-span limit of at least 4096 meet it?

## 4. Task 3c dispatched against a representation that doesn't exist (controller error)
- **Defect:** the controller wrote Task 3c assuming `Reassembly` is a range set and dispatched it without a preflight. The implementer stopped before changing anything.
- **Escape:** controller-added tasks skipped the preflight that plan tasks get.
- **Class:** C16, plan drift.
- **Catch:** every controller-added task gets a recorded preflight read of each type and fn it names (representation, cost) before dispatch. 9r2's plan-lint extends to checking that the named items and their fields exist.

## 5. Missing RFC citation on quictls `report` (9a T2 review I1)
- **Defect:** the alert-to-code mapping in `report` had no RFC 9001 §4.8 `//=` citation. Fixed on phase-9a in 256d44e.
- **Escape:** the citation rule is prose. `check_quotes.py` verifies the quotes that exist and cannot see missing ones.
- **Class:** C1.
- **Catch (in place, 9r2 T3):** `tools/citations.py cite` (verify.sh, after check-quotes) requires a `//= https://www.rfc-editor.org/rfc/..#..` line with a `//#` quote in the comment block above every `allowed_*err` spec fn, every exec fn whose ensures pin `close_spec() == Some((app, code, reason))` with a literal, a codes.rs constant or a call in `code`, and every spec fn such a call names (`report_code`). `tools/citations.py closes` also requires a `tools/mutants.tsv` row (fn column) for each close-code fn. On the current tree: 5 predicates/mappings and 4 close-code fns, all cited and all with rows. Evidence: scripts/gate-demos.sh "citations" demos strip the citation from a predicate, a close-code fn and a mapping fn (each fails naming the fn), and fail with no row, a row naming the fn only in origin or regex, no tsv, no crates/, no codes.rs. Known limit: it checks that a citation exists, not that it is the right one.

## 6. task-brief extracted two tasks into one brief
- **Defect:** the SDD `task-brief` script matched `### Task 3` as a prefix, so Task 3b's text went into Task 3's brief. Caught by the controller before dispatch.
- **Class:** C16 (tooling).
- **Catch:** before each dispatch the controller checks that the brief has exactly one `^### ` heading. The script is external plugin code and is not edited here.

## 7. C8 recurred three times in one night (T3 I2, T4 I1, T6 I1)
- **Defect:** three `allowed_*err` predicates read the code's own bookkeeping instead of RFC quantities. T3 used the read-offset window, T4 the `seen` mask, T6 rfc_recv's running `high`. Each proof then checked the code against itself. All three are fixed on phase-9a: fcf9ff0, 9afdf5e, 0a8c534.
- **Escape:** rule 1d (state floors over RFC quantities) was added after the first instance, but only as prose. Nothing required a per-predicate re-anchoring mutation, so the third instance slipped past again until review.
- **Catch:**
  - Plan rule 1d now names one re-anchoring mutation per predicate (model and code together). Reviewers check that list (phase-9a facc168).
  - In place since 9r2 T4: `scripts/rfc-quantity.sh` (tools/rfc_quantity.py, run by verify.sh) reads every `allowed_*err` body and the spec fns it calls, transitively, and fails on a struct field, a non-vstd method, `self`, an unscanned call, or a name read outside a call argument, unless a cited `// rfc-quantity: READ:` line naming that read, a cited line of tools/rfc-quantity-allow.txt (a ratchet: ALLOW_DIGEST, a sha256 of its lines in the tool, pins it) or a line of the shrinking tools/rfc-quantity-open.txt vouches for it. The `seen` instance needed the name rule: `seen & tp_bit(id)` reads no field. Every vouch is keyed by its root predicate and pinned to a sha256 of the source text the predicate reaches, so a one-token edit that changes no list (the walk arm `None => true`, an open-listed counter passed as a vouched parameter) fails until the vouches are re-reviewed.
  - Still open, owner 9c: the open ratchet's 6 lines (10 reads). `recv_allowed_err`'s helpers read the model's `final_size` and `limit` and the caller's `conn_room`, none tied to the RFC quantity by a lemma (9a final review M1; design §3.3 re-anchors `final_size`, lifts `conn_room` and only notes `limit`). `s.ins` is vouched: it is the RFC's STREAM frames received while the final size is unknown, which recv_inv ties (`state is Recv <==> final_size is None`).
- **Evidence:** the three originals, canned under tools/gate-demos/rfcq/bad/, fail the gate: T6's helpers on `s.high`, T4's `allowed_tp_err_from` on `seen`, T3's `crypto_allowed_err` on `s.reassembly()` (gate-demos.sh "rfc-quantity: T6's/T4's/T3's original" demos; the same three files dropped into a copy of the real tree fail against the real lists, `.worktrees/vt-9r2-evidence/r4/originals-on-real-tree.log`). T4-M3 verified on the pre-fix tree and fails after the fix. T6-M2 fails both `lemma_data_step` and `lemma_recv_err_rfc` after the fix. M4 fails the T3 floor lemma. Since 9r2 T2 the three re-anchoring mutations are registry rows T4-M3, T6-M2 and T3-M4, re-run mechanically before every merge (`.worktrees/vt-9r2-evidence/r2/mutants-run.log`).

## 8. Open items for 9r2 gathered tonight
- Missing-citation gate (§5 above).
- The model-state gate for `allowed_*err` bodies (§7).
- The `Reassembly::insert` class fix: `insert`'s own ensures should make an empty insert a no-op, so no future holder can repeat 753ec2d or T6. Scheduled with 3c', which reworks Reassembly.
- shellcheck repo-wide. It needs the user's sudo. A controller-side unquoted heredoc lost two words of a ledger line tonight, a class shellcheck flags.
