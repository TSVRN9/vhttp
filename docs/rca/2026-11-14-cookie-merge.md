# The cookie merge: a quadratic copy in the call that completes a request's HEADERS frame (C15, phase 9b3)

Status: complete (9b3 Task 13). Written with the 9b3 spec (`docs/superpowers/specs/2026-11-14-phase-9b3-h3-input-costs-design.md`,
D5, D13) before the fix; Task 1 committed the failing test (1271446), Task 4 the fix (05adcf1). Line numbers in
Defect through Escape are at e8d97e5 (phase-9b2's tip; h3 is unchanged from main a293f81).

- **Defect**: `build_headers` (crates/h3/src/message.rs:1374-1436) builds `Request.headers` for every request HEADERS
  frame. `validate_request` calls it at :1493, and `headers_frame` (request.rs:839) calls `validate_request`. It merges
  cookie lines as RFC 9114 §4.2.1 requires. For each cookie line after the first it does five things:
  1. `find_first(out, "cookie")` (:1396) scans `out` from the start.
  2. `slice_to_vec(&out[k].value)` (:1399) copies the whole accumulated value into an exact-capacity `Vec`.
  3. `extend_from_slice("; ")` (:1401) outgrows that capacity, so a `realloc` can move the whole value again.
  4. `extend_from_slice(&f.value)` (:1402) appends the line's value, and `slice_to_vec` of the name (:1403) copies 6 bytes.
  5. `out.set(k, ..)` (:1418) frees the previous value.

  After k extra lines the value holds `L_k = v + k·(v + 2)` bytes, for lines of `v` bytes each. With every realloc
  moving, line k copies `2·L_{k-1} + v + 8` bytes, so n lines copy about `n²·(v + 2)` bytes. The rescans are a second
  quadratic term. `find_first` (:871) scans all of `out`, with no early exit. `out` holds the regular fields so far,
  with cookies already merged into one line. So each cookie line compares names against every non-cookie field before
  it, and a frame of `r` other fields then `c` cookie lines costs `c·(r + 1)` comparisons. That is at most `(n/2)²`,
  about 739,000 for `n` = 1,719 empty-valued lines. A cookie-only frame rescans almost nothing, because `out` stays
  one line long.

  What bounds it is the decoded budget. Each line charges `6 + v + 32` against `MAX_FIELD_SECTION_SIZE` = 65536
  (limits.rs:24, enforced by `decode_field_section_bounded`), so `n ≤ 65536/(38 + v)`. Maximizing
  `(65536/(38 + v))²·(v + 2)` over `v` gives `(38 + v) = 2·(v + 2)`, so `v = 34` and `n ≈ 910`. Encoded, each such line
  is `v + 2` bytes (`0x55`, the length, the value), so the frame is about 33 KB: under the 65536-byte HEADERS cap, and
  the decoded budget is what binds.

  The cost is per call. A HEADERS frame that arrives over many calls is decoded and merged in the one call that
  delivers its last byte (`RequestStream::top_up` and `run`, request.rs:1695 and :1210), so a call given `d = 1`
  pays all of it.
- **Incidents**: introduced in 7feebeb (2026-10-28, phase 2b, "verified request/response field validation") along with
  the comment at :1372. Found 2026-11-12 by the cost sweep (`docs/rca/2026-11-12-cost-sweep.md` rows H1 and H2; the
  sweep's §F notes that the comment leaves out the copy). No test or interop run has triggered it: `cookie_merge`
  (crates/h3/tests/message.rs) merges two lines.
- **Escape**:
  1. Cost was in no contract (C15). `build_headers` ensures only `fields_view(out@) == request_headers(..)`. Verus checks
     the result, so a quadratic implementation of a linear spec verifies.
  2. The comment named the cheap part and had no tracker. It reads: "each cookie line rescans `out` for the first
     cookie, O(n^2) in field count; fields are capped by MAX_FIELD_SECTION_SIZE (2048 lines at most)". Its O(n²)
     is a valid bound on the rescans, but the comment says nothing about the value copies, which are the larger term in
     bytes (29.6 MB at the worst case below). Both terms are about equal in time (below). So its "2048 lines" read as
     a harmless count of comparisons. No `ponytail:` or `shortcut:`
     comment has a carryover row or a gate, so nothing sent a review back to check the claim.
  3. No cost check reached it. The 8b MIR cost analysis has the decoder `none`
     (`decode_field_section_bounded Unsupported`, tools/ct-driver/expected-cost.txt:24). `validate_request` and
     `build_headers` are not cost targets (tools/ct-driver/cost-targets.txt). h3's only counting-allocator test
     (crates/quic/tests/h3_alloc.rs) covers `H3Server::flush`, not input.
  4. Per-call budgets counted the completed unit by name, not by proof. 9b2's D14 lists "QPACK field-section decode"
     as O(message) work for 9b5, but nothing proves the processing of a completed frame linear, and the quadratic
     term sat inside that unproved term.
  5. Tests scale nothing: `cookie_merge` has two lines.
- **Class**: C15 (algorithmic cost not in contracts). Two sub-classes, each needing its own catch:
  - (a) work hidden in an unproved "completed unit" term, or in a callee with no cost contract;
  - (b) comments that admit a cost but have no tracker.
- **Catch** (as built; the spec proposed a cost-charge gate, which Task 12 retired, below):
  1. A proof (README order 1), 05adcf1. `build_headers` merges in two passes into exact `CapVec`s (`cookie_scan` counts
     the merged length, `build_headers` pushes at most that many bytes, so no push reallocates). It returns a
     `Ghost<nat>` with ensures `r.1@ <= c_bh()·(fields_size(fv) + n + 1)`, `c_bh() = 20`, and `eq_bytes_w`,
     `copy_line` and `cookie_scan` carry their own. The bound is part of D9's completed-frame term: `validate_request`
     binds it, `headers_frame` and `RequestStream::on_data` (1bdd1ff, b790f8e) carry it into their ensures, and
     `H3Conn::on_stream_data`, `on_stream_reset` and `on_stop_sending` (c3072f4) prove the per-call bound over it, so
     every call that completes a HEADERS frame has a proved bound linear in the frame, with the stream table's
     `log n` and N6's `removed_fields` term named. The decoder under it is proved too (0f7e4fe: `decode_lines_bounded`,
     `huffman_decode_w`, `decode_string`, each on an exact `CapVec`).
  2. The gate (the spec's order 3, D13) is retired. Task 12 recorded the coordinator's ruling of 2026-11-21 that
     `cost_charge.py` is being retired, so it was not extended to h3. What replaces it for sub-class (a):
     - the proved cost ensures above: a quadratic body cannot meet `c_bh()·(fields_size + n + 1)`, and every caller up
       to `H3Conn`'s entry points sums its callees' returned costs;
     - the same shape at every costed loop with an early exit (`frame::lemma_paid`; `rca-early-return-cost`, the RCA
       2026-11-21-early-return-cost.md) and `carryovers.py`'s cited-id check;
     - the linear `Budget` of the scaffold (row `sc-h3-budget`, owner sc), which closes by construction what the ghost
       returns leave to convention: uncounted std copies, dropped callee `Ghost`s and uncharged looping callees.
     No `tools/cost-uncharged.txt` exists and the cost-gate demos were never written for h3.
  3. Mutants (order 1), applied by hand to Task 4's `build_headers` and rejected by Verus:
     - 9b3-M1, a later cookie copies `merged` into a fresh `CapVec::new(T)` charged `1 + |merged|`: invariant not
       satisfied at the end of the loop body, on `work <= w1 + 2 + 12·i + fields_size(fv.take(i))`;
     - 9b3-M8, a charged `find_first(out)` rescan per cookie line: the same invariant;
     - 9b3-M2, `CapVec::new(T - 1)`: invariant not satisfied before the loop, on `merged.cap() == tot`.
     They are not in `tools/mutants.tsv` (owner, 2026-11-21: mutants are secondary, no mutant row is a deliverable).
     The rows that are there for h3 are 9b3-A1..A4 (the acceptance clauses and the lines budget, Tasks 6 and 12).
  4. A test (order 4; it pins the allocator behaviour the proof's cost model assumes and does not replace the proof):
     `cookie_lines_linear` and `cookie_rescans_linear` in `crates/h3/tests/input_cost.rs` (its own counting
     allocator), the first at n, 2n and 4n (n = 226), whole and one byte per call. Per call: no `realloc`, requested
     bytes at most `COST_A·d + COST_B` (more only for the completing call, by `H3_F` per frame byte), and at most 3x
     per doubling. Task 1 committed them ignored; the tasks that removed their last cause un-ignored them, and all ten tests of the file run and pass at the tip.
  5. Sub-class (b), comments (order 3), built in part:
     - `ponytail:` at message.rs:1372 is gone with the fix, and no `ponytail:` or `shortcut:` comment in
       `crates/h3/src` states an input-path cost any more: limits.rs:18's stale comment (it said the cap was the
       encoded size) is deleted, huffman.rs's one-bit-per-step comment names `cat-C15-stream-parse`, and
       static_table.rs:361's linear scan is the encode side, a constant 99, not an input path (sweep status "no
       change");
     - `tools/carryovers.py check` (Task 12) fails a `crates/*/src` comment that cites a carryover id the tsv lacks or
       holds closed, so a tracker cannot rot silently (it found one closed id cited in quic's send_stream.rs);
     - not built: a check that every cost-admitting comment names an id. It would be a script carrying a guarantee,
       which `CLAUDE.local.md` rule 4 forbids unless written and proved in Verus, and the class's other half (a
       cost the code has and no one admits) is the proof's. A new cost comment that cites no id goes to review.
  6. The residual (pre-flight F26) is unchanged in kind and now has named closers. Each charge is written by hand and
     the cost ensures are upper bounds, so a loop charged too little still verifies: `cat-C15-semantic-cost` (9b4;
     its close must cover 9b3's h3 fns or leave a row open for them), `sc-h3-budget` (the linear `Budget` for h3's
     cost returns), `rca-early-return-cost` (exits), and `cat-C15-mir-cost` (the MIR step cross-check of the bounds
     Verus proves as ghost costs: `parse_varint_w`'s constant, `sort_ids_w`, the QPACK decode fns).
- **Evidence**:
  - Fix: 05adcf1, `build_headers` in two passes into exact buffers. The surrounding chain: 0f7e4fe (QPACK decode and
    Huffman on exact `CapVec`s with proved costs), 1bdd1ff (request buffer on `ByteQueue`, one `Body` per call),
    82c71ef (uni streams), c3072f4 (stream table on `byteq::avl`, the per-call bound), 4261fd4 (constant-size answers).
  - Task 1's failing test (1271446; log: `cookie_lines_linear`, `cookie_rescans_linear`, `control_bytewise` failed on
    the code of e8d97e5) and Task 4's and the tip's numbers, release build, requested bytes (reallocs in the whole
    run):

    | test (n) | Task 1 (before) | Task 4 (after) | tip (6a43542) |
    |---|---|---|---|
    | `cookie_lines_linear` whole, 226 | 2,780,221 (232) | 53,133 (6) | 127,053 (0) |
    | whole, 452 | 11,075,945 (459) | 105,733 (7) | 155,077 (0) |
    | whole, 904 | 44,216,017 (912) | 210,933 (8) | 211,125 (0) |
    | bytewise, 226, completing call | 2,780,222 | 53,134 | 127,053 |
    | bytewise, 904, completing call | 44,216,018 | 210,934 | 211,125 |
    | `cookie_rescans_linear` 215 / 430 / 860 | 215,791 / 708,769 / 2,526,775 | 74,625 / 148,717 / 296,901 | 77,553 / 148,909 / 198,789 |

    Task 1's doubling ratios were 3.98 to 3.99 (quadratic); Task 4's 1.99 to 2.00. The tip's figures are larger at
    n = 226 and flatter in n mostly because Task 6 sized the decoder's `out` at `min(lines, budget/32)` slots of 48 bytes
    (98,304 bytes, `cat-C15-9b3-slots`), a constant the completing call pays once. They are inside the test's own
    budget for a completing call, `H3_F` per frame byte plus `COST_B` (not the `8·d + 4096` of a call that completes
    nothing), and each doubling of n multiplies the requested bytes by 1.2 to 1.9 (Task 1: 3.98).
    Zero `realloc` in every call of every test at the tip (Task 1: 232 to 925).
  - The mutants of Catch 3 and Task 4's rlimit table (`build_headers` 1,346,185, `validate_request` 831,862, well
    under the 8M cap; the five-seed sweep at the tip: h3 max `conn::feed_req` 4,843,695).
  - The new tests in `crates/h3/tests/message.rs`: `cookie_first_after_other_fields`, `cookie_single_line`,
    `cookie_empty_values`, `cookie_alternating_matches_model` (a model merge in the test), `cookie_merge` kept.
  - The residual `cat-C15-semantic-cost` and its successors in Catch 6, all open rows.

## Measured (9b3 spec, release build of h3 at e8d97e5)

Method: one HEADERS frame on a fresh `h3::request::RequestStream`, fed whole to `on_data`.
- The frame holds `:method GET`, `:scheme https` and `:path /` (static indexed lines), `:authority a` (a name
  reference), then n literal lines with static name reference 5 (`cookie`), each with a raw value of v bytes `a`.
- The control frame is the same with name reference 6 (`date`), which is not merged.
- The counters are a counting `#[global_allocator]`: allocations, reallocs, and requested bytes (alloc sizes plus
  realloc new sizes).
- "Copied" counts the merge loop's own copies from the code's steps, assuming every realloc moves:
  `Σ (2·L_{k-1} + v + 8)` plus the first line's `v + 6`.
- Time is the fastest of 3 runs on the developer machine.
- The harness was a throwaway, not kept. Task 1's `cookie_lines_linear` reproduces the v = 34 rows.

| lines | v | frame bytes | allocs | reallocs | requested bytes | copied by the merge | time | merged value |
|---|---|---|---|---|---|---|---|---|
| cookie 214 | 0 | 439 | 656 | 218 | 163,153 | 92,022 | 0.052 ms | 426 |
| cookie 1,719 | 0 | 3,449 | 5,171 | 1,726 | 9,067,195 | 5,913,362 | 0.361 ms | 3,436 |
| date 1,719 | 0 | 3,449 | 3,453 | 18 | 407,113 | - | 0.121 ms | - |
| cookie 1,420 | 8 | 14,211 | 5,695 | 1,429 | 30,441,763 | 20,166,842 | 0.485 ms | 14,198 |
| cookie 113 | 34 | 4,079 | 467 | 118 | 700,937 | 459,912 | 0.039 ms | 4,066 |
| cookie 226 | 34 | 8,147 | 919 | 232 | 2,780,221 | 1,839,190 | 0.095 ms | 8,134 |
| cookie 453 | 34 | 16,319 | 1,827 | 460 | 11,124,801 | 7,388,432 | 0.204 ms | 16,306 |
| **cookie 907** | **34** | **32,665** | **3,643** | **915** | **44,509,357** | **29,617,180** | **0.800 ms** | **32,650** |
| date 907 | 34 | 32,665 | 3,643 | 16 | 265,685 | - | 0.124 ms | - |
| cookie 640 | 64 | 42,253 | 2,575 | 648 | 40,630,999 | 27,034,882 | 0.744 ms | 42,238 |
| cookie 413 | 120 | 50,399 | 1,667 | 420 | 31,240,873 | 20,810,246 | 0.698 ms | 50,384 |

Worst case per HEADERS frame (v = 34, n = 907, the budget's maximum with the four pseudo lines):
- **29.6 MB copied** by the merge from a 32.7 KB frame, which is 44.5 MB requested from the allocator in 915 reallocs;
- **0.80 ms**, against 0.27 MB requested and 0.12 ms for the same frame with non-cookie lines. The rescan-heavy shape
  (half other fields, then empty cookies) takes about as long, 0.7-0.9 ms, with 2.5 MB requested;
- 1,363 requested bytes per frame byte, where 9b2's per-call test budget (`8·d + 4096`) allows 265,416 for this `d`.

The rescan term, measured the same way, with empty values, fastest of 3 (times vary about ±30% between runs):

| frame | lines | requested bytes | time |
|---|---|---|---|
| 860 `accept` lines (static 29) only | 860 | 207,073 | 0.068 ms |
| 859 cookie lines only | 859 | 2,315,071 | 0.12-0.14 ms |
| 860 `accept` then 859 cookie lines (739,000 name comparisons) | 1,719 | 2,521,615 | 0.69-0.93 ms |
| 500 `accept` then 640 cookie lines, v = 34 | 1,140 | 22,361,521 | 0.73 ms |

Each doubling of n multiplies requested bytes by 3.96-4.0, against 1x per line for `date`. The time is modest,
because glibc's `realloc` often grows in place and `memcpy` is fast, but the work is quadratic in the frame. One
merge runs per request stream, at most 100 at once (`MAX_LOCAL_STREAMS`), and streams can follow one another without
limit.

The same harness also fed a `date`-line frame one byte per call. That run corrects sweep row H4:
- A call that completes nothing re-parses only the frame header: `step_frame` returns `Ok(None)` from `len > avail`
  (request.rs:1141), and `parse_frame_header` reads two varints.
- Such a call's excess is `top_up`'s `append` (request.rs:1734-1735). Its realloc moves the buffered partial frame:
  65,537 bytes requested for `d = 1` at byte 32,768 of a 50,399-byte frame, 28 reallocs over the frame.

The spec's D3 takes that up.
