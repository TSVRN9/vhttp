# The cookie merge: a quadratic copy in the call that completes a request's HEADERS frame (C15, phase 9b3)

Status: written with the 9b3 spec (`docs/superpowers/specs/2026-11-14-phase-9b3-h3-input-costs-design.md`, D5, D13),
before the fix. 9b3 Task 1 commits the failing test below. 9b3's last task completes Catch and Evidence with the fix
commit, the gate demos and the mutant ids. Line numbers are at e8d97e5 (phase-9b2's tip; h3 is unchanged from main
a293f81).

- **Defect**: `build_headers` (crates/h3/src/message.rs:1374-1436) builds `Request.headers` for every request HEADERS
  frame. `validate_request` calls it at :1493, and `headers_frame` (request.rs:839) calls `validate_request`. It merges
  cookie lines as RFC 9114 §4.2.1 requires. For each cookie line after the first it does five things:
  1. `find_first(out, "cookie")` (:1396) scans `out` from the start.
  2. `slice_to_vec(&out[k].value)` (:1399) copies the whole accumulated value into an exact-capacity `Vec`.
  3. `extend_from_slice("; ")` (:1401) outgrows that capacity, so a `realloc` can move the whole value again.
  4. `extend_from_slice(&f.value)` (:1402) appends the line's value, and `slice_to_vec` of the name (:1403) copies 6 bytes.
  5. `out.set(k, ..)` (:1418) frees the previous value.

  After k extra lines the value holds `L_k = v + k·(v + 2)` bytes, for lines of `v` bytes each. With every realloc
  moving, line k copies `2·L_{k-1} + v + 8` bytes, so n lines copy about `n²·(v + 2)` bytes. The rescans add `n²/2`
  name comparisons of 6 bytes.

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
     cookie, O(n^2) in field count; fields are capped by MAX_FIELD_SECTION_SIZE (2048 lines at most)". That covers the
     rescans (6-byte name comparisons) but not the value copies, which are larger by a factor of `v + 2` and about
     150x larger at the worst case measured below. So its "2048 lines" read as harmless. No `ponytail:` or `shortcut:`
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
- **Catch** (proposed in the 9b3 spec; filled in by 9b3's last task):
  1. A proof (README order 1). `build_headers` merges in two passes into an exact `CapVec` (spec D5). It returns a
     `Ghost<nat>`, with ensures `work ≤ c·(decoded size + n + 1)`. This work is part of D9's proved completed-frame
     term, so every call that completes a HEADERS frame has a proved bound linear in the frame.
  2. A gate (order 3) for sub-class (a): the cost-charge gate's extension in spec D13.
     - It gates per fn, so the input-path fns of message.rs, request.rs, uni.rs, frame.rs, field_section.rs,
       huffman.rs and conn.rs are covered without the response-side fns at the rlimit ceilings.
     - Inside gated fns it refuses byte copies outside byteq's cost fns (`slice_to_vec`, `extend_from_slice`,
       `append`, `split_off`, `to_vec`, `clone`), so a copy is charged or it fails.
     - A gated fn that calls a looping or recursive fn which returns no `Ghost<nat>` fails unless that callee is
       listed in `tools/cost-uncharged.txt` with an owner phase and an open carryover id.
     - Demos in `scripts/gate-demos.sh`: each rule fails on the original `build_headers` (its `slice_to_vec` and
       `extend_from_slice` on the accumulated value, and its `find_first` loop with no charge).
  3. A mutant (order 1) that reintroduces the per-line copy of the accumulated value with its charge must fail the
     cost ensures (a Verus error, registered in `tools/mutants.tsv`).
  4. A test (order 4; it pins the allocator behaviour the proof's cost model assumes and does not replace the
     proof): `cookie_lines_linear` in a new `crates/h3/tests/input_cost.rs` (its own `#[global_allocator]`). It feeds
     the v = 34 pattern at n, 2n and 4n (n = 226), plus the same frames fed one byte per call. It checks:
     - requested bytes at most 3x per doubling;
     - no `realloc` in the completing call;
     - the completing call's requested bytes at most `A·frame + B`.

     It fails today: 2.78 MB, 11.1 MB and 44.5 MB requested.
  5. Sub-class (b), comments (order 3): `scripts/carryovers.sh` (or a new gate it calls) fails on any `ponytail:` or
     `shortcut:` comment under `crates/*/src` whose text states a cost (`O(`, `quadratic`, `rescan`, `linear scan`,
     `linear lookup`, `copies`, `amortized`) unless it names a carryover id that `docs/carryovers.tsv` holds open. A
     closed id fails, so the comment goes when its row closes. Demo: a cost comment with its id removed.
- **Evidence** (to complete): the measurement below; Task 1's failing test; the gate demos and the mutant at 9b3's
  last task.

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
- **0.80 ms**, against 0.27 MB requested and 0.12 ms for the same frame with non-cookie lines;
- 1,363 requested bytes per frame byte, where 9b2's per-call test budget (`8·d + 4096`) allows 265,416 for this `d`.

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
