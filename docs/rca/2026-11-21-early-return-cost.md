# A costed loop's early return dropped part of its iteration's charge (C15, phase 9b3)

Status: fixed in 9b3 Task 9 fix round 1 for `deliver`, and in 9b3 Task 12 at every costed loop of crates/h3/src (the
sites below). The class for code written later is the scaffold's: carryover `rca-early-return-cost` (owner sc), closed
structurally by h3's move onto the linear Budget (carryover `sc-h3-budget`).

- **Defect**: `h3::conn::deliver` (crates/h3/src/conn.rs) charges each event of its loop at the loop's end. It used a
  literal lump, `work + 6`, for the pop, the output push and the event's move.
  - An event the connection answers itself (a CONNECT, or a non-http scheme) leaves the loop through an early
    `return (true, ..)` before that line, and that return built its own charge.
  - 9b3 Task 7 charged the return as `work + 32 + frees(..)`, where the `32` was a placeholder for `answer`.
  - Task 9 replaced the placeholder with the bound costs of `is_http_scheme` and `answer` (`cs + ca`), and the frees.
    In doing so it dropped what the placeholder had silently covered:
    1. the free of the reversed buffer `rv`, found by the Task 9 self-check and fixed in 7af3915;
    2. the pop of event k, which the Task 9 review found (I1).
  - Both units still verified: the return's bound has at least 20 units of margin.
- **Incidents**: the two misses above, at the same return, in one task. The Task 7 review's I1 was the same kind of
  gap on the same path (the frees of dropped events charged nowhere). 9b3 Task 12's sweep found more, all verifying
  under their bounds' margin:
  - an exit before the loop's end charge dropped the unit of the byte or compare that triggered it: `eq_bytes_w`,
    `field_name_ok_w`, `field_value_ok_w`, `parse_cl_w` (two exits), `eq_ci_x`, `no_at_x` (message.rs) and
    `parse_prefix_int_w` (qpack/int.rs, two exits);
  - an exit dropped the free of a list it owned: `decode_lines` and `decode_lines_bounded` (`out` and its lines'
    names and values, qpack/field_section.rs), `huffman_decode_w` (`out`, qpack/huffman.rs; its `None` after the loop
    too).
- **Escape**:
  - The ensures is an upper bound with margin. A charge left out of an expression under the bound verifies, so Verus
    cannot see it.
  - The structural rules (followed by hand in h3; `tools/cost_charge.py` covers quic and byteq only and is being retired, so
    no script rule was added for h3) check that every `while` names `work`, and that
    every callee's `Ghost` is bound. Neither looks at primitive operations on a path that leaves the loop early.
  - The loop's lump and the return's charge were written separately, so nothing tied them together.
- **Class**: C15 (algorithmic cost not in contracts), in its accounting form: a charge written per path drifts between
  a loop's end and its early exits.
- **Catch**:
  - Structural:
    - The per-iteration lump is one name, `c_step()`, used at the loop's end and at the early return.
    - The return's charge is one ghost value, `extra = c_step() + cs + ca + 1`, which is both returned and passed to
      `lemma_answered_cost`.
  - Proof obligation: `lemma_answered_cost` requires `c_step() + 1 <= extra`. An early return that drops the step or
    the free fails a precondition, whatever the margin.
  - For every costed loop of crates/h3/src (9b3 Task 12; `tools/cost_charge.py` is being retired, so no script rule
    was added):
    - The iteration's terms are charged where they are incurred, before any exit that follows: each callee's `Ghost`
      is added to `work` as it returns, and the iteration's own unit at the top of the body (or after the read it pays
      for). An exit then returns `work` itself, the same value the loop's end carries on. This shape alone is a
      convention: moving the unit back below the exit verifies (9b3 Task 12 review I2).
    - What the verifier checks: `frame::lemma_paid(w, t, ret)` requires `w + t <= ret`. At a unit-step loop's exit
      (message.rs `eq_bytes_w`, `field_name_ok_w`, `field_value_ok_w`, `pseudo_first_x`, `parse_cl_w`, `eq_ci_x`,
      `no_at_x`; int.rs `parse_prefix_int_w`) it is called with the units charged before this iteration (the exact
      invariant's `i + 1`, or `i`), `t = 1` and the `work` the exit returns, so an exit whose returned value lacks its
      iteration's unit fails a precondition. Every other costed loop snapshots `w_it = work` at the top of its body
      and calls `lemma_paid(w_it, t, work)` at each exit with `t` the iteration's charges up to that exit (its
      callees' costs and its step: `w + 1`, `1 + cp`, `cl`, `2 + cf`, `c1 + c2`, ...). At an exit that owes a term of its own (the free of what it drops:
      `c_pfree`, `c_hfree`, `lines_free(n)`), the returned value is one ghost `ret = work + t`, passed to
      `lemma_paid(work, t, ret)` (and in `parse_settings` to `lemma_pset_cost`) and returned as `Ghost(ret)`, so a
      `ret` that drops `t` fails a precondition whatever the margin. The first review found the earlier form
      (`lemma_exit_pays(t, extra)`, checking only `t <= t`) vacuous (I1).
  - The sites, each costed `while` with an early `return` (none uses `break`):

    | site | outcome |
    |---|---|
    | conn.rs `deliver` | the answered return: deliver's catch (Task 9); its two other returns follow `assert(false)` |
    | frame.rs `parse_settings` (2 exits) | each `parse_varint_w` cost charged as it returns; the free of `pairs` in `ret`, checked by `lemma_paid` and `lemma_pset_cost` |
    | message.rs `eq_bytes_w`, `field_name_ok_w`, `field_value_ok_w`, `eq_ci_x`, `no_at_x`, `parse_cl_w` (2) | undercharge fixed: the unit charged at the body's top; `lemma_paid(i + 1, 1, work)` at the exit |
    | message.rs `pseudo_first_x` | its exit wrote `work + 1` itself: the unit moved to the body's top; `lemma_paid` at the exit |
    | message.rs `syntax_ok_x`, `no_conn_x`, `cl_ok_x`, `validate_trailers` | already charged before the exit; no owned value dropped |
    | qpack/field_section.rs `decode_lines`, `decode_lines_bounded` | the line's cost charged as it returns; the free of `out` in `ret`, checked by `lemma_paid` |
    | qpack/huffman.rs `huffman_decode_w` (inner loop's exit) | the free of `out` in `ret`, checked by `lemma_paid` (also at the `None` after the loop) |
    | qpack/instructions.rs `process_encoder_stream` (4 exits), `process_decoder_stream` (3) | per-exit `+ 1` and `+ cp + 1` replaced by charges at the body's top and after the parse |
    | qpack/int.rs `parse_prefix_int_w` (3 exits) | undercharge fixed: byte i's unit charged after its read; `lemma_paid(i, 1, work)` at the two exits after the read |
    | request.rs `run` | already charged before its exits |
    | request.rs `RequestStream::on_data` | `w + 1` charged before the match; the exit adds only `emit_body`'s cost, the same call the loop's end makes |
    | uni.rs `control_frames` (3 exits), `UniStream::consume_control`, `UniStream::consume_qpack` | per-exit charges replaced by one charge before the branch |

    The loops with early exits and no ghost cost (conn.rs `fits_peer_x`, message.rs `check_response`, qpack
    static_table.rs `find_static` and `bytes_eq`) are on the send side, whose costs are carryover cat-C15-9b4's.
  - Residual: a new costed loop is not checked for this shape; deleting an exit's `lemma_paid` call together with its
    term still verifies; and an exit that returns `Ghost(work)` in place of `Ghost(ret)` still verifies, since the
    fns' cost ensures are upper bounds. These close when h3's costs move onto the linear Budget (carryover
    `sc-h3-budget`): every operation then consumes budget, so no path can skip a charge. quic, quictls and byteq were not swept for
    this class here (their costs are carryover cat-C15-semantic-cost's and the scaffold's FD-7).
- **Evidence**:
  - 9b3 Task 12's commit (the sites above); `scripts/quick.sh h3` and `scripts/rlimit-seeds.sh h3 5` pass on it.
  - Hand checks (9b3 Task 12 fix round 1, not mutant rows): `parse_settings`' first exit with `ret = work` (the free
    dropped) fails `quick.sh h3/frame` with "precondition not satisfied" at `lemma_paid`; `eq_bytes_w` with its unit
    moved back below the exit (b6b00ab's body) fails `quick.sh h3/message` the same way; `control_frames` with its
    `w + 1` moved to the loop's end fails `quick.sh h3/uni` at the `lemma_paid` of both exits it then skips; `parse_settings` returning
    `Ghost(work)` with `ret` left as is verifies (the residual above).
  - Mutants `9b3-T9-5` (`c_step()` removed from `extra`) and `9b3-T9-6` (the `+ 1` free removed) both fail `deliver`
    with "precondition not satisfied" at the `lemma_answered_cost` call. Applied by hand to 7af3915's `deliver` (this
    RCA, cd431a6), not registered (owner 2026-11-21).
  - Before the lower bound existed, `9b3-T9-5`'s mutation verified (`quick.sh h3/conn/deliver` ok). That is the escape,
    reproduced.
