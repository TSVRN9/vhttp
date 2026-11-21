# A costed loop's early return dropped part of its iteration's charge (C15, phase 9b3)

Status: fixed in 9b3 Task 9 fix round 1 for `deliver`. The gate rule for every costed loop is Task 12's (carryover
`rca-early-return-cost`).

- **Defect**: `h3::conn::deliver` (crates/h3/src/conn.rs) charges each event of its loop at the loop's end. It used a
  literal lump, `work + 6`, for the pop, the output push and the event's move.
  - An event the connection answers itself (a CONNECT, or a non-http scheme) leaves the loop through an early
    `return (true, ..)` before that line, and that return built its own charge.
  - 9b3 Task 7 charged the return as `work + 32 + frees(..)`, where the `32` was a placeholder for `answer`.
  - Task 9 replaced the placeholder with the bound costs of `is_http_scheme` and `answer` (`cs + ca`), and the frees.
    In doing so it dropped what the placeholder had silently covered:
    1. the free of the reversed buffer `rv`, found by the Task 9 self-check and fixed in e87e29b;
    2. the pop of event k, which the Task 9 review found (I1).
  - Both units still verified: the return's bound has at least 20 units of margin.
- **Incidents**: the two misses above, at the same return, in one task. The Task 7 review's I1 was the same kind of
  gap on the same path (the frees of dropped events charged nowhere).
- **Escape**:
  - The ensures is an upper bound with margin. A charge left out of an expression under the bound verifies, so Verus
    cannot see it.
  - The structural rules (until Task 12's gate, followed by hand) check that every `while` names `work`, and that
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
  - For the class in every costed loop: a Task 12 rule in `tools/cost_charge.py`. A `return` inside a costed `while`
    must add the loop body's per-iteration term, and that term must be a named `c_*` spec fn (carryover
    `rca-early-return-cost`).
- **Evidence**:
  - Mutants `9b3-T9-5` (`c_step()` removed from `extra`) and `9b3-T9-6` (the `+ 1` free removed) both fail `deliver`
    with "precondition not satisfied" at the `lemma_answered_cost` call. The patches and logs are in the 9b3 workspace
    under mutants/.
  - Before the lower bound existed, `9b3-T9-5`'s mutation verified (`quick.sh h3/conn/deliver` ok). That is the escape,
    reproduced.
