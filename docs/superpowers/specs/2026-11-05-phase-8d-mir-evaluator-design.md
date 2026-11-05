# Phase 8d: an executable MIR semantics evaluator — design addendum

Addendum to `docs/superpowers/specs/2026-11-03-phase-8c-verified-front-end-design.md`. Its trust
table, §MIR semantics (decisions 1–8) and §8c result still apply. This file states only what 8d
adds or changes.

## The gap

`ctmir::sem` is the main residual trust of 8c. It is spec-only (`mir_run_fn`, with outcomes
`Done`/`Panic`/`Unsup`/`Fuel`), and nothing executes it.
- `ctmir::interp` is proved equal to core's `run_fn`.
- `theorem_sim` goes one way only: a MIR `Done` implies an equal core run.

So the selftest and the 31723 semconf vectors show only that `sem` never completes with a wrong
value on those inputs. They do not show that it completes at all.

Never-Stuck, meaning `sem` does not `Panic` or give `None` where Rust completes on rustc-typed
in-subset MIR, has no executable evidence. If `sem` wrongly panicked on a construct that every
crypto root uses, every `root .. ok` line would be vacuous while every gate stayed green. This is
final review I1, and 8c Task 6's C1 was a bug of exactly that kind, found only by audit.

## Goal

1. An exec MIR evaluator in `ctmir`, proved against `mir_run` and `mir_entry` under the crate's
   `cpol(pol)`.
2. The evaluator runs, in `scripts/ct-check.sh`, on:
   - every vector of `selftest.txt` (crypto and the parser crates);
   - every vector of semconf.
3. Each vector must give `Done` with native's value where native completes, and `Panic` where
   native panics.
4. Every crypto `root .. ok` root and every parser `bounded` root has at least one vector that
   reaches `Done`.
5. TRUSTED.md's never-Stuck statement then narrows to "on inputs not exercised". §8c's Goal 4 is
   met for the exercised inputs.

Non-goals:
- Proving never-Stuck. That is type soundness of `sem` on rustc-typed MIR, and it stays open.
- Building event traces.
- `decode_crate` functionality.
- quic CT roots.
- The fixtures' and the negative control's `ok`/`bounded` lines. They are fixtures of the
  checker, not shipped code, and are not covered by item 4.

## Decision 1: an evaluator, not a backward simulation

The alternative was a backward simulation: `lowers`, `wt_args` and a core `Some` together imply
a MIR `Done`.

**As stated, it is false.** Core is total where MIR is partial:
- `/` and `%` by 0 give 0 in core (`ctcore/src/sem.rs:93-94`), but `rv_bin`'s `bin_ok` makes them
  `None` in `sem`;
- an out-of-bounds `Index` reads `Unit` in core and is `None` in `sem` (`proj_step`);
- core reads a non-`Int` operand as 0 (`interp.rs`'s `local_int` mirrors this), where `sem` panics
  on a value of the wrong shape.

A true version needs two more premises:
- rustc's guard `Assert`s dominate every partial operation;
- values keep their types along the run.

That is never-Stuck itself. 8c Task 6 tried to build that typing invariant and gave it up: its
`run_tf` was over-strong, and `cv` could not be a function. The ledger ruling of 2026-11-03
replaced it with representation alignment.

**The evaluator is a per-function mirror of `sem`.** It has the same shape as `ctmir::interp`
mirroring `ctcore::sem`. It needs no typing invariant and no new proof idea, and it costs about
what `interp` did. It also tests `sem` against native directly, not through the translator.

**Ruling.** Build the evaluator. A backward simulation, or a proof of never-Stuck, stays the
follow-up. The evaluator's runs are then its regression check.

Cost if wrong: the evidence covers finite inputs only. That is what Goal 4 asked for.

## Decision 2: the evaluator's contract

```
pub enum Ev { Done(CFrame, u64), Panic, Fuel, GaveUp }
ev_ok(o: Out, r: Ev) :=
    Done(f, n) ==> o matches Out::Done(g, _, s) && fv(f) == g && n == s
    Panic      ==> o is Panic
    Fuel       ==> o is Fuel
    GaveUp     ==> true
mir_eval(m, tabs, pol, i, args, slots, fuel) -> (r: Ev)
    requires tabs_ok(m, tabs), in_subset(m, cpol(pol), i)
    ensures  ev_ok(mir_run(m, cpol(pol), i, mir_entry(m, i, cvs(args), cvs(slots)), fuel), r)
```

- **Equal on every outcome it reports, not total.** `GaveUp` makes no claim. It is used for:
  - a step count or a count that passes `u64`;
  - an allocation past a cap;
  - an arm a mirror leaves out, such as `CheckedBinaryOp` and the `*Unchecked` binops, which the
    translator never lowers (preflight C4).

  Exact equality everywhere would need exact versions of `look.rs`'s one-way predicates
  (`x_ty_free`, `x_zst_dest`, `x_sig_ok`) and of every `Unsup` arm, and the gate would gain
  nothing. The gate fails on any `GaveUp`, so `GaveUp` can only cost a false alarm, never a false
  pass. Internal mirrors return `Result<T, Halt>`, where `Halt` is `Panic` (the spec gives `None`)
  or `GaveUp` (no claim).
- **No events.** This is `interp`'s precedent. A 1.5e8-step trace does not fit in memory, and no
  gate reads it: CT is already a theorem. `Done` claims the frame and the steps.
- **Only lowered fns.** `in_subset` comes from `lower`'s `Ok` through
  `theorem_lowers_in_subset(.., 0)`. Its witness sets `(s, rs)` are passed as ghost arguments.
  - Every block the run enters is in `rs(j)`, so it is `block_ok` without an exec check.
  - Every body callee is in `s`.
  - So the evaluator never re-checks `block_ok`, and never meets `Unsup`.
- **Fuel is mirrored exactly**: 1 per block entered, 1 per body call (glue included), 0 per leaf.

## Decision 3: fuel monotonicity stays a follow-up

The evaluator mirrors fuel exactly, so it needs no monotonicity lemma. The lemma pays off only if
`ct_mir` is restated over two fuels. That would change `report_sound`, the trusted statement,
and is a different claim from never-Stuck.

Ruling: not in 8d. The follow-up list keeps `lemma_mir_run_fuel_mono`, with `ct_mir` over two
fuels. Cost if wrong: TRUSTED keeps "at a common fuel" one phase longer.

## Decision 4: the selftest runs MIR, and a `pass` line is a claim

- **`check_vector` runs the evaluator, not core.** By `theorem_sim`, a MIR `Done` already
  implies the core run with the same frame and steps. The core run therefore adds no evidence, and
  it costs about half the selftest time.
  - `ctmir::interp` (`interp.rs`) is deleted, together with the core-program cases of
    `tests/interp.rs`.
  - `interp_val.rs` and `interp_arith.rs` stay; the evaluator uses them.
  - The vector grammar and the argument shaping (`entry_args`, `entry_slots`, `shape_ok`,
    `widths_ok`) stay. They are read from the lowered root's core body, whose parameter types are
    `lowers_ty` images of the MIR ones.
- **The vectors themselves.**
  - A completing vector passes only on `Done` with the wanted return value and `mut:` pointees.
  - A `=> panic` vector passes only on `Panic`. `Fuel` and `GaveUp` no longer count; before, core
    `None` included fuel.
  - The arguments must also pass `x_wt_args`, which implies `wt_args`. That puts the run inside
    the theorems' domain. At a `&mut` parameter the argument is `Mut(Slot(j))`, not the raw
    pointee: `wt_rec` accepts only a `Mut` there, and `entry_local` reads the slot.
- **`line_ok` gains `pass_ok`.** Formats stay byte-identical: `pass <path> steps=<n>` and
  `pass <path> panic`. `pass_ok` reads:

  ```
  exists path, i, args, slots, n:
      root_of(m, path, i) && wt_args(m, i, args, slots) &&
      let o = mir_run(m, cpol(pol), i, mir_entry(m, i, args, slots), FUEL);
      (l == clean("pass " + path + " steps=" + digits(n)) + "\n" && o matches Out::Done(_, _, k) && k == n)
   || (l == clean("pass " + path + " panic") + "\n" && o is Panic)
  ```

  (`clean` and `digits` are `text.rs`'s. A dedicated `pass_line` writer emits these lines; `info`'s
  `no_claim` excludes the `pass ` prefix, and the root and bounded writers refute it; preflight C3.) So the report says what the
  gate reads. The match with native's value stays in
  `check_vector`'s ensures (`passes`/`panics`), next to the vector it is about.
- A `pass .. panic` line is not never-Stuck evidence: `Out::Panic` also covers a stuck state
  (sem.rs:1163-1166, :1225). Only `steps=` lines are (preflight C6).

## Decision 5: performance

The `sem` lookups are first-match linear `find`s. crypto's dump has 558 `tys`, 183 `insts` and
168 `calls`, and `rv_bin` resolves two operand types on every binop. A literal mirror would be
hundreds of times slower than `interp`.

Spike, on main 0b0061c's crypto dump with `interp`:
- the 22 crypto vectors take 21.5 s (`p256_ecdsa_sign` 1.5e8 core steps);
- an RSA-2048 `rsa_pss_sign_inner` vector takes 12.8 s, at 3.78e8 steps.

Rulings:
- **Index tables.** For each table, a `Vec<Option<usize>>` from id to its first row, proved equal
  to `find` (`tabs_ok`), is built once per pipeline call. Ids are not dense in row order but are
  below a few thousand. An id past 2^24 makes `tabs` give `None`, and the selftest then fails
  closed.
- The step loop's lookups go through the tables, and so do `ul_val`'s, since every body call
  enters through `mir_entry`. `mir_entry`'s mirror takes its arguments by value, so no call
  deep-clones them (preflight M1).
- **Acceptance.** The crypto selftest, including the RSA vector, runs under its own 150 s `front`
  bound in ct-check, so the bound is enforced, not just measured (preflight M1). Otherwise:
  1. add a per-type `ul_val` table, or one entry template per instance. Memoizing `const_val` is
     unlikely to pay: crypto's largest in-body constant is 32 bytes (preflight M1);
  2. failing that, give the RSA vector its own `front` run with its own bound.

  Never shrink the inputs.

## Decision 6: coverage

Goal 4 needs a completing vector for every covered root. Today these have none:
- `crypto::rsa::rsa_pss_sign_inner`;
- 13 of the 19 bounded parser roots: `wire::varint::{exec_min_len, parse_varint}`,
  `h3::frame::parse_frame_header`, `h3::qpack::huffman::{feed_bit, lookup}`, and
  `quic::frame::{stream_data_at, parse_reset_stream, parse_two_varints, parse_crypto, parse_stream, parse_one_varint, parse_close, parse_frame_type}`.

How the values are sourced:
- **RSA.** The value comes from a native run. `crates/crypto/tests/rsa_pss.rs`'s
  `pss_rfc9500_2048` asserts that its signature equals the vector's value. That is a test-only
  edit; `crates/crypto/src` is not touched.
- **The parser fns.** Most are private. Their values are derived, as the existing
  `quic::frame::vint_at`/`bytes_at` lines are, from a public test whose run passes through that
  input, and each line names that test.
- **quic.** quic's tests are only read, because Phase 4c owns `crates/quic`.

ct-check gains a coverage gate: each crypto `root P ok` path, and each parser `bounded P` path,
needs at least one `pass P steps=` line. A root whose only vectors are panic vectors fails the
gate.

## Decision 7: a disagreement is a semantics finding

When the evaluator gives `Panic` or a wrong value where native completes, that is a finding about
`sem`, not a test to adjust.
- The task stops and reports.
- The ruling is one of two:
  - the vector is wrong (re-derive it natively);
  - `sem` is wrong. Then the `sem.rs` edit is minimal, pinned by a `sem_sanity` fact that fails
    without it, audited clean-room, and followed by a forced re-verify of all of `ctmir`, because
    `theorem_sim` and `lowers` read `sem`.
- The clean-room audit is a separate seat. It reads `sem.rs`, `sem_sanity.rs`, the case's dumped
  MIR and MiniRust, and does not read `lower*`, `sim*`, `eval*` or the case's motivation.

`GaveUp` is the evaluator's incompleteness: fix the evaluator.

## What changes in TRUSTED.md

- **Row 45** (preflight C5): the vectors run `ctmir::sem` itself, through `ctmir::eval`. A
  `pass` line is a proved claim (`pass_ok`): the root's MIR run on well-typed arguments reaches
  `Done` in the printed steps, or `Panic`. The match with the vector's values is in
  `check_vector`'s ensures.
  - Both sentences that call `pass` lines informational go.
  - `pass_ok` joins the row's statements, and `vectors.rs` (for `FUEL`) its file column.
  - The awk-prefix sentence adds `pass `.
- **Row 48** (preflight C6): never-Stuck is no longer "no executable evidence". In three parts:
  - **proved**: every crypto `ok` root and every parser `bounded` root reaches `Done` under
    `mir_run` on at least one `wt_args` input (`pass_ok` on a `steps=` line);
  - **verified, outside `report_sound`**: the values equal the vector's;
  - **trusted**: that the vector's values are native's.

  Only `steps=` lines are never-Stuck evidence. `pass .. panic` lines are not, since
  `Out::Panic` includes stuck states. Never-Stuck stays trusted for inputs not exercised, and for
  the fixtures and the negative control.
- **§8c result**: Goal 4 is met for the exercised inputs, with a pointer to this file's "8d
  result" section.

## 8d result

- **Verified**: 1273 verified, 0 errors (forced `ctmir` re-run at `--rlimit 4`); verify.sh ends with its
  usual line (`cost 19/36`, `escapes accounted (0)`, `binary ok (49 fns)`). `sem.rs` is unchanged.
- **Vectors**: the crypto selftest has 23 (new: `rsa_pss_sign_inner`, 378 million MIR steps, from the
  RFC 9500 2048-bit key; the signature equals the spike's `8febad92..`), the parser selftest 28 (new: 13,
  one per bounded root that had none), semconf 31723. Every one runs `ctmir::sem` through `ctmir::eval`
  and passes; none gave an unwanted outcome (217 semconf `=> panic` vectors gave `Panic`; no `Fuel` or `GaveUp`).
- **Coverage gate**: `ct-check: done roots 11/11, bounded 19/19`. Removing the RSA vector from
  `selftest.txt` fails the run on that root; so do deleting a parser root's `pass` lines, turning them
  into `pass .. panic`, and a pass path with a space (evidence: `vt-8d-evidence/t4/demo`).
- **Timings**: crypto selftest 74 s under its 150 s bound; `eval_probe` (sha256 and p256_public_key step
  counts equal the deleted core interpreter's) 16 s, now run by ct-check; ct-check 1 min 44 s, verify.sh
  2 min 51 s with ctmir re-verified.
- **Findings**: none; no vector disagreed with the evaluator. Two parser vectors (`feed_bit`, `lookup`)
  are hand-traced from the decode loop over the named test's input, since no public test shows the
  intermediate state.
- **Left trusted**: never-Stuck for inputs no vector exercises (TRUSTED row 48); fuel monotonicity.
