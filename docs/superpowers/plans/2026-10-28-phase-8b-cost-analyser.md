# Phase 8b: Verified step-bound analyser for attacker-reachable parsers (attempt) — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** For each target parser function, either prove `steps <= eval(b, inputs)` for a polynomial `b` in its input lengths, or report `None` with a reason.
- **The deliverable is the coverage number**: bounded targets out of all targets. It is reported against three predictions:
  - the spec's original pre-registration, 27 of 38;
  - the same after the preflight's I3 ruling (two QuicVarInt rows are not cost roots), 25 of 36;
  - the final re-baseline X′ of 36, which Task 2 records in the spec before Tasks 3+ start, so it stays pre-registered relative to the proofs. Task 1b's 23/36 is its upper bound.
- A step bound is **not** wall-clock time and **not** memory (spec §Cost analyser).

**Spec:** `docs/superpowers/specs/2026-10-28-phase-8-verified-ct-cost-design.md`, §Cost analyser and D8/D9, as amended by the preflight rulings. 8a's plan, `docs/superpowers/plans/2026-10-28-phase-8a-ct-checker.md`, fixed the shared interfaces this plan consumes:
- `ctcore::syntax::*`;
- `sem.rs`'s `run_fn`/`run_from`/`exec_stmts`/`exec_intr`/`call_enter`/`call_leave`/`init_entry`/`len_ok`/`uval`, with steps in `Res`;
- `ct.rs`'s `wf`, `ok_prog`, `plc` and `no_mut`, `ct_lemmas.rs`'s `lemma_plc_*`, `check_program`, `check::check_wf` and `infer::callee_order`;
- the driver's `translate_closure()` and its manifest (preflight). `translate_closure` is label-free; 8a's check mode applies the root-label rule separately.

**Branch:** `phase-8b`, cut from `main` at 6641fa2 (8a merged). The escape count stays at main's value, **1**.

**Architecture.** All new code is additive. **No 8a file changes**, except:
- `crates/ctcore/src/lib.rs`: new `mod` lines, explicit re-exports and `analyze`;
- `tools/ct-driver/src/main.rs`: the `cost` mode (Task 6), and `-Zalways-encode-mir` for `translate-crate` crates (Task 1b);
- `tools/ct-driver/src/manifest.rs`: the `cost-root` kind (Task 6; 8a's loader rejects unknown kinds);
- `tools/ct-driver/src/translate.rs`: Task 1b's coverage mappings only;
- `tools/ct-driver/src/interp.rs`: tuple, bool and enum-variant values in the selftest vector grammar (Task 1b; not in the TCB);
- `tools/ct-driver/manifest.txt` and `selftest.txt`: Task 1b's `intr`/`translate-crate` lines and parser vectors;
- `tools/ct-fixtures/{src/lib.rs, manifest.txt, expected.txt}`: Task 1b's coverage fixtures (appended) and Task 6's cost fixtures;
- `scripts/ct-check.sh` (preflight).

The 8b modules:
- `crates/ctcore/src/cost.rs` holds the trusted cost spec:
  - atoms, polynomials, facts and certificates;
  - `cert_sem_ok`/`cert_for`;
  - `theorem_cost`.
- `crates/ctcore/src/cost_sym.rs` holds the abstract block effect, as spec plus lemmas.
- `crates/ctcore/src/cost_check.rs` holds the verified validator, `check_cert(..) ==> cert_for(..)`.
- `crates/ctcore/src/loops.rs` holds the untrusted inference: dominators, natural loops, counted loops and potentials. Its only route to a `Some` is through `check_cert`, which `analyze` (in `lib.rs`) applies.

**Tech Stack:** as 8a. No new dependencies.

## Global Constraints (copy verbatim into every task brief)

*8a's Global Constraints, repeated verbatim with the 8b deltas marked **[8b]**:*

- **Escapes.**
  - `crates/ctcore` adds **zero** escapes, and the `verify.sh` count stays at main's value **[8b: 1, from main's verify.sh line `escapes accounted (1)`; write it in every report]**.
  - The gate greps every `*.rs` under `crates/`, code *and* comments, for `assume(`, `admit(`, `external_body`, `assume_specification`, `verifier::external`/`verifier(external` and the bare word `axiom`.
  - Never write those strings in `crates/` (write "premise", "hypothesis").
  - Never name a lemma `*assume*` or `*axiom*`.
- **No new dependencies.** `ctcore` depends on vstd only. `ct-driver` depends on the `rustc_*` crates and `ctcore`. Text formats are parsed by hand.
- **Toolchain.**
  - The pinned 1.98.1 from `rust-toolchain.toml`.
  - `export PATH=$HOME/.local/opt/verus/0.2026.10.04.426d8b0/verus-x86-linux:$PATH`.
  - `RUSTC_BOOTSTRAP=1` only inside `scripts/ct-check.sh`. **[8b] Exemption:** scratch census, dry-run and MIR-dump runs under the scratchpad (Task 1, Task 1b Step 6, Task 2 Step 4, the Task 7 Step 0 rerun) may set it by hand. So may the driver builds for them, which also need `RUSTFLAGS="-L $(rustc --print sysroot)/lib"`. Nothing they produce is committed except as recorded text.
- **Verus usage.**
  - `cd crates/ctcore && cargo verus verify -- --rlimit 4`, narrowing with `--verify-only-module`/`--verify-function`.
  - **On a fresh target dir, first run without `--rlimit`** (vstd fails at 4).
  - Edit, don't `touch`, to force re-verification.
  - No `#[verifier::rlimit(..)]` and no `by (compute*)` in ctcore. `spinoff_prover` is allowed and reported.
- **Known Verus gotchas.**
  - let-else crashes this build: use `if let`/`match`.
  - `#[verifier::loop_isolation(false)]` on exec fns whose loops need facts from an enclosing match.
  - Early `return false` needs witness asserts.
  - Nested-index quantifiers need a named trigger predicate.
  - Recursion under `forall` over `Seq<Val>` works.
- **Proof patterns.**
  - One lemma per construct plus a dispatcher (`decreases fuel, 1nat` / `0nat`).
  - Opaque `binop`/`unop`/`cast`.
  - Trace algebra in helpers.
  - **[8b]** Polynomial facts in small standalone lemmas (`lemma_mono_*`, `lemma_poly_*`). `by (nonlinear_arith)` only with at most one product per side.
- **Trusted-spec freeze.**
  - **[8b]** 8a's `syntax.rs`, `sem.rs`, `ct.rs`, `ct_lemmas.rs`, `ni.rs`, `check.rs`, `infer.rs` and `sem_sanity.rs` are frozen for the whole phase. `git diff main -- <those files>` must be empty in every commit.
  - **[8b]** `tools/ct-driver/src/translate.rs` and `interp.rs` change only in Task 1b. From Task 1b on, crypto's ct-check output is byte-identical to main's in every task: `report-crypto.txt`, `selftest-crypto.txt` and the negative run's `report-crypto.txt`, and the lines `crypto ok (84 fns, 10 roots, 10 declassify)`, `selftest 15/15` and `negative control rejected`.
  - From the end of Task 2, `cost.rs`'s spec fns and the `theorem_cost` statement are frozen too.
  - A change to either needs a `SPEC-CHANGE:` paragraph and a controller ruling.
  - **A target that needs a new intrinsic or a semantics change is a `None` (`Unresolved`), never a reason to edit 8a's semantics.**
- **The four checks, every task:**
  1. ctcore verifies at `--rlimit 4`: `0 errors`.
  2. `cargo build && cargo test && cargo build --release`: 0 warnings.
  3. `scripts/verify.sh` prints its success line with main's escape count (**[8b]** from Task 7, with `cost X/Y`).
  4. `scripts/ct-check.sh` exits 0 with the summary the task names.
- **Evidence run.** `CARGO_TARGET_DIR` and `CT_TARGET_DIR` under `<scratch>/` (`vt-8b-tN`, `ct-8b-tN`), absolute. `rm -rf` both after. `<scratch>` is `/home/tavern/Projects/rust/web-server/.worktrees` (git-excluded), and "the scratchpad" in this plan means the same directory.
- **Proof-time budget.** Report the five slowest functions. No function may exceed 10 s. ctcore's total must stay under 90 s **[8b: was 60 s; Task 1 records the baseline]**.
- **Mutations** fail on a named postcondition or expected line, never on rlimit. Revert immediately.
- **Never weaken a test**, and never flip an expected verdict to pass a run. A bounded target turning `None` is a regression; stop and report it. **[8b]** `tools/ct-fixtures/expected.txt`'s 44 lines are append-only.
- **[8b] The inference is untrusted.**
  - Give `loops.rs` no proof obligations beyond termination and memory safety.
  - Every `Some` an API returns must pass through `check_cert` on the final summary vector.
- **[8b] Degree ≤ 2.**
  - Monomials have at most 2 atoms, kept in canonical order (`atom_lt`).
  - Coefficient arithmetic is checked: an overflow means `None`.
  - Put a `ponytail:` comment on the degree cap: higher degree needs a multiset-product lemma.
- **No edits outside a task's Files list. Plan code is signatures only.**

## Review Focus

1. **The statement is the amended spec's.** `theorem_cost` matches the spec text as amended by the preflight rulings (I1, C2) and C1 option B: `ok_prog(p, ls)`, `entry_plc`, the `cert_for` premise, the `certs`/`sums` length premises, `vals_len_ok`, `poly_val`, the typed `Val(local, IntTy)` atom. `cert_for` requires entry facts to be empty, `sums[f]` to be `Some` and `poly_same(sums[f].unwrap(), pot[0])`. `cert_sem_ok` quantifies over **all** `ls` with `ok_prog`, **all** frames satisfying `plc`, the facts and `frame_len_ok`, and **all** callee outcomes within the summary (dst and `&mut` targets havocked).
2. **There is no unchecked route to `Some`.** `analyze`'s ensures comes from `check_cert` on the final vector. `loops.rs` output never reaches the report without it. A `bounded` line also needs the driver's `check_program` `Ok`, which supplies `ok_prog`.
3. **Honesty of the number.**
   - The coverage line equals `expected-cost.txt`.
   - The Task 7 report shows the result against 27/38, 25/36 and the final X′/36, which Task 2 committed before Tasks 3+.
   - Every divergence from the pre-registered table is explained.
   - Every `None` has a reason.
4. **Non-vacuity.**
   - Task 2's proof mutations fail.
   - Task 3's write-rule mutations fail.
   - Tampered certificates are rejected (Task 4).
   - Negative cost fixtures stay `None`.
   - A seeded unbounded loop in a real target is `None` (Task 7).
5. **Wording.** TRUSTED.md, the spec and the report say "steps", never "time"; and "not memory; Vec growth hidden".
6. **8a freeze held.** The `git diff` of 8a's frozen files, `sem_sanity.rs` included, is empty.
7. **Translator coverage (Task 1b) is CT-TCB surface.**
   - Each new mapping has a fixture or vector, a mutation that fails it, and a TRUSTED note.
   - Crypto's ct-check output is byte-identical.
   - The 44 existing fixture lines are unchanged.

---

### Task 1: Baseline, target census, dry run and pre-registration check (no commit)

**Files:** none in the repo. Scratch output goes under the scratchpad. The census, dry-run and MIR runs use the GC's `RUSTC_BOOTSTRAP` exemption (M6).

**Consumes:** merged 8a.

- [ ] **Step 1: 8a interfaces present, and baselines.**
  - `grep -n 'pub open spec fn \(run_fn\|run_from\|exec_stmts\|exec_intr\|call_enter\|call_leave\|init_entry\|len_ok\|wf\)(' crates/ctcore/src/*.rs` finds each exactly once. The `(` keeps `wf` from also matching `wf_body` (preflight).
  - `Res` is `Option<(Frame, Seq<Event>, nat)>`.
  - Record the escape count from `scripts/verify.sh` (expected 1).
  - **ctcore proof-time baseline** (M10): on a fresh target dir, run once without `--rlimit`, then `cargo verus verify -- --rlimit 4 --time-expanded`. Record the total and the five slowest functions. Task 8's `< 60 s` gate and the GC's 90 s budget compare against it.
  - **Crypto ct-check baseline:** run `scripts/ct-check.sh` on main. Keep `report-crypto.txt`, `selftest-crypto.txt` and the negative run's `report-crypto.txt` under the scratchpad (`ct-baseline/`). Task 1b's invariant compares against them.
- [ ] **Step 2: Census.**
  - Write a scratch manifest with `root` lines for the spec's target def paths, **36 of them** (I3): drop both `<QuicVarInt<_> as Parser>::parse` rows.
    - The impl is generic, so `pick_roots` can't take it as a root.
    - `QuicVarInt<true>` has no exec instance.
    - `<QuicVarInt<false>>::parse` is counted inside `wire::varint::parse_varint`'s closure.
  - Get exact paths by `grep`.
  - Add `translate-crate wire` (and `vest_lib` if the census shows trait plumbing through it).
  - Run the driver in `CT_MODE=census` over `wire`, `h3` and `quic` (`CT_CRATES=wire,h3,quic cargo build --release -p wire -p h3 -p quic`).
  - Record every reached callee with no 8a intrinsic mapping. Record the `body=` column for `wire::varint::parse_varint` in the h3 and quic builds (I4e: `body=no` means Task 1b needs (ii)).
  - **vest_lib bodies.** If the census needs vest_lib bodies, check their release MIR for `*WithOverflow` (it is there under the base profile's `overflow-checks = true`). Escalate for a ruling: a `[profile.release.package.vest_lib] overflow-checks = false` override plus a TRUSTED note, or accept the `None`s.
- [ ] **Step 3: Dry run (I4).**
  - Use `CT_MODE=check` with the Step 2 manifest (scratch `root` lines plus `translate-crate wire`) over `CT_CRATES=wire,h3,quic`. It needs no driver change.
  - `verdict()` runs `translate_closure` first. Then:
    - `reject <root> Unsupported|Unresolved ..` is a translation failure;
    - `reject <root> Root .. needs a ct:: attribute` is a clean translation.
  - Per target, record clean or failed. For a failure, record its first error, classified as I4 (a) `str`, (b) intrinsic element-type guard, (c) `copy_from_slice`, (d) Drop, (e) no MIR body, or **other**.
- [ ] **Step 4: Loop classification.**
  - Dump the MIR with `RUSTC_BOOTSTRAP=1 cargo rustc --release -p <crate> -- -Zinline-mir=no -Zunpretty=mir > <scratch>/<crate>.mir` (in a scratch target dir).
  - For each target, list its back edges and the guard/increment pattern.
  - Compare with the spec's table. Every row that changes gets a one-line reason.
- [ ] **Step 5: Report.** Include:
  - the final target list, Y = 36;
  - the original 27/38 and the I3 base 25/36;
  - the dry-run table by category;
  - the census's unmapped callees;
  - the loop classification.

  Translation failures in classes (a)–(e) are Task 1b's input, not a stop. List any failure classed **other** for the controller: it is outside Task 1b's scope.

---

### Task 1b: Translator coverage for the cost targets

**Files:**
- Modify:
  - `tools/ct-driver/src/translate.rs`: (i), (iii), (iv);
  - `tools/ct-driver/src/main.rs`: (ii);
  - `tools/ct-driver/src/manifest.rs`: only if (ii) needs it. None is expected, since `translate_crates` already exists;
  - `tools/ct-driver/src/interp.rs`: new values in `parse_vector`'s grammar. The interpreter is not in the TCB. Today it has no tuple, bool or non-`Option` enum form, which `settings_ok` (`-> bool`, `&Vec<(u64, u64)>`), `parse_prefix_int` (`-> PrefixInt`) and the `Option<(..)>` returns need. The new forms:
    - `(v,v,..)`, a tuple;
    - `true`/`false`, a `Bool` int;
    - `#k(v,..)`, variant k of an enum with those fields;
  - `tools/ct-driver/manifest.txt`: `translate-crate wire`, plus the census-derived `intr` lines the parser closures need, mapping only to 8a's existing intrinsics (e.g. `VecNew`, `VecIndex`, `SliceToVec`);
  - `tools/ct-driver/selftest.txt`: parser vectors;
  - `tools/ct-fixtures/src/lib.rs`, `tools/ct-fixtures/manifest.txt`, `tools/ct-fixtures/expected.txt`: new lines only;
  - `scripts/ct-check.sh`;
  - `TRUSTED.md`: the CT front-end row;
  - `docs/superpowers/specs/2026-10-28-phase-8-verified-ct-cost-design.md`: the re-baseline line in §Cost analyser only.

**Consumes:** the Task 1 dry-run table and census, and the Step 1 crypto baseline.

**Invariant:** crypto's ct-check output stays byte-identical (GC). `cmp` against Task 1's `ct-baseline/` files, and check that the three crypto summary lines are unchanged.

**Interfaces (produces)**, one per I4 ruling:
- **(i) `str` and `&'static str` become `Unit`.**
  - `Cx::ty`: `RigidTy::Str` gives `c::Ty::Unit`, and `Ref(_, str, Not)` gives `c::Ty::Unit`. `&mut str` stays Unsupported.
  - `Cx::constant`: an `Allocated` constant of type `&str` gives `Lit(ConstVal::Unit)`. Today it falls into `const_val` and errors.
  - Every read of a `str` stays rejected: `PtrMetadata` accepts slice refs only, and `str` methods have no `intr` line (Unresolved).
- **(ii) Encoded upstream MIR.**
  - `main.rs` pushes `-Zalways-encode-mir` with its other flags when the crate being compiled under the driver (in `CT_CRATES`) is named by a `translate-crate` line.
  - The gate is the `translate-crate` line, not cost mode. Cost mode doesn't exist until Task 6, and the Step 6 re-baseline runs in check mode. Crypto's manifest has no `translate-crate` line, so crypto's builds are unchanged.
  - It lands only if Task 1 recorded `body=no` for `wire::varint::parse_varint`. Otherwise only the `translate-crate wire` line lands, and (ii)'s flag is recorded as not needed.
  - The flag only changes which MIR is available, never what it is.
- **(iii) The intrinsic element-type guard, widened per intrinsic.** `sem.rs`'s `intr_eff` and `intr_cost` never inspect an element's type, so every Vec/slice intrinsic is element-type-generic there.
  - `Cx::intr_types` gains an element check, `elem_ok(k, E)`. It accepts `u8` for every Vec/slice row, as today. It also accepts exactly the (intrinsic, element) pairs the Task 1 dry run reports, never wider. Expected:
    - `(u64, u64)` for `VecLen`/`VecIndex`/`VecPush`/`VecNew`;
    - `h3::qpack::field_section::FieldLine` for `VecNew`/`VecPush`.
  - `VecPush`'s `x` must be `E`, and `VecIndex`'s dst must be `&E`.
  - `SliceToVec`, `VecExtendFromSlice` and `ArrayAsSlice` stay `u8`-only. Their per-element cost of 1 is honest only for a bitwise copy, not a deep `Clone`.
  - Fix the existing `ponytail:` comment to name the pair list.
- **(iv) Drop glue as a no-op.** `sem.rs` has no Drop construct: the translator lowers `Drop` to `Goto(target)`. So this needs no frozen-file change.
  - Admit a `Drop` whose type's glue frees a bounded number of `Vec<int>` buffers and runs no user code. Such a type is `Vec<int>`, `Option<T>`, a tuple, or a struct/enum whose fields are ints, `Unit`-mapped types, `Vec<int>`, or such types recursively, and with no `impl Drop` of its own. Examples: `Option<Vec<u8>>`, `FieldLine`.
  - `Vec<E>` for a non-int `E` stays Unsupported: its glue is O(len) work, which the step model would hide. Examples: `Vec<Vec<u8>>`, `Vec<FieldLine>`.
  - Step 1 confirms how rustc_public exposes an ADT's own `Drop` impl. If it exposes none, (iv) admits only `Vec<int>`, `Option` and tuples, and struct-of-Vec drops stay `None`. Record which.
- **(v) `copy_from_slice`: None.** It has no intrinsic in the closed set, and adding one is a SPEC-CHANGE to frozen `syntax.rs`/`sem.rs`. `parse_path` and everything that reaches it stay `None (Unresolved)`.

**Tests** (one fixture plus one selftest vector per new mapping):
- **Fixtures**, appended to `tools/ct-fixtures` as `root` lines and `expected.txt` lines in sorted position. The 44 existing lines stay unchanged:
  - `pos_str_unit` (i): `fn(x: u8) -> Option<&'static str>` returning `Some("e")` or `None`. Expected `ok`.
  - `neg_str_len` (i): `s.len()` on `s: &str`. Expected `reject .. Unresolved` (`core::str::<impl str>::len`, no `intr` line).
  - `pos_vec_elem_pair` (iii): `v.len()` and `v[i].0` on `&Vec<(u64, u64)>`, through the same keys as the h3 `intr` lines. Expected `ok`. The existing `neg_intr_type_args` (`Vec<u64>::push`) stays `Unsupported`, which is (iii)'s boundary.
  - `pos_drop_bounded` (iv): drops an `Option<Vec<u8>>` and a `struct TwoVecs { a: Vec<u8>, b: Vec<u8> }`. Expected `ok`. The existing `neg_drop_non_vec` (`Vec<Vec<u8>>`) stays `Unsupported`, which is (iv)'s boundary.
  - `neg_drop_user_impl` (iv): a struct with `impl Drop`. Expected `reject .. Unsupported`.
  - (ii) has no fixture: `ct-fixtures` is a single-crate workspace. Its check is the cross-crate vectors below.
  - New total: `ct-check: fixtures 49/49`.
- **Selftest vectors** in `tools/ct-driver/selftest.txt`. Each expected value is cited to an existing test in its crate, as 8a requires. One vector may serve two mappings if each mapping's mutation fails it.
  - `h3::frame::parse_exact_varint` covers (i) and (ii): it reaches `wire::varint::parse_varint` and its `PResult`/`&'static str` locals.
  - `quic::frame::vint_at` covers (ii).
  - `h3::frame::settings_ok` covers (iii) (a `[(..),(..)]` argument).
  - `h3::qpack::field_section::decode_string` (or `scan_string`, whichever the dry run shows dropping `Option<Vec<u8>>`) covers (iv).
  - For M12, also add `wire::varint::exec_len`, `h3::qpack::int::parse_prefix_int`, `h3::qpack::huffman::huffman_decode` and `quic::frame::bytes_at`. These cover the new `intr` lines and give every parser crate a vector.
- **`ct-check.sh`:**
  - `analyse()` takes a comma-separated crate list (the M14 part needed here). `CT_CRATES` is the list, `cargo clean -p` runs per crate, and it writes one report per crate.
  - It adds a selftest run over `wire,h3,quic` (own target dir `$CT_TARGET_DIR/parsers`).
  - Selftest counts are per crate prefix. The crypto line stays `ct-check: selftest 15/15`, and a new line prints `ct-check: selftest parsers K/K`, with K = 8.

- [ ] **Step 1:** Confirm the rustc_public API for (iv)'s user-`Drop` check, and record it. Implement (i)–(iv) as above. Gate (ii) on Task 1's `body=` record.
- [ ] **Step 2:** Add the three value forms to `interp.rs`, plus a unit test for each. Add the fixtures, the vectors, the manifest lines and the `ct-check.sh` changes.
- [ ] **Step 3: Invariant.** Run `scripts/ct-check.sh`, then `cmp` the three crypto files against `ct-baseline/`. Expected output:
  - `fixtures 49/49`;
  - `selftest 15/15`;
  - `selftest parsers 8/8`;
  - `crypto ok (84 fns, 10 roots, 10 declassify)`;
  - `negative control rejected`.
- [ ] **Step 4: Mutations**, one per new mapping, each failing a named expected line or vector. Revert each.
  - (i): remove the `Str` arm. `pos_str_unit` becomes `reject .. Unsupported` (diff), and the `parse_exact_varint` vector fails translation.
  - (ii) (if landed): drop the flag. The `parse_exact_varint` and `vint_at` vectors fail with `no MIR body`.
  - (iii): widen `elem_ok` to any int element, and `neg_intr_type_args` flips to `ok` (diff). Restore `u8`-only, and the `settings_ok` vector fails translation.
  - (iv): admit `Vec<E>` for any `E`, and `neg_drop_non_vec` flips to `ok` (diff). Skip the user-`Drop` check, and `neg_drop_user_impl` flips. Restore `Vec<int>`-only, and `pos_drop_bounded` flips and the (iv) vector fails.
- [ ] **Step 5: TRUSTED.md.** Add one sentence per mapping to the "CT front end" row:
  - (i): `str` is opaque `Unit`, and every read of it stays rejected;
  - (ii): `-Zalways-encode-mir` for `translate-crate` crates changes only which MIR is available;
  - (iii): the admitted (intrinsic, element) pairs, with the len-cost rows `u8`-only;
  - (iv): drop glue counts as one step. For the admitted types it frees a bounded number of buffers and runs no user code. Memory is not modelled.
  - (v): `copy_from_slice` is unmapped.
- [ ] **Step 6: Re-baseline before Task 2.**
  - Rerun Task 1's dry run with the 1b driver.
  - X′ = the targets the spec predicts `Some`, minus the two I3 rows, minus every target that still fails translation (parse_path included, by (v)). This is an upper bound: Task 2 Step 4 subtracts what Task 3's domain can't keep.
  - Append one dated line under the spec's pre-registered table, `Re-baseline (8b Task 1b, before Task 2): X′/36 predicted bounded`, with the targets that changed and why. **Never edit the table rows or the 27/38 line.**
  - **Stop rule:** stop for a ruling if more than 5 targets the spec predicts `Some` (excluding `parse_path`) still fail translation, or if any failure is outside I4's classes.
- [ ] **Step 7: Run the four checks and the evidence run.**
- [ ] **Step 8: Commit:** `feat(ct-driver): translator coverage for cost targets (str as Unit, encoded upstream MIR, per-intrinsic element types, bounded drop glue); re-baseline X'/36`

---

### Task 2: Cost spec and `theorem_cost` (semantic certificates)

**Files:**
- Create: `crates/ctcore/src/cost.rs`, `crates/ctcore/src/cost_sanity.rs` (counted-loop certificates and `theorem_cost` end to end, the phase's non-vacuity evidence; it stays green)
- Modify: `crates/ctcore/src/lib.rs` (`pub mod cost;`, `pub mod cost_sanity;`); the spec's §Cost analyser (§Bounds' `Len` and `nth` reads; the final X′ line and its correction, Step 4)

**Consumes:** `sem.rs` (`run_from`, `exec_stmts`, `exec_intr`, `call_enter`, `call_leave`, `init_entry`, `len_ok`, `uval`), `ct.rs` (`ok_prog`, `plc`, `no_mut`) and `ct_lemmas.rs` (`lemma_plc_stmt`, `lemma_plc_intr`, `lemma_plc_call_leave`, `lemma_call_enter_frames`, `lemma_agree_refl`, `lemma_entry_agree`, `lemma_shape_refl`).

**Interfaces (produces):**
- **Exec types**, used by the spec through `@`:
  - `pub enum Atom { Const(u64), Val(usize, IntTy), Len(usize), Gap(Box<Atom>, Box<Atom>) }`. `Val` is typed (C2): it reads the local at a width, as MIR's comparisons do;
  - `pub struct Mono { pub coef: u64, pub atoms: Vec<Atom> }` (≤ 2 atoms);
  - `pub struct Poly { pub monos: Vec<Mono> }`;
  - `pub enum Fact { Le(Atom, Atom), Lt(Atom, Atom) }`;
  - `pub struct BlockCert { pub facts: Vec<Fact>, pub pot: Poly }`;
  - `pub struct Cert { pub blocks: Vec<BlockCert> }`.
- **Spec values** (`pub open spec fn`):
  - `val_nat(ty: IntTy, v: Val) -> nat`: `Int(x)` gives `uval(ty, x)`; anything else gives 0 (C2);
  - `shr_len(v: Val) -> nat` (`decreases v`): the length of the `Arr` at the end of any number of `Shr`; 0 otherwise;
  - `len_nat(fr: Frame, v: Val) -> nat`: `shr_len(read_loc(fr, l))` for a `Mut(l)`, else `shr_len(v)`;
  - `gap(a: nat, b: nat) -> nat`: `if a >= b { a - b } else { 0 }`;
  - `atom_val(fr: Frame, a: Atom) -> nat` (`decreases a`). `Val(x, ty)` is `val_nat(ty, nth(fr.locals, x))`, `Len(x)` is `len_nat(fr, nth(fr.locals, x))`, and `Gap(a, b)` is `gap(atom_val(a), atom_val(b))`;
  - `mono_val(fr, m) -> nat`, `poly_val(fr: Frame, p: Poly) -> nat`;
  - `fact_holds(fr, f) -> bool`, `facts_hold(fr, fs: Seq<Fact>) -> bool`;
  - `frame_len_ok(fr: Frame) -> bool`: `len_ok` of every local and slot;
  - `vals_len_ok(vs: Seq<Val>) -> bool`: `forall|i| 0 <= i < vs.len() ==> len_ok(vs[i])` (I1);
  - `entry_plc(p: Program, f: nat, args: Seq<Val>, slots: Seq<Val>) -> bool`: `args.len() == nargs`, `slots.len() == nargs`, `no_mut(args[j])` for every `j` whose parameter local `1 + j` is not `Mut`-typed, and `no_mut(slots[j])` for every `j`. These are `args_agree`'s facts for one run.
- **Block and certificate conditions:**
  - `block_step_ok(p: Program, f: nat, b: nat, c: Cert, sums: Seq<Option<Poly>>, fr: Frame) -> bool`, per the spec §Cost analyser. Its parts:
    - `k = stmts.len()`, `fr1 = exec_stmts(..).0`;
    - `Goto`/`Switch` (taken target)/`Assert` (on success): the successor's facts hold at `fr1`, and `poly_val(fr, pot_b) >= k + 1 + poly_val(fr1, pot_succ)`;
    - `Return`: `>= k + 1`;
    - `Abort`: true;
    - `Call(Intr)`: on `Some((fr2, _, extra))`, the next block's facts at `fr2` and `>= k + 1 + extra + pot_next(fr2)`;
    - `Call(Fn(g))`: `sums[g] is Some`, and `forall|out: Frame, n: nat| frame_len_ok(out) && n <= poly_val(call_enter(..).0, sums[g].unwrap())` ⇒ next facts at `fr2 = call_leave(fr1, out, wb, dst).0` and `>= k + 1 + n + pot_next(fr2)`.
  - `cert_sem_ok(p, f, c, sums) -> bool`: `c.blocks@.len() == nblocks(f)`, and for all `ls`, b and fr, `ok_prog(p, ls) && plc(p, ls, f, fr) && facts_hold(fr, c.blocks@[b].facts@) && frame_len_ok(fr) ==> block_step_ok(p, f, b, c, sums, fr)`.
    - **`ls` is quantified, not fixed to all-public.** `check_program`'s `ensures` gives `ok_prog` for the labels it returns and says nothing about their values, and no cost proof reads a label. So `cert_for`, `check_cert` and `analyze` keep their signatures, and `theorem_cost` takes `ls` as a parameter.
    - `ok_prog` is in the hypothesis because 8a's single-frame lemmas (`lemma_eval_op_plc`, `lemma_place_plc`) need `ok_op`/`ok_place`.
    - `block_step_ok` takes no `ls`, and its `Call(Fn)` `out` quantifier stays without `plc`: Task 3's rule doesn't need it. `cost_from` gets the real `out`'s `plc` from `lemma_plc_reachable`.
  - `cert_for(p, f, c, sums) -> bool`: `cert_sem_ok` ∧ `c.blocks@[0].facts@.len() == 0` ∧ `sums[f] is Some` ∧ `poly_same(sums[f].unwrap(), c.blocks@[0].pot)`. `poly_same` compares coefficients and atom views: `Vec` has no extensional `==`, so no exec check can establish `sums[f] == Some(..)` (Task 4 SPEC-CHANGE).
- **Lemmas:**
  - `proof fn lemma_run_len_ok(p, f, b, fr, fuel)`: `frame_len_ok(fr)` and `run_from(..) is Some` imply `frame_len_ok(final)`.
  - `proof fn lemma_exec_stmts_len_ok(..)`, `proof fn lemma_intr_len_ok(..)`.
  - `proof fn lemma_init_entry_len_ok(p, f, args, slots)`: `vals_len_ok(args) && vals_len_ok(slots) ==> frame_len_ok(init_entry(p, f, args, slots))`.
  - `proof fn lemma_gap_dec(a: nat, x: nat)`: `x < a ==> gap(a, x) == gap(a, x + 1) + 1`. Tasks 3 and 4 consume it.
  - `proof fn lemma_shr_len_ok(v)`: `len_ok(v) ==> shr_len(v) <= USIZE_MAX`; `proof fn lemma_elems_le_len_nat(fr, v)`: `elems(fr, v).len() <= len_nat(fr, v)`. Task 3 consumes them.
  - `proof fn lemma_entry_plc(p, ls, f, args, slots)`: `f < p.fns@.len() && entry_plc(p, f, args, slots) ==> plc(p, ls, f, init_entry(p, f, args, slots))`, through `lemma_entry_agree(p, ls, f, args, args, slots, slots)` and `lemma_shape_refl`.
  - `proof fn lemma_plc_stmts(p, ls, f, ss, k, fr)`: folds `lemma_plc_stmt` over `exec_stmts`.
  - `lemma_plc_reachable`, the run-level composition, in `cost.rs`. Its other parts: `lemma_plc_intr`; the callee entry from `lemma_call_enter_frames` with `fr1 == fr2` and `lemma_agree_refl`; `lemma_plc_call_leave`.

    ```rust
    pub proof fn lemma_plc_reachable(p: Program, ls: Seq<FnLab>, f: nat, b: nat, fr: Frame, fuel: nat)
        requires ok_prog(p, ls), f < p.fns@.len(), plc(p, ls, f, fr), run_from(p, f, b, fr, fuel) is Some,
        ensures plc(p, ls, f, run_from(p, f, b, fr, fuel).unwrap().0),
        decreases fuel,
    ```
  - `proof fn cost_from(p, ls, certs, sums, f, b, fr, fuel)`, `decreases fuel`:
    - requires `ok_prog(p, ls)`, all-`cert_for` (as in the theorem), `sums[f] is Some`, `plc(p, ls, f, fr)`, `facts_hold(fr, certs[f].blocks@[b].facts@)`, `frame_len_ok(fr)` and `run_from(p, f, b, fr, fuel) is Some`;
    - ensures `steps <= poly_val(fr, certs[f].blocks@[b].pot)`.
- **The theorem**, the amended spec's statement (I1, C1 option B):

```rust
pub proof fn theorem_cost(p: Program, ls: Seq<FnLab>, certs: Seq<Cert>, sums: Seq<Option<Poly>>, f: nat,
                          args: Seq<Val>, slots: Seq<Val>, fuel: nat, b: Poly)
    requires
        ok_prog(p, ls), f < p.fns@.len(), certs.len() == p.fns@.len(), sums.len() == p.fns@.len(),
        sums[f as int] == Some(b),
        forall|g: int| 0 <= g < p.fns@.len() && sums[g] is Some ==> cert_for(p, g as nat, certs[g], sums),
        entry_plc(p, f, args, slots), vals_len_ok(args), vals_len_ok(slots),
        run_fn(p, f, init_entry(p, f, args, slots), fuel) is Some,
    ensures
        run_fn(p, f, init_entry(p, f, args, slots), fuel).unwrap().2
            <= poly_val(init_entry(p, f, args, slots), b),
```

- [ ] **Step 1:** Write the spec fns. `lemma_run_len_ok` comes first, since it relies on 8a's overflow-gives-`None` rule for push/extend/to_vec (`grow`, `SliceToVec`; sem.rs:405-411, 455-458). If that rule is missing from 8a's `sem.rs`, stop: that's a SPEC-CHANGE to 8a.
- [ ] **Step 2:** Prove `lemma_gap_dec`, `lemma_init_entry_len_ok`, `lemma_entry_plc`, `lemma_plc_stmts`, `lemma_plc_reachable`, `cost_from` (one case lemma per terminator kind, plus the dispatcher) and `theorem_cost`.
- [ ] **Step 3: Proof mutations**, each failing a named lemma:
  - `block_step_ok`'s `Return` requires `>= k` instead of `>= k + 1`;
  - the `Call(Fn)` case drops `n`;
  - `cert_for` drops `facts@.len() == 0`, so `theorem_cost` can't discharge the entry facts;
  - `gap(a, b)` defined as `a`, which fails `lemma_gap_dec` (M4);
  - `len_nat` as `elems(fr, v).len()`, one layer, which fails `sanity_len_double_ref` and `lemma_b0_double_ref`;
  - `cost_from` drops `plc` from its `requires`, so its body can't instantiate `cert_sem_ok`. Dropping `plc` from `cert_sem_ok` itself only strengthens the premise and fails nothing here; Task 3's `lemma_sym_block_sound` is what needs it.
- [ ] **Step 4: Final X′, before Tasks 3+.**
  - The spec's 23/36 is an upper bound. Dump the MIR of the 23 targets (Task 1 Step 4's command) and apply Task 3's write rule: subtract a target whose potential or facts need a non-`Mut`-typed local's atom across a writer, then subtract its callers (`CalleeNone`).
  - Expected about 19, from a scan of wire, h3 and quic MIR at the 2026-11-02 amendment. `huffman_decode` takes its `&mut`s in bb6 and calls `feed_bit` in bb8, so its counters don't survive, which loses it, `scan_string`, `decode_string` and `decode_field_line`. vest_lib was not dumped, so include it here.
  - Append one dated line after the spec's re-baseline line, `Final X′ (8b Task 2, before Task 3): X′/36`, naming each target lost and why. **Never edit the table rows, the 27/38 line or the 23/36 line.**
- [ ] **Step 5: Run the four checks and the evidence run.** The cost spec freeze starts after this commit.
- [ ] **Step 6: Commit:** `feat(ctcore): step-bound certificates and theorem_cost (steps <= summary(inputs))`

---

### Task 3: Abstract block effect (`cost_sym.rs`): spec and soundness lemmas

**Files:**
- Create: `crates/ctcore/src/cost_sym.rs`
- Modify: `crates/ctcore/src/lib.rs` (`pub mod cost_sym;` only) (I5)

**Consumes:** `cost.rs` (Task 2), `sem.rs`, `ct.rs` (`plc`, `mut_op`), `ct_lemmas.rs` (`lemma_eval_op_plc`, `lemma_place_plc`, `lemma_read_loc_mut`).

**Interfaces (produces):**
- **Types** (exec, used by the spec):
  - `pub enum Rel { Same, ValEq(Atom, u64 /* + k */), ValLe(Atom), LenEq(Atom), LenLe(Atom), Unknown }`: each local's post-state value in terms of pre-state atoms;
  - `pub struct Eff { pub rel: Vec<Rel>, pub edge: Vec<(usize /* succ block */, Vec<Fact> /* post-state facts on that edge */)> }`.
- **Spec:**
  - **What `plc` proves.** A `Mut` sits only at the top of a `Mut`-typed local; every other local and every slot is `no_mut`; a target's root is a slot or **any** non-`Mut`-typed local. It does not limit targets to `RefMut` roots: `locals[1] = Mut(Local(2))`, with local 2 a never-borrowed counter, satisfies `plc`, and `cert_sem_ok` ranges over all `plc` frames. So no address-taken set is sound here.
  - `pub open spec fn writer_place(b: Body, pl: Place) -> bool`: `b.locals@[pl.local] is Mut`, `pl.proj@.len() > 0` and `pl.proj@[0] is Deref`.
  - **Writers**, all syntactic:
    - a `writer_place` assigned by `Assign`, `SetDiscr` or a `Call` dst;
    - a `mut_op` arg 0 of `VecPush`/`VecSet`/`VecExtendFromSlice`;
    - a `mut_op` arg of `Call(Fn)`.

    Any other operand is `no_mut` (`lemma_eval_op_plc`), so `grow` and `write_back` do nothing for it.
  - `pub open spec fn rel_sound(rel: Rel, x: nat, pre: Frame, post: Frame) -> bool`. `Same` means the value **and** `len_nat` are unchanged, so Task 4's rewrites need no `plc`. With `v`, `w` the local's value in `pre`, `post`:
    - `Same`: `w == v` and `len_nat(post, w) == len_nat(pre, v)`.
    - `ValEq(Val(y, ty), k)`: `val_nat(ty, w) == atom_val(pre, Val(y, ty)) + k`. At `ty` only.
    - `ValEq(Const(c), 0)`: for every `ty2`, `val_nat(ty2, w) <= c`. The `Const` rule gives `Unknown` unless `n == uval(ty, n)`.
    - `ValLe(A)`: for every `ty2`, `val_nat(ty2, w) <= atom_val(pre, A)`.
    - `LenEq(A)`, `LenLe(A)`: `len_nat(post, w)` `==`, `<=` `atom_val(pre, A)`.
  - `pub open spec fn eff_sound(e: Eff, pre: Frame, post: Frame, succ: nat) -> bool`: every `rel` is sound, and the edge facts for `succ` hold at `post`.
- **Transfer:** `pub open spec fn sym_stmts(b: Body, stmts: Seq<Stmt>, facts: Seq<Fact>) -> Eff`: the rels from the block's start to `exec_stmts(..).0`, with an empty `edge`. `sym_block` extends it with the terminator. Lemma: `lemma_sym_stmts_sound`, same `requires` as `lemma_sym_block_sound`, ensuring `forall|s| eff_sound(sym_stmts(..), fr, exec_stmts(blk.stmts@, 0, fr).0, s)`.
- **Transfer:** `pub open spec fn sym_block(b: Body, blk: Block, facts: Seq<Fact>) -> Eff`, recognizing exactly:
  - `x = Copy(y)` (int, same `IntTy`), giving `ValEq(Val(y, ty), 0)`;
  - `x = Const(ty, n)`, giving `ValEq(Const(uval(ty, n)), 0)`. If `uval(ty, n) > u64::MAX`, it gives `Unknown` (M8);
  - `x = Bin(Add, ty, Copy(x), Const(1))` and `Wrapping(Add, ty)(x, 1)`, unsigned `ty` only (C2), giving `ValEq(Val(x, ty), 1)`, **only if** a pre-fact `Lt(Val(x, ty), A)` exists, where `A` is one of:
    - a `Const` ≤ `max(ty)`;
    - a `Val(_, ty)` of the same `IntTy`;
    - a `Len` with `ty == Usize`;
  - `x = Len(y)`/`VecLen(y)`, `y` an empty-projection local, giving `ValLe(Len(y))`, since `eval_rv`'s `Len` reads one layer and the atom reads all (`lemma_elems_le_len_nat`). Any other projection gives `Unknown` (M8);
  - `x = RefShr(y)`/`VecAsSlice(y)`, giving `LenEq(Len(y))`;
  - `x = copy (*y)`, giving `LenLe(Len(y))`;
  - `SliceSubrange(r, ..)`, giving `LenLe(Len(r))`;
  - `SliceToVec(r)`, giving `LenLe(Len(r))`;
  - **In-block composition:** a rule's atom is rewritten through the rel so far, so every rel lands on pre-state atoms: `_3 = copy (*_2); _4 = Len(_3)` gives `_4` `ValLe(Len(2))`. An operand whose rel so far is `Unknown` gives `Unknown`;
  - **Writes through `Mut`** (C1 option B): a writer makes **every** local `Unknown`, because it may target any non-`Mut`-typed local and a `Mut`-typed local's `Len` reads through its target. Put a `ponytail:` comment on this: it loses counters across any `&mut` call, and the upgrade is a frame invariant limiting targets to `RefMut` roots;
  - **Direct writes:** a non-writer place writes only its root local. If that root is not `Mut`-typed, every `Mut`-typed local also becomes `Unknown`, since it may target that root;
  - every other assignment to x gives `Unknown`;
  - untouched locals give `Same`.
  - **Edge facts** (unsigned compares only, C2):
    - `Switch(Copy(c))` where c was set in this block by `Bin(Lt, ty, a, b)` and is unchanged afterwards: `Lt(a', b')` on the non-zero target and `Le(b', a')` on the zero target, with a′, b′ the atoms of the operands' post values at `ty`;
    - `Gt`/`Ge`/`Le` likewise;
    - the `Assert(Lt(..), true, b)` success edge gives `Lt`;
    - an operand `Copy(z)` whose rel is `ValEq(Val(y, ty), 0)`, with `y` `Same` at the end of the block, gives the atom `Val(y, ty)`, so `_15 = copy _13; Lt(_15, _8)` gives `Lt(Val(13), Val(8))`. An operand `Const(ty, n)` gives `Const(uval(ty, n))` if it fits u64;
    - **Carry:** on every edge, every pre-fact whose atoms read only `Same` locals.
- **Lemmas:**
  - `proof fn lemma_sym_block_sound(p, ls, f, b, blk, facts, fr)`: requires `ok_prog(p, ls)`, `plc(p, ls, f, fr)`, `facts_hold(fr, facts)` and `frame_len_ok(fr)`. It ensures `eff_sound(sym_block(..), fr, post, succ)` for the successor the terminator actually takes, with `post` the **successor frame** (I2):
    - `fr1 = exec_stmts(..).0` for `Goto`/`Switch`/`Assert`;
    - `exec_intr(k, fr1, ..).0` for `Call(Intr)`;
    - for every `out` with `frame_len_ok(out)`, `call_leave(fr1, out, wb, dst).0` for `Call(Fn)`.
  - **Per-pattern lemmas:**
    - `lemma_rel_copy`, `lemma_rel_const`, `lemma_rel_len`, `lemma_rel_shr`, `lemma_rel_deref`, `lemma_rel_subrange`, `lemma_edge_lt`;
    - `lemma_rel_inc`: the no-wrap argument, from the `Lt` fact, the width bound and `lemma_gap_dec`;
    - `lemma_nonwriter_root(p, ls, f, fr, pl)`: under `plc` and `ok_place`, a non-`writer_place`'s `place_loc`, if any, is rooted at `pl.local`.

- [ ] **Step 1:** Write `lemma_rel_inc` first, as the bounded probe. If it needs `nonlinear_arith` with more than one product, or rlimit > 4 after one split, stop and report.
- [ ] **Step 2:** Write `lemma_nonwriter_root`, the remaining lemmas and `lemma_sym_block_sound`. Use per-statement and per-intrinsic helper lemmas from the start, not one big match (8a lesson).
- [ ] **Step 3: Mutations**, each failing a named lemma:
  - the increment rule without the `Lt` pre-fact (`lemma_rel_inc`);
  - `SliceSubrange` as `LenEq` (`lemma_rel_subrange`);
  - `x = Len(y)` as `ValEq(Len(y), 0)`, false on `Shr(Shr(Arr))` (`lemma_rel_len`);
  - a writer that keeps a never-borrowed non-`Mut`-typed local `Same`, i.e. the address-taken rule (`lemma_sym_block_sound`) (C1);
  - a writer, or a direct write to a non-`Mut`-typed local, that keeps a `Mut`-typed local `Same` (`lemma_sym_block_sound`) (C1);
  - `lemma_sym_block_sound` stated at `exec_stmts(..).0` for `Call(Intr)`, which fails on the `VecLen` dst (I2);
  - carry keeps a fact over a non-`Same` local (`lemma_sym_block_sound`).
- [ ] **Step 4: Run the four checks and the evidence run.**
- [ ] **Step 5: Commit:** `feat(ctcore): sound abstract block effect for cost certificates (counter increment, lengths, Mut writes, edge facts)`

---

### Task 4: Verified validator `check_cert`

**Files:**
- Create: `crates/ctcore/src/cost_check.rs`, `crates/ctcore/tests/cost_check.rs`
- Modify: `crates/ctcore/src/lib.rs`: `pub mod cost_check;` and the explicit `pub use cost_check::check_cert;`, with no glob (I5, M2)

**Consumes:** Tasks 2 and 3. From `cost_sym.rs`: `Rel`, `Eff`, `SymEff`, `eff_view`, `eff_sound`, `sym_block`, `sym_stmts`, `sym_block_sound`, `lemma_sym_block_sound`, `lemma_sym_stmts_sound`. `sym_block` and `sym_stmts` are spec fns over `Seq` and return a `SymEff`; `eff_view(e: Eff) -> SymEff` bridges. Both lemmas have the signature `(p, ls, f: nat, b: nat, blk, facts, fr)`, with `b` the block index, and require `ok_prog(p, ls)`, `f < p.fns@.len()`, `b < p.fns@[f as int].blocks@.len()`, `blk == p.fns@[f as int].blocks@[b as int]`, `plc(p, ls, f, fr)`, `facts_hold(fr, facts)`, `frame_len_ok(fr)`. From `check.rs`: `is_mut_op`.

**Interfaces (produces):** all `pub fn`, each with the stated `ensures`.
- **Hand copies** (M18; ctcore's types derive nothing): `atom_copy(a: &Atom) -> (r: Atom) ensures r == *a`, plus the same for `IntTy` (`int_ty_copy`) and `Fact`. `mono_copy` and `poly_copy` ensure `mono_view_eq` and `monos_same`, not `==`: `Vec` has no extensional `==`. Budget for them, and for the overflow and bounds obligations of every exec fn here. Also `rel_clone(r: &Rel) -> (s: Rel) ensures s == *r` and `binop_clone(o: &BinOp) -> (s: BinOp) ensures s == *o`. Not `rel_copy`: `cost_sym::rel_copy` is a spec fn.
- **Effect builders**, the exec twins of Task 3's spec:
  - `exec_sym_stmts(b: &Body, stmts: &Vec<Stmt>, facts: &Vec<Fact>) -> (r: Eff) ensures eff_view(r) == sym_stmts(*b, stmts@, facts@)`;
  - `exec_sym_block(b: &Body, blk: &Block, facts: &Vec<Fact>) -> (r: Eff) ensures eff_view(r) == sym_block(*b, *blk, facts@)`.

  Each mirrors the spec one unfold at a time: a loop with invariant `sym_from(*b, ss, k, st_k, facts@) == sym_from(*b, ss, 0, st_0, facts@)`, with `st_k` built from a `Vec<Rel>` and an `Option<Cmp>` (`Cmp` is an exec struct; `SymSt` is not), and likewise for `carry_from`. Budget for these twins, each ending in `=~=` on `Seq`: `rule_stmt`, `rule_intr`, `write_root`, `all_unknown`, `st_write`, `new_cmp`, `cmp_atom`, `term_rels`, `term_edges`, `switch_edges`, `switch_target`, `atom_same`, `writer_place`, `intr_writer`, `call_writer` and `rel_inc`, whose `exists` is a search loop whose hit is the witness.
  - `exec_uval(ty: &IntTy, n: u128) -> (r: u128) ensures r as int == uval(*ty, n)` covers all 13 `IntTy`: `rel_const` has no sign guard. `cost_sym`'s `lemma_uval_bounds` and `lemma_unsigned_width` are private, and the latter requires `!signed(ty)`. Use `lemma2_to64` and `lemma_pow2_strictly_increases(64, 128)`; no `by (compute)`.
- **Atom order:** `atom_lt(a: &Atom, b: &Atom) -> (r: bool)`, a total order with its spec twin `spec_atom_lt`. Canonical means non-decreasing under `atom_lt`; `Len(1)·Len(1)` is legal.
- **Polynomial operations:**
  - `poly_add(a: &Poly, b: &Poly) -> (r: Option<Poly>)` ensures `r matches Some(q) ==> forall fr. poly_val(fr, q@) == poly_val(fr, a@) + poly_val(fr, b@)`;
  - `poly_dominates(lhs: &Poly, rhs: &Poly, extra: u64) -> (r: bool)` ensures `r ==> forall|fr| poly_val(fr, lhs) >= poly_val(fr, rhs) + extra`. It works by syntactic monomial matching on canonical atom lists with coefficient ≥, with `extra` taken from the constant monomial.
- **Rewrites:**
  - `pull_post(q: &Poly, e: &Eff, facts: &Vec<Fact>) -> (r: Option<(Poly, Poly)>)` ensures `r matches Some((up, credit)) ==> forall|pre: Frame, post: Frame, s: nat| facts_hold(pre, facts@) && #[trigger] eff_sound(eff_view(*e), pre, post, s) ==> poly_val(post, *q) + poly_val(pre, credit) <= poly_val(pre, up)`. A `Val(x, _)` or `Len(x)` with `x >= e.rel.len()` gives `None`: `eff_sound` says nothing of it. It maps post-atoms to pre-atoms, each by its local's one rel:
    - `Const(c)` to itself;
    - `Val(x, ty)`: `Same` to itself; `ValEq(Val(y, ty), 0)` to `Val(y, ty)`, same `ty`; `ValEq(Const(c), 0)` to `Const(c)`; `ValLe(A)` to `A`; anything else `None`;
    - `Len(x)`: `Same` to itself; `LenEq(A)` or `LenLe(A)` to `A`; anything else `None`;
    - `Gap(a, b)`, with `a'` the map of `a` (`None` if none):
      - `b = Val(x, ty)` with rel `Same` or `ValEq(Val(y, ty), 0)`, or `b = Len(x)` with rel `Same` or `LenEq(A)`: `Gap(a', B)`, with `B` its image;
      - `b = Val(i, ty)` with rel `ValEq(Val(i, ty), 1)`: `Gap(a', Val(i, ty))`, a **decrement** if `facts` has `Lt(Val(i, ty), a')` (`lemma_gap_dec`);
      - any other `b`, including `Const`, `Unknown`, `ValLe`, `LenLe` and nested `Gap`: `a'`, since `Gap(a, x) <= a`.

    A monomial `c·a1·a2` maps atom by atom, sorted non-decreasing, with `Const` atoms folded into `coef` (checked; overflow gives `None`). Its first decrement atom adds `c` times the other atom's image to `credit` (`c` alone for one atom), since `g'·u' + u <= g·u` when `g' + 1 <= g` and `u' <= u`. Further decrements in the monomial earn nothing.
  - `bound_post(p: &Poly, pot: &Poly, e: &Eff, pre_facts: &Vec<Fact>, post_facts: &Vec<Fact>) -> (r: Option<Poly>)` ensures `r matches Some(q) ==> forall|fr| facts_hold(fr, post_facts@) ==> poly_val(fr, q) >= poly_val(fr, p)`. Let `budget` be `pot` plus the credits of those monomials of `p` that `pull_post` maps. A monomial whose image's atoms appear in `budget` is kept. Any other has each top-level atom and each `Gap` minuend `t` replaced by `u`, for the first `Le(t, u)` or `Lt(t, u)` in `post_facts`; this is one pass, not repeated. The order of `post_facts` comes from the certificate's block facts, so the result is determined.
  - `instantiate(sum: &Poly, p: &Program, g: usize, args: &Vec<Operand>) -> (r: Option<Poly>)` ensures `r matches Some(q) ==> forall|fr| poly_val(fr, q) >= poly_val(call_enter(*p, g as nat, fr, args@).0, sum@)` (M3). It substitutes callee param atoms with arg atoms:
    - `Copy(Place { local, proj: [] })` maps `Val(j, ty)` to `Val(local, ty)`, with matching `IntTy` (C2), and `Len(j)` to `Len(local)`;
    - `Gap(a, b)` maps by recursion on `a` and `b`;
    - `Const(ty, n)` maps to `Const(uval(ty, n))` when it fits u64, and only if the atom's `ty` equals the operand's;
    - callee non-param atoms map to `Const(0)`, since those locals are `Unit` at entry;
    - anything else gives `None`, per atom: an arg no atom reads may be anything;
    - the result is re-sorted and folded as in `pull_post`.
- **Facts:** `facts_imply(have: &Vec<Fact>, need: &Vec<Fact>) -> (r: bool)` ensures `r ==> forall|fr| facts_hold(fr, have@) ==> facts_hold(fr, need@)`. Syntactic: each needed fact appears, or follows by `Lt ⇒ Le`.
- **Blocks and certificates:**
  - `check_cost_block(p: &Program, f: usize, b: usize, c: &Cert, sums: &Vec<Option<Poly>>) -> (r: bool)` ensures `r ==> forall|ls, fr| ok_prog(*p, ls) && plc(*p, ls, f as nat, fr) && facts_hold(fr, c.blocks@[b].facts@) && frame_len_ok(fr) ==> block_step_ok(*p, f as nat, b as nat, *c, sums@, fr)`. It is named `check_cost_block`, not `check_block`, because `lib.rs` glob-imports `check::*` (M2);
  - `check_cost_block` returns false if `f`, `b` or a successor is out of range, or `c.blocks.len()` differs from the block count. For a block with `k` statements, `facts = &c.blocks[b].facts`, `e = exec_sym_block(&p.fns[f], blk, facts)`, `es = exec_sym_stmts(&p.fns[f], &blk.stmts, facts)`. Its proof calls `lemma_sym_block_sound` and `lemma_sym_stmts_sound` at `(*p, ls, f as nat, b as nat, blk, c.blocks@[b as int].facts@, fr)` inside the `forall|ls, fr|`. For `Switch`, prove by induction on `switch_target` that the target taken is some `e.edge[i].0`, and read that edge's facts through `eff_sound`. Every entry for one target has the same facts.
    - **Each edge** the terminator can take to `s` (every `Switch` target, `Assert`'s success edge, `Goto`, `next`), with `post_facts` the edge's facts from `e`: `facts_imply(post_facts, s's facts)`, `need = bound_post(pot_s, pot_b, e, facts, post_facts)`, `(up, cr) = pull_post(need, e, facts)`.
    - **Charge**, at the frame after the statements: `Call(Fn(g))` is `instantiate(sums[g], ..)`, with `sums[g]` `Some` or the block fails. `SliceToVec(Copy(y))` and `VecExtendFromSlice(_, Copy(y))`, with `y` an empty-projection local, are `Len(y)` (`lemma_elems_le_len_nat`), and any other operand fails the block. Other intrinsics are 0. `(upc, crc) = pull_post(charge, es, facts)`.
    - **Check:** `poly_dominates(pot_b + cr + crc, up + upc, k + 1)`, with `+` as checked `poly_add`.
    - `Return`: `poly_dominates(pot_b, empty, k + 1)`. `Abort`: true.
  - `check_cert(p: &Program, f: usize, c: &Cert, sums: &Vec<Option<Poly>>) -> (r: bool)` ensures `r ==> cert_for(*p, f as nat, *c, sums@)`.
- **`tests/cost_check.rs`**, hand-built core programs with hand-written certificates:
  - `accepts_straight_line_const`
  - `accepts_counted_loop_const_bound`
  - `accepts_counted_loop_len_bound`
  - `accepts_nested_quadratic`: `settings_ok`'s shape. `_2 = VecLen(_1)` as a terminator, an outer counter from 0, the inner counter set by `_11 = copy _3; _10 = Add(_11, 1)`, both tests through temp copies, a call or `VecIndex` in each body, entry `c·Len(1)·Len(1) + ..`
  - `accepts_bound_from_le_fact`: `parse`'s bb3-bb11. The bound `_8` is a call's result, bounded only by `Le(Val(8), Val(4))` from a zero edge, `Val(4)` by `ValLe(Len(2))`, the header's facts empty
  - `accepts_mid_body_exit`: `parse_prefix_int`'s shape, counter from 1, temp-copy test, increment two blocks later, empty header facts
  - `accepts_len_cost_intrinsic`: `bytes_at`'s tail, `Len(1) + 3` through `Len(12) + 2`
  - `accepts_arg_is_dst`: `_3 = &_1; _3 = g(_3)`
  - `accepts_call_with_summary`
  - `accepts_double_ref_len`: `_3 = copy (*_2); _4 = Len(_3)` over a counted loop, paid by `Len(2)`, and a caller's `_3 = &_1` passing its `Len(1)`
  - `rejects_pot_too_small_by_one`
  - `rejects_missing_lt_fact`
  - `rejects_wrong_successor_facts`
  - `rejects_unknown_atom_in_rhs`
  - `rejects_entry_facts_nonempty`
  - `rejects_summary_mismatch`
  - `rejects_signed_counter`: an `I64` counter with an `Lt` fact gets no increment rule (C2)

- [ ] **Step 1:** Write the hand copies, then the polynomial and fact helpers, verifying each.
- [ ] **Step 2:** Write `check_cost_block` per terminator kind (`loop_isolation(false)` where needed) and `check_cert`.
- [ ] **Step 3:** All tests pass.
- [ ] **Step 4: Exec mutations**, each failing a named `ensures`:
  - `poly_dominates` ignores `extra`;
  - `pull_post` maps an `Unknown` atom as `Same`;
  - `pull_post` earns credit without the `Lt` fact;
  - `check_cost_block` skips the successor-facts check.
- [ ] **Step 5: Run the four checks and the evidence run.**
- [ ] **Step 6: Commit:** `feat(ctcore): verified cost-certificate validator (check_cert ==> cert_for)`

---

### Task 5: Untrusted inference (`loops.rs`) and the `analyze` API

**Files:**
- Create: `crates/ctcore/src/loops.rs`, `crates/ctcore/tests/cost_infer.rs`
- Modify: `crates/ctcore/src/lib.rs` (`pub mod loops;` and `analyze`). `Poly` and `Cert` live in `cost`, `use cost::{Cert, Poly}` by name, no glob (M2).

**Consumes:** Task 4, `check::check_wf`, `infer::callee_order`.

**Interfaces (produces):**
- **Graph structure** (`loops.rs`):
  - `pub fn dominators(b: &Body) -> Vec<Vec<bool>>`: iterative dataflow with a pass bound;
  - `pub fn back_edges(b: &Body, dom: &Vec<Vec<bool>>) -> Vec<(usize, usize)>`;
  - `pub fn natural_loop(b: &Body, latch: usize, header: usize) -> Vec<bool>`.
- **Loops** (`loops.rs`):
  - `pub struct Counted { pub header: usize, pub body: Vec<bool>, pub counter: usize, pub ty: IntTy, pub bound: Atom, pub test_block: usize, pub inc_block: usize }`;
  - `pub fn recognize(b: &Body, lp: &Vec<bool>, header: usize) -> Option<Counted>`, by the spec's counted-loop definition, unsigned counters only (C2);
  - `pub enum CostWhy { Bounded, NotCounted(usize /* a header, or the block where the region got stuck */), Unresolved, Recursion, CalleeNone(usize), DegreeCap, Overflow, Validator(usize /* block */), NotWf, NotTyped }` (M15). Only the driver builds `NotTyped` (Task 6); `analyze` never returns it.
- **Certificates** (`loops.rs`): `pub fn build_cert(p: &Program, f: usize, sums: &Vec<Option<Poly>>) -> Result<Cert, CostWhy>`.
  - Block costs are local.
  - **What `check_cert` checks, from `ctcore::cost_check`.** It is syntactic, so take forms from its own functions: `exec_sym_block`, `exec_sym_stmts`, `pull_post`, `bound_post`, `instantiate`, `term_charge`, `atom_lt`, `atom_copy`, `fact_copy`, `poly_copy`. Don't modify `cost_check.rs`.
    - **Pots.** Atoms in a monomial are non-decreasing under `atom_lt` (`Const < Val < Len < Gap`), at most 2, else `check_cert` is false. No `Const` atom in a monomial: fold it into `coef`, because the left side is not normalised. `pull_post`'s output is already folded and sorted. Omit zero-coefficient monomials. Duplicates and monomial order don't matter; `poly_add` concatenates and never returns `None`.
    - **`Gap`.** `Gap(a, b)` keeps `b` only if `b`'s rel is `Same`, a plain copy (`LenEq` for a `Len`) or the increment. Otherwise, including `b = Const(c)` and a counter just initialised, it pulls to `a`'s image.
    - **Facts first, forward.** A block's facts must each appear on every incoming edge, as `exec_sym_block`'s `edge[i].1` gives them, with only `Lt ⇒ Le` as inference. Entry facts are empty. So derive facts from those edges, not by hand: `Lt(Val(counter, ty), bound)` is the test edge's, with `bound` and the temp copy as `cmp_atom` normalises them, and it holds from the test to the increment, not after it. An outer loop's `Lt` is carried through the inner loop. The header has no `Lt`: `Le(counter, bound)` is false at `parse`'s entry (`_13 = 1`, `_8` havocked).
    - **Pots second, backward**, in postorder with back edges cut: every successor before its predecessors. At block `b` with `k` statements, `e = exec_sym_block`, `es = exec_sym_stmts`, charge `(upc, crc) = pull_post(term_charge(..), es, facts)`; for each edge to `s`, `(up, cr) = pull_post(pot_s, e, facts)`. Then `pot_b` is the monomial-wise maximum over edges of `up + upc + (k + 1) - cr - crc`, each coefficient floored at 0. `Return`: `k + 1`. `Abort`: an empty pot and no facts.
    - **Headers.** A loop's header has `P·Gap(bound, Val(counter, ty)) + P + rest`, with `rest` the monomial-wise maximum of its exits' pots. Find `P` by a first backward pass over the body with the header's pot seeded as `rest` and the increment earning no credit: `P` is the header's result minus `rest`. Then run the pass again with the real header pot; the increment's credit pays the `+ P` back. Nesting comes out by itself, because the inner `Gap` pulls to `bound` where its counter is set. Do inner loops first. These two results pass `check_cert`. `parse_prefix_int`: `P = 34`, `rest = 7`, header `34·Gap(V3, V13) + 41`, entry `34·Len2 + 55`. `settings_ok`, with `A = Gap(V2, V3)` and `I = Gap(V2, V10)`: inner `P = 13`, outer `P = 13·V2 + 27`, outer header `13·V2·A + 27·A + 13·V2 + 30`, inner header `13·I + 13·V2·A + 27·A + 18`, outer increment `13·V2·A + 27·A + 5`, entry `13·Len1·Len1 + 40·Len1 + 33`. Do not emit `Gap·Gap`.
    - **Raising.** `bound_post` keeps a monomial whose image's atoms are already in `b`'s pot or its credits, and raises it under the edge's first `Le(t, u)` or `Lt(t, u)` otherwise. So raise only when needed: pull without raising first. If a predecessor's `pull_post` returns `None` on an atom `t` (`parse`'s `_8`, a call result), mark `t` and redo the backward pass, replacing `t` by `u` at the block whose edge has `Le(t, u)`, so that block's pot doesn't read `t`. Raising everything is wrong: `settings_ok`'s inner exit has `Le(V2, V10)`, and `V2` must stay.
    - **Reasons.** `pull_post`'s `None` doesn't say why. Your own degree over 2 is `DegreeCap`, your own failed `checked_*` is `Overflow`, a `pull_post` `None` is `Validator(b)`.
  - Writers lose every local: a loop whose body holds a `Mut`-arg call or `VecPush` has no counter left, as X′ predicts. The expectation for the four Task 2 losses is exact: `huffman_decode` is `NotCounted(<header>)`, because `recognize` rejects any loop whose body holds a `Mut`-arg call (`block_writer`); `scan_string`, `decode_string` and `decode_field_line` are `CalleeNone(<fn index>)`. A `Validator(..)` for `huffman_decode` would be a mismatch to explain, not the predicted verdict.
  - Its exec code under `verus!` still carries Verus's overflow and bounds obligations, which is the GC's "memory safety" (M9). Budget for them and for the hand copies (M18).
- **The API** (`lib.rs`, verified, like `check_program`; M9): `pub fn analyze(p: &Program) -> (r: (Vec<Option<Poly>>, Vec<Cert>, Vec<CostWhy>))`.
  - `ensures r.0@.len() == p.fns@.len() && r.1@.len() == p.fns@.len() && forall|g: int| 0 <= g < r.0@.len() && r.0@[g] is Some ==> cert_for(*p, g as nat, r.1@[g], r.0@)`.
  - It runs `check::check_wf` first: a non-wf program gives all-`None` with `NotWf`.
  - It works bottom-up in `infer::callee_order`. Recursion (`Err`) gives `None` with `Recursion`.
  - Then `pub fn revalidate(p: &Program, certs: &Vec<Cert>, sums: Vec<Option<Poly>>) -> (r: Vec<Option<Poly>>)`, requiring both lengths to equal `p.fns@.len()`, ensures `r@.len() == p.fns@.len()` and `forall|g: int| 0 <= g < r@.len() && r@[g] is Some ==> cert_for(*p, g as nat, certs@[g], r@)`. Each pass runs `check_cert` on every `Some` and sets failures to `None`; an unchanged pass returns. Decrease a pass counter starting at `n`, and return all-`None` if it runs out: the proof needs no count of `Some`s, and its only invariant is `!changed ==> forall|j: int| 0 <= j < g && sums@[j] is Some ==> cert_for(*p, j as nat, certs@[j], sums@)`. A summary is `Some(poly_copy(&cert.blocks[0].pot))`; `check_cert` compares by `poly_eq`, so the copy needs no proof. A `None` entry's cert is `Cert { blocks: Vec::new() }`. For `Validator(b)`, the first `b` with `!check_cost_block(p, g, b, &certs[g], &sums)`, or 0 if there is none. `analyze`'s `Some` says nothing without `check_program` `Ok`; the driver supplies that (Task 6).
  - `theorem_cost` is never re-exported (E0432). It stays at `ctcore::cost::theorem_cost`.
- **`tests/cost_infer.rs`:**
  - `infers_counted_const`
  - `infers_counted_len`
  - `infers_nested_quadratic`
  - `infers_mid_body_exit`
  - `infers_counter_from_one`
  - `infers_call_chain`
  - `none_for_off_progress_loop`
  - `none_for_recursion`
  - `none_for_unknown_bound`
  - `none_for_not_wf`
  - `revalidation_drops_dependent_caller`: calls `revalidate` directly with hand-built certs where the callee's is one lower than valid and the caller's is valid against the callee's summary. Both come back `None`.

- [ ] **Step 1:** Write the dominators, loops and recognizer (with plain unit tests), then `build_cert` and `analyze`.
- [ ] **Step 2:** All tests pass. `analyze`'s ensures verifies.
- [ ] **Step 3: Mutation.** Make `build_cert` emit a potential one lower in the loop body. The tests then show `None` (via `Validator(..)`), not a wrong `Some`. Record this.
- [ ] **Step 4: Run the four checks and the evidence run.**
- [ ] **Step 5: Commit:** `feat(ctcore): untrusted counted-loop inference producing validated step-bound certificates`

---

### Task 6: Driver `cost` mode and cost fixtures

**Files:**
- Modify:
  - `tools/ct-driver/src/main.rs` (`CT_MODE=cost`);
  - `tools/ct-driver/src/manifest.rs` (the `cost-root <def-path>` line kind);
  - `tools/ct-fixtures/src/lib.rs` (cost fixtures);
  - `scripts/ct-check.sh`.
- Create: `tools/ct-fixtures/cost-manifest.txt` (the fixtures' `cost-root` lines; I6), `tools/ct-fixtures/expected-cost.txt`

**Consumes:** `ctcore::analyze`, `ctcore::check_program`, 8a's `translate_closure()` (preflight), Task 1b's `analyse()` crate list.

**Interfaces (produces):**
- **Cost mode** translates from the `cost-root` lines. It reads no labels. `translate_closure` applies no label rule, so 8a's root-label rule, which runs in check mode only, doesn't apply here (preflight).
  - It keeps only cost roots whose crate prefix is the crate being compiled, through a `crate_cost_roots` twin of `crate_roots`. It analyses each root's closure as its own `Program`, as in 8a. A crate with no cost root writes an empty file.
  - **Typing first (C1 option B).** Before `analyze`, it calls `check_program(&p, &vec![None; n])`: no declared secrets, so all-public labels. `Ok(ls)` supplies `theorem_cost`'s `ok_prog(p, ls)`. The driver prints a `Recursion` reject itself, as `none <def-path> Recursion`, without calling `analyze`. Any other reject, `NotWf` included, is `none <def-path> NotTyped`. A cost root matching no monomorphic fn stays a hard error.
  - ct-check.sh fails if any `cost-root` got no verdict line in any crate.
- **Entry premises.** No code calls `theorem_cost`: it stays at `ctcore::cost::theorem_cost`, and a `bounded` line means its statement applied to the program. `entry_plc` and `vals_len_ok` are about the Rust caller's values. As with `theorem_ct`'s `args_agree`, nothing discharges them mechanically; `wf_local_ty` shows a non-`&mut` parameter's type and a `&mut` pointee's type have no `Mut`, and the argument rests on that. The TRUSTED cost-model row says so (Task 7).
- **It calls `analyze` and writes `cost-<crate>.txt`**, one line per cost root:
  - `bounded <def-path> deg=<0|1|2> steps <= <poly in source param names>`;
  - `none <def-path> <Why>`, from `analyze`'s third vector at the root's fn index, when its first vector holds `None` at that index. `CostWhy` is `ctcore::loops::CostWhy`; the crate root does not re-export it, and it has no `Debug` or `Display`, because it is declared inside `verus!`. Render it with a hand-written function in `main.rs`: the variant name, with `(n)` appended for the three that carry a number: `NotCounted(h)` (h is a block index), `CalleeNone(g)` (g is a fn index in the closure's `Program`), `Validator(b)` (b is a block index); the others are bare (`Unresolved`, `Recursion`, `DegreeCap`, `Overflow`, `NotWf`, `NotTyped`). `Bounded` with a `None` cannot occur; treat it as an internal error and fail the run. After `check_program` is `Ok`, `analyze` itself returns neither `Recursion` nor `NotWf` for the root, so the driver's own `Recursion` and `NotTyped` lines are the only ones printed.
  - `none <def-path> NotTyped` or `none <def-path> Recursion`, when `check_program` rejects (above);
  - or `none <def-path> Unsupported|Unresolved <first error>`, when `translate_closure` fails (M15).
- **Cost fixtures**, in `lib.rs` as plain Rust (`cost_pos_*` must be `bounded`; `cost_neg_*` must be `none`). Loops are `while` loops, because `for`/Range calls `Iterator::next`, which is Unresolved. Vecs and slices are of `u8` only, or a Task 1b pair (M16).
  - `cost_pos_straight` (deg 0)
  - `cost_pos_loop_const` (deg 0)
  - `cost_pos_loop_len` (deg 1)
  - `cost_pos_nested` (deg 2)
  - `cost_pos_early_exit` (deg 1)
  - `cost_pos_call` (deg 1)
  - `cost_neg_off_progress`
  - `cost_neg_parsed_count`: a loop bound read from input bytes
  - `cost_neg_recursion`
  - `cost_neg_while_true_break_on_data`
  - `cost_neg_not_typed`: must translate cleanly and then fail `check_program`, expected `none .. NotTyped`. The candidate is `fn(x: &mut u8) -> &mut u8`, since `wf_body` forbids `Mut` in local 0. Step 1 confirms it.
    This fixture shows an ill-typed program gets `none <root> NotTyped` and no bound, because `check_cert`'s `true` says nothing without `check_program` `Ok` (M6).
  - Expected verdicts, which Step 1 confirms and does not just record: `cost_neg_off_progress`: `NotCounted(<header>)`. `cost_neg_while_true_break_on_data`: `NotCounted(<header>)`, because there is no `counter < bound` test. `cost_neg_parsed_count`: `Validator(<block>)`, not `NotCounted`: the loop is counted, but the bound is a havocked read that `pull_post` cannot carry to the entry (the shape of `none_for_unknown_bound`). `cost_neg_recursion`: `Recursion`. `cost_neg_not_typed`: `NotTyped`.
  - These are not `root`s, so the 58 check verdicts don't change.
- **`expected-cost.txt`** lines are `bounded <path> deg=<d>` or `none <path> <Why>`. Coefficients are not pinned. Pin `CalleeNone(g)` and `Validator(b)` payloads only where a fixture needs them. The payload is a fn or block index in the closure's own numbering, so it moves when the closure changes.
- **`ct-check.sh`** (M14):
  - `analyse()` gains a mode-to-filename map (`check` gives `report-`, `selftest` gives `selftest-`, `cost` gives `cost-`).
  - The fixtures' cost run passes `tools/ct-fixtures/manifest.txt:tools/ct-fixtures/cost-manifest.txt` as `CT_MANIFEST`.
  - It prints `ct-check: cost fixtures 11/11`.
  - The Task 6 report gives the added cold and warm ct-check time.

- [ ] **Step 1:** Implement the cost mode and fixtures. The diff is empty.
- [ ] **Step 2: Translator-side mutation** (M5). The translator maps blocks 1:1 and has no notion of a back edge. So translate **every** `Goto` as `Return`.
  - Expect `cost_neg_off_progress`, `cost_neg_parsed_count` and `cost_neg_while_true_break_on_data` to become `bounded`, which the diff catches.
  - `cost_neg_recursion` stays `none Recursion`.
  - Record which lines changed. Revert.
  - Separately, skip the `check_program` call: `cost_neg_not_typed` becomes `none .. NotWf`, which the diff catches. Map every reject to `NotTyped`: `cost_neg_recursion` becomes `none .. NotTyped`, which the diff catches. Revert both.
- [ ] **Step 3: Run the four checks and the evidence run.**
- [ ] **Step 4: Commit:** `feat(ct-driver): cost mode — step-bound report for cost roots; cost fixtures`

---

### Task 7: Run over the parser targets, record coverage, add the gate, update docs

**Files:**
- Create:
  - `tools/ct-driver/cost-targets.txt`: the `cost-root` lines for the 36 targets, each followed by `# predicted: bounded|none (<why>)`. The prediction is Task 2's final X′, and it also names the original 27/38 row;
  - `tools/ct-driver/expected-cost.txt` (M13).
- Modify:
  - `tools/ct-driver/manifest.txt`: only `intr` lines a Step 0 rerun finds beyond Task 1b's, and only mappings to 8a's existing intrinsics;
  - `tools/ct-driver/selftest.txt`: one vector per such new `intr` line (M12);
  - `scripts/ct-check.sh`, `scripts/verify.sh`, `TRUSTED.md`, `docs/superpowers/specs/2026-10-27-verified-http3-design.md`.

**Consumes:** Task 6, Task 2's final X′.

**Interfaces (produces):**
- **`ct-check.sh` cost run:** `CT_MODE=cost CT_CRATES=wire,h3,quic`, through `analyse()`'s crate list, with `CT_MANIFEST=tools/ct-driver/manifest.txt:tools/ct-driver/cost-targets.txt`. Then it compares with `expected-cost.txt`:
  - a `bounded` that becomes `none` is a failure;
  - a new `bounded` is a failure until `expected-cost.txt` is updated in the same commit, with the bound in the report;
  - it prints `ct-check: cost X/36 bounded`.
- **`verify.sh`'s final line** becomes `verify.sh: all crates verified, duvet ok, ct ok (10 declassify), cost X/Y, escapes accounted (1)`. X/Y is read from ct-check's `cost X/Y bounded` line (M11).
- **TRUSTED.md** gains the spec's cost-model row, verbatim, with the entry-premise sentence from §Cost analyser and "of a returning run; aborts and panics are outside".
- **The design spec's Phase 8 entry** gains the measured coverage `X/Y` and one line: "bounds are core steps, not time or memory".

- [ ] **Step 0: Census rerun** (M17). `phase-3d` has merged to main (510aac3), so rerun Task 1's census and dry run on the rebased branch first. Task 1's census output was lost to a reboot, and this run regenerates it under `<scratch>`. Record any change.
- [ ] **Step 1:** Run over the targets and write `expected-cost.txt` from the result.
- [ ] **Step 2: Coverage report.**
  - A table of the 36 targets, plus the two dropped QuicVarInt rows marked `not a root (I3)`. Columns:
    - `original` (27/38 table);
    - `re-baseline` (Task 2's final X′);
    - `actual`;
    - the bound (for bounded) or the `CostWhy`/translation error (for none);
    - a one-line explanation for each miss against either prediction.
  - The expectation for the four Task 2 losses is exact: `huffman_decode` is `NotCounted(<header>)`, because `recognize` rejects any loop whose body holds a `Mut`-arg call (`block_writer`); `scan_string`, `decode_string` and `decode_field_line` are `CalleeNone(<fn index>)`. A `Validator(..)` for `huffman_decode` would be a mismatch to explain, not the predicted verdict.
  - `CalleeNone(g)` and `Validator(b)` payloads are printed as found. They are indices in the closure's own numbering, so a change is not a regression.
  - The headline: **X of 36 targets bounded**, against 27/38, 25/36 and X′/36.
- [ ] **Step 3: Real-code mutation** (in a scratch copy made by `git archive`, never the worktree). In `h3::frame::settings_ok`, change the inner `j += 1` to `j += 0`. `settings_ok` must become `none`. (`huffman_decode` is expected `none` already under Task 3's write rule, so it can't serve.)
- [ ] **Step 4:** Edit verify.sh, TRUSTED.md and the design spec. Run the four checks and the evidence run.
- [ ] **Step 5: Commit:** `feat: verified step bounds for X/36 parser targets (wire, h3/QPACK, quic); cost gate in verify.sh`

---

### Task 8 (stretch; controller go/no-go): off-progress loops via callee return facts

**Also on the go/no-go list: `at_ok`.** A second frame hypothesis beside `plc` (every `Mut` target's root is a slot or a `RefMut` root) would make an address-taken write rule sound and recover `huffman_decode`, `scan_string`, `decode_string` and `decode_field_line`. Estimate: one spec fn, one syntactic set, about five lemmas. `theorem_cost`'s statement does not change; `cert_sem_ok` only gains a hypothesis, so Tasks 2-4's proofs stay valid inputs. Decide from Task 7's measured blockers.

**Go only if** all of these hold (M10):
- Tasks 1–7 are reviewed and approved;
- ctcore's total proof time is < 60 s, measured as Task 1 Step 1 did, next to its recorded baseline;
- at least 4 targets satisfy both of these:
  - **off-progress:** the verdict is `none <path> NotCounted(<header>)`, where the header's loop advances by `off = off + consumed`, with `consumed` from a callee's return;
  - **sole blocker:** the target translates, every callee in its closure is `bounded`, and that header is its only failure.

Otherwise record `not attempted` with those numbers. Under the post-1b translator, the candidates are `parse_settings`, `decode_lines(_bounded)`, `parse_payload` and `parse_ack`. Any that still fails translation doesn't count.

**Design:** this is a `SPEC-CHANGE` to 8b's own `cost.rs`, needing a ruling. 8a's files stay frozen.
- Summaries gain return facts, `RetFact::ConsumedGe1(field path)`. They are certified by `facts_hold` at every `Return` block on the returned tuple's field.
- A new atom, `Ret(local, field path)`, is valid until the next write to that local.
- The recognizer gains "progress loops": `off < len` at the header, and `off = off + c` with `c >= 1` from a callee `RetFact`. The potential is `Gap(Len(b), Val(off, Usize))`.
- Targets this would flip: `parse_settings`, `decode_lines(_bounded)`, `parse_payload`, `parse_ack` (its loop also needs off-progress, not count).

**Tasks if go:** the same cycle as Tasks 2–7 (spec+theorem → abstract effect → validator → inference → fixtures → rerun), each with its own mutations, as one task per layer. They need their own short plan, with Files and interfaces, before dispatch. Exit: coverage re-reported.

---

## Exit criteria (Phase 8b)

- `theorem_cost` verifies at `--rlimit 4` with its statement equal to the amended spec's, and the Task 2 mutations each fail on a named lemma.
- `check_cert ==> cert_for` and `analyze`'s ensures verify. The Task 4 tamper tests and the Task 5 dropped-caller test pass.
- `ct-check.sh` prints:
  - `fixtures 58/58`;
  - `selftest 15/15`;
  - `selftest parsers K/K`;
  - `crypto ok (84 fns, 10 roots, 10 declassify)`;
  - `negative control rejected`;
  - `cost fixtures 11/11`;
  - `cost X/36 bounded`, matching `expected-cost.txt`.

  `verify.sh` ends with `cost X/36, escapes accounted (1)`.
- Crypto's ct-check reports are byte-identical to main's.
- The Task 7 coverage table is in the phase summary, with original, re-baseline and actual, and every `none` explained. X′ = 23/36 was an upper bound; Task 2 recorded the final X′ before Tasks 3+. The original 27/38 pre-registration stands, and the result is reported against both.
- TRUSTED.md has the cost-model row and the Task 1b front-end notes. The design spec carries `X/Y` and the steps-not-time-or-memory line.
- `git diff main -- crates/ctcore/src/{syntax,sem,ct,ct_lemmas,ni,check,infer,sem_sanity}.rs` is empty.
- `phase-8b` is merged into `main`. Task 8 is recorded as done or `not attempted`, with the go/no-go numbers.

## Self-review (done while writing; amended for the preflight rulings)

- **Shared interfaces come from 8a's plan:**
  - `Res` carries steps (8a D8);
  - lengths are kept ≤ `usize::MAX` by 8a's push/extend/to-vec `None` rule;
  - `SliceSubrange` clamps (`len(dst) <= len(r)`);
  - the driver has a manifest with `root`/`intr`/`translate-crate` lines.

  Task 2 Step 1 stops if any of these is missing, so 8b never edits 8a's semantics.
- **Soundness never depends on the inference:**
  - Task 2 is a semantic theorem;
  - Task 4 is a one-directional validator;
  - Task 5 re-validates the final vector.
- **Honesty:**
  - The predictions are pre-registered in the spec, and the 27/38 rows are never edited.
  - The I3 denominator (36) and Task 1b's upper bound are recorded before any proof work, the final X′ before Tasks 3+, and the report compares against all three.
  - The coverage regression gate is in verify.sh.
  - A seeded unbounded loop must come out `none`.
- **Translator changes are bounded:** Task 1b is the only task that touches `translate.rs`. Each mapping is justified by `sem.rs`'s element-agnostic intrinsics or by Drop being `Goto`. Each has a mutation, and crypto's output is byte-identical.
- **Not probed by the planner:**
  - the degree-2 dominance proofs;
  - the counter-increment no-wrap lemma (Task 3 Step 1 is its bounded probe);
  - the coverage cost of Task 3's write rule beyond the `huffman_decode` family (Task 2 Step 4 measures it).
