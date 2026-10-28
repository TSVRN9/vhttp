# Phase 8a: Verified constant-time checker — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove, in Verus, that every function of `crates/crypto` reachable from the manifest's roots is constant time at MIR level (no secret-dependent branch, index, div/rem operand, shift amount or allocation size), relative to explicitly declassified values. Run the proof as a check inside `scripts/verify.sh`.

**Spec:** `docs/superpowers/specs/2026-10-28-phase-8-verified-ct-cost-design.md` (copied from the scratchpad by the controller). Section names below refer to it: §Core language, §Core semantics, §CT typing, §Front end, §Trust boundary, D1–D10.

**Branch:** `phase-8a`, cut from `main`. The escape count on `main` is **4** and stays 4 throughout; 8a adds no escapes.

**Architecture:**
- **`crates/ctcore`** (new, verified, vstd only):
  - core syntax, spec semantics and CT typing;
  - lemmas and `theorem_ct`;
  - the exec checker `check_prog` (`ensures r == ok_prog(..)`);
  - unverified-functionality exec label inference.
- **`tools/ct-driver`** (new, unverified, `rustc_private`): runs as `RUSTC_WORKSPACE_WRAPPER` under `cargo build --release` and translates monomorphic MIR 1:1 to `ctcore::syntax`.
  - It links `ctcore` in-process and writes a text report.
- **`tools/ct-fixtures`** (new, plain Rust): positive and negative controls.
- **`scripts/ct-check.sh`** (new), called by `scripts/verify.sh`.

**Tech Stack:**
- rustc **1.98.1**, pinned by `rust-toolchain.toml` (Task 1), with the `rustc-dev` component.
- Verus 0.2026.10.04.426d8b0 (`~/.local/opt/verus/0.2026.10.04.426d8b0/verus-x86-linux`).
- vstd `=0.0.0-2026-10-04-0306`.
- No new crates.io dependencies anywhere.

## Global Constraints (copy verbatim into every task brief)

- **Escapes.**
  - `crates/ctcore` adds **zero** escapes, and the `verify.sh` count stays **4**.
  - The gate greps every `*.rs` under `crates/`, code *and* comments, for `assume(`, `admit(`, `external_body`, `assume_specification`, `verifier::external`/`verifier(external` and the bare word `axiom`.
  - Never write those strings in `crates/` (write "premise", "hypothesis").
  - Never name a lemma `*assume*` or `*axiom*`.
- **No new dependencies.** `ctcore` depends on vstd only. `ct-driver` depends on the `rustc_*` crates (via `extern crate`) and `ctcore` (path). `ct-fixtures` has no dependencies. Text formats are parsed by hand with `split_whitespace`.
- **Toolchain.**
  - Every command runs under the pinned 1.98.1 from `rust-toolchain.toml` (after Task 1).
  - `export PATH=$HOME/.local/opt/verus/0.2026.10.04.426d8b0/verus-x86-linux:$PATH` for Verus.
  - `RUSTC_BOOTSTRAP=1` appears **only** inside `scripts/ct-check.sh` (driver build and analysis build). It never appears in `verify.sh`'s crate loop, in `cargo build`/`cargo test`, or in docs as a shipping instruction.
- **Verus usage.**
  - Iterate with `cd crates/ctcore && cargo verus verify -- --rlimit 4`, narrowing with `--verify-only-module <m>` / `--verify-function <f>`. `--verify-module` together with `--verify-function` is rejected.
  - **On a fresh target dir, first run without `--rlimit`.** Otherwise `-- --rlimit 4` also applies to vstd, and vstd's `lemma_indistinguishable_quotients` fails (planner probe P1).
  - **`touch` does not force re-verification**; edit the file.
  - **No `#[verifier::rlimit(..)]` attributes and no `by (compute)`/`by (compute_only)` in ctcore.** Split a lemma instead. `#[verifier::spinoff_prover]` is allowed, and is reported with its time.
- **Known Verus gotchas (from the spikes).**
  - **let-else crashes this Verus build** (`rust_to_vir_expr.rs:3842` dump). Use `if let`/`match`.
  - **Loop isolation:** exec fns whose loops need facts from an enclosing `match` take `#[verifier::loop_isolation(false)]`, or restate the facts as invariants.
  - **Early `return false`** in exec checkers needs witness asserts so Z3 refutes the quantified spec: `assert(args@[i] == a)`, `assert(!ok_x(..))`.
  - **Quantifiers over nested indexing** (`p.fns@[f].blocks@[b]`) need a named predicate as trigger, e.g. `ok_block(..)` (probe P2).
  - **Recursion under `forall` over `Seq<Val>` works** with `decreases v` and `#[trigger] s[i]` (probe P1).
- **Proof patterns.**
  - One lemma per statement kind, rvalue kind, terminator kind and intrinsic, plus one dispatcher. The dispatcher uses `decreases fuel, 1nat`; the case lemmas use `decreases fuel, 0nat`.
  - `binop`/`unop`/`cast` are `#[verifier::opaque]`, and no lemma reveals them.
  - The trace algebra lives in `dv_append`/`dv_prefix`, with an explicit `choose` and a `dv_at` trigger.
  - Traces are built `pre + rest`.
  - Guard agreement assertions with `if !diverge(t1, t2)` (spike step 6).
- **Trusted-spec freeze from the end of Task 3.**
  - Frozen items:
    - every spec fn in `sem.rs`;
    - in `ct.rs`: `wf`, `ok_*`, `shape_eq`, `agree`, `plc`, `args_agree`, `out_agree`, `dv_at`, `diverge`;
    - the statement of `theorem_ct`.
  - Any change needs a `SPEC-CHANGE:` paragraph in the task report (what, why, which lemmas re-verified) and a controller ruling before commit.
- **The four checks, every task** (a check that doesn't exist yet is skipped and noted):
  1. `cargo verus verify` in `crates/ctcore` at `-- --rlimit 4`: `0 errors`.
  2. `cargo build && cargo test && cargo build --release` at the workspace root: 0 warnings, all tests pass.
  3. `scripts/verify.sh` prints `verify.sh: all crates verified, duvet ok, escapes accounted (4)` (Task 10 changes this line).
  4. From Task 7: `scripts/ct-check.sh` exits 0 and prints the summary the task names.
- **Evidence run.**
  - `CARGO_TARGET_DIR=/tmp/claude-1000/-home-tavern-Projects-rust-web-server/19d690a3-7cab-4802-bc1f-9aa0173a905e/scratchpad/vt-8a-tN scripts/verify.sh`, and for Task 7 on, `CT_TARGET_DIR=…/scratchpad/ct-8a-tN`. Both paths are absolute.
  - Then `rm -rf` both. The tmpfs is shared and capped at 16 GB.
- **Proof-time budget.**
  - Each report lists the five slowest ctcore functions (`--output-json --time-expanded`) and ctcore's total.
  - No function may exceed 10 s, and ctcore's total must stay under 60 s.
- **Mutations** must fail on a named postcondition, assertion or expected-verdict line, never on rlimit. Revert each one immediately and re-run.
- **Never weaken a test.** Never flip a fixture expectation or edit the negative control so that a run passes. A negative that starts passing is a checker or translator bug; stop and report it.
- **Labels only through attributes:** `#[cfg_attr(ct_check, ct::secret(..))]`, `ct::public(..)`, bare `ct::public`. `// ct:` comments are documentation and are never parsed.
- **No edits outside a task's Files list.** In particular: no `spec fn`, `requires`/`ensures` or proof edits in `crates/{wire,h3,quic,tls,crypto}`. Task 9 adds attributes, `ct.rs`, one `declassify` call and the `ct_negative` module only.
- **Plan code is signatures only.** Bodies are the implementer's.

## Review Focus

1. **The theorem is the spec's.**
   - `theorem_ct`'s `requires`/`ensures` match the spec text.
   - `ok_prog` includes `wf`.
   - `check_prog` ensures `r == ok_prog(..)` in both directions.
   - `check_program` returns `Ok` only through `check_prog(..) == true`.
2. **The trusted translator is 1:1 and fail-closed.**
   - Each match arm in `translate.rs` corresponds to one row of the spec's mapping table.
   - There is no catch-all arm that produces core code.
   - Every unsupported family has a rejecting fixture.
   - Unresolved callees, unknown attribute names, unlabeled roots and unresolvable root paths are errors.
3. **Non-vacuity at every layer.**
   - The Task 5 proof mutations and the Task 6 exec mutations fail.
   - Every negative fixture is rejected *for its stated reason*.
   - The crypto negative control is rejected.
   - The Task 9 real-code mutations are rejected.
   - The Task 8 selftest catches a translator mutation.
4. **Declassify accounting.** The report's `declassify` lines, the TRUSTED `ct-declassify:` rows and the source-grep count agree. Each row's justification is specific.
5. **Toolchain and profile.**
   - `rust-toolchain.toml` pins exactly 1.98.1.
   - `overflow-checks = false` appears only in per-package release overrides for verified crates.
   - `RUSTC_BOOTSTRAP` appears only in `scripts/ct-check.sh`.
   - The TRUSTED pins paragraph is updated.
6. **Escapes:** 4 before and after; no escape words in ctcore.
7. **Proof cost:** the slowest functions against the budget.

---

### Task 1: Pin rustc 1.98.1 and the shipped release profile

**Files:**
- Create: `rust-toolchain.toml`
- Modify: `Cargo.toml` (root), `TRUSTED.md` (the "Pinned versions" paragraph only), plus any file whose new 1.98.1 warning needs a fix (see Step 5).

**Interfaces (produces):**
- `rust-toolchain.toml`, exactly:
  ```toml
  [toolchain]
  channel = "1.98.1"
  components = ["rustc-dev"]
  ```
- Root `Cargo.toml` gains:
  ```toml
  [profile.release]
  overflow-checks = true
  [profile.release.package.wire]
  overflow-checks = false
  [profile.release.package.h3]
  overflow-checks = false
  [profile.release.package.quic]
  overflow-checks = false
  [profile.release.package.tls]
  overflow-checks = false
  [profile.release.package.crypto]
  overflow-checks = false
  ```
  Task 2 adds `ctcore`. Each block carries one comment line: `# verified: Verus proves exec arithmetic does not overflow` for the overrides, `# unverified code keeps the checks` for the base.
- In TRUSTED.md, replace the sentence "The shipped artifact is built by plain `cargo build` on the user's default stable rustc (unpinned; currently 1.92.0) … No `rust-toolchain.toml` is needed." with: "The shipped artifact is built by `cargo build --release` with rustc 1.98.1, pinned by `rust-toolchain.toml`, which is Verus's own toolchain, so the compiler that checks the proofs is the compiler that builds the binary. The release profile keeps overflow checks on, except in the verified crates (per-package overrides in `Cargo.toml`), where Verus proves the absence of overflow. `verus!` erasure is done by `verus_builtin_macros` (version from `Cargo.lock`, currently 0.0.0-2026-09-20-0158)."

- [ ] **Step 1: Baseline on 1.92.** Before any edit, run `cargo build`, `cargo test` and `scripts/verify.sh`. Record:
  - the warning count;
  - per-crate test counts (`cargo test 2>&1 | grep 'test result'`);
  - the verify.sh line;
  - verify.sh's wall time.
- [ ] **Step 2: Install the component.** `rustup component add rustc-dev --toolchain 1.98.1`, then confirm with `ls "$(rustc +1.98.1 --print sysroot)/lib/rustlib/x86_64-unknown-linux-gnu/lib" | grep -c 'librustc_public'`, which must be ≥ 1.
  - If the download fails (offline), stop and report. The spike's tarball overlay is a fallback only on a controller ruling.
- [ ] **Step 3: Add `rust-toolchain.toml`.**
  - `rustc --version` in the repo root and in `crates/crypto` prints `rustc 1.98.1`.
  - Then run `cargo verus verify` in `crates/wire`, the cheapest crate, and record its `verification results` line. It must equal the Step 1 numbers for wire. If cargo-verus errors on the toolchain file, stop and report the message.
- [ ] **Step 4: Add the profile blocks.** `cargo build --release` succeeds.
- [ ] **Step 5: New lints.**
  - `cargo build`, `cargo test` and `cargo build --release` must show 0 warnings.
  - **Allowed fixes:**
    - mechanical edits in unverified code (`tests/`, `shim.rs`, `#[cfg(test)]` modules);
    - an item-level `#[allow(<lint>)] // 1.98.1 lint; <reason>` inside `verus!` when the fix would touch verified exec code.
  - **Not allowed:** any edit to a spec, proof, `requires`/`ensures`, or a verified exec body.
  - **Stop and escalate** with the full warning list if there are more than 20 new warnings or any one needs a disallowed edit.
- [ ] **Step 6: Equal results.**
  - Test counts equal Step 1's.
  - `scripts/verify.sh` prints `… escapes accounted (4)`.
  - Report verify.sh's wall time against Step 1's.
- [ ] **Step 7: Run the four checks and the evidence run.** `rm -rf` the target dir.
- [ ] **Step 8: Commit:** `build: pin rustc 1.98.1 (= Verus toolchain) and the release profile; overflow checks off only in verified crates`

---

### Task 2: `ctcore` crate, core syntax, spec semantics and semantics sanity lemmas

**Files:**
- Create: `crates/ctcore/Cargo.toml`, `crates/ctcore/src/lib.rs`, `crates/ctcore/src/syntax.rs`, `crates/ctcore/src/sem.rs`, `crates/ctcore/src/sem_sanity.rs`
- Modify: root `Cargo.toml` (`[profile.release.package.ctcore] overflow-checks = false`); `docs/superpowers/specs/2026-10-28-phase-8-verified-ct-cost-design.md` (the intrinsic enum and table only, Step 0)

**Consumes:** Task 1's toolchain.

**Interfaces (produces):**
- **`Cargo.toml`** follows `crates/crypto/Cargo.toml`'s shape:
  - `vstd = "=0.0.0-2026-10-04-0306"`;
  - `[package.metadata.verus] verify = true`;
  - `[lints.rust] unexpected_cfgs = { level = "warn", check-cfg = ['cfg(verus_only)'] }`.
- **`syntax.rs`:** the spec's §Core language block, verbatim (all `pub`, inside `verus!`). Add `impl View`-free plain enums; the spec reads Vec fields through `@`.
- **`sem.rs`** (all `pub open spec fn` unless marked), implementing the spec's §Core semantics:
  - **Types:** `Val`, `Loc { root: Root, path: Seq<PE> }`, `Root { Local(nat), Slot(nat) }`, `PE { Field(nat), Index(nat), Variant(nat) }`, `Frame { locals: Seq<Val>, slots: Seq<Val> }`, `Event`, `pub type Res = Option<(Frame, Seq<Event>, nat)>`.
  - **Opaque arithmetic:** `#[verifier::opaque] binop(op: BinOp, ty: IntTy, a: u128, b: u128) -> u128`, `#[verifier::opaque] unop(op: UnOp, ty: IntTy, a: u128) -> u128`, `#[verifier::opaque] cast(from: IntTy, to: IntTy, a: u128) -> u128`, plus `bits(ty: IntTy) -> nat` (Usize/Isize = 64, Bool = 1).
  - **Value navigation:** `get(v: Val, e: PE) -> Val` and `put(v: Val, e: PE, w: Val) -> Val`, total per the spec's totality rules; `read_at(v: Val, path: Seq<PE>) -> Val` and `write_at(v: Val, path: Seq<PE>, w: Val) -> Val`, both `decreases path.len()`.
  - **Frames and places:**
    - `read_loc(fr: Frame, l: Loc) -> Val`, `write_loc(fr: Frame, l: Loc, w: Val) -> Frame`;
    - `read_place(fr: Frame, pl: Place) -> (Val, Seq<Event>)`, `place_loc(fr: Frame, pl: Place) -> Option<(Loc, Seq<Event>)>`;
    - `const_val(c: ConstVal) -> Val`, `eval_op(fr: Frame, op: Operand) -> (Val, Seq<Event>)`, `eval_rv(fr: Frame, rv: Rvalue) -> (Val, Seq<Event>)`.
  - **Statements:** `exec_stmt(fr: Frame, s: Stmt) -> (Frame, Seq<Event>)`; `exec_stmts(ss: Seq<Stmt>, k: nat, fr: Frame) -> (Frame, Seq<Event>)` with `decreases ss.len() - k when k <= ss.len()`.
  - **Intrinsics:** `exec_intr(k: Intrinsic, fr: Frame, args: Seq<Operand>, dst: Place) -> Option<(Frame, Seq<Event>, nat)>`, which gives the extra steps beyond the terminator's 1; `intr_cost(k: Intrinsic, fr: Frame, args: Seq<Operand>) -> nat`.
  - **Calls:**
    - `call_enter(p: Program, g: nat, fr: Frame, args: Seq<Operand>) -> (Frame, Seq<Option<Loc>>, Seq<Event>)`: the callee frame, the write-back locs per parameter, and the arg events;
    - `call_leave(fr: Frame, callee: Frame, wb: Seq<Option<Loc>>, dst: Place) -> (Frame, Seq<Event>)`.
  - **Runs:**
    - `run_from(p: Program, f: nat, b: nat, fr: Frame, fuel: nat) -> Res` with `decreases fuel`;
    - `run_fn(p: Program, f: nat, fr: Frame, fuel: nat) -> Res`;
    - `init_entry(p: Program, f: nat, args: Seq<Val>, slots: Seq<Val>) -> Frame`;
    - `len_ok(v: Val) -> bool`, true when every `Arr` inside has length ≤ `usize::MAX`; it is used by 8b.
- **`sem_sanity.rs`** holds proof fns that pin the semantics on tiny literal programs, using `reveal_with_fuel(run_from, k)` only. Each ensures one concrete `run_fn(..) == Some((…))` or `is None`:
  - `sanity_switch_matching_target`
  - `sanity_switch_otherwise`
  - `sanity_assert_failure_is_none`
  - `sanity_index_emits_idx`
  - `sanity_div_emits_operands`
  - `sanity_shift_emits_amount`
  - `sanity_steps_count`: 2 blocks, 3 statements, so 5 steps
  - `sanity_mut_arg_written_back`: the callee writes `*m = 7` and the caller sees 7
  - `sanity_shr_snapshot`: `Len` through `Deref` of a `Shr(Arr)`
  - `sanity_push_appends`
  - `sanity_declassify_event`
  - `sanity_fuel_zero_is_none`
  - `sanity_subrange_clamps`: `hi > len` gives `len(dst) <= len(r)`
  - `sanity_push_overflow_is_none`: a push onto an `Arr` of length `usize::MAX` gives `None`. 8b relies on both of these.

- [ ] **Step 0: Callee census, which fixes the intrinsic set before any proof.**
  - Build the spike driver: `RUSTC_BOOTSTRAP=1 rustc --edition 2021 -O /tmp/claude-1000/-home-tavern-Projects-rust-web-server/19d690a3-7cab-4802-bc1f-9aa0173a905e/scratchpad/spike-ct-front/c-driver/main.rs -o <scratch>/ct-census -C link-args=-Wl,-rpath,$(rustc --print sysroot)/lib`.
  - Run it: `RUSTC_WORKSPACE_WRAPPER=<scratch>/ct-census CT_FNS= CT_OUT=<scratch>/census RUSTC_BOOTSTRAP=1 CARGO_TARGET_DIR=<scratch>/t2-census cargo build --release -p crypto 2> <scratch>/census.log`. An empty `CT_FNS` selects every fn.
  - `grep '  callee ' <scratch>/census.log | sort -u` lists every callee. Map each one that isn't a crypto fn to one of the spec's intrinsics.
  - Add an intrinsic for each callee with no fit, for example `<[T; N]>::as_slice`, `copy_from_slice` or `vec!`'s `from_elem`. Give each one a row in the spec's intrinsic table: effect, events, steps, and the typing rule for Task 3.
  - Paste the census and the final enum into the report, then `rm -rf` the census target dir.
  - **After this step the `Intrinsic` enum is closed.** Adding one later is a SPEC-CHANGE.
- [ ] **Step 1: Probe (≤ 30 min).**
  - Create the crate with `syntax.rs` and a stub `sem.rs` containing `Val`, `get`/`put`/`read_at`/`write_at`.
  - Verify: no let-else; `p.fns@[f as int].blocks@[b as int]` reads in spec; recursion through `Seq<Val>` (P1).
  - On a fresh target, first run without `--rlimit`, then with it.
- [ ] **Step 2: Write `sem.rs` in the spec's order.**
  - Write Event order inside statements exactly as the spec states: rvalue events, then place events.
  - For a call: the arg events, then the callee trace, then the dst-place events.
- [ ] **Step 3: Write the sanity lemmas** and make them verify.
- [ ] **Step 4: Mutations**, each failing a named sanity lemma:
  - `Switch` takes `otherwise` first;
  - `Assert` ignores `expected`;
  - `Index` omits `Idx`;
  - `call_leave` skips write-back;
  - the steps of a block omit the terminator.
- [ ] **Step 5: Run the four checks and the evidence run.** verify.sh now also verifies ctcore and still prints `(4)`. Report the five slowest functions. `rm -rf` the target dir.
- [ ] **Step 6: Commit:** `feat(ctcore): core language and leakage/step semantics (spec) with sanity lemmas`

---

### Task 3: CT typing, well-formedness, agreement and the value/place lemmas

**Files:**
- Create: `crates/ctcore/src/ct.rs` (spec part), `crates/ctcore/src/ct_lemmas.rs`

**Consumes:** `sem.rs` (Task 2).

**Interfaces (produces):** all `pub open spec fn`, implementing the spec's §CT typing table exactly.
- **Labels:** `pub struct FnLab { pub locals: Vec<bool> }`; `lab(l: FnLab, x: nat) -> bool`; `slot_lab(l: FnLab, j: nat) -> bool` (= `l.locals@[1 + j]`).
- **Well-formedness:** `ty_has_mut(t: Ty) -> bool` (`decreases t`); `wf_body(p: Program, f: nat) -> bool`; `wf(p: Program) -> bool`.
- **Per-construct typing:**
  - `sec_op(b: Body, l: FnLab, op: Operand) -> bool`;
  - `ok_place(b: Body, l: FnLab, pl: Place) -> bool`: index locals public and in range;
  - `sec_rv(b, l, rv) -> bool`, `ok_rv(b, l, rv) -> bool`, `ok_stmt(b, l, s) -> bool`;
  - `ok_intr(b: Body, l: FnLab, k: Intrinsic, args: Seq<Operand>, dst: Place) -> bool`;
  - `ok_term(p: Program, ls: Seq<FnLab>, f: nat, t: Term) -> bool`.
- **Per-program typing:** `ok_block(p, ls, f, blk: Block) -> bool`, the trigger predicate; `ok_body(p, ls, f) -> bool`; `ok_prog(p: Program, ls: Seq<FnLab>) -> bool` (= `wf(p) && ls.len() == p.fns@.len() && forall f. ok_body`).
- **Agreement:**
  - `shape_eq(a: Val, b: Val) -> bool` (`decreases a`);
  - `agree(p, ls, f, fr1: Frame, fr2: Frame) -> bool`;
  - `plc(p, ls, f, fr: Frame) -> bool`: every top-level `Mut(loc)` in local x has a root whose label equals `lab(x)`;
  - `args_agree(p, ls, f, a1, a2, s1, s2) -> bool`;
  - `out_agree(p, ls, f, fr1, fr2) -> bool`: local 0 and the slots.
- **Trace relations:** `dv_at(t1, t2, i: int) -> bool` and `diverge(t1, t2) -> bool`, as in the spike.
- **Lemmas** (`ct_lemmas.rs`, `pub proof fn`):
  - `lemma_shape_refl(a)`, `lemma_shape_sym(a, b)`, `lemma_shape_trans(a, b, c)`;
  - `lemma_read_at_shape(v1, v2, path)` and `lemma_write_at_shape(v1, v2, path, w1, w2)` (P1 has the latter's pattern);
  - `lemma_read_place_agree(p, ls, f, fr1, fr2, pl)`:
    - requires `agree`, `plc` and `ok_place`;
    - ensures equal events, equal values when `!lab(pl.local)`, and `shape_eq` otherwise;
  - `lemma_place_loc_agree(p, ls, f, fr1, fr2, pl)`: both `None`, or both `Some` with the same `Loc` and the same events;
  - `lemma_eval_op_agree(..)`, `lemma_eval_rv_agree(..)`: equal events; values equal when `!sec_rv`, `shape_eq` always;
  - `lemma_write_loc_agree(p, ls, f, fr1, fr2, l: Loc, w1, w2)`: requires the root label ⊒ the value relation; preserves `agree`;
  - `lemma_plc_stmt(p, ls, f, fr, s)`: `ok_stmt` and `plc` before imply `plc` after `exec_stmt`.

- [ ] **Step 1: Probe (≤ 45 min).**
  - Write `shape_eq` and `lemma_read_place_agree` for a place with one `Deref` of a `Mut` local, then one `Index`.
  - Stop rule: if it doesn't verify at rlimit 4 after one split into helper lemmas, report the failing query and stop for a ruling.
- [ ] **Step 2: Write the spec fns**, transcribing the spec's rule table row by row. Put one `// rule: <table row>` comment per arm.
- [ ] **Step 3: Write the lemmas**, in the order listed.
- [ ] **Step 4: Mutations**, each failing a named lemma:
  - `ok_place` without "index local public" (`lemma_read_place_agree`);
  - `shape_eq` on `Arr` without the length equality (`lemma_read_at_shape`, via `Len`);
  - `RefMut` rule `⊑` instead of `==` (`lemma_plc_stmt`).
- [ ] **Step 5: Run the four checks and the evidence run.** The spec freeze starts after this commit.
- [ ] **Step 6: Commit:** `feat(ctcore): CT typing, wf, shape agreement and place/value lemmas`

---

### Task 4: NI for statements, intra-function terminators and intrinsics

**Files:**
- Create: `crates/ctcore/src/ni.rs`

**Consumes:** `ct.rs`/`ct_lemmas.rs` (Task 3, frozen).

**Interfaces (produces):**
- `pub open spec fn no_fn_calls(p: Program) -> bool`: a temporary premise for this task only; Task 5 deletes it.
- `pub open spec fn ni_ok(p, ls, f, r1: Res, r2: Res) -> bool`: `(t1 == t2 && n1 == n2 && agree(p, ls, f, fin1, fin2) && plc(.., fin1) && plc(.., fin2)) || diverge(t1, t2)`.
- **Statements:**
  - `proof fn ni_stmt(p, ls, f, s: Stmt, fr1, fr2)`: requires `ok_stmt`, `agree`, `plc` on both; ensures equal events, `agree` and `plc` after.
  - `proof fn ni_stmts(p, ls, f, ss: Seq<Stmt>, k: nat, fr1, fr2)` (`decreases ss.len() - k`).
- **Intrinsics:** `proof fn ni_intr(p, ls, f, k: Intrinsic, args, dst, fr1, fr2)`: both `None`, or both `Some` with equal steps and `(equal events && agree && plc)`, or `diverge` (`Declassify` only).
- **Trace algebra:** `proof fn dv_append(t1, t2, x, y)` and `proof fn dv_prefix(pre, t1, t2)`, statements as in the spike.
- **Terminator cases** (each `decreases fuel, 0nat`; requires `ni_pre(p, ls, f, b, fr1, fr2, fuel)` and `no_fn_calls(p)`; ensures `ni_ok(..)`):
  - `proof fn ni_goto(..)`, `ni_switch(..)`, `ni_assert(..)`, `ni_call_intr(..)`, `ni_return(..)`.
- **Dispatcher:** `pub proof fn ni_local(p, ls, f, b: nat, fr1, fr2, fuel)`, `decreases fuel, 1nat`. It requires `ok_prog(p, ls)`, `no_fn_calls(p)`, `f < len`, `b < blocks len`, `agree`, `plc` on both, and both runs `Some`. It ensures `ni_ok(p, ls, f, run_from(..fr1..), run_from(..fr2..))`.
  - `pub open spec fn ni_pre(..)` bundles those premises.

- [ ] **Step 1:** Write `ni_stmt`/`ni_stmts` first, then the intrinsic cases one by one, verifying each before the next.
- [ ] **Step 2:** Write the terminator lemmas and `ni_local`.
- [ ] **Step 3: Run the four checks and the evidence run.** Report per-lemma times. Expected: each under 1 s (the spike's while case was 75k units).
- [ ] **Step 4: Commit:** `feat(ctcore): lockstep non-interference for statements, intrinsics and intra-function control flow`

---

### Task 5: NI across calls, `theorem_ct`, and the proof-mutation suite

**Files:**
- Modify: `crates/ctcore/src/ni.rs`

**Consumes:** Task 4.

**Interfaces (produces):**
- `proof fn lemma_call_enter_agree(p, ls, f, g, args, fr1, fr2)`: under the call-site rule of `ok_term`, the two callee frames agree and satisfy `plc` under `ls[g]`, and the write-back locs are equal.
- `proof fn lemma_call_leave_agree(..)`: callee `out_agree` plus caller `agree` before imply caller `agree`/`plc` after the write-back and the dst assignment.
- `proof fn ni_call_fn(..)`, `decreases fuel, 0nat`: it applies `ni` to the callee at `fuel - 1` and handles divergence with `dv_prefix`/`dv_append`. Guard agreement assertions with `if !diverge(..)`.
- `pub proof fn ni(p, ls, f, b, fr1, fr2, fuel)`, `decreases fuel, 1nat`: the general dispatcher. Delete `ni_local` and `no_fn_calls`, or make `ni_local` a one-line wrapper and delete the premise.
- `pub proof fn theorem_ct(..)`: exactly the spec's statement. Proof: build the entry frames, establish `agree`/`plc` from `args_agree`, call `ni`, and weaken `agree` to `out_agree`.

- [ ] **Step 1:** Write `ni_call_fn` and the general `ni`.
- [ ] **Step 2:** Prove `theorem_ct`. Diff its signature against the spec text and paste the diff (empty) in the report.
- [ ] **Step 3: Proof mutations.** Each must make a *named* lemma fail; record which. Revert each one.
  - **M1:** `ok_term` allows a secret `Switch` condition.
  - **M2:** it allows a secret `Assert` condition.
  - **M3:** `ok_place` allows a secret `Index` local.
  - **M4a:** a secret Div divisor. **M4b:** a secret Rem dividend.
  - **M5:** a secret shift amount.
  - **M6:** `exec_intr(Declassify)` omits the `Declass` event.
  - **M7:** a secret arg into a public param.
  - **M8:** a secret callee return into a public dst.
  - **M9:** `RefMut` with `lab(dst) ⊑ wr(pl)` instead of `==`.
  - **M10:** `args_agree` drops `shape_eq` for secret params (so `Len` of a secret slice may differ).
  - **M11:** `VecWithCapacity` with a secret n.
- [ ] **Step 4: Run the four checks and the evidence run.** Report ctcore's slowest five and its total.
- [ ] **Step 5: Commit:** `feat(ctcore): theorem_ct — constant-time non-interference with calls, relative to declassified values`

---

### Task 6: Exec checker, label inference and the `check_program` API

**Files:**
- Create: `crates/ctcore/src/check.rs`, `crates/ctcore/src/infer.rs`, `crates/ctcore/tests/check.rs`
- Modify: `crates/ctcore/src/lib.rs`

**Consumes:** the frozen `ct.rs` spec.

**Interfaces (produces):**
- **`check.rs`**, every fn `pub`, each with `ensures r == <spec>`:
  - `check_ty_has_mut(t: &Ty) -> (r: bool)`, `check_wf(p: &Program) -> (r: bool)`;
  - `check_place(b: &Body, l: &FnLab, pl: &Place) -> (r: bool)`;
  - `sec_operand(b: &Body, l: &FnLab, op: &Operand) -> (r: bool)`;
  - `check_rv(b, l, rv) -> (r: (bool, bool))` (ok, secret), `check_stmt(b, l, s) -> (r: bool)`;
  - `check_intr(b, l, k, args: &Vec<Operand>, dst: &Place) -> (r: bool)`;
  - `check_term(p: &Program, ls: &Vec<FnLab>, f: usize, t: &Term) -> (r: bool)`, `check_block(p, ls, f, blk) -> (r: bool)`;
  - `check_body(p, ls, f) -> (r: bool)`, `check_prog(p: &Program, ls: &Vec<FnLab>) -> (r: bool)`, with `ensures r == ok_prog(*p, ls@)`.
  - Use `#[verifier::loop_isolation(false)]` where loops sit inside match arms.
- **`infer.rs`** (exec; no functional ensures beyond lengths):
  - `pub fn infer_labels(p: &Program, decl: &Vec<Option<Vec<bool>>>) -> (r: Result<Vec<FnLab>, usize>)` ensures `r is Ok ==> r->Ok_0@.len() == p.fns@.len()`.
  - It processes callees before callers. Recursion gives `Err(f)`.
  - Per fn it computes the least fixpoint of the flow constraints, starting from declared param labels (`None` = all public). It runs at most `nlocals + 1` passes (`decreases`), and gives `Err` if the fixpoint fails.
  - Return label = `locals[0]`.
- **`lib.rs`:**
  - `pub enum RejectKind { SecretSwitch, SecretAssert, SecretIndex, SecretDivOperand, SecretShift, SecretAlloc, SecretRange, ArgLabel(usize), RetLabel, MutLabel, NotWf, Recursion, InferFailed }`;
  - `pub struct Reject { pub f: usize, pub block: usize, pub stmt: Option<usize>, pub kind: RejectKind }`;
  - `pub fn explain(p: &Program, ls: &Vec<FnLab>) -> Vec<Reject>` (no functional ensures);
  - `pub fn check_program(p: &Program, decl: &Vec<Option<Vec<bool>>>) -> (r: Result<Vec<FnLab>, Vec<Reject>>) ensures r is Ok ==> ok_prog(*p, r->Ok_0@)`;
  - re-export `syntax::*`.
- **`tests/check.rs`** (`cargo test`), hand-built core programs, one `#[test]` each:
  - `accepts_masked_select`
  - `rejects_secret_switch`
  - `rejects_secret_assert`
  - `rejects_short_circuit_on_secret`: MIR-shaped, a switch on the lhs
  - `rejects_secret_index`
  - `rejects_secret_divisor`
  - `rejects_secret_dividend`
  - `rejects_secret_shift_amount`
  - `accepts_constant_shift_of_secret`
  - `accepts_len_of_secret_slice`
  - `rejects_secret_with_capacity`
  - `rejects_secret_arg_to_public_param`
  - `rejects_secret_ret_to_public_dst`
  - `rejects_mut_label_mismatch`
  - `rejects_mut_in_tuple_wf`
  - `accepts_declassified_branch`
  - `inference_propagates_callee_secret_ret`
  - `unlabeled_callee_is_all_public`
  - `rejects_recursion`
  - Each reject test also asserts that the expected `RejectKind` appears in `explain`.

- [ ] **Step 1:** Write `check.rs` bottom-up, verifying each fn at rlimit 4.
- [ ] **Step 2:** Write `infer.rs`, `explain` and `check_program`.
- [ ] **Step 3:** Write `tests/check.rs`. All pass.
- [ ] **Step 4: Exec mutations.** Each must fail verification of the named fn's `ensures`:
  - `check_term` skips the `Switch` check;
  - `check_place` skips the index check;
  - `check_intr` skips `VecWithCapacity`'s public-length check.
- [ ] **Step 5: Consistent mutation.** Relax both `ok_term` (Switch) and `check_term` together. `check_prog` verifies, `rejects_secret_switch` fails, **and** `theorem_ct`/`ni_switch` fails. Record all three.
- [ ] **Step 6: Run the four checks and the evidence run.**
- [ ] **Step 7: Commit:** `feat(ctcore): verified exec checker (check_prog == ok_prog), label inference, check_program API`

---

### Task 7: The MIR driver, census mode, fixtures and `ct-check.sh`

**Files:**
- Create:
  - `tools/ct-driver/Cargo.toml` (`[workspace]`, `ctcore = { path = "../../crates/ctcore" }`);
  - `tools/ct-driver/src/{main.rs, translate.rs, manifest.rs}`, `tools/ct-driver/manifest.txt`;
  - `tools/ct-fixtures/Cargo.toml` (`[workspace]`), `tools/ct-fixtures/src/lib.rs`, `tools/ct-fixtures/manifest.txt`, `tools/ct-fixtures/expected.txt`;
  - `scripts/ct-check.sh`.
- Modify: root `.gitignore`, if target dirs under `tools/` need it.

**Consumes:** `ctcore::check_program`, `ctcore::syntax::*`, `ctcore::explain` (Task 6).

**Interfaces (produces):**
- **The driver.** `tools/ct-driver` builds with `RUSTC_BOOTSTRAP=1 cargo build --release --manifest-path tools/ct-driver/Cargo.toml` (`#![feature(rustc_private)]`; `extern crate rustc_driver, rustc_interface, rustc_middle, rustc_public`, as in the spike's `C-driver-main.rs`). Its binary is `ct-driver`.
- **Environment:**
  - `CT_CRATES`: comma-separated crate names to analyse. Others pass through to rustc unchanged.
  - `CT_MANIFEST`: colon-separated manifest paths.
  - `CT_OUT`: the report dir.
  - `CT_MODE`: `check` (default) or `census`; Task 8 adds `selftest`.
- **Flags** appended for analysed crates: `-Zinline-mir=no`, `--cfg ct_check`, `-Zcrate-attr=feature(register_tool)`, `-Zcrate-attr=register_tool(ct)`.
- **`manifest.rs`:**
  - `pub struct Manifest { pub roots: Vec<String>, pub intr: Vec<(String, ctcore::Intrinsic)>, pub labels: Vec<(String, Vec<String>, Vec<String>)>, pub translate_crates: Vec<String>, pub excludes: Vec<(String, String)> }`;
  - `pub fn load(paths: &[std::path::PathBuf]) -> Result<Manifest, String>`: unknown kinds and malformed lines are errors that name the file and line.
- **`translate.rs`:**
  - `pub struct FnInfo { pub path: String, pub is_root: bool, pub decl: Option<Vec<bool>>, pub param_names: Vec<String>, pub block_spans: Vec<String>, pub declassify_sites: Vec<String> }`;
  - `pub enum TrErr { Unsupported { path: String, what: String, span: String }, Unresolved { path: String, callee: String, span: String }, Attr { path: String, msg: String }, Root { path: String, msg: String } }`;
  - `pub fn translate_root(m: &Manifest, root: &str) -> Result<(ctcore::Program, Vec<FnInfo>), Vec<TrErr>>`, called inside `rustc_public::run!` once per root of the crate being compiled; roots with another crate prefix are skipped.
  - **Each root's closure is its own `Program`** and gets its own `check_program` call and its own verdict line (spec §Front end, per-root programs).
  - It works from the root (`all_local_items()` filtered by the manifest's root paths, as `Instance`s), follows `Call`s via `Instance::resolve`, and applies the spec's lookup order. It translates by the spec's mapping table, **one match arm per row**; everything else is `TrErr::Unsupported`.
  - Param names come from `var_debug_info` for argument locals.
- **Report** (`$CT_OUT/report-<crate>.txt`): the spec's §Front end line formats. For translation errors, `reject <path> <TrErr text>`.
  - Census mode writes `census-<crate>.txt`: one line per reached callee, `callee <def-path> crate=<name> body=<yes|no>`, sorted and unique.
- **`tools/ct-fixtures/src/lib.rs`:** plain Rust, no `verus!`. It defines `pub fn declassify<T>(x: T) -> T { x }`, and its manifest maps it: `intr ct_fixtures::declassify Declassify`.
  - **Positive controls** (verdict `ok`):
    - `pos_masked_select`
    - `pos_public_loop_over_secret_array`
    - `pos_len_of_secret_slice`
    - `pos_declassified_branch`
    - `pos_call_chain`
    - `pos_mut_param_update`
    - `pos_u128_mul_mask`
  - **Negative controls** (verdict `reject <kind>`):
    - `neg_secret_if` (SecretSwitch)
    - `neg_secret_match` (SecretSwitch)
    - `neg_secret_and_and` (SecretSwitch)
    - `neg_secret_early_return` (SecretSwitch)
    - `neg_secret_while` (SecretSwitch)
    - `neg_secret_index` (SecretIndex)
    - `neg_secret_div` (SecretDivOperand)
    - `neg_secret_rem_u128` (SecretDivOperand)
    - `neg_secret_shift` (SecretShift)
    - `neg_secret_to_unlabeled_helper` (ArgLabel)
    - `neg_unresolved_callee`: calls `u64::count_ones`, which has no manifest mapping (Unresolved)
    - `neg_unknown_param_name` (Attr)
    - `neg_root_without_label` (Root)
    - `neg_float` (Unsupported)
    - `neg_raw_pointer` (Unsupported)
  - Every fixture is a root in `tools/ct-fixtures/manifest.txt`.
- **`tools/ct-fixtures/expected.txt`:** one line per fixture, `ok <path>` or `reject <path> <Kind>`, sorted.
- **`scripts/ct-check.sh`** (POSIX sh, `set -eu`, `CT_TARGET_DIR` defaulting to `$root/target/ct`):
  - build the driver;
  - build the fixtures with `RUSTC_WORKSPACE_WRAPPER=<driver> RUSTC_BOOTSTRAP=1 CT_CRATES=ct_fixtures …`;
  - normalize the report to `ok|reject <path> <Kind>` and `diff` it against `expected.txt`;
  - fail if any manifest `root` got no verdict line;
  - print `ct-check: fixtures N/N`.
  - Task 9 adds the crypto runs.

- [ ] **Step 1: Driver skeleton.** Pass-through wrapper plus census mode. Run census over crypto with the 7 spec roots in `tools/ct-driver/manifest.txt`, and paste `census-crypto.txt` into the report.
- [ ] **Step 2: Write the crypto `intr` lines from the census.** Only the paths the census printed, each mapped to an intrinsic in Task 2's closed enum, plus `intr crypto::ct::declassify Declassify`.
  - A census callee that fits no existing intrinsic is a **SPEC-CHANGE escalation**. Never map it to a near-miss intrinsic.
  - Callees with translatable bodies need no line.
- [ ] **Step 3: Write `translate.rs`** and the fixtures, then the remaining controls. Iterate until the fixtures diff is empty.
- [ ] **Step 4: Translator mutations**, each turning a fixtures diff non-empty (record which line):
  - `SwitchInt` translated as `Goto(otherwise)`;
  - `Index` projection translated as `ConstIndex(0)`;
  - `Assert` dropped;
  - attribute names mapped by position instead of by name.
- [ ] **Step 5: Run the four checks** (ct-check prints `ct-check: fixtures 22/22`) **and the evidence run.** `rm -rf` `$CT_TARGET_DIR`.
- [ ] **Step 6: Commit:** `feat(ct-driver): rustc_public MIR→core translator, manifest, report, fixtures and ct-check.sh`

---

### Task 8: Translation validation by vectors (interpreter selftest)

**Files:**
- Create: `tools/ct-driver/src/interp.rs`, `tools/ct-driver/selftest.txt`
- Modify: `tools/ct-driver/src/main.rs` (the `selftest` mode), `scripts/ct-check.sh` (run selftest)

**Consumes:** Task 7's translator.

**Interfaces (produces):**
- **`interp.rs`** (unverified, test-only, not in the TCB):
  - `pub enum IVal { Int(u128), Unit, Tup(Vec<IVal>), Adt(usize, Vec<IVal>), Arr(Vec<IVal>), Shr(Box<IVal>), Mut(usize, Vec<IPe>) }`;
  - `pub fn run(p: &ctcore::Program, f: usize, args: Vec<IVal>, fuel: u64) -> Option<(IVal, u64)>`.
  - It mirrors `sem.rs` construct for construct, with a comment naming the spec fn each arm mirrors. `binop`/`cast` are Rust's own wrapping ops per `IntTy`.
- **`selftest.txt`** format: `<def-path> <arg>... => <expected>`. Args: hex bytes are a slice `Shr(Arr(..))`; `0x…u128` is an Int. The vectors:
  - `crypto::aes::aes128_encrypt_block` FIPS 197 C.1: key `000102…0f`, block `00112233…ff` ⇒ `69c4e0d86a7b0430d8cdb78070b4c55a`;
  - `crypto::sha256::sha256` `"abc"` ⇒ `ba7816bf…15ad`;
  - `crypto::hmac::hmac_sha256` RFC 4231 TC1 ⇒ `b0344c61…cff7`;
  - `crypto::gcm::aes128_gcm_seal` GCM TC2 (key 0¹⁶, nonce 0¹², aad ∅, pt 0¹⁶) ⇒ `0388dace60b6a392f328c2b971b2fe78ab6e47d42cec13bdf53a67b21257bddf`;
  - `crypto::gcm::gf128_mul_exec` `C·H` from GCM TC2, with the expected value computed by a `python3 -I` SP 800-38D Algorithm 1 script. Check the script first: it must reproduce TC2's GHASH `f38cbb1a…f885`, and the script goes in the report.
- **`ct-check.sh`** prints `ct-check: selftest 5/5`.

- [ ] **Step 1:** Write the interpreter and the selftest mode. All 5 vectors pass.
- [ ] **Step 2: Mutations**, each failing a named vector:
  - the translator maps `BinOp::Sub` to `Add`;
  - the translator drops `Cast`;
  - the interpreter skips `&mut` write-back (this one is a selftest-harness check).
- [ ] **Step 3: Run the four checks and the evidence run.**
- [ ] **Step 4: Commit:** `test(ct-driver): core interpreter selftest — translated crypto reproduces FIPS 197, SHA-256, HMAC, GCM vectors`

---

### Task 9: Label the crypto crate, declassify the GCM tag compare, run the checker, and the negative control

**Files:**
- Create: `crates/crypto/src/ct.rs` (exactly the spec's D3 definition), `crates/crypto/src/ct_negative.rs`, `tools/ct-driver/manifest-negative.txt`
- Modify:
  - `crates/crypto/src/lib.rs`: `pub(crate) mod ct;` and `#[cfg(ct_negative)] pub mod ct_negative;`;
  - `crates/crypto/Cargo.toml`: check-cfg becomes `['cfg(verus_only)', 'cfg(ct_check)', 'cfg(ct_negative)']`;
  - `crates/crypto/src/{aes,gcm,sha256,hmac,hkdf}.rs`: attributes only, plus the single `declassify` edit in `aes128_gcm_open`;
  - `tools/ct-driver/manifest.txt`: roots, `exclude` for RSA;
  - `scripts/ct-check.sh`.

**Consumes:** Tasks 7 and 8.

**Interfaces (produces):**
- **Root attributes**, exactly the spec's §Labels list. Internal fns receiving secrets get `#[cfg_attr(ct_check, ct::secret(..), ct::public(..))]`, discovered by running the checker. Each `ArgLabel` reject at an unlabeled helper means "label this helper". Never label something secret merely to silence a reject at a branch.
- **`aes128_gcm_open`:** `if diff != 0 {` becomes `if crate::ct::declassify(diff) != 0 {`. The existing `ponytail:` comment stays. No other exec change.
- **`ct_negative.rs`**, verbatim:
  ```rust
  // Negative control for scripts/ct-check.sh: compiled only with --cfg ct_negative; must be rejected.
  #[cfg_attr(ct_check, ct::secret(k))]
  pub fn secret_branch(k: &[u8; 16]) -> u8 {
      if k[0] == 0 { 1 } else { 0 }
  }
  ```
- **`manifest-negative.txt`:** `root crypto::ct_negative::secret_branch`.
- **`ct-check.sh` gains two runs.**
  - **The crypto run:** `CT_CRATES=crypto`, `cargo build --release -p crypto`. It requires 0 `reject` lines and every root `ok`. It prints `ct-check: crypto ok (F fns, 7 roots, 1 declassify)`.
  - **The negative run:** the same, plus `RUSTFLAGS='--cfg ct_negative'` and both manifests, in a separate target subdir. It requires exactly one `reject` line, `reject crypto::ct_negative::secret_branch SecretSwitch …`, and the 7 roots `ok`. It prints `ct-check: negative control rejected`.

- [ ] **Step 1: Run the checker over crypto unlabeled.**
  - Expect `Root` rejects for all 7 roots.
  - Add the root attributes and iterate on `ArgLabel`/`RetLabel` rejects by labeling helpers.
  - **Any `SecretSwitch`/`SecretIndex`/`SecretDivOperand`/`SecretShift` reject other than the GCM tag compare is a finding.** Stop and report it with the MIR span. Don't change exec code to fix it.
- [ ] **Step 2: Add `ct.rs` and the one `declassify` edit.**
  - `cargo verus verify` for crypto shows the same verified count + 1 (the `declassify` fn) and 0 errors.
  - The crypto run is clean and reports 1 declassify.
- [ ] **Step 3: Add the negative control** and the negative run.
- [ ] **Step 4: Real-code mutations** (one at a time, reverted):
  - `xtime_ct`'s mask replaced by `if b & 0x80 != 0 { … } else { … }` ⇒ `SecretSwitch` in `crypto::aes::xtime_ct`;
  - the `declassify` removed in `aes128_gcm_open` ⇒ `SecretSwitch`;
  - the `sha256` root labeled `public(msg)` ⇒ `ArgLabel` at `hmac_sha256`'s call.
- [ ] **Step 5: P-256.**
  - **If `phase-5c` is merged to `main`:** merge `main`, convert each `// ct: secret …` line to the attribute, confirm binding notes B1/B2 are applied (spec §Labels), add the P-256 roots, and run. Each declassify site is listed for Task 10's rows.
  - **If 5c is not merged:** write `P-256: not on main at Task 9; checker run deferred to 5c merge (B1–B3 notes delivered)` in the report.
- [ ] **Step 6: Run the four checks** (ct-check prints the fixtures, selftest, crypto and negative lines) **and the evidence run.**
- [ ] **Step 7: Commit:** `feat(crypto): constant-time labels; checker accepts aes/gcm/sha256/hmac/hkdf with one declassify (GCM tag compare)`

---

### Task 10: verify.sh integration, TRUSTED.md, design-spec amendment and gate mutations

**Files:**
- Modify: `scripts/verify.sh`, `TRUSTED.md`, `docs/superpowers/specs/2026-10-27-verified-http3-design.md`

**Consumes:** Task 9's report formats.

**Interfaces (produces):**
- **`verify.sh`.** After `duvet report` and before the escape gate:
  - run `"$root/scripts/ct-check.sh"`;
  - then the **declassify gate**:
    - every `declassify <X>#<k>` line in the crypto report has a TRUSTED.md row starting `| ct-declassify: <X>#<k>: `;
    - `grep -c '^| ct-declassify: '` equals the line count;
    - `grep -o 'declassify(' crates/crypto/src/*.rs` with `ct.rs` excluded gives the same count. The definition is `declassify<T>(`, so it never matches.
  - Failure messages follow the existing `fail "…"` style.
  - The final line is `verify.sh: all crates verified, duvet ok, ct ok ($d declassify), escapes accounted ($attrs)`.
- **TRUSTED.md:**
  - the spec's §Trust boundary rows, verbatim modulo file paths;
  - the AES/GCM timing row reworded as the spec says;
  - the declassify row `| ct-declassify: crypto::gcm::aes128_gcm_open#0: tag-compare outcome (accept/reject) is public; the caller learns it anyway | crates/crypto/src/gcm.rs | NI is relative to declassified values | never |`.
- **Design spec:**
  - the non-goal bullet "Non-goal: proven constant-time execution" is amended per the spec;
  - add a Phase 8 entry to the roadmap: "8a CT checker (MIR level, crypto); 8b step bounds for parsers (attempt)".

- [ ] **Step 1:** Edit verify.sh and run it. It prints `… ct ok (1 declassify), escapes accounted (4)`. Report the added wall time of `ct-check.sh`.
- [ ] **Step 2:** Edit TRUSTED.md and the design spec.
- [ ] **Step 3: Gate mutations** (each makes verify.sh fail with the named message, then reverted):
  - delete the `ct-declassify:` row;
  - add a second `crate::ct::declassify(` call in gcm.rs with no row;
  - change `tools/ct-fixtures/expected.txt`'s `neg_secret_if` line to `ok`, which is a diff failure;
  - make `ct_negative::secret_branch` branch-free, so the negative run's "exactly one reject" fails.
- [ ] **Step 4: Run the four checks and the evidence run.**
- [ ] **Step 5: Commit:** `ci(verify): constant-time check and declassify gate in verify.sh; TRUSTED rows for the CT checker`

---

## Exit criteria (Phase 8a)

- `scripts/verify.sh` prints `verify.sh: all crates verified, duvet ok, ct ok (1 declassify), escapes accounted (4)`. The declassify count is 1 plus the P-256 sites if 5c merged first.
- `crates/ctcore` has no escapes, and `theorem_ct` verifies at `--rlimit 4` with its statement equal to the spec's. Each of M1–M11 fails on a named lemma (Task 5 report).
- `ct-check.sh` reports:
  - fixtures 22/22;
  - selftest 5/5;
  - crypto ok (F fns, 7 roots, 1 declassify);
  - negative control rejected.
- TRUSTED.md has the new rows (front end, manifest, semantics/leakage, compiler/CPU, one `ct-declassify:` per site), the reworded AES/GCM timing row, and the pins paragraph from Task 1.
- `rust-toolchain.toml` pins 1.98.1. The release profile has per-package `overflow-checks = false` for the 6 verified crates only.
- Binding notes B1–B3 (spec §Labels) are recorded in the 5c SDD ledger before 5c Task 7 is dispatched. This is the controller's action.
- `phase-8a` is merged into `main`. The phase summary lists the measured ctcore proof time and the added verify.sh time.

## Self-review (done while writing)

- **The spec's calls map to tasks:**
  - toolchain/profile → T1;
  - core and semantics → T2;
  - typing → T3;
  - NI → T4–T5;
  - exec checker → T6;
  - driver → T7;
  - translation validation → T8;
  - crypto run and negative control → T9;
  - verify.sh and TRUSTED → T10.
- **Non-vacuity at four layers:**
  - proof mutations (T5);
  - exec mutations, including a consistent one (T6);
  - translator mutations (T7, T8);
  - real-code and gate mutations (T9, T10).
- **Probed by the planner:**
  - CFG lockstep NI with step equality (P2);
  - recursion over `Seq<Val>` and `write_at` shape preservation (P1);
  - the fresh-target `--rlimit` gotcha.
- **Not probed:** the frame-local `Mut`/`plc` lemmas (T3 has a stop rule) and the driver's `Instance`-based traversal. The spike used `CrateItem::body()`; Task 7 Step 1 exercises `Instance::resolve` first.
