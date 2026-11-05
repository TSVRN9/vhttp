# Phase 8d: Executable MIR Semantics Evaluator — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Run the trusted MIR semantics `ctmir::sem` itself on every selftest and semconf vector, using an exec evaluator proved against `mir_run`/`mir_entry`. Then every crypto `ok` root and every parser `bounded` root is shown to reach `Done` with native's value on real inputs.

**Architecture:**
- Four new modules in `crates/ctmir`:
  - `eval_tab` holds the id-index tables;
  - `eval_const` evaluates constants and unit-like values;
  - `eval` evaluates places, operands, rvalues, statements and the entry frame;
  - `eval_run` evaluates terminators, calls, Drop, std rows, the block loop and `mir_eval`.
- Each exec fn mirrors one `sem` spec fn, and its ensures says so per outcome.
- `vectors::check_vector` runs `mir_eval` in place of the core interpreter, and `interp.rs` goes.
- `pipeline`'s `line_ok` gains `pass_ok`.
- `ct-check.sh` gains a coverage gate.

**Tech Stack:** Verus 0.2026.10.04.426d8b0, vstd =0.0.0-2026-10-04-0306, rustc 1.98.1, the existing `ctcore`/`ctmir`.

**Spec:** Read both before any task:
- `docs/superpowers/specs/2026-11-05-phase-8d-mir-evaluator-design.md`, the 8d addendum. Its decisions 1–7 are binding.
- `docs/superpowers/specs/2026-11-03-phase-8c-verified-front-end-design.md`, for §MIR semantics and §8c result.

## Global Constraints

- Every Verus function verifies at `--rlimit 4`.
  - On a fresh target, run a default `cargo verus verify` first.
  - To force a real re-run, delete `target/debug/.fingerprint/ctmir-*`, `target/debug/deps/*ctmir*` and the `verus-partial` fingerprints.
  - Rank functions by `--output-json --time-expanded`.
  - Never raise rlimit. Split the function instead.
  - nonlinear_arith is heavy-tailed: isolate it in small asserts.
  - Hiding a spec fn that is absent from a spinoff's pruned context crashes Verus ("undeclared fuel"). Hide only what the function's context mentions.
- Do not lengthen `lemma_call_leaf` (~8M) or `lemma_ops_prefix` (8.2M). New proofs must not call them.
- No `assume(`, `external_body`, `verifier::external` or `axiom` anywhere under `crates/` outside `crates/crypto/src`, in code or comments: verify.sh:54-62 greps them all (preflight M3). verify.sh's final line stays byte-identical:
  `verify.sh: all crates verified, duvet ok, ct ok (10 declassify), cost 19/36, escapes accounted (0), binary ok (49 fns)`.
  New `ct-check:` lines before it are fine.
- `crates/ctcore/src` is frozen. `crates/crypto/src` is never edited; `crates/crypto/tests` may be.
- `crates/ctmir/src/sem.rs` is trusted. An evaluator result that differs from native is a semantics finding (addendum decision 7). On one, stop and report before any `sem.rs` edit. Any edit is minimal, pinned by a `sem_sanity` fact that fails without it, audited clean-room by a separate seat, and followed by a forced re-verify of all of `ctmir`.
- The `Vec`-holding AST and values are compared only through views (`@`, `cv`, `fv`), never with spec `==` on exec structs (8c ruling M6).
- No new dependencies. `Cargo.lock` and `tools/*/Cargo.lock` must not change.
- Report formats are byte-compatible: `pass <path> steps=<n>`, `pass <path> panic` and `fail <path> <why>`. ct-check counts lines by these prefixes.
- Phase 4c runs in parallel in wt-4c (crates tls, quic, quictls, server).
  - Do not edit those crates, their tests included.
  - The merge points are TRUSTED.md (8d edits only the CT rows 45 and 48), the quic lines of `tools/ct-driver/selftest.txt` (they depend on quic's code), and `Cargo.lock` (which must be unchanged).
  - After merging main, re-run ct-check.
- Work in `/home/tavern/Projects/rust/web-server/.worktrees/wt-8d` (branch `phase-8d`). Scratch goes under `/home/tavern/Projects/rust/web-server/.worktrees/vt-8d-evidence/`, never `/tmp`. Commits carry no attribution or Co-Authored-By lines.
- Reuse before writing anything new:
  - `interp_val.rs`: `CVal`, `CFrame`, `cv`, `cvs`, `fv`, `XPE::Snap`, `nav`, `at`, `set_at`, `push_at`, `cclone`, `ceq_vec`;
  - `interp_arith.rs`: `binop_exec`, `unop_exec`, `cast_exec`, `bits_exec`, all proved against the ctcore fns `sem` imports. `bin_ok`, `in_range` and `ival` (sem.rs:716-732) have no exec mirror, and `binop_exec` gives 0 for `/ 0`, so `x_bin_ok` is new (preflight C4);
  - `look.rs`: the exact mirrors (`x_unit_like`, `x_ul_arr`, `x_has_arr`, `x_std_model`, `x_is_leaf`, `x_int_of`);
  - `lower_const.rs`: `x_le`, `x_no_prov`, `x_prov_at`, `x_rd_int`, `x_tag_bytes`, `x_tag_variant`, `x_adt_sel`;
  - `policy.rs`: `has_exec` and `lemma_set_of`;
  - `sem_subset.rs`'s fuel induction, as the proof template.

## Review Focus

1. **Duplicate or out-of-range ids in a dump table.** `find` is first-match. The index must return the first row, and an id past the cap must make `tabs` give `None`, not allocate. Task 1, `tabs_first_match_and_cap`.
2. **Vector arguments that are not well-typed for the root's MIR signature**, such as an int where `&[u8; 4]` is expected. The line must be `fail .. args not well-typed`, never `pass`. Task 3, `selftest_ill_typed_args_fail`.
3. **A `=> panic` vector whose run ends in `Fuel` or `GaveUp`.** It must fail, because only `Panic` passes. Task 3, the proof mutation "`Ev::Fuel` accepted as panic", and `selftest_panic_vector_needs_panic`.
4. **A root whose only vectors are panic vectors**, or whose `pass` lines are missing. The coverage gate must fail. Task 4, the doctored-report check.
5. **The I1 class: a `sem`-level panic on a construct the roots use.** The gate must go red. Task 3's gate mutation, in a scratch copy of the evaluator, makes `PtrMetadata` of a `Shr`-held pointee panic, and every `sha256` line must fail. 8c Task 6's C1 itself cannot be replanted, because the translator and ct-zarr reject `ul_arr` `ZeroSized` constants (preflight C1).

---

### Task 1: Tables, constants, places, rvalues, statements, the entry frame

**Files:**
- Create: `crates/ctmir/src/eval_tab.rs`, `crates/ctmir/src/eval_const.rs`, `crates/ctmir/src/eval.rs`
- Modify: `crates/ctmir/src/lib.rs` (three `pub mod` lines)
- Test: `crates/ctmir/tests/eval.rs` (new), on `tests/data/tiny.json`. Copy `tests/lower.rs`'s `edit` helper for JSON edits.

**Interfaces:**
- Consumes: `sem`'s spec fns, and the reuse list in Global Constraints.
- Produces:
  - In `eval_tab.rs`:
    - `pub struct Tabs { pub tys, pub adts, pub layouts, pub consts, pub allocs, pub insts, pub drops, pub calls: Vec<Option<usize>> }`. Each maps a key to the index of the first row with that key. The keys are `TyRow.id`, `Adt.ty`, `LayoutRow.ty`, `ConstRow.id`, `AllocRow.id`, `Inst.id`, `DropRow.ty` and `Call.fn_ty`.
    - `pub open spec fn tabs_ok(m: MirCrate, t: Tabs) -> bool`. For each table, `t.X@[k] == find(m.X@, key == k)` (as `Option<nat>`) for `k < t.X@.len()`, and no row's key is `>= t.X@.len()`.
    - `pub const ID_CAP: usize = 1 << 24;` and `pub fn tabs(m: &MirCrate) -> (r: Option<Tabs>) ensures r matches Some(t) ==> tabs_ok(*m, t)`. It returns `None` iff some key is `>= ID_CAP`.
    - `pub fn t_rigid<'a>(m: &'a MirCrate, tb: &Tabs, t: Ty) -> (r: Option<&'a RigidTy>)`, with the ensures of `look::x_rigid`.
    - Likewise `t_adt_row`, `t_layout`, `t_const_usize`, `t_alloc_mem`, `t_inst_idx`, `t_drop_row`, `t_int_ty`, `t_callee_of(m, tb, func: &Operand) -> (r: Option<(usize, &GenericArgs)>)` (against `callee_of`) and `t_inst_body` (against `inst_body`). All require `tabs_ok(*m, *tb)`.
  - In `eval.rs`:
    - `pub enum Halt { Panic, GaveUp }`, with `pub type R<T> = Result<T, Halt>`. The ensures pattern of every mirror below is: `Ok(x)` means the spec gives `Some(view(x))`, `Err(Halt::Panic)` means the spec gives `None`, and `GaveUp` carries no claim.
    - `pub struct ECur { pub root: CRoot, pub path: Vec<XPE>, pub loc: bool }`, and `pub open spec fn ecur_v(fr: Frame, c: ECur) -> PRes`:
      - when `loc`, it is `PRes::At(Loc { root: root_v(c.root), path: xpes(c.path@) })`, with the path free of `Snap`;
      - otherwise it is `PRes::Snap(xread(base_v(fr, root_v(c.root)), c.path@))`.
    - `pub fn e_eval_place(fr: &CFrame, p: &Place) -> (r: R<ECur>)`, against `eval_place(fv(*fr), *p)`'s place, events ignored.
    - `pub fn e_read_place(fr: &CFrame, p: &Place) -> (r: R<CVal>)`, against `read_place`.
    - `pub fn e_eval_op(m: &MirCrate, tb: &Tabs, fr: &CFrame, op: &Operand) -> (r: R<(CVal, u64)>)`, against `eval_op`'s value and charge.
    - `pub fn e_eval_ops(m, tb, fr, ops: &Vec<Operand>) -> (r: R<(Vec<CVal>, u64)>)`, against `eval_ops(.., ops@, ops@.len())`.
    - `pub fn e_eval_rv(m, tb, b: &Body, fr, rv: &Rvalue) -> (r: R<(CVal, u64)>)`, against `eval_rv`. Write one exec fn per `rv_*` spec fn. `CheckedBinaryOp` and the `*Unchecked` binops give `GaveUp`: the translator never lowers them (lower.rs:275-288), and exact mirrors would need 128-bit exact-overflow arithmetic (preflight C4). New: `pub fn x_bin_ok(op: &BinOp, it: &CTy, rt: &CTy, a: u128, c: u128) -> (r: bool) ensures r == bin_ok(*op, *it, *rt, a, c)`, needed for Div/Rem (a zero divisor, `MIN / -1` on bit patterns) and the masked shifts (preflight C4).
    - `pub fn e_store(fr: &mut CFrame, l: &CLoc, w: CVal) -> (r: R<()>)`, against `store`. The frame is updated in place.
    - `pub fn e_exec_stmts(m, tb, b: &Body, fr: &mut CFrame, ss: &Vec<Statement>) -> (r: R<u64>)`. Ensures: `Ok(n) ==> exec_stmts(*m, *b, fv(*old(fr)), ss@, ss@.len()) matches Some((f, _, s)) && fv(*final(fr)) == f && s == n as nat`, and `Err(Halt::Panic) ==> exec_stmts(..) is None`.
    - `pub fn e_mir_entry(m, tb, i: usize, args: Vec<CVal>, slots: Vec<CVal>) -> (r: R<CFrame>)`, with `Ok(fr) ==> fv(fr) == mir_entry(*m, i as nat, cvs(args@), cvs(slots@))`. It takes the `Vec`s by value, so a call does not deep-clone its arguments (preflight M1). `mir_entry` is total, so its `R` only ever carries `GaveUp` from a cap.
    - `pub fn x_wt_args(m: &MirCrate, tb: &Tabs, i: usize, args: &Vec<CVal>, slots: &Vec<CVal>) -> (r: bool) ensures r ==> wt_args(*m, i as nat, cvs(args@), cvs(slots@))`. It may reject more.
  - In `eval_const.rs`:
    - `pub fn e_ul_val(m, tb, t: Ty) -> (r: R<CVal>)`, with `Ok(v) ==> cv(v) == ul_val(*m, t)`.
    - `pub fn e_dec(m, tb, t: Ty, a: &Allocation, off: usize, fuel: usize) -> (r: R<(CVal, u64)>)`, against `dec`, together with its `dec_*` companions.
    - `pub fn e_const_val(m, tb, c: &ConstOperand) -> (r: R<(CVal, u64)>)`, against `const_val`.
    - Allocation caps: a `Repeat` count, a `unit_like` array length, or any built `Vec` past `1 << 24` elements is `GaveUp`.

- [ ] **Step 1: Write the failing tests** in `tests/eval.rs`. Decode `tiny.json` with `json::parse` and `schema::decode`, build `tabs`, and assert:
  - `tabs_first_match_and_cap`:
    - append a duplicate `tys` row (same `id`, different kind) to the JSON; `t_rigid` on that id gives the first row's kind;
    - set one `tys` id to `16777216`; `tabs` gives `None`.
  - `entry_frame_tiny`: `e_mir_entry` of `tiny::tiny` with `args = [Shr(Arr[0x0a,0x0b,0x0c,0x0d]), Int(5)]` and slots `[Unit, Unit]`.
    - Locals 1 and 2 are the args.
    - Every other local is `Unit`, unless its type is unit-like with an array.
    - `x_wt_args` is true.
    - With `Int(5)` as the first argument, `x_wt_args` is false.
  - `stmts_tiny`: `e_exec_stmts` over `tiny::tiny`'s block 0 from that frame is `Ok`. Local 5, which is assigned `i & 3`, holds `Int(1)`.
  - `const_opt`: the `Some(3)` constant operand in `tiny::opt`'s body is `Allocated [1, 3]`, and `e_const_val` evaluates it to `(Adt(1, [Int(3)]), 1)`.
- [ ] **Step 2:** Run `cargo test -p ctmir --test eval`. Expected: it fails to compile (no `ctmir::eval`).
- [ ] **Step 3: Implement the Produces block.**
  - Each `e_X` follows `sem::X`'s match arm by arm, and calls the mirrors of the spec fns `X` calls.
  - The step loop's lookups (`rigid`, `int_ty`, `adt_row`, `layout`, `place_ty`, `op_ty`, `callee_of`, `inst_body`) go through `Tabs`.
  - `e_ul_val` and `e_mir_entry` are not cold: every body call enters through `mir_entry`. Route `e_ul_val`'s `unit_like`/`has_arr` lookups through `Tabs` (Tabs-based copies of `x_unit_like`/`x_has_arr`). A per-type `ul_val` table in `Tabs` is the next step if Task 2's probe shows entry as hot; Task 2 decides (preflight M1, M8).
  - `tabs`: build each index in one pass over the rows, setting an entry only while it is `None`. The invariant is the first-match `find` over the prefix; reuse `look::lemma_find`.
  - No events are built.
- [ ] **Step 4:** Run the tests, then verify ctmir: default run first, then a forced run, ranked by rlimit. Expected: tests pass, and `cargo verus verify -p ctmir -- --rlimit 4` reports 0 errors.
- [ ] **Step 5: Mutations.** Each must fail a proof. Record each under `vt-8d-evidence/t1/`, then revert.
  1. `tabs` keeps the last match.
  2. `Index`'s bound check uses `<=`.
  3. `ConstantIndex` `from_end` uses `vs.len() - offset + 1`.
  4. `x_bin_ok` drops the Div/Rem zero-divisor check (preflight C4).
  5. `e_mir_entry` binds `Mut(Slot(k))` in place of `Mut(Slot(k - 1))`.
  6. `e_ul_val` ignores `ul_arr` and always gives `Unit`.
- [ ] **Step 6: Commit** `feat(8d T1): exec mirrors of sem's places, operands, constants, rvalues, statements and entry, with id-index tables`.

### Task 2: Terminators, calls, Drop, std rows, the run and `mir_eval`

**Files:**
- Create: `crates/ctmir/src/eval_run.rs`
- Modify: `crates/ctmir/src/lib.rs`; `crates/ctmir/src/look.rs`, to make `x_zst_dest` exact (`r == zst_dest(..)`), which removes a `GaveUp` path for the ghost and `GhostNew` leaves (preflight M10)
- Test: `crates/ctmir/tests/eval.rs`

**Interfaces:**
- Consumes: from Task 1, `Tabs`/`tabs_ok`, `Halt`/`R`, `ECur`/`ecur_v`, `e_eval_op(s)`, `e_eval_place`, `e_store`, `e_exec_stmts` (frame in place) and `e_mir_entry`.
- Produces (`eval_run.rs`):
  - `pub enum Ev { Done(CFrame, u64), Panic, Fuel, GaveUp }`, and `pub open spec fn ev_ok(o: Out, r: Ev) -> bool` exactly as in addendum decision 2.
  - `pub fn e_std_apply(m, tb, f: &StdFn, dty: Option<Ty>, vs: Vec<CVal>, fr: &mut CFrame) -> (r: R<(CVal, u64)>)`. The ensures, against `std_apply(.., cvs(vs@), fv(*old(fr)))`: on `Ok`, the value, `fv(*final(fr))` and the extra cost are the spec's; on `Err(Halt::Panic)`, the spec gives `None`.
  - `pub fn e_leaf_call(m, tb, pol: &Policy, key: &[u8], g: &GenericArgs, dty: Option<Ty>, vs: Vec<CVal>, fr: &mut CFrame) -> (r: R<(CVal, u64)>)`, against `leaf_call(.., cpol(*pol), ..)`.
  - The terminator mirrors and the block loop take `Ghost(s): Ghost<Set<nat>>, Ghost(rs): Ghost<spec_fn(nat) -> Set<nat>>`, with `requires closed(*m, cpol(*pol), s, rs), s.contains(j as nat)` and, for the terminator and block mirrors, `*b == inst_body(*m, j as nat)->Some_0` and `rs(j as nat).contains(bb as nat)` (preflight M8). Reveal `block_ok` and `exec_stmt` (both opaque) only where needed. A visited block is in `rs(j)`, so `block_ok` holds without an exec check (`body_in`).
  - `pub fn e_run(m, tb, pol, Ghost(s), Ghost(rs), j: usize, fr: CFrame, fuel: u64) -> (r: Ev) ensures ev_ok(mir_run(*m, cpol(*pol), j as nat, fv(fr), fuel as nat), r)`. It loops over blocks as `interp::run_exec` does, and body calls recurse.
  - `pub fn mir_eval(m: &MirCrate, tb: &Tabs, pol: &Policy, i: usize, args: &Vec<CVal>, slots: &Vec<CVal>, fuel: u64) -> (r: Ev)`, with `requires tabs_ok(*m, *tb), in_subset(*m, cpol(*pol), i as nat)` and `ensures ev_ok(mir_run(*m, cpol(*pol), i as nat, mir_entry(*m, i as nat, cvs(args@), cvs(slots@)), fuel as nat), r)`. It chooses `(s, rs)` from `in_subset` in ghost. An `Err(GaveUp)` from `e_mir_entry` gives `GaveUp`.

- [ ] **Step 1: Write the failing tests** in `tests/eval.rs`. Each runs `mir_eval` with `FUEL` on `tiny.json`, under the empty policy. Get `in_subset` by lowering first: `lower` must be `Ok`.
  - `eval_tiny`:
    - `tiny::tiny` (`0a0b0c0d`, 5) gives `Done` with return `Int(9)`;
    - `tiny::opt` true gives `Some(3)`'s value and false gives `None`'s;
    - `tiny::call` (`0a0b0c0d`) gives `Int(0xe)`;
    - each step count equals the `steps=` that today's selftest prints for the same vector. No test prints tiny's counts today (`selftest_report` checks only the prefix), so print them by running the selftest at 0b0061c and record them in the test, before Task 3 deletes the core path (preflight T2 row).
  - `eval_fuel`: `tiny::call` at fuel 1 gives `Ev::Fuel`.
  - `eval_panic`: with `tiny::tiny`'s bounds-check `Assert` edited to `expected: false`, the run gives `Ev::Panic`.
  - `eval_probe` (`#[ignore]`, reads `CT_DUMP_DIR/crypto/mir-crypto.json` and `../../tools/ct-driver/manifest.txt`; it shapes the arguments by hand, wrapping each `&[u8]` argument in `Shr`, since `check_vector` still runs core in Task 2 (preflight M9)): runs `sha256("abc")` and `p256_public_key(d = 3)` from `selftest.txt`, and prints the `Ev` kind, the steps and the elapsed time. Expected steps: 9591 and 149653114, the core counts. This is the early timing probe for Task 3's 150 s bound.
- [ ] **Step 2:** Run `cargo test -p ctmir --test eval`. Expected: it fails to compile.
- [ ] **Step 3: Implement in two commits.**
  1. **Call-free:** `Goto`, `SwitchInt` (first matching branch, `find`), `Assert`, `Return`, `Unreachable`/`Abort`, and the loop. `Call` and `Drop` give `GaveUp`. Commit `feat(8d T2a): call-free MIR evaluator`.
  2. **Calls:**
     - `body_call`: the fuel check first, then `args_ok` (sem.rs:1256; the other order gives `Panic` where the spec gives `Fuel`, preflight M2), `call_slots`, enter through `e_mir_entry`, 1 fuel, `return_to` with `write_back` in parameter order;
     - `call_step`: policy and std leaves first, then bodies; destination last; cost `1 + charges + x`;
     - `drop_step`: an empty shim or the `Vec<int>` leaf costs 1; glue costs `2 + steps` on `Mut(l)`;
     - every `std_apply` row, with the `USZ` checks.

     If calls do not verify, land the call-free commit and stop-report.
- [ ] **Step 4:** Run the tests and verify ctmir, forced and ranked. Expected: tests pass, 0 errors. Run `eval_probe` against a ct-check output dir: `CT_DUMP_DIR=<CT_OUT> cargo test --release -p ctmir --test eval -- --ignored eval_probe --nocapture`. Record the times in `vt-8d-evidence/t2/probe.txt`. If entry (`e_mir_entry`'s `ul_val`s) dominates, add the per-type `ul_val` table to `Tabs` or one entry template per instance here (preflight M1, M8).
- [ ] **Step 5: Mutations.** Each must fail a proof:
  1. a failed `Assert` gives `Done`;
  2. `Assert` ignores `expected`;
  3. a Drop of glue costs 1;
  4. `write_back` is skipped;
  5. `body_call` takes no fuel;
  6. `VecSet`'s bound uses `<=`;
  7. `SwitchInt` takes the last matching branch;
  8. `SliceSubrange` requires `lo < hi`.
- [ ] **Step 6: Commit** `feat(8d T2b): MIR evaluator calls, Drop, std rows; mir_eval`.

### Task 3: The selftest runs `ctmir::sem`, and a `pass` line is a claim

**Files:**
- Modify: `crates/ctmir/src/vectors.rs` (`vec_run`, `passes`, `panics`, `check_vector`; its header line 2), `crates/ctmir/src/pipeline.rs` (`selftest`, `line_ok`, new `pass_ok`, `no_claim`, `info`, the root, bounded and checked writers, the `Lowered` cache, the doc at :1238; preflight C3, M7), `crates/ctmir/src/interp_val.rs` (header line 1), `crates/ctmir/src/lib.rs`, `tools/ct-fixtures/semconf/src/lib.rs` (line 4, "verified core interpreter"; preflight M7), `scripts/ct-check.sh` (comments on what the selftest runs, the semconf panic comment, the crypto selftest's own 150 s bound)
- Delete: `crates/ctmir/src/interp.rs`. Before deleting, `grep -rn 'interp::' crates tools` must show only `vectors.rs` and `tests/interp.rs`.
- Test: `crates/ctmir/tests/interp.rs`. Delete its hand-built core-`Program` cases. Keep the arithmetic, vector-syntax and selftest cases. Cases that call `check_vector` directly go through the `selftest` helper, since its new signature takes `m`, `tb`, `pol` and `i`. Deleting `vector_checks` loses the only tests of the shape, width and `mut:` errors, so re-express them as `selftest` lines over tiny (preflight M6).

**Interfaces:**
- Consumes: from Tasks 1–2, `mir_eval`, `Ev`, `ev_ok`, `tabs`, `x_wt_args`. Also `lower_fn::theorem_lowers_in_subset(m, pol, path, p, infos, 0)`, and `lower`'s `Ok((p, infos))`, which `selftest` now keeps.
- Produces:
  - `pub open spec fn mir_args(b: ctcore::syntax::Body, v: VSpec) -> Seq<Val>`. It is `entry_args(b, v)`, except that at each `mut_param(b, j)` the argument is `Val::Mut(Loc { root: Root::Slot(j), path: seq![] })`.
    - `entry_args` puts the raw pointee there, and `wt_rec` accepts only a `Mut` at a `&mut` type (sem.rs:326), so `wt_args` would reject every `mut:` vector.
    - `entry_local` ignores the argument at a `&mut` parameter and uses the slot (sem.rs:1105-1108), so the frame is unchanged.
    - Check both arms before writing it.
  - `pub open spec fn vec_run(m: MirCrate, pol: Policy, i: nat, p: Program, v: VSpec) -> Out`. It is `mir_run(m, cpol(pol), i, mir_entry(m, i, a, sl), FUEL as nat)` with `a = mir_args(p.fns@[0], v)` and `sl = entry_slots(p.fns@[0], entry_args(p.fns@[0], v))`.
  - `passes(m, pol, i, p, v, n)`, with `a` and `sl` as above:
    - `shape_ok(p, v) && !v.panic && wt_args(m, i, a, sl)`;
    - `vec_run(..) matches Out::Done(fr, _, k) && k == n`;
    - `seq![nth(fr.locals, 0)] + mouts(v.args, fr.slots, v.args.len()) == v.want`.
  - `panics(m, pol, i, p, v)`: `shape_ok && v.panic && wt_args(..) && vec_run(..) is Panic`.
  - `pub fn check_vector(m: &MirCrate, tb: &Tabs, pol: &Policy, i: usize, p: &Program, v: &Vector) -> (r: Result<Option<u64>, Vec<u8>>)`, with `requires tabs_ok(*m, *tb), in_subset(*m, cpol(*pol), i as nat), p.fns@.len() > 0` and `ensures Ok(Some(n)) ==> passes(.., n as nat), Ok(None) ==> panics(..)`. The `fail` texts:
    - `args not well-typed`;
    - `mir: panic`;
    - `mir: fuel`;
    - `mir: gave up`;
    - `the run completed (want panic)`;
    - `got .. want ..` (as today).
  - In `pipeline.rs`, `pub open spec fn pass_ok(m: MirCrate, pol: Policy, l: Seq<u8>) -> bool`, exactly as in addendum decision 4. `line_ok` gains `starts(l, b"pass "@) ==> pass_ok(m, pol, l)`.
  - `selftest` builds `tabs` once. On `None` it returns `Err("dump: a table id past ID_CAP")`.
  - Line writers (preflight C3):
    - `no_claim` (pipeline.rs:497) also excludes `pass `, so `info` can no longer write a `pass` line.
    - A dedicated writer, `pass_line(Ghost(m), Ghost(pol), Ghost(i), Ghost(args), Ghost(slots), acc, path, steps: Option<u64>)`, `put_clean`s the whole body, proves `l == clean(..) + "\n"` and pushes it under `pass_ok`.
    - The root, bounded and checked writers (:1066-1129, :1203-1224) prove `!starts(l, "pass ")`: `no_claim` covers `checked`, and root and bounded get a `starts_pub(&l, b"pass ")` guard, as they have for each other.
  - The cache becomes `Lowered = Vec<(Vec<u8>, Result<(c::Program, usize), Vec<u8>>)>`, with the loop invariant `Ok((p, i)) ==> root_of(m, path@, i) && in_subset(m, cpol(pol), i) && p.fns@.len() > 0` plus the vector-shaping facts. Establish it once, at lowering, with `lemma_root_shape` and `theorem_lowers_in_subset(.., 0)`; `lowers` is existential, so `infos.len() >= 1` needs a `choose` on `lowers_rs` (preflight C3).
  - Move the per-vector body of `selftest` into a helper fn, so both fit rlimit 4 (preflight C3).

- [ ] **Step 1: Write the failing tests** in `tests/interp.rs`, using its existing `selftest` helper over `tiny.json`:
  - The existing selftest test still gives the same `pass`/`fail` lines.
  - `selftest_ill_typed_args_fail`: `tiny::tiny 0a0b0c 0x5usize => 0x0u8` gives `fail tiny::tiny args not well-typed`. The vector passes 3 bytes for `[u8; 4]`, with no width suffix, so the existing width check passes it to `x_wt_args`.
  - `selftest_vector_shape_errors`: the arity, width and `mut:`-on-a-non-`&mut`-parameter errors, as `selftest` lines over tiny, each a `fail` with today's text (preflight M6).
  - Not a test, since `tiny.json` has no `&mut` parameter: `check_vector` runs `x_wt_args` on `mir_args`, not on `entry_args`. The crypto selftest's `serialize_ecdsa_der` and semconf's write-back vectors are the runtime check (preflight M6).
  - `selftest_mir_panics_where_core_completes`, the I1 scenario: edit `tiny.json` so `tiny::tiny`'s index is unguarded. Make the mask constant `3` into `7` and the bounds `Assert` into a `Goto` to its target. A vector with `i = 5` must then give a line starting `fail tiny::tiny mir: panic`.
  - `selftest_panic_vector_needs_panic`: `tiny::opt true => panic` is a `fail` with `the run completed (want panic)`, and `pass` is never printed for it.
- [ ] **Step 2:** Run `cargo test -p ctmir --test interp`. Expected: the new tests fail.
- [ ] **Step 3: Implement the Produces block.**
  - `check_vector` keeps today's shape and width checks. It builds `slots` as today and `args` per `mir_args` (a `Mut(Slot(j))` at each `mut:` parameter), requires `x_wt_args`, runs `mir_eval(.., FUEL)`, and reads the return local and the `mut:` slots out of `Ev::Done`'s frame.
  - `selftest` prints `pass <path> steps=<n>` with the MIR step count.
  - Prove `pass_ok` for each `pass` line from `check_vector`'s ensures and the cache invariant, through `pass_line`.
  - Delete `interp.rs` and the `lib.rs` line.
- [ ] **Step 4:** Run the tests, verify ctmir (forced), then run `scripts/ct-check.sh` with `CT_OUT` under `vt-8d-evidence/t3/`. Expected:
  - `ct-check: selftest 22/22`, `selftest parsers 15/15` and `semconf 31723/31723`, with every `pass` line on the evaluator;
  - all the other lines unchanged.

  The crypto selftest's `front` call gets its own 150 s bound (`front 150 ..`), so the bound is enforced, not only measured; update the "about 20 s" comment (ct-check.sh:123-124). If it is slower, apply addendum decision 5's fallbacks in order and record each measurement (preflight M1).

  Any `fail .. mir: panic` or `got .. want ..` is a semantics finding: stop and report (Global Constraints). Fix any `mir: gave up` in the evaluator.
- [ ] **Step 5: Mutations.**
  - Proof mutations. Each must fail verification:
    1. `check_vector` returns `Ok(None)` on `Ev::Fuel`;
    2. it passes on `Ev::GaveUp`;
    3. it skips `x_wt_args`;
    4. `passes`/`panics` (vectors.rs) without `wt_args`, with `pass_ok` and pipeline.rs unchanged: the pass-line proof must fail (preflight C2).
  - Gate mutation, unverified, in a scratch copy of the worktree under `vt-8d-evidence/t3/c1/`. Replant an I1-class panic on a construct the roots use: `e_eval_rv`'s `PtrMetadata` gives `Halt::Panic` when the pointee is held by `Shr` (sha256's closure has 3 `PtrMetadata` and 28 `Index` projections). Build `ct-front` with `cargo build`, without verifying, and run the crypto selftest. Expected: `fail crypto::sha256::sha256 mir: panic` on every sha256 line, and the selftest gate red. Record the report. (8c Task 6's C1 itself cannot fire: lower_const.rs:1007 and rel.rs:243 reject `ul_arr` `ZeroSized` constants, and ct-zarr fails such a dump; preflight C1.)
- [ ] **Step 6: Commit** `feat(8d T3): selftest and semconf vectors run ctmir::sem through the verified evaluator; pass lines proved (pass_ok); core interpreter deleted`.

### Task 4: Coverage of every `ok`/`bounded` root, and the trust text

**Files:**
- Modify: `tools/ct-driver/selftest.txt` (its new lines and its header line 4, which still names `ctmir::interp`; preflight M7), `crates/crypto/tests/rsa_pss.rs` (test only), `scripts/ct-check.sh`, `TRUSTED.md` (rows 45 and 48 only), `docs/superpowers/specs/2026-11-03-phase-8c-verified-front-end-design.md` (§8c result: the Goal 4 paragraph and the follow-ups), and the addendum's "8d result" section.

**Interfaces:**
- Consumes: Task 3's `pass` lines, and ct-check's report paths: `$CT_OUT/crypto/report-crypto.txt`, `$CT_OUT/crypto/selftest-crypto.txt`, `$CT_OUT/parsers/cost-all.txt` and `$CT_OUT/parsers/selftest.txt`.
- Produces:
  - A new ct-check line, `ct-check: done roots <a>/<R>, bounded <b>/<B>`, after the crypto line. All four numbers are computed from the reports, none hard-coded, since 4c can move quic's bounded count (preflight M5). `a` and `b` are the ok/bounded roots that have a `pass <path> steps=` line.
  - ct-check fails unless `a == R` (the `root .. ok` lines) and `b == B` (the `bounded` lines).
  - The join rests on the selftest and the check/cost runs reading the same dump under the same `cpol` (cost-targets.txt holds only `cost-root` lines, and `cpol` reads only declassify and ghost lines); a comment in ct-check.sh states it. Paths are awk `$2`; none of the covered paths has a space today. If the RSA vector gets its own run (decision 5's fallback), the gate reads that report too (preflight M5).

- [ ] **Step 1: The RSA vector.**
  - Change `pss_rfc9500_2048` so that it asserts `check(..)`'s signature equals a hex constant. That constant is the vector's expected value.
  - Add a test that prints, or asserts against constants, the `n` and `d` that `rsa_pss_sha256_sign` passes to `rsa_pss_sign_inner`, so the vector's inputs are native's own.
  - Add the `selftest.txt` line: `crypto::rsa::rsa_pss_sign_inner <n> <d> <msg> <salt> <ghost> => <sig>`. Its comment names the test.
  - Use RustCrypto's `d` (`key()` already does, tests/rsa_pss.rs:20-24). For fixed `(n, e)` every valid `d` gives the same signature, so the want must equal the spike's `8febad92…`; a mismatch is a red flag, not a `d` effect. `d`'s encoded length moves only the step count, through `pad_be` (preflight M4).
  - The `Ghost<RsaKeySpec>` argument takes the form `x_wt_args` accepts; record it in the comment.
- [ ] **Step 2: Parser vectors**, one completing vector per uncovered bounded root:
  - `wire::varint::{exec_min_len, parse_varint}`;
  - `h3::frame::parse_frame_header`;
  - `h3::qpack::huffman::{feed_bit, lookup}`;
  - `quic::frame::{stream_data_at, parse_reset_stream, parse_two_varints, parse_crypto, parse_stream, parse_one_varint, parse_close, parse_frame_type}`.

  Derive each value from a named public test whose run passes through that call with that input, as the existing `vint_at`/`bytes_at` lines do, and name the test in a comment. quic's tests are read, never edited (Phase 4c).
- [ ] **Step 3: The coverage gate in `ct-check.sh`.**
  - Root paths come from `awk '$1 == "root" && $3 == "ok"'`, bounded paths from `awk '$1 == "bounded"'`, and pass paths from `awk '$1 == "pass" && $3 ~ /^steps=/'`. Join them with `comm`.
  - Check the gate against doctored copies of the reports under `vt-8d-evidence/t4/`:
    - delete one root's `pass` lines;
    - turn one into `pass <path> panic`.

    Each copy must make the gate fail. Record both runs.
- [ ] **Step 4: Run** `scripts/verify.sh`. Expected:
  - `ct-check: selftest 23/23`, `selftest parsers 28/28`, `semconf 31723/31723` and `done roots 11/11, bounded 19/19`;
  - verify.sh's final line byte-identical to Global Constraints;
  - the crypto selftest within its own 150 s `front` bound.
- [ ] **Step 5: The text.**
  - TRUSTED row 45 (preflight C5):
    - the vectors run `ctmir::sem` through `ctmir::eval`; `pass` lines are claims (`pass_ok`); the native value is matched in `check_vector`'s ensures;
    - replace both sentences `pass_ok` makes false: "Selftest `pass` lines are not claims of `report_sound`, and the theorems do not rest on them", and the list "`reject`, `none`, `checked`, `declassify`, `pass` and `fail` lines are informational" (drop `pass` from it);
    - add `pass_ok` to the row's list of statements, and `crates/ctmir/src/vectors.rs` to its file column, since `pass_ok` reads `FUEL` (vectors.rs:33);
    - the sentence on reading the claims "with `awk` by their `root `/`bounded ` prefixes" adds `pass `, which the coverage gate reads.
  - TRUSTED row 48, never-Stuck, in three parts (preflight C6):
    - **proved** (`pass_ok`): each `pass <path> steps=<n>` line's root reaches `Done` in `n` steps under `mir_run` on `wt_args` arguments, under the dump's `cpol`; every crypto `ok` root and every parser `bounded` root has one;
    - **verified, outside `report_sound`**: `check_vector`'s match of the return value and `mut:` pointees with the vector's;
    - **trusted**: that the wanted values are native's (the named tests, semconf's native generator).
    - Only `steps=` lines count as never-Stuck evidence. `pass .. panic` lines are none, since `Out::Panic` includes stuck states (sem.rs:1163-1166, :1225). Never-Stuck stays trusted for inputs not exercised, and for the fixtures and the negative control.
  - §8c result: Goal 4 met for the exercised inputs. In the follow-ups, replace the evaluator item with "never-Stuck proof (type soundness, or a backward simulation with typing premises)" and add "`lemma_mir_run_fuel_mono` with `ct_mir` over two fuels".
  - Fill the addendum's "8d result": verified count, timings, vector counts, findings and mutations.
- [ ] **Step 6: Commit** `feat(8d T4): every ok/bounded root reaches Done on a native vector (coverage gate); TRUSTED never-Stuck narrowed`.

---

## Preflight

| Pair / task | Shared files or interfaces | Finding |
|---|---|---|
| T1→T2 | `Tabs`/`tabs_ok`, `Halt`/`R`, `ECur`, `e_eval_ops`, `e_eval_place`, `e_store`, `e_exec_stmts` (frame in place), `e_mir_entry` | T2 consumes exactly T1's Produces. `e_mir_entry` returns `R`, so T2 maps `GaveUp` |
| T1→T3 | `x_wt_args`, `tabs` | consistent; `tabs`'s `None` is a pipeline `Err` in T3 |
| T2→T3 | `mir_eval`, `Ev`, `ev_ok`; `in_subset` from `theorem_lowers_in_subset(.., 0)` | `selftest`'s `Lowered` cache drops `infos` and every `lowers` fact; T3 caches `(Program, usize)` under a `root_of`/`in_subset` invariant (preflight C3) |
| T3 ↔ pipeline line writers | `line_ok` gains `pass_ok` | `info` proves `line_ok` for anything `no_claim` admits; `no_claim` excludes `pass `, a dedicated `pass_line` writer, and root/bounded writers refute the `pass ` prefix (preflight C3) |
| T3 gate mutation ↔ translator, ct-zarr | `ul_arr` `ZeroSized` constants | rejected before the evaluator runs, so the mutation replants on `PtrMetadata` of a `Shr` pointee instead (preflight C1) |
| T2 tests vs T3 deletion | T2's expected step counts come from the core selftest | T2 records them before T3 deletes `interp.rs` |
| T3→T4 | `scripts/ct-check.sh` (T3 edits comments and the 150 s bound; T4 adds the gate), `selftest.txt` (T4 only; its header names `interp` between T3 and T4), TRUSTED.md (T4 only: row 45's two sentences, statement list, file column and awk prefixes; row 48's three parts) | sequential: T4 after T3 (preflight C5, C6, M7) |
| T1..T3 ↔ `sem.rs` | a finding may edit `sem.rs` | a forced re-verify of all of ctmir (`sim*`, `lower*`, `pipeline`), a clean-room seat, and a `sem_sanity` fact |
| T1 self | first-match tables; `look.rs`'s one-way predicates; the arithmetic guards | `e_ul_val`/`e_mir_entry` need exact ones (`x_unit_like`, `x_ul_arr` are exact); `x_ty_free` only where a `false` is sound; `x_zst_dest` made exact in T2 (preflight M10); `x_bin_ok` new, `CheckedBinaryOp`/`*Unchecked` `GaveUp` (preflight C4) |
| T2 self | fuel and cost accounting | block 1 fuel, body call and glue 1 (fuel checked before `args_ok`, preflight M2), leaves 0; Drop glue `2 + steps`; steps in `u64` (overflow is `GaveUp`) |
| T3 self | `x_wt_args` on the 37 selftest and 31723 semconf vectors; the mutations | a vector that fails `x_wt_args` is a vector or `x_wt_args` finding; fix the vector or prove more, never weaken `wt_args`. Mutation 4 targets the producer (`passes`/`panics`), since weakening `pass_ok` cannot fail (preflight C2) |
| T4 self | native provenance of 14 new vectors; 4c owns quic | values only from named public tests or a crypto test; quic read-only |

## Rulings (2026-11-05)

All six accepted as recommended by the coordinator (ledger: `.superpowers/sdd/2026-11-05-phase-8d-mir-evaluator/progress.md`).

1. **Delete `interp.rs` and the core vector run.** Recommended: yes. `theorem_sim` makes a MIR `Done` imply the core run, so the core run adds no evidence and costs about 20 s. Cost if wrong: re-adding it is a revert.
2. **`pass_ok` in `line_ok`, with `wt_args`.** Recommended: yes. Without it, the report does not state what the coverage gate reads. Cost: one existential and its witness in `selftest`.
3. **Parser vectors for private fns, cited through public tests** (precedent: `vint_at`, `bytes_at`). Recommended: yes. The alternative, native unit tests in `crates/{wire,h3,quic}/src`, edits verified crates and quic (owned by 4c).
4. **The RSA vector in the crypto selftest run.** Recommended: yes, if the crypto selftest stays at most 150 s. Otherwise it gets its own `front` run with its own bound, after the per-type `ul_val` table (decision 5, preflight M1).
5. **Fuel monotonicity.** Decided: not in 8d (addendum decision 3), and listed as a follow-up. Override if the user wants `ct_mir` over two fuels now. That would be a fifth task touching `pipeline.rs`'s `ct_mir`/`theorem_ct_mir` and TRUSTED row 48.
6. **`GaveUp` on the gate.** Recommended: treat every `GaveUp` as evaluator work in Task 3 and do not ship with any. If one needs a large mirror, for example an `Unsup` arm never met, stop and report rather than widen the plan.
