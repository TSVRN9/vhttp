# Phase 8c: Verified MIR Front End — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the unverified MIR→core translator, the manifest and attribute readers, the verdict glue and the selftest interpreter with verified Verus code. The CT and cost results then trust only rustc, Verus, Z3, vstd, a decision-free MIR dumper, a JSON/schema spec and an independently written MIR semantics.

**Architecture:**
- `tools/ct-driver` becomes `ct-dump`: rustc_public values serialized with rustc's own serde, plus lookup tables.
- A new verified crate, `crates/ctmir`, parses that JSON and decodes it into a MIR AST. It gives the AST a clean-room semantics (`ctmir::sem`) and translates it to `ctcore::Program`, with a simulation proof. It then runs the existing verified checkers and emits the report bytes, with the end-to-end theorems in its ensures.
- `tools/ct-front` is I/O only.

**Tech Stack:**
- Verus 0.2026.10.04.426d8b0 and vstd =0.0.0-2026-10-04-0306;
- rustc 1.98.1 with rustc-dev (rustc_public, sysroot serde_json);
- the existing `ctcore`.

**Spec:** `docs/superpowers/specs/2026-11-03-phase-8c-verified-front-end-design.md`. Read it before any task: its trust table, §Dump, §JSON, §Schema, §MIR semantics (with its fixed modelling decisions 1–8), §Translator and simulation, §Pipeline and §Gate are binding.

## Global Constraints

- Every Verus function verifies at `--rlimit 4`.
  - A fresh target fails inside vstd at rlimit 4, so run a default `cargo verus verify` first.
  - `cargo verus` replays results after `cargo clean -p` when only the args change, so delete the `verus-partial` fingerprints before a re-run that must be real.
  - Rank slow functions by the `rlimit` field of `--output-json --time-expanded`.
  - nonlinear_arith is heavy-tailed: split the assert if one flips.
- No `assume`, no `external_body`, and no `#[verifier::external]` on anything a theorem relies on. `verify.sh`'s final line must say `escapes accounted (0)`.
- `crates/ctcore/src/*` is frozen. Do not edit it; lemmas about ctcore go in `ctmir`.
- `ctmir/Cargo.toml` is like `ctcore`'s: `vstd = "=0.0.0-2026-10-04-0306"`, `[package.metadata.verus] verify = true`, `ctcore = { path = "../ctcore" }`, plus a root `Cargo.toml` release profile entry `overflow-checks = false`.
- `tools/ct-front` has its own `[workspace]`, like `tools/ct-driver`. It contains no `verus!` code and no decisions.
- Report formats stay byte-compatible with today's, as `scripts/ct-check.sh` and `scripts/verify.sh` parse them:
  - `root <path> ok`
  - `reject <path> <Kind> <site> ..`
  - `checked <path> secret=<names> ret=<s|p>`
  - `declassify <fn>#<k> <file>:<line>`
  - `bounded <path> deg=<d> steps <= <text>`
  - `none <path> <Why>`
  - `pass/fail` selftest lines.
- Work in `/home/tavern/Projects/rust/web-server/.worktrees/wt-8c` (branch `phase-8c`), with its own `target/`. Never write to `/tmp`; scratch goes under `.worktrees/vt-8c-evidence/`.
- Commit messages carry no attribution or Co-Authored-By lines.
- Downloaded material, such as the MiniRust source, goes in its own directory under `.worktrees/vt-8c-evidence/dl/` and is only read. Any Python that touches it runs with `-I`.

## Review Focus

1. **A dump table missing an entry that `ctmir` needs must give `Unresolved`/`Unsupported`, never acceptance.** Task 5 has a test that deletes one `calls` entry and one `adts` entry from a dump and expects a reject.
2. **Clean-room independence of `ctmir::sem`.** The Task 4 reviewer reads it against MiniRust and the rustc_public types, and records every place it agrees with `translate.rs` only because both made the same choice that MIR's meaning does not force.
3. **Toolchain drift.** An unknown enum variant name must decode to `Unknown` and then be rejected. Task 3 has a test with a renamed variant.
4. **Uninitialized constant bytes (`null`) and pointer-tagged constants must be rejected.** Task 5 has tests.
5. **Labels.** A typo in a `ct::secret` name, a duplicate name, or an unlabelled root must reject, as today. Task 7 ports `translate.rs`'s `labels` unit tests as exec tests of `decl_spec`'s implementation.

---

### Task 1: The dump (`ct-dump`)

**Files:**
- Create: `tools/ct-driver/src/dump.rs`
- Modify: `tools/ct-driver/src/main.rs`, adding a `CT_MODE=dump` beside the old modes. The old modes stay working until Task 9, because the equivalence gate needs them.
- Create: `scripts/ct-dump.sh` (`analyse`-style: builds the driver and runs one dump per `<run> <crates> <manifest>`), sharing `ct-check.sh`'s flags.

**Interfaces:**
- Produces `$CT_OUT/<run>/mir-<crate>.json`, one compact JSON object per analysed crate. The format is exactly the spec's §Dump. The `key` is the existing `ct_key(&inst)`.
- Produces the dump tables named in the spec, and no others.

- [ ] **Step 1:** Write `dump.rs`. It walks the closure from every local fn item over `calls`/`drops` resolutions, filling the tables with `serde_json::to_string` of rustc_public values (`extern crate serde_json;` under `rustc_private`; the spike at `.worktrees/spike-json` shows the pattern). No `if` may depend on a value's meaning. Only "already visited?" checks and `Option`/`Result` unwrapping into `null` are allowed.
- [ ] **Step 2:** Run it on crypto, `tools/ct-fixtures`, the negative control and the parser crates (wire, h3, quic), with the same `cargo build` invocation `ct-check.sh` uses. Record each dump's size and wall time in the task report.
- [ ] **Step 3:** Write a self-check, `tools/ct-driver/src/dump.rs` `#[cfg(test)]`, over a hand-built `serde_json::Value`. Every `Ty` id referenced in `tys`/`adts`/bodies appears in `tys`; every `AllocId` in an allocation's provenance appears in `allocs`. Also run it as a `CT_MODE=dump` post-pass that fails the build on a dangling id, so the dump is closed by construction.
- [ ] **Step 4:** Commit `feat(ct-dump): decision-free MIR dump with lookup tables`.

### Task 2: `ctmir` scaffold and the verified JSON reader

**Files:**
- Create: `crates/ctmir/{Cargo.toml, src/lib.rs, src/json.rs}`
- Create: `crates/ctmir/tests/json.rs`
- Modify: root `Cargo.toml`, adding the release-profile entry.

**Interfaces:**
- Produces:

  ```
  pub enum Json { Null, Bool(bool), Num(bool, u128), Str(Vec<u8>), Arr(Vec<Json>), Obj(Vec<(Vec<u8>, Json)>) }
  pub open spec fn print(j: Json) -> Seq<u8>
  pub fn parse(b: &[u8]) -> (r: Option<Json>) ensures r matches Some(j) ==> print(j) == b@ && depth(j) <= 256
  pub fn obj_get<'a>(fields: &'a Vec<(Vec<u8>, Json)>, k: &[u8]) -> (r: Option<&'a Json>)   // with a spec twin
  ```

  `print` is serde_json's compact writer, per spec §JSON. `Num(neg, mag)` with `neg && mag == 0` is not printed by serde, and the parser rejects `-0`.

- [ ] **Step 1:** Write the exec tests in `tests/json.rs`. Each parses the given bytes and asserts the expected value: `null`, `true`, `[1,-2,{"a":"x\"\\\n\u0001é"}]`, `340282366920938463463374607431768211455`. Each of these is rejected: `[1, 2]` (whitespace), `01`, `-0`, `1.5`, `{"a":1,"a":2}`, `"A"` (serde writes `A` raw, so this is non-canonical), and 300 nested `[`.
- [ ] **Step 2:** Implement `parse` as an index-based recursive descent with a depth counter, and prove the `ensures`. Prove `print` injective only if a later task needs it.
- [ ] **Step 3:** Parse every Task 1 dump with a test binary or `cargo test -- --ignored` that reads `$CT_OUT`. Record the parse time for crypto's dump.
- [ ] **Step 4:** Verify at rlimit 4, run `cargo test -p ctmir`, add `ctmir` to the workspace (verify.sh already loops over `crates/*`), then commit.

### Task 3: The MIR AST and the schema decode

**Files:**
- Create: `crates/ctmir/src/mir.rs` (the datatypes), `crates/ctmir/src/schema.rs` (the spec `decode_*` and the exec decoders), `crates/ctmir/tests/schema.rs`.

**Interfaces:**
- Produces `pub struct MirCrate { crate_name, items, insts, calls, drops, tys, adts, consts, layouts, allocs, spans }`, mirroring spec §Dump. Bodies follow rustc_public:
  - `Body`, `LocalDecl`, `BasicBlock`, `Statement`/`StatementKind`, `Terminator`/`TerminatorKind`;
  - `Place`/`ProjectionElem`, `Operand`, `ConstOperand`/`MirConst`/`ConstantKind`, `Allocation`;
  - `Rvalue`, `BinOp`, `UnOp`, `CastKind`, `PointerCoercion`, `AggregateKind`, `BorrowKind`, `SwitchTargets`;
  - `TyKind`/`RigidTy`, `IntTy`/`UintTy`, `GenericArgs`, `TyConst`;
  - `LayoutShape`/`FieldsShape`/`VariantsShape`/`TagEncoding`/`Scalar`/`Primitive`, `GlobalAlloc`, `VarDebugInfo`.

  Each enum has a final `Unknown(Json)` variant. Fields the semantics never reads are `Json`.
- Produces `pub open spec fn decode_crate(j: Json, m: MirCrate) -> bool` and `pub fn decode(j: Json) -> (r: Option<MirCrate>)`. Its ensures: `Some(m) ==> decode_crate(j, m)`, and `None ==> forall m. !decode_crate(j, m)`. The relation form is ruled; see the ledger.
- Rule: a body that contains an `Unknown` is still decoded. The decision to reject it belongs to the translator. `None` means only that the JSON does not have the shape serde would write for these types.

- [ ] **Step 1:** Write the tests:
  - decode a committed tiny dump, `crates/ctmir/tests/data/tiny.json`, made by Task 1's dumper from the spike's `t.rs` plus one enum constant and one call, and assert three chosen fields;
  - a renamed variant decodes to `Unknown`;
  - a struct whose fields are out of order decodes to `None`.
- [ ] **Step 2:** Implement and prove the decode, following serde's conventions (spec §Schema). Check each type side by side with `$(rustc --print sysroot)/lib/rustlib/rustc-src/rust/compiler/rustc_public/src`, and put the rustc_public file:line in a doc comment on each mirrored type.
- [ ] **Step 3:** Decode every Task 1 dump. Report how many bodies contain an `Unknown`, and where.
- [ ] **Step 4:** Verify at rlimit 4, test, commit.

### Task 4: `ctmir::sem` — the MIR semantics, clean room

**Files:**
- Create: `crates/ctmir/src/sem.rs`, `crates/ctmir/src/sem_sanity.rs`

**Clean-room rule (binding, spec §MIR semantics):**
- The implementer must not open:
  - `tools/ct-driver/src/translate.rs`;
  - `tools/ct-driver/src/interp.rs`;
  - `crates/ctcore/src/sem.rs` past the "frames and places" heading;
  - the 8a/8b spec's §Front end.
- It may import from `ctcore::sem` exactly the shared vocabulary the spec lists.
- Its sources are the rustc_public types, the MiniRust specification (clone github.com/minirust/minirust into `.worktrees/vt-8c-evidence/dl/minirust` and read it there), the rustc dev guide's MIR chapter, and the spec.
- The report lists every source consulted.

**Interfaces:**
- Produces:

  ```
  pub open spec fn mir_run_fn(m: MirCrate, pol: CallPolicy /* declassify and ghost paths */, i: nat /* insts index */, fr: Frame, fuel: nat) -> Res
  pub open spec fn mir_entry(m: MirCrate, i: nat, args: Seq<Val>, slots: Seq<Val>) -> Frame
  pub open spec fn wt_val(m: MirCrate, ty: TyId, v: Val) -> bool   // the value is a well-typed value of `ty`
  pub open spec fn std_model(key: Seq<u8>, gargs: GenericArgs) -> Option<StdFn>
  pub open spec fn decode_const(m: MirCrate, ty: TyId, a: Allocation, off: nat) -> Option<Val>
  ```

  Everything follows the spec's fixed decisions 1–8: the run shape, no unwinding, the `&`/`&mut` model, Drop via glue, constants by layout, the leakage table, the cost table (with the ADT-constant charge) and the std model rows equal to today's `intr` lines at today's admitted types.

- [ ] **Step 1:** Write `sem_sanity.rs` first. Each item is a proof of a concrete fact:
  - the `tiny` body from `tests/data/tiny.json` (Task 3), hand-built as a `MirCrate` value, returns `a[i&3] ^ 2`. Its events and steps are computed by hand from that MIR and the spec's tables. For the spike's MIR these are `[Cond(1), Idx(i&3)]` and 7 steps: 3 assignments, the Assert, 2 assignments and the Return; StorageLive/Dead cost 0;
  - `Drop` of a `Vec<u8>` local is a no-op on the frame;
  - an `Option<NonZeroU8>`-shaped niche constant decodes to `Adt(0, [])` for byte 0;
  - a call with a `&mut` argument writes the callee's slot back.

  The exact step and event counts come from the spec's tables. Compute them by hand, and put the arithmetic in comments.
- [ ] **Step 2:** Write `sem.rs`, and prove the sanity facts at rlimit 4.
- [ ] **Step 3:** Commit, then report. The reviewer does the independence check (Review Focus 2).

### Task 5: The translator (`ctmir::lower`)

**Files:**
- Create: `crates/ctmir/src/lower.rs` (exec translator), `crates/ctmir/src/rel.rs` (`spec fn lowers_*`: the per-construct relation between a MIR item and its core image), `crates/ctmir/tests/lower.rs`.

**Interfaces:**
- Consumes: `MirCrate` and `ctcore::syntax`.
- Creates `crates/ctmir/src/policy.rs` with only `pub struct Policy { roots, cost_roots, labels: Vec<(Vec<u8>, Vec<Vec<u8>>, Vec<Vec<u8>>)>, internal_crates, translate_crates }`. Its tests build values directly; Task 7 adds the parser. `FnInfo` carries `attrs: Vec<Vec<u8>>` and no `decl`/`attr_err`: Task 7 computes the labels.
- Produces:

  ```
  pub struct FnInfo { path: Vec<u8>, is_root: bool, attrs: Vec<Vec<u8>>, param_names: Vec<Vec<u8>>, block_sites: Vec<Vec<u8>>, declassify_sites: Vec<Vec<u8>>, stmt_sites: Vec<Vec<Vec<u8>>>, inst: usize }
  pub enum Reject { Unsupported { path, what, site }, Unresolved { path, callee, site }, Attr { path, msg }, Root { path, msg } }
  pub fn lower(m: &MirCrate, pol: &Policy, root: &[u8]) -> (r: Result<(Program, Vec<FnInfo>), Vec<Reject>>)
      ensures r is Ok ==> lowers(m, pol, root, r->Ok_0.0, r->Ok_0.1) && ctcore::sem::wf(r->Ok_0.0)
  ```

  `lowers` says:
  - fn 0 is the root;
  - each fn `g` is the image of `insts[infos[g].inst]`;
  - locals and blocks are 1:1 and in `reach(body)`, with all others `Abort`;
  - each statement, terminator, operand, place and type is related by its `lowers_*` relation;
  - each `Callee::Intr(k)` callee has `std_model(key, gargs) == Some(k-row)`;
  - each `Callee::Fn(h)` callee is internal by policy and resolved through `calls`;
  - each `Drop` goes through its `drops` glue (empty → `Goto`; Vec leaf → the Vec-drop intrinsic image the semantics names; otherwise a `Call` of the glue fn).
- Rule: if Drop-glue translation needs a core form that ctcore lacks, express it with existing core forms, or reject. Never extend ctcore.

- [ ] **Step 1:** Write the tests:
  - `tiny.json` lowers to the expected 2-block core body;
  - deleting a `calls` entry gives `Unresolved`, and deleting an `adts` entry gives `Unsupported` (Review Focus 1);
  - a `null` constant byte gives `Unsupported`, and a pointer in an integer constant gives `Unsupported` (Review Focus 4);
  - two instances sharing a key give `Reject::Root`/`Unsupported` "ambiguous key".
- [ ] **Step 2:** Implement and prove `ensures`.
- [ ] **Step 3:** Over the Task 1 dumps: for every crypto, fixture and parser root, lower with the new translator and translate with the old one (still present). Diff the two `Program`s through a debug printer in the test, a test-only `Debug` outside `verus!`. Every difference must be either Drop glue (expected) or a bug in one of the two. Record the classification in the report.
- [ ] **Step 4:** Verify at rlimit 4, test, commit.

### Task 6: The simulation proof

**Files:**
- Create: `crates/ctmir/src/sim.rs`, plus `sim_*.rs` splits as needed.

**Interfaces:**
- Produces:

  ```
  pub proof fn theorem_sim(m: MirCrate, pol: Policy, root: Seq<u8>, p: Program, infos: Seq<FnInfo>, g: nat, args: Seq<Val>, slots: Seq<Val>, fuel: nat)
      requires lowers(m, pol, root, p, infos), g < p.fns.len(), wt_args(m, infos[g].inst, args, slots)
      ensures mir_run_fn(m, pol, infos[g].inst, mir_entry(m, infos[g].inst, args, slots), fuel) is Some ==>
              ctcore::sem::run_fn(p, g, ctcore::sem::init_entry(p, g, args, slots), fuel)
                == mir_run_fn(m, pol, infos[g].inst, mir_entry(m, infos[g].inst, args, slots), fuel)
  ```

  This is the exact form. If a construct forces the fallback, the fallback is spec §Translator's weaker form, and the report says which constructs needed it.
- Produces `pub proof fn lemma_entry_premises(...)`: `wt_args` implies `ctcore::cost::entry_plc`, `vals_len_ok(args)` and `vals_len_ok(slots)`.

- [ ] **Step 1:** Write the per-construct lemmas: place walk, operand (including constants: `decode_const` against the core `Const`/`Lit`/temp image), rvalue, statement, intrinsic and std row, call enter/leave, Drop, and switch/assert/goto/return.
- [ ] **Step 2:** Prove the block and run induction on fuel, with the reachable-set invariant.
- [ ] **Step 3:** Verify at rlimit 4 and commit. If the call case resists, land the call-free form as the spec's fallback allows, open a TRUSTED row draft in the report, and stop for a ruling.

### Task 7: The pipeline, the end-to-end theorems and `ct-front`

**Files:**
- Modify: `crates/ctmir/src/policy.rs`, adding the manifest grammar spec and the verified parser for the `Policy` struct from Task 5: `root`, `label`, `cost-root`, `internal-crate`, `translate-crate`; `intr` lines are rejected as obsolete; `decl_spec` for `ct::` attributes), `crates/ctmir/src/pipeline.rs`, `crates/ctmir/src/text.rs` (report line spec and exec renderers, including `poly_text_spec`/`atom_text_spec` and reject texts), `crates/ctmir/tests/policy.rs`.
- Create: `tools/ct-front/{Cargo.toml, src/main.rs}`.

**Interfaces:**
- Produces:

  ```
  pub enum Mode { Check, Cost, Selftest(Vec<u8> /* vectors file */) }
  pub fn pipeline(dump: &[u8], manifests: &Vec<Vec<u8>>, mode: &Mode) -> (r: Result<Vec<u8>, Vec<u8>>)
      ensures r is Ok ==> report_sound(dump@, manifests@, mode, r->Ok_0@)
  ```

  `report_sound` is spec §Pipeline. The `root ok` lines carry the CT conclusion (theorem_ct carried by theorem_sim) and the `bounded` lines the cost conclusion (theorem_cost carried by theorem_sim plus `lemma_entry_premises`). The text equals `poly_text_spec`.
- `ct-front <mode> <dump.json> <out-file> <manifest>...` reads the files, calls `pipeline`, and writes `Ok` to the out-file or `Err` to stderr with exit 1.

- [ ] **Step 1:** Port `translate.rs`'s `labels` unit tests and `manifest.rs`'s tests to `tests/policy.rs`, against the verified implementations.
- [ ] **Step 2:** Implement and prove. Report lines sort and dedupe as `main.rs` does today: a BTreeSet ordering of the lines' bytes, the first two words of a reject deduped per root, declassify numbering per fn in site order.
- [ ] **Step 3:** Run `ct-front` over every Task 1 dump in each mode, beside the old driver's reports, and diff them. Every difference is recorded in the report and classified.
- [ ] **Step 4:** Verify at rlimit 4, test, commit.

### Task 8: The verified interpreter, selftest and conformance

**Files:**
- Create: `crates/ctmir/src/interp.rs`, `crates/ctmir/src/vectors.rs` (the selftest line grammar, ported from `interp.rs`'s parser: spec and verified parser).
- Create: `tools/ct-fixtures/semconf/{Cargo.toml, src/lib.rs, tests/vectors.rs}`.
- Modify: `crates/ctmir/src/pipeline.rs` (`Mode::Selftest`).

**Interfaces:**
- Produces `pub fn interp(p: &Program, g: usize, args: &Vec<CVal>, slots: &Vec<CVal>, fuel: u64) -> (r: Option<(CVal, Vec<CVal>, u64)>)`. Its ensures: `r` views to the return local and the slots of `run_fn(p, g, init_entry(...), fuel)` when that run is `Some` and fits u64, and `r is None` when the run is `None`. `CVal` is an exec value type with `view() -> Val`.
- `semconf` covers the constructs in the spec's §Verified interpreter. Its test writes `target/semconf-vectors.txt` in `selftest.txt`'s format from native runs, seed `0x8c8c8c8c`, with 64 inputs per fn plus the edge values `0`, `1`, `MAX`, `MIN` and `-1`. It also includes the two regression vectors.

- [ ] **Step 1:** Write `semconf` and its vector-writing test. Run it and commit the generated vectors file as `tools/ct-fixtures/semconf/vectors.txt`. `ct-check.sh` regenerates it and diffs, so a native change shows up.
- [ ] **Step 2:** Implement and prove `interp`, and wire `Mode::Selftest`.
- [ ] **Step 3:** Both `selftest.txt` (crypto and parsers) and `semconf/vectors.txt` must pass through `ct-front`. A failure is a semantics finding: fix the semantics (Task 4's file) or the translator, never the vector.
- [ ] **Step 4:** Verify at rlimit 4, test, commit.

### Task 9: Equivalence gate, switch-over, deletion, docs

**Files:**
- Modify: `scripts/ct-check.sh` (dump → `ct-front` for every run; add the semconf run and the labels pin, a new file `tools/ct-driver/expected-labels.txt` with every `checked` line of crypto's report), `scripts/verify.sh` (the final-line counts are unchanged).
- Delete: `tools/ct-driver/src/{translate.rs, interp.rs, manifest.rs}` and the decision logic in `main.rs`, the `intr` lines from the manifests, and `CT_MODE` `check`/`census`/`selftest`/`cost`.
- Modify: `TRUSTED.md` (spec §Gate), `docs/superpowers/specs/2026-10-28-phase-8-verified-ct-cost-design.md` (a pointer from §Front end to the 8c spec), and the 8c spec (a "## 8c result" section with the final trust table filled in).

- [ ] **Step 1:** Run the equivalence gate: old `ct-check.sh` against the new pipeline on the same tree. Paste both summaries and the classified diff into the report. Every difference must already be justified by Task 5/7 classifications; otherwise stop.
- [ ] **Step 2:** Switch, delete, and update the expected files only where the gate justified it.
- [ ] **Step 3:** Run `scripts/verify.sh`. Its final line must read `verify.sh: all crates verified, duvet ok, ct ok (10 declassify), cost 19/36, escapes accounted (0)`, unless the gate justified different numbers. Also run `cargo test` at the workspace root and in `tools/ct-driver` and `tools/ct-front`, with 0 warnings.
- [ ] **Step 4:** Commit.
