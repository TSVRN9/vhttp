# Phase 8b: Verified step-bound analyser for attacker-reachable parsers (attempt) — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** For each target parser function, either prove `steps <= eval(b, inputs)` for a polynomial `b` in its input lengths, or report `None` with a reason.
- **The deliverable is the coverage number**: bounded targets out of all targets, compared with the spec's pre-registered predictions (27 of 38).
- A step bound is **not** wall-clock time and **not** memory (spec §Cost analyser).

**Spec:** `docs/superpowers/specs/2026-10-28-phase-8-verified-ct-cost-design.md`, §Cost analyser and D8/D9. 8a's plan, `docs/superpowers/plans/2026-10-28-phase-8a-ct-checker.md`, fixed the shared interfaces this plan consumes:
- `ctcore::syntax::*`;
- `sem.rs`'s `run_fn`/`run_from`/`exec_stmts`/`exec_intr`/`call_enter`/`call_leave`/`init_entry`/`len_ok`, with steps in `Res`;
- `ct.rs`'s `wf`;
- the driver's `translate_closure()` and its manifest (preflight). `translate_closure` is label-free; 8a's check mode applies the root-label rule separately.

**Branch:** `phase-8b`, cut from `main` **after `phase-8a` merges**. The escape count stays at main's value (4, or 3/2 if 5c landed).

**Architecture.** All new code is additive. **No 8a file changes**, except `crates/ctcore/src/lib.rs` (new `mod` lines and re-exports), `tools/ct-driver/src/main.rs` (the `cost` mode), `tools/ct-driver/src/manifest.rs` (the `cost-root` kind; 8a's loader rejects unknown kinds), `tools/ct-fixtures/src/lib.rs` (cost fixtures) and `scripts/ct-check.sh` (preflight).
- `crates/ctcore/src/cost.rs` holds the trusted cost spec:
  - atoms, polynomials, facts and certificates;
  - `cert_sem_ok`/`cert_for`;
  - `theorem_cost`.
- `crates/ctcore/src/cost_sym.rs` holds the abstract block effect, as spec plus lemmas.
- `crates/ctcore/src/cost_check.rs` holds the verified validator, `check_cert(..) ==> cert_for(..)`.
- `crates/ctcore/src/loops.rs` holds the untrusted inference: dominators, natural loops, counted loops and potentials. Its only route to a `Some` is through `check_cert`.

**Tech Stack:** as 8a. No new dependencies.

## Global Constraints (copy verbatim into every task brief)

*8a's Global Constraints, repeated verbatim with the 8b deltas marked **[8b]**:*

- **Escapes.**
  - `crates/ctcore` adds **zero** escapes, and the `verify.sh` count stays at main's value **[8b: read it from main's verify.sh line at branch time and write it in every report]**.
  - The gate greps every `*.rs` under `crates/`, code *and* comments, for `assume(`, `admit(`, `external_body`, `assume_specification`, `verifier::external`/`verifier(external` and the bare word `axiom`.
  - Never write those strings in `crates/` (write "premise", "hypothesis").
  - Never name a lemma `*assume*` or `*axiom*`.
- **No new dependencies.** `ctcore` depends on vstd only. `ct-driver` depends on the `rustc_*` crates and `ctcore`. Text formats are parsed by hand.
- **Toolchain.**
  - The pinned 1.98.1 from `rust-toolchain.toml`.
  - `export PATH=$HOME/.local/opt/verus/0.2026.10.04.426d8b0/verus-x86-linux:$PATH`.
  - `RUSTC_BOOTSTRAP=1` only inside `scripts/ct-check.sh`.
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
  - **[8b]** 8a's `syntax.rs`, `sem.rs`, `ct.rs`, `ct_lemmas.rs`, `ni.rs`, `check.rs` and `infer.rs` are frozen for the whole phase. `git diff main -- <those files>` must be empty in every commit.
  - From the end of Task 2, `cost.rs`'s spec fns and the `theorem_cost` statement are frozen too.
  - A change to either needs a `SPEC-CHANGE:` paragraph and a controller ruling.
  - **A target that needs a new intrinsic or a semantics change is a `None` (`Unresolved`), never a reason to edit 8a's semantics.**
- **The four checks, every task:**
  1. ctcore verifies at `--rlimit 4`: `0 errors`.
  2. `cargo build && cargo test && cargo build --release`: 0 warnings.
  3. `scripts/verify.sh` prints its success line with main's escape count (**[8b]** from Task 7, with `cost X/Y`).
  4. `scripts/ct-check.sh` exits 0 with the summary the task names.
- **Evidence run.** `CARGO_TARGET_DIR` and `CT_TARGET_DIR` under `/tmp/claude-1000/-home-tavern-Projects-rust-web-server/19d690a3-7cab-4802-bc1f-9aa0173a905e/scratchpad/` (`vt-8b-tN`, `ct-8b-tN`), absolute. `rm -rf` both after. The tmpfs is 16 GB shared.
- **Proof-time budget.** Report the five slowest functions. No function may exceed 10 s. ctcore's total must stay under 90 s **[8b: was 60 s]**.
- **Mutations** fail on a named postcondition or expected line, never on rlimit. Revert immediately.
- **Never weaken a test**, and never flip an expected verdict to pass a run. A bounded target turning `None` is a regression; stop and report it.
- **[8b] The inference is untrusted.**
  - Give `loops.rs` no proof obligations beyond termination and memory safety.
  - Every `Some` an API returns must pass through `check_cert` on the final summary vector.
- **[8b] Degree ≤ 2.**
  - Monomials have at most 2 atoms, kept in canonical order (`atom_lt`).
  - Coefficient arithmetic is checked: an overflow means `None`.
  - Put a `ponytail:` comment on the degree cap: higher degree needs a multiset-product lemma.
- **No edits outside a task's Files list. Plan code is signatures only.**

## Review Focus

1. **The statement is the spec's.** `theorem_cost` matches the spec text. `cert_for` requires entry facts to be empty and `sums[f] == Some(pot[0])`. `cert_sem_ok` quantifies over **all** callee outcomes within the summary (dst and `&mut` targets havocked).
2. **There is no unchecked route to `Some`.** `analyze`'s ensures comes from `check_cert` on the final vector. `loops.rs` output never reaches the report without it.
3. **Honesty of the number.**
   - The coverage line equals `cost-expected.txt`.
   - Every divergence from the spec's pre-registered table is explained in the Task 7 report.
   - Every `None` has a reason.
4. **Non-vacuity.**
   - Task 2's proof mutations fail.
   - Tampered certificates are rejected (Task 4).
   - Negative cost fixtures stay `None`.
   - A seeded unbounded loop in a real target is `None` (Task 7).
5. **Wording.** TRUSTED.md, the spec and the report say "steps", never "time"; and "not memory; Vec growth hidden".
6. **8a freeze held.** The `git diff` of 8a's files is empty.

---

### Task 1: Baseline, target census and pre-registration check (no commit)

**Files:** none in the repo. Scratch output goes under the scratchpad.

**Consumes:** merged 8a.

- [ ] **Step 1: 8a interfaces present.**
  - `grep -n 'pub open spec fn \(run_fn\|run_from\|exec_stmts\|exec_intr\|call_enter\|call_leave\|init_entry\|len_ok\|wf\)(' crates/ctcore/src/*.rs` finds each exactly once. The `(` keeps `wf` from also matching `wf_body` (preflight).
  - `Res` is `Option<(Frame, Seq<Event>, nat)>`.
  - Record the escape count from `scripts/verify.sh`.
- [ ] **Step 2: Census.**
  - Write a scratch manifest with `root` lines for the spec's 38 target def paths. Get exact paths by `grep`, and for `<QuicVarInt<_> as Parser>::parse` from census output.
  - Add `translate-crate wire` (and `vest_lib` if the census shows trait plumbing through it).
  - Run the driver in `CT_MODE=census` over `wire`, `h3` and `quic` (`CT_CRATES=wire,h3,quic cargo build --release -p wire -p h3 -p quic`).
  - Record every reached callee with no 8a intrinsic mapping. Each one makes its callers `Unresolved`, so list those targets as `None (unresolved: <callee>)`.
  - **vest_lib bodies.** If the census needs vest_lib bodies, check their release MIR for `*WithOverflow` (it is there under the base profile's `overflow-checks = true`). Escalate for a ruling: a `[profile.release.package.vest_lib] overflow-checks = false` override plus a TRUSTED note, or accept the `None`s.
- [ ] **Step 3: Loop classification.**
  - Dump the MIR with `RUSTC_BOOTSTRAP=1 cargo rustc --release -p <crate> -- -Zinline-mir=no -Zunpretty=mir > <scratch>/<crate>.mir` (in a scratch target dir).
  - For each target, list its back edges and the guard/increment pattern.
  - Compare with the spec's table. Every row that changes gets a one-line reason.
- [ ] **Step 4: Report** the final target list (the denominator Y), the revised predictions, and the Unresolved list. Stop for a ruling only if Y < 25 or more than 5 targets are Unresolved.

---

### Task 2: Cost spec and `theorem_cost` (semantic certificates)

**Files:**
- Create: `crates/ctcore/src/cost.rs`
- Modify: `crates/ctcore/src/lib.rs` (`pub mod cost;`)

**Consumes:** `sem.rs` (`run_from`, `exec_stmts`, `exec_intr`, `call_enter`, `call_leave`, `init_entry`, `len_ok`) and `ct.rs` (`wf`).

**Interfaces (produces):**
- **Exec types**, used by the spec through `@`:
  - `pub enum Atom { Const(u64), Val(usize), Len(usize), Gap(Box<Atom>, Box<Atom>) }`;
  - `pub struct Mono { pub coef: u64, pub atoms: Vec<Atom> }` (≤ 2 atoms);
  - `pub struct Poly { pub monos: Vec<Mono> }`;
  - `pub enum Fact { Le(Atom, Atom), Lt(Atom, Atom) }`;
  - `pub struct BlockCert { pub facts: Vec<Fact>, pub pot: Poly }`;
  - `pub struct Cert { pub blocks: Vec<BlockCert> }`.
- **Spec values** (`pub open spec fn`):
  - `val_nat(v: Val) -> nat`: `Int(x)` gives x; anything else gives 0.
  - `len_nat(fr: Frame, v: Val) -> nat`: the length of the `Arr` reached through `Shr`/`Mut`; 0 otherwise.
  - `atom_val(fr: Frame, a: Atom) -> nat` (`decreases a`). `Gap(a, b)` is `if a >= b { a - b } else { 0 }`.
  - `mono_val(fr, m) -> nat`, `poly_val(fr: Frame, p: Poly) -> nat`.
  - `fact_holds(fr, f) -> bool`, `facts_hold(fr, fs: Seq<Fact>) -> bool`.
  - `frame_len_ok(fr: Frame) -> bool`: `len_ok` of every local and slot.
- **Block and certificate conditions:**
  - `block_step_ok(p: Program, f: nat, b: nat, c: Cert, sums: Seq<Option<Poly>>, fr: Frame) -> bool`, per the spec §Cost analyser. Its parts:
    - `k = stmts.len()`, `fr1 = exec_stmts(..).0`;
    - `Goto`/`Switch` (taken target)/`Assert` (on success): the successor's facts hold at `fr1`, and `poly_val(fr, pot_b) >= k + 1 + poly_val(fr1, pot_succ)`;
    - `Return`: `>= k + 1`;
    - `Abort`: true;
    - `Call(Intr)`: on `Some((fr2, _, extra))`, the next block's facts at `fr2` and `>= k + 1 + extra + pot_next(fr2)`;
    - `Call(Fn(g))`: `sums[g] is Some`, and `forall|out: Frame, n: nat| frame_len_ok(out) && n <= poly_val(call_enter(..).0, sums[g].unwrap())` ⇒ next facts at `fr2 = call_leave(fr1, out, wb, dst).0` and `>= k + 1 + n + pot_next(fr2)`.
  - `cert_sem_ok(p, f, c, sums) -> bool`: `c.blocks@.len() == nblocks(f)`, and for all b and fr, `facts_hold(fr, c.blocks@[b].facts@) && frame_len_ok(fr) ==> block_step_ok(p, f, b, c, sums, fr)`.
  - `cert_for(p, f, c, sums) -> bool`: `cert_sem_ok` ∧ `c.blocks@[0].facts@.len() == 0` ∧ `sums[f] == Some(c.blocks@[0].pot)`.
- **Lemmas:**
  - `proof fn lemma_run_len_ok(p, f, b, fr, fuel)`: `frame_len_ok(fr)` and `run_from(..) is Some` imply `frame_len_ok(final)`.
  - `proof fn lemma_exec_stmts_len_ok(..)`, `proof fn lemma_intr_len_ok(..)`.
  - `proof fn cost_from(p, certs, sums, f, b, fr, fuel)`, `decreases fuel`:
    - requires `wf(p)`, all-`cert_for` (as in the theorem), `sums[f] is Some`, `facts_hold(fr, certs[f].blocks@[b].facts@)`, `frame_len_ok(fr)` and `run_from(p, f, b, fr, fuel) is Some`;
    - ensures `steps <= poly_val(fr, certs[f].blocks@[b].pot)`.
- **The theorem:** `pub proof fn theorem_cost(..)`, exactly the spec's statement, with the premise `forall|g: int| 0 <= g < p.fns@.len() && sums[g] is Some ==> cert_for(p, g as nat, certs[g], sums)` and `certs.len() == sums.len() == p.fns@.len()`.

- [ ] **Step 1:** Write the spec fns. `lemma_run_len_ok` comes first, since it relies on 8a's overflow-gives-`None` rule for push/extend/to_vec. If that rule is missing from 8a's `sem.rs`, stop: that's a SPEC-CHANGE to 8a.
- [ ] **Step 2:** Prove `cost_from` (one case lemma per terminator kind, plus the dispatcher) and `theorem_cost`.
- [ ] **Step 3: Proof mutations**, each failing a named lemma:
  - `block_step_ok`'s `Return` requires `>= k` instead of `>= k + 1`;
  - the `Call(Fn)` case drops `n`;
  - `cert_for` drops `facts@.len() == 0`, so `theorem_cost` can't discharge the entry facts;
  - `Gap` defined as `a - b` in int (no saturation), which fails the nat typing.
- [ ] **Step 4: Run the four checks and the evidence run.** The cost spec freeze starts after this commit.
- [ ] **Step 5: Commit:** `feat(ctcore): step-bound certificates and theorem_cost (steps <= summary(inputs))`

---

### Task 3: Abstract block effect (`cost_sym.rs`): spec and soundness lemmas

**Files:**
- Create: `crates/ctcore/src/cost_sym.rs`

**Consumes:** `cost.rs` (Task 2), `sem.rs`.

**Interfaces (produces):**
- **Types** (exec, used by the spec):
  - `pub enum Rel { Same, ValEq(Atom, u64 /* + k */), ValLe(Atom), LenEq(Atom), LenLe(Atom), Unknown }`: each local's post-state value in terms of pre-state atoms;
  - `pub struct Eff { pub rel: Vec<Rel>, pub edge: Vec<(usize /* succ block */, Vec<Fact> /* post-state facts on that edge */)> }`.
- **Spec:**
  - `pub open spec fn mut_taken(b: Body, x: nat) -> bool`: some `RefMut` place in the body is rooted at x.
  - `pub open spec fn rel_sound(rel: Rel, x: nat, pre: Frame, post: Frame) -> bool`.
  - `pub open spec fn eff_sound(e: Eff, pre: Frame, post: Frame, succ: nat) -> bool`: every `rel` is sound, and the edge facts for `succ` hold at `post`.
- **Transfer:** `pub open spec fn sym_block(b: Body, blk: Block, facts: Seq<Fact>) -> Eff`, recognizing exactly:
  - `x = Copy(y)` (int), giving `ValEq(Val(y), 0)`;
  - `x = Const(c)`, giving `ValEq(Const(c), 0)`;
  - `x = Bin(Add, ty, Copy(x), Const(1))` and `Wrapping(Add, ty)(x, 1)`, giving `ValEq(Val(x), 1)`, **only if** a pre-fact `Lt(Val(x), A)` exists with `A` a `Const` ≤ `max(ty)`, a `Val` of a local of the same `IntTy`, or a `Len` with `ty == Usize`;
  - `x = Len(pl)`/`VecLen`, giving `ValEq(Len(root), 0)`;
  - `x = RefShr(y)`/`VecAsSlice(y)`, giving `LenEq(Len(y))`;
  - `SliceSubrange(r, ..)`, giving `LenLe(Len(r))`;
  - `SliceToVec(r)`, giving `LenEq(Len(r))`;
  - every other assignment to x, and every local in `mut_taken` after any write-through or call, gives `Unknown`;
  - untouched locals give `Same`.
  - **Edge facts:**
    - `Switch(Copy(c))` where c was set in this block by `Bin(Lt, _, a, b)` and is unchanged afterwards: `Lt(a', b')` on the non-zero target and `Le(b', a')` on the zero target, with a′, b′ the atoms of the operands' post values;
    - `Gt`/`Ge`/`Le` likewise;
    - the `Assert(Lt(..), true, b)` success edge gives `Lt`.
- **Lemmas:**
  - `proof fn lemma_sym_block_sound(p, f, b, blk, facts, fr)`: requires `facts_hold(fr, facts)` and `frame_len_ok(fr)`; ensures `eff_sound(sym_block(..), fr, exec_stmts(..).0, succ)` for the successor the terminator actually takes.
  - **Per-pattern lemmas:** `lemma_rel_copy`, `lemma_rel_const`, `lemma_rel_inc` (the no-wrap argument, from the `Lt` fact and the width bound), `lemma_rel_len`, `lemma_rel_shr`, `lemma_rel_subrange`, `lemma_edge_lt`.

- [ ] **Step 1:** Write `lemma_rel_inc` first, as the bounded probe. If it needs `nonlinear_arith` with more than one product, or rlimit > 4 after one split, stop and report.
- [ ] **Step 2:** Write the remaining lemmas and `lemma_sym_block_sound`.
- [ ] **Step 3: Mutations**, each failing a named lemma:
  - the increment rule without the `Lt` pre-fact (`lemma_rel_inc`);
  - `SliceSubrange` as `LenEq` (`lemma_rel_subrange`);
  - `mut_taken` ignored, so a write through `Mut` keeps `Same`.
- [ ] **Step 4: Run the four checks and the evidence run.**
- [ ] **Step 5: Commit:** `feat(ctcore): sound abstract block effect for cost certificates (counter increment, lengths, edge facts)`

---

### Task 4: Verified validator `check_cert`

**Files:**
- Create: `crates/ctcore/src/cost_check.rs`, `crates/ctcore/tests/cost_check.rs`

**Consumes:** Tasks 2 and 3.

**Interfaces (produces):** all `pub fn`, each with the stated `ensures`.
- **Atom order:** `atom_lt(a: &Atom, b: &Atom) -> (r: bool)`, a total strict order with its spec twin `spec_atom_lt`.
- **Polynomial operations:**
  - `poly_add(a: &Poly, b: &Poly) -> (r: Option<Poly>)` ensures `r matches Some(q) ==> forall fr. poly_val(fr, q@) == poly_val(fr, a@) + poly_val(fr, b@)`;
  - `poly_dominates(lhs: &Poly, rhs: &Poly, extra: u64) -> (r: bool)` ensures `r ==> forall|fr| poly_val(fr, lhs) >= poly_val(fr, rhs) + extra`. It works by syntactic monomial matching on canonical atom lists with coefficient ≥, with `extra` taken from the constant monomial.
- **Rewrites:**
  - `rewrite_pre(p: &Poly, e: &Eff, facts: &Vec<Fact>) -> (r: Option<Poly>)` ensures `r matches Some(q) ==> forall|pre, post, s| facts_hold(pre, facts@) && eff_sound(*e, pre, post, s) ==> poly_val(pre, p) >= poly_val(post, q)`. It rewrites pre-atoms into post-atoms:
    - a `Gap(A, Val(i))` with `ValEq(Val(i), 1)` and a pre-fact `Lt(Val(i), A)` becomes `Gap(A, Val(i))′ + 1`, expanded;
    - `Same` atoms are kept;
    - monomials over `Unknown` atoms are dropped (sound for the LHS).
  - `bound_post(p: &Poly, e: &Eff, post_facts: &Vec<Fact>) -> (r: Option<Poly>)` ensures `r matches Some(q) ==> forall|fr| facts_hold(fr, post_facts@) ==> poly_val(fr, q) >= poly_val(fr, p)`. It applies the upper-bound rewrites: `Le`/`Lt` facts, `Gap(a, x) <= a`, and `LenLe`. It returns `None` if an `Unknown` atom remains.
  - `instantiate(sum: &Poly, b: &Body, args: &Vec<Operand>) -> (r: Option<Poly>)` ensures `r matches Some(q) ==> forall|fr| poly_val(fr, q) >= poly_val(call_enter(..).0, sum@)`. It substitutes callee param atoms with arg atoms (`Copy(local)` or `Const`); anything else gives `None`.
- **Facts:** `facts_imply(have: &Vec<Fact>, need: &Vec<Fact>) -> (r: bool)` ensures `r ==> forall|fr| facts_hold(fr, have@) ==> facts_hold(fr, need@)`. Syntactic: each needed fact appears, or follows by `Lt ⇒ Le`.
- **Blocks and certificates:**
  - `check_block(p: &Program, f: usize, b: usize, c: &Cert, sums: &Vec<Option<Poly>>) -> (r: bool)` ensures `r ==> forall|fr| facts_hold(fr, c.blocks@[b].facts@) && frame_len_ok(fr) ==> block_step_ok(*p, f as nat, b as nat, *c, sums@, fr)`;
  - `check_cert(p: &Program, f: usize, c: &Cert, sums: &Vec<Option<Poly>>) -> (r: bool)` ensures `r ==> cert_for(*p, f as nat, *c, sums@)`.
- **`tests/cost_check.rs`**, hand-built core programs with hand-written certificates:
  - `accepts_straight_line_const`
  - `accepts_counted_loop_const_bound`
  - `accepts_counted_loop_len_bound`
  - `accepts_nested_quadratic`
  - `accepts_mid_body_exit`
  - `accepts_call_with_summary`
  - `rejects_pot_too_small_by_one`
  - `rejects_missing_lt_fact`
  - `rejects_wrong_successor_facts`
  - `rejects_unknown_atom_in_rhs`
  - `rejects_entry_facts_nonempty`
  - `rejects_summary_mismatch`

- [ ] **Step 1:** Write the polynomial and fact helpers, verifying each.
- [ ] **Step 2:** Write `check_block` per terminator kind (`loop_isolation(false)` where needed) and `check_cert`.
- [ ] **Step 3:** All tests pass.
- [ ] **Step 4: Exec mutations**, each failing a named `ensures`:
  - `poly_dominates` ignores `extra`;
  - `rewrite_pre` keeps `Unknown` monomials as `Same`;
  - `check_block` skips the successor-facts check.
- [ ] **Step 5: Run the four checks and the evidence run.**
- [ ] **Step 6: Commit:** `feat(ctcore): verified cost-certificate validator (check_cert ==> cert_for)`

---

### Task 5: Untrusted inference (`loops.rs`) and the `analyze` API

**Files:**
- Create: `crates/ctcore/src/loops.rs`, `crates/ctcore/tests/cost_infer.rs`
- Modify: `crates/ctcore/src/lib.rs`

**Consumes:** Task 4.

**Interfaces (produces):**
- **Graph structure:**
  - `pub fn dominators(b: &Body) -> Vec<Vec<bool>>`: iterative dataflow with a pass bound;
  - `pub fn back_edges(b: &Body, dom: &Vec<Vec<bool>>) -> Vec<(usize, usize)>`;
  - `pub fn natural_loop(b: &Body, latch: usize, header: usize) -> Vec<bool>`.
- **Loops:**
  - `pub struct Counted { pub header: usize, pub body: Vec<bool>, pub counter: usize, pub bound: Atom, pub test_block: usize, pub inc_block: usize }`;
  - `pub fn recognize(b: &Body, lp: &Vec<bool>, header: usize) -> Option<Counted>`, by the spec's counted-loop definition;
  - `pub enum CostWhy { Bounded, NotCounted(usize /* header */), Unresolved, Recursion, CalleeNone(usize), DegreeCap, Overflow, Validator(usize /* block */) }`.
- **Certificates:** `pub fn build_cert(p: &Program, f: usize, sums: &Vec<Option<Poly>>) -> Result<Cert, CostWhy>`.
  - Block costs are local.
  - Loop potentials: `Gap(bound, Val(counter)) × (per-iteration cost)` plus the exit continuation. Nested loops multiply, up to degree 2.
  - Facts: `Lt(Val(counter), bound)` on the loop's body blocks and `Le(Val(counter), bound)` at the header. Carry `Le` facts from dominating length checks (`if len > b.len() - off { return }`).
- **The API:** `pub fn analyze(p: &Program) -> (r: (Vec<Option<Poly>>, Vec<Cert>, Vec<CostWhy>))`.
  - `ensures wf(*p) ==> (r.0@.len() == p.fns@.len() && r.1@.len() == p.fns@.len() && forall|g: int| 0 <= g < r.0@.len() && r.0@[g] is Some ==> cert_for(*p, g as nat, r.1@[g], r.0@))`.
  - It works bottom-up over the call graph; recursive SCCs give `None`.
  - Then it re-validates every `Some` with `check_cert` against the current vector, sets failures to `None`, and repeats until a pass changes nothing. That loop is `decreases` the number of `Some`s.
- **`tests/cost_infer.rs`:**
  - `infers_counted_const`
  - `infers_counted_len`
  - `infers_nested_quadratic`
  - `infers_mid_body_exit`
  - `infers_call_chain`
  - `none_for_off_progress_loop`
  - `none_for_recursion`
  - `none_for_unknown_bound`
  - `revalidation_drops_dependent_caller`: a callee forced to `None` makes its caller `None`.

- [ ] **Step 1:** Write the dominators, loops and recognizer (with plain unit tests), then `build_cert` and `analyze`.
- [ ] **Step 2:** All tests pass. `analyze`'s ensures verifies.
- [ ] **Step 3: Mutation.** Make `build_cert` emit a potential one lower in the loop body. The tests then show `None` (via `Validator(..)`), not a wrong `Some`. Record this.
- [ ] **Step 4: Run the four checks and the evidence run.**
- [ ] **Step 5: Commit:** `feat(ctcore): untrusted counted-loop inference producing validated step-bound certificates`

---

### Task 6: Driver `cost` mode and cost fixtures

**Files:**
- Modify: `tools/ct-driver/src/main.rs` (`CT_MODE=cost`), `tools/ct-driver/src/manifest.rs` (the `cost-root <def-path>` line kind), `tools/ct-fixtures/src/lib.rs` (cost fixtures), `scripts/ct-check.sh`
- Create: `tools/ct-fixtures/expected-cost.txt`

**Consumes:** `ctcore::analyze`, 8a's `translate_closure()` (preflight).

**Interfaces (produces):**
- **Cost mode** translates from the `cost-root` lines. It reads no labels. `translate_closure` applies no label rule, so 8a's root-label rule, which runs in check mode only, doesn't apply here (preflight).
  - It keeps only cost roots whose crate prefix is the crate being compiled, and analyses each root's closure as its own `Program`, as in 8a.
  - ct-check.sh fails if any `cost-root` got no verdict line in any crate.
- **It calls `analyze` and writes `cost-<crate>.txt`**, one line per cost root:
  - `bounded <def-path> deg=<0|1|2> steps <= <poly in source param names>`; or
  - `none <def-path> <CostWhy>`.
- **Cost fixtures** (`cost_pos_*` must be `bounded`; `cost_neg_*` must be `none`):
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
- **`expected-cost.txt`** lines are `bounded <path> deg=<d>` or `none <path> <Why>`. Coefficients are not pinned.
- **`ct-check.sh`** prints `ct-check: cost fixtures 10/10`.

- [ ] **Step 1:** Implement the cost mode and fixtures. The diff is empty.
- [ ] **Step 2: Translator-side mutation.** Translate `Goto` back edges as `Return`, which makes everything look straight-line. `cost_neg_*` must become `bounded`, so the diff catches it. Record which lines changed.
- [ ] **Step 3: Run the four checks and the evidence run.**
- [ ] **Step 4: Commit:** `feat(ct-driver): cost mode — step-bound report for cost roots; cost fixtures`

---

### Task 7: Run over the parser targets, record coverage, add the gate, update docs

**Files:**
- Create: `tools/ct-driver/cost-targets.txt` (the `cost-root` lines for the Task 1 target list, each followed by `# predicted: bounded|none (<why>)`), `tools/ct-driver/cost-expected.txt`
- Modify: `tools/ct-driver/manifest.txt` (new `intr`/`translate-crate` lines from the Task 1 census; only mappings to 8a's existing intrinsics), `scripts/ct-check.sh`, `scripts/verify.sh`, `TRUSTED.md`, `docs/superpowers/specs/2026-10-27-verified-http3-design.md`

**Consumes:** Task 6.

**Interfaces (produces):**
- **`ct-check.sh` cost run:** `CT_MODE=cost CT_CRATES=wire,h3,quic cargo build --release -p wire -p h3 -p quic`, then compare with `cost-expected.txt`:
  - a `bounded` that becomes `none` is a failure;
  - a new `bounded` is a failure until `cost-expected.txt` is updated in the same commit, with the bound in the report;
  - it prints `ct-check: cost X/Y bounded`.
- **`verify.sh`'s final line** gains `, cost X/Y`.
- **TRUSTED.md** gains the spec's cost-model row, verbatim.
- **The design spec's Phase 8 entry** gains the measured coverage `X/Y` and one line: "bounds are core steps, not time or memory".

- [ ] **Step 1:** Run over the targets and write `cost-expected.txt` from the result.
- [ ] **Step 2: Coverage report.**
  - A table of the targets with `predicted`, `actual`, the bound (for bounded) or the `CostWhy` (for none), and a one-line explanation for each prediction miss.
  - The headline: **X of Y targets bounded**.
- [ ] **Step 3: Real-code mutation** (in a scratch copy made by `git archive`, never the worktree). In `huffman_decode`, change `j += 1` to `j += 0`. `huffman_decode` must become `none`.
- [ ] **Step 4:** Edit verify.sh, TRUSTED.md and the design spec. Run the four checks and the evidence run.
- [ ] **Step 5: Commit:** `feat: verified step bounds for X/Y parser targets (wire, h3/QPACK, quic); cost gate in verify.sh`

---

### Task 8 (stretch; controller go/no-go): off-progress loops via callee return facts

**Go only if** all of these hold:
- Tasks 1–7 are reviewed and approved;
- ctcore's total proof time is < 60 s;
- at least 4 `none` targets have the reason "off-progress" (`off += consumed`).

Otherwise record `not attempted` with those numbers.

**Design:** this is a `SPEC-CHANGE` to 8b's own `cost.rs`, needing a ruling. 8a's files stay frozen.
- Summaries gain return facts, `RetFact::ConsumedGe1(field path)`. They are certified by `facts_hold` at every `Return` block on the returned tuple's field.
- A new atom, `Ret(local, field path)`, is valid until the next write to that local.
- The recognizer gains "progress loops": `off < len` at the header, and `off = off + c` with `c >= 1` from a callee `RetFact`. The potential is `Gap(Len(b), Val(off))`.
- Targets this would flip: `parse_settings`, `decode_lines(_bounded)`, `parse_payload`, `parse_ack` (its loop also needs off-progress, not count).

**Tasks if go:** the same cycle as Tasks 2–7 (spec+theorem → abstract effect → validator → inference → fixtures → rerun), each with its own mutations, as one task per layer. Exit: coverage re-reported.

---

## Exit criteria (Phase 8b)

- `theorem_cost` verifies at `--rlimit 4` with its statement equal to the spec's, and the Task 2 mutations each fail on a named lemma.
- `check_cert ==> cert_for` and `analyze`'s ensures verify. The Task 4 tamper tests and the Task 5 dropped-caller test pass.
- `ct-check.sh` prints `cost fixtures 10/10` and `cost X/Y bounded`, matching `cost-expected.txt`. `verify.sh` ends with `, cost X/Y`.
- The Task 7 coverage table is in the phase summary, with predicted against actual and every `none` explained.
- TRUSTED.md has the cost-model row, and the design spec carries `X/Y` and the steps-not-time-or-memory line.
- `git diff main -- crates/ctcore/src/{syntax,sem,ct,ct_lemmas,ni,check,infer}.rs` is empty.
- `phase-8b` is merged into `main`. Task 8 is recorded as done or `not attempted`, with the go/no-go numbers.

## Self-review (done while writing)

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
- **Honesty:** the predictions are pre-registered in the spec and re-checked in Task 1, the coverage regression gate is in verify.sh, and a seeded unbounded loop must come out `none`.
- **Not probed by the planner:** the degree-2 dominance proofs and the counter-increment no-wrap lemma. Task 3 Step 1 is the bounded probe for the latter.
