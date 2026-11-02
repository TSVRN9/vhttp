# Phase 8: a verified constant-time checker (8a) and a verified step-bound analyser (8b) — design

Date: 2026-10-28. Base: `main` at 60b940d (Phase 5b merged; escape count 4). Pinned Verus 0.2026.10.04.426d8b0.

## Context

**What the user asked for** (their words): "go ahead with the verified checker and I'd like you to attempt the verified automatic cost analyser."

**8a: the constant-time (CT) checker.** It has four parts:
- a small core language;
- a leakage semantics for it;
- a non-interference (NI) theorem, proved in Verus;
- the checker, as verified exec code whose verdict is tied to the theorem.

Its job is to make "constant-time style" a checked property of `crates/crypto`, not just a reviewed one. Today TRUSTED.md says the timing is unverified.

**8b: the cost analyser.** It is a verified step-count bound analysis over the same core language. The aim is DoS bounds for attacker-reachable parsers.
- "Attempt" means the honest outcome is a coverage number: how many target functions get a proven bound.
- Any function the analyser can't bound returns `None`.

**Inputs this design rests on:**
- `scratchpad/spike-ct-proof/REPORT.txt`: the NI theorem for a structured toy core, calls included, verifies at rlimit 4 (passes at 0.1).
- `scratchpad/spike-ct-front/REPORT.txt`: recommends front end C, a `rustc_public` MIR driver.
- `scratchpad/timing-discussion.md`: what stays trusted.
- `scratchpad/wt-5c/.superpowers/sdd/2026-10-28-phase-5c-p256/ct-discipline.md`: the CT rules and the 4 declassify points the in-flight P-256 code follows.
- Two planner probes (§Evidence).

## Controller's calls (recorded; already made)

1. **Front end: C, the MIR driver.** Everything in the unverified translator is trusted, so it stays a thin, mechanical MIR-to-core mapping. Structure recovery (loops, dominators) and every analysis go in verified code. This design picks a **CFG core** on that basis; see D1.
2. **Shipped build.**
   - Fix the overflow-check problem by setting the shipped profile explicitly (release, with `overflow-checks = false` justified by Verus's no-overflow proofs; D5 refines this).
   - Pin the build toolchain with `rust-toolchain.toml` to the rustc the driver links against: **rustc 1.98.1**. That is also the toolchain Verus pins. Today the binary builds on unpinned stable 1.92.0.
   - Installing the `rustc-dev` component at user level is allowed; no sudo.
3. **Labels.**
   - Attributes `ct::secret`, `ct::public`, and a declassify marker (D3 picks its form).
   - A def-path manifest covers code that can't be annotated.
   - Fail closed: an unlabeled reachable fn or an unresolved callee is an error (D4 refines the first half).
4. **Leakage model.** The observable events are:
   - branch conditions: `switchInt`, including short-circuit `&&`/`||`, which MIR makes explicit;
   - memory indices: `Index` and bounds-check asserts on secret indices;
   - div/rem operands, including the u128 lowering;
   - variable shift amounts;
   - calls, by summary.

   Overflow is absent by Verus proof, given the profile decision. The model does **not** cover LLVM/backend transformations, CPU microarchitecture, or cache timing beyond indices (§Leakage model).
5. **Trust boundary.** New TRUSTED.md rows:
   - the MIR translator;
   - the core semantics and leakage model;
   - one reviewed row per declassify point;
   - rustc/LLVM/CPU preserving CT.

   Binary-level checks (dudect-style) stay a later item.
6. **Cost analyser.**
   - Steps are counted per core statement, with callee summaries.
   - Soundness: `analyze(p) == Some(b)` and the run terminates ⇒ `steps <= eval(b, inputs)`.
   - Only recognized counted loops are bounded, and they are inferred in verified code from MIR, because `decreases` clauses are erased.
   - Targets: wire varint, h3 frame parsing, QPACK integer/string/Huffman decode, quic frame parse.
   - Bounds are stated in terms of input length.
   - A step bound is not wall-clock time and not memory. Memory relates to the known Vec-capacity gap.
7. **Phasing.**
   - **8a:** core, semantics, proof, exec checker, driver, verify.sh integration, and a run over the 5a/5b crypto code.
   - **8b:** the cost analyser, built on 8a's core and front end.

## Design calls made here (the controller or user can override them)

**D1. CFG core, not a structured core.**
- Core function bodies are MIR-shaped: a vector of basic blocks, each with statements and one terminator. The translator maps MIR blocks 1:1 and does no structure recovery.
- **For constant time, no structure recovery is needed at all.** Every `switchInt`/`Assert` condition must be public, so two runs from publicly-equal inputs take the same block sequence. NI is then a lockstep induction on fuel: one lemma per statement kind and one per terminator kind, with the spike's dispatcher pattern.
- The planner probe (§Evidence, P2) verified exactly this shape at `--rlimit 4` on the first run: `ni` took 28 ms, including equality of step counts.
- **Loops matter only to 8b.** Dominators, natural loops and counted-loop recognition run in 8b's crate code. Their output is a *certificate* that a verified validator checks (D9). A bug in loop recognition can therefore cost coverage, but never soundness.
- A structured core would put about 300 LOC of loop recovery into the trusted translator (front spike), and early-return/`&&` lowering would change every case lemma (proof spike). Both are avoided.

**D2. Memory model: values, frame-local `&mut`, and snapshot `&`.**
- **Locals hold tree values.** `Val` is `Int | Unit | Tup | Adt(variant, fields) | Arr | Shr(Box<Val>) | Mut(Loc)`.
- **A shared reference `&T` is a snapshot** of its pointee, `Shr(value)`. This is faithful because Rust forbids mutation while a shared borrow is live (there is no interior mutability in verified code).
- **A mutable reference is `Mut(Loc)`.** `Loc` names a local or a slot of the *current frame*, plus a resolved path.
- **Calls copy `&mut` arguments in and out.** The pointee is copied into a callee slot and written back on return. This is faithful because `&mut` arguments are unique (borrow checker).
- **Supported subset.** A verified `wf` check limits `Mut` to top-level locals: not inside aggregates, not returned, not inside a snapshot. Anything outside that subset is rejected.
- Both fidelity arguments rest on rustc's borrow checker, which goes in the translator/semantics TRUSTED row.
- **Why not a heap of cells with pointers:** that is the obvious alternative. It needs a pointer-label-consistency invariant over the whole memory, and the copy semantics avoids it. The copy semantics also makes 8b's `Len(param)` atoms trivially stable.

**D3. The declassify marker is an identity function.** It is `crate::ct::declassify(x)`, recognized by def path and mapped to the core intrinsic `Declassify`.
- MIR has no statement attributes, so a branch-level attribute cannot reach the checker. A fn-level attribute naming a callee is coarser and harder to review.
- The cost is a one-line code edit at each point.
- The definition, identical whoever adds it first (8a Task 9 or 5c Task 7). These are the exact bytes of `crates/crypto/src/ct.rs` (preflight):
  ```rust
  use vstd::prelude::*;

  verus! {
  /// Constant-time checker marker: the result is treated as public. Every call site has a
  /// `ct-declassify:` row in TRUSTED.md.
  #[inline(always)]
  pub(crate) fn declassify<T>(x: T) -> (r: T)
      ensures r == x,
  { x }
  }
  ```
- `lib.rs` gets `pub(crate) mod ct;` on the line after `pub mod bytes;` (preflight).
- **Never `use crate::ct;`**, and put no `ct::` attribute in `lib.rs` (preflight). With the module `ct` in scope, `ct::secret` resolves to the module and fails with E0433, but only under `--cfg ct_check`.
- Call the marker as `crate::ct::declassify(..)`, or import the fn with `use crate::ct::declassify;`.

**D4. Refinement of controller call 3 ("an unlabeled reachable fn is an error").**
- ct-discipline.md says public-only exec fns get no comment, e.g. `sec1_decode_exec`, which `p256_ecdh` reaches. Requiring a label there would be a retrofit beyond turning comments into attributes. The rules below stay fail-closed:
- **Roots** are listed in the manifest (`root <def-path>`). A root without a `ct::` attribute (or a manifest `label` line, below) is an error, and so is a root path that doesn't resolve.
- **A reachable non-root fn with a body and no attribute is checked as all-public.** Any call site that passes a secret argument to it is then rejected, so a missing label can never cause a silent accept.
- **Bodyless, unresolved, or non-manifest foreign callees are an error.**
- **A fn with an attribute must name every non-ghost parameter** in exactly one of `secret(..)` / `public(..)`. Unknown names, duplicates and missing names are errors. A bare `ct::public` (no list) means all parameters are public.
- **Only `secret(..)` is enforced** (by the verified `decl_ok` check, D10). `ct::public(..)` and bare `ct::public` declarations are not enforced: inference may still label such a parameter secret. This is sound for CT: an extra-public label only weakens the claim on that fn's inputs and never hides a leak of a secret (8a Task 6).
- **A manifest `label` line may label a root** (8a Task 7b ruling), under the same naming check as an attribute; the manifest is reviewed (TRUSTED.md). A root with neither a `ct::` attribute nor a `label` line is an error.

**D5. Profile: release, with overflow checks off only for verified crates.**
- The release profile turns overflow checks off by default, including in unverified code, which the Verus justification doesn't cover. So, in the root `Cargo.toml`:
  ```toml
  [profile.release]
  overflow-checks = true          # unverified code (the future server shell, tests' deps) keeps the checks
  [profile.release.package.wire]
  overflow-checks = false         # verified: Verus proves no exec arithmetic overflows
  # ...the same 2-line override for h3, quic, tls, crypto, ctcore
  ```
- The shipped artifact is `cargo build --release`.
- The driver analyses that exact build with one addition, `-Zinline-mir=no`, so function bodies stay per function. The shipped build still inlines at MIR level. That difference goes in the "compiler preserves CT" row: MIR inlining copies bodies and is trace-preserving at this model's level.
- `RUSTC_BOOTSTRAP=1` is set only for the driver build and the analysis build, never for the shipped build or for `cargo verus`.

**D6. The u128 multiply is not an event.**
- x86-64 lowers `u128 * u128` to `mul`/`imul` sequences, which are constant time on current Intel/AMD cores.
- u128 `/` and `%` lower to `__udivti3`/`__umodti3`, which are data-dependent loops. That is why Div/Rem events cover every width.
- The mask idiom `bit * u128::MAX` could be rewritten by LLVM into a branch. That risk belongs to the backend row, not the model.

**D7. Shapes are public.**
- `agree` relates secret values only when they have the same *shape*: the same array/slice/Vec lengths, the same enum variants, and the same `Mut` targets.
- So `Len`/`PtrMetadata` and `Discriminant` reads are public.
- This is required: bounds-check asserts compare indices with lengths, and crypto takes secret slices whose lengths are public (`key@.len() == 16`).
- Checked programs preserve shape equality, because variants and lengths change only under public control flow. The theorem's quantifier states the restriction explicitly.

**D8. Steps are part of 8a's semantics.**
- 8a's `run` returns `Option<(Frame, Seq<Event>, nat)>`. The `nat` counts every executed statement and terminator, plus extra intrinsic costs.
- NI also proves that the step counts are equal. That costs nothing extra in the lockstep proof (probe P2) and gives a stronger CT statement: the same instruction count at core level.
- 8b reuses `run` unchanged, which is what fixes the shared interface well enough to write a full 8b plan.

**D9. 8b certifies bounds instead of proving an analysis.**
- An exec inference in `ctcore` produces, per function, a certificate: per-block facts plus a potential polynomial. It does this with dominators, natural loops, counted-loop recognition and callee summaries.
- A verified validator checks the certificate. It is incomplete but sound: `check_cert(..) == true ==> cert_for(..)`, where `cert_for` is `cert_sem_ok` plus empty entry facts and `sums[f] == Some(pot[0])` (8b preflight I1).
- A separate theorem turns `cert_for` for every summarised fn into the step bound by fuel induction.
- The inference has no correctness proof and needs none.
- Soundness doesn't need an acyclic call graph either. The inference simply returns `None` for recursive SCCs.

**D10. Label inference is unverified exec.** Its output only reaches the verdict through verified code (preflight):
- `check_prog`, whose `ensures r == ok_prog(..)` ties it to the theorem;
- a verified `decl_ok` check: every declared-secret parameter is secret in the inferred labels.

All-public labels satisfy `ok_prog` for any program. So without `decl_ok`, a wrong inference could cause a vacuous accept. With both checks, a wrong inference can only cause a rejection.

## Architecture

```
crates/ctcore/            verified (Verus) library; in the workspace, so verify.sh's loop and
  src/lib.rs              escape gate cover it; depends on vstd only
  src/syntax.rs           core language (exec datatypes, shared by spec and exec)
  src/sem.rs              values, frames, places, run (spec), events, steps; binop (opaque)
  src/ct.rs               labels, wf, ok_* typing (spec)
  src/ct_lemmas.rs, ni.rs NI lemmas; ni.rs holds theorem_ct (ctcore::ni::theorem_ct, no re-export)
  src/check.rs            exec checker check_prog (ensures == ok_prog)
  src/infer.rs            exec label inference (unverified functionally)
  src/cost.rs, loops.rs   8b: certificates, validator, theorem_cost; inference
tools/ct-driver/          unverified rustc_private driver (own [workspace]); links ctcore in-process
  src/main.rs             RUSTC_WORKSPACE_WRAPPER entry; modes: check | census | selftest | cost
  src/translate.rs        MIR (rustc_public) -> ctcore::syntax, 1:1
  src/manifest.rs         line-format manifest reader
  src/interp.rs           test-only core interpreter (selftest; not in the TCB)
  manifest.txt            roots, intrinsic mappings, label lines, translate-crates (preflight)
tools/ct-fixtures/        plain-Rust crate (own [workspace]): positive and negative controls
  src/lib.rs, expected.txt
scripts/ct-check.sh       builds the driver, runs it over crypto (+ the negative control) and the fixtures
```

- **In-process linking.** The driver builds `ctcore::syntax` values directly and calls `ctcore::check_program`, so no serializer or deserializer joins the TCB.
- **Workspace placement.** `tools/*` sit outside `members = ["crates/*"]`; each has its own `[workspace]` table, so `cargo verus` never sees `rustc_private` code.

## Toolchain and shipped build (exact versions)

| Component | Version | Where pinned |
|---|---|---|
| rustc / cargo (build, test, driver, analysis) | **1.98.1** (`1.98.1-x86_64-unknown-linux-gnu`) | new `rust-toolchain.toml`: `channel = "1.98.1"`, `components = ["rustc-dev"]` |
| rustc-dev (provides `rustc_public`, `rustc_driver`) | 1.98.1 | rustup component, user level |
| Verus | 0.2026.10.04.426d8b0 (its own toolchain 1.98.1) | `~/.local/opt/verus/0.2026.10.04.426d8b0/verus-x86-linux` |
| Z3 | 4.16.0 (bundled) | |
| vstd | =0.0.0-2026-10-04-0306 | Cargo.lock |
| erasure macros (`verus_builtin_macros`) | 0.0.0-2026-09-20-0158 | Cargo.lock |
| previous build compiler | stable 1.92.0, unpinned | replaced |

- **Effect: the compiler that builds the binary is now the one that checks the proofs.** TRUSTED.md's caveat that "the compiler that checks the proofs is not the compiler that builds the binary" is deleted.
- **Bump rule:** a Verus pin bump that changes its rustc also bumps `rust-toolchain.toml` and the driver's `rustc_public` fix-ups, in the same phase.

## Core language (`crates/ctcore/src/syntax.rs`, inside `verus!`)

These exec datatypes are used directly by the spec (Vec fields viewed with `@`). Local 0 is the return place, locals `1..=nargs` are the parameters, and indices are dense `usize`s assigned by the translator.

```rust
pub enum IntTy { U8, U16, U32, U64, U128, Usize, I8, I16, I32, I64, I128, Isize, Bool }
pub enum BinOp { Add, Sub, Mul, Div, Rem, BitXor, BitAnd, BitOr, Shl, Shr, Eq, Ne, Lt, Le, Gt, Ge }
pub enum UnOp { Not, Neg }
pub enum Proj { Deref, Field(usize), Index(usize /* local */), ConstIndex(u64), Downcast(usize) }
pub struct Place { pub local: usize, pub proj: Vec<Proj> }
pub enum ConstVal { Int(u128), Unit, Arr(Vec<ConstVal>), Shr(Box<ConstVal>) }   // promoteds, const arrays
pub enum Operand { Copy(Place), Const(IntTy, u128), Lit(ConstVal) }
pub enum AggKind { Tuple, Array, Adt(usize /* variant */) }
pub enum Rvalue {
    Use(Operand), Bin(BinOp, IntTy, Operand, Operand), Un(UnOp, IntTy, Operand),
    Cast(IntTy /* from */, IntTy /* to */, Operand), Len(Place), Discr(Place),
    Aggregate(AggKind, Vec<Operand>), Repeat(Operand, u64), RefShr(Place), RefMut(Place),
}
pub enum Stmt { Assign(Place, Rvalue), SetDiscr(Place, usize) }
pub enum Intrinsic {   // closed by 8a Task 2 Step 0 (callee census); adding one is a SPEC-CHANGE
    Declassify, GhostUnit, VecNew, VecWithCapacity, VecPush, VecExtendFromSlice, VecAsSlice,
    ArrayAsSlice, VecLen, VecSet, VecIndex, SliceSubrange, SliceToVec, Wrapping(BinOp, IntTy),
}
pub enum Callee { Fn(usize), Intr(Intrinsic) }
pub enum Term {
    Goto(usize), Switch(Operand, Vec<(u128, usize)>, usize), Assert(Operand, bool, usize),
    Call(Callee, Vec<Operand>, Place, usize), Return, Abort,
}
pub struct Block { pub stmts: Vec<Stmt>, pub term: Term }
pub enum Ty { Int(IntTy), Unit, Tuple(Vec<Ty>), Adt(Vec<Vec<Ty>>), Array(Box<Ty>, u64),
              Slice(Box<Ty>), Vec(Box<Ty>), Shr(Box<Ty>), Mut(Box<Ty>) }
pub struct Body { pub nargs: usize, pub locals: Vec<Ty>, pub blocks: Vec<Block> }
pub struct Program { pub fns: Vec<Body> }
```

## Core semantics (`sem.rs`, spec; part of the trusted semantics)

**Values**, spec-only:
- `enum Val { Int(u128), Unit, Tup(Seq<Val>), Adt(nat, Seq<Val>), Arr(Seq<Val>), Shr(Box<Val>), Mut(Loc) }`
- `Loc { root: Root, path: Seq<PE> }`, with `Root = Local(nat) | Slot(nat)` and `PE = Field(nat) | Index(nat) | Variant(nat)`.
- `Frame { locals: Seq<Val>, slots: Seq<Val> }`; slot `j` belongs to parameter `1 + j`.
- Ints are raw bit patterns. The width comes from the instruction. `binop(op, ty, a, b)`, `unop` and `cast` are `#[verifier::opaque]` spec fns transcribing Rust's release-mode (wrapping) semantics:
  - shifts mask the amount to the bit width;
  - signed values are two's complement;
  - `/` and `%` by 0 give 0 (unreachable: Verus proves it);
  - comparisons give 0/1.

**Totality: the semantics never gets stuck on shape mismatches.**
- A projection on a mismatching shape reads `Unit`.
- An out-of-bounds index reads `Unit`, and an out-of-bounds write is a no-op. Verus proves in-bounds for the real code.
- `Downcast(k)` re-tags the variant.
- Field writes into a short `Tup`/`Adt` pad with `Unit`.
- Only `Abort`, a failed `Assert`, fuel exhaustion, Vec length overflow and an out-of-range fn or block index (which `wf` excludes) give `None`.

**Places.**
- `read_place(fr, pl) -> (Val, Seq<Event>)` starts at `Local(pl.local)` and applies each projection:
  - `Deref` follows a `Mut(loc)` (switching root and path) or enters a `Shr` snapshot;
  - `Index(x)` reads local `x` as an Int `i`, emits `Idx(i)` and descends;
  - `ConstIndex(k)` descends with no event.
- `place_loc(fr, pl) -> Option<(Loc, Seq<Event>)>` does the same for writes, and gives `None` through a `Shr`. A write to `None` is a no-op that still emits the place's events (as do `RefMut` and `SetDiscr` of a `None` place).

**Statements.**
- `Assign(pl, rv)`: the events are those of `rv`, then those of `pl`; then the value is written. Steps: 1.
- `SetDiscr(pl, k)`: re-tags the variant. Steps: 1.

**Rvalues.**
- `Bin` emits `DivOps(a, b)` for Div/Rem and `Shamt(b)` for Shl/Shr.
- `Len` gives the length of the `Arr` at the place, looking through `Shr`/`Mut` (MIR's `PtrMetadata` takes a reference operand).
- `Discr` gives the variant, or 0.
- `Repeat(op, n)` gives `Arr` of n copies.
- `RefShr(pl)` gives `Shr(read_place)`.
- `RefMut(pl)` gives `Mut(place_loc)`.

**Terminators** (1 step each):
- `Goto`.
- `Switch`: emits `Cond(v)`, then takes the first matching target, else `otherwise`.
- `Assert(c, exp, b)`: emits `Cond(v)`; if `(v != 0) == exp`, go to `b`, else `None`.
- `Return`.
- `Abort`: `None`.
- `Call(Fn(g), args, dst, next)`:
  - evaluate the args;
  - each top-level `Mut(loc)` arg `j` becomes `Mut(Slot(j), [])`, with `slots[j] := read(loc)`;
  - the callee frame is `locals = [Unit] + args + Unit…`;
  - run the callee with fuel − 1;
  - write back each such slot to its `loc` in caller order;
  - assign the callee's `locals[0]` to `dst`.
  - Trace is `args events + callee trace + dst events`. Steps are `1 + callee steps`.

**Intrinsics** (`Call(Intr(k), …)`), with their events and costs:

| Intrinsic | Effect | Events | Steps |
|---|---|---|---|
| `Declassify(x)` | `dst := x` | `Declass(x)` | 1 |
| `GhostUnit(..)` | `dst := Unit` | none | 1 |
| `VecNew()` | `dst := Arr([])` | none | 1 |
| `VecWithCapacity(n)` | `dst := Arr([])` | `Alloc(n)` | 1 |
| `VecPush(m, x)` | appends `x` at `m`'s target | none | 1 |
| `VecExtendFromSlice(m, s)` | appends the snapshot | none | 1 + len(s) |
| `VecAsSlice(r)` | `dst := r` | none | 1 |
| `ArrayAsSlice(r)` (`<[T; N]>::as_slice`; CT typing: result ⊒ source, as `VecAsSlice`) | `dst := r` | none | 1 |
| `VecLen(r)` | `dst := len` | none | 1 |
| `VecSet(m, i, x)` | `target[i] := x` | `Idx(i)` | 1 |
| `VecIndex(r, i)` | `dst := Shr(elem i)` | `Idx(i)` | 1 |
| `SliceSubrange(r, lo, hi)` | `dst := Shr(subrange)`, with `lo`/`hi` clamped to the length so `len(dst) <= len(r)` | `Range(lo, hi)` | 1 |
| `SliceToVec(r)` | `dst := Arr(copy)` | none | 1 + len(r) |
| `Wrapping(op, ty)(a, b)` | as `Bin` | as `Bin` | 1 |

- Push, extend and to-vec give `None` if the result length would exceed `usize::MAX`: Rust panics with capacity overflow. This keeps every length `<= usize::MAX`, which 8b relies on.
- `push` counted as 1 step hides realloc copies (amortized O(1)), and capacity is not modelled. A step bound is not wall-clock time and not memory.

**Runs.**
- `run_from(p, f, b, fr, fuel) -> Option<(Frame, Seq<Event>, nat)>` decreases fuel. Every block transition and every call consumes 1 fuel.
- `run_fn(p, f, fr, fuel) = run_from(p, f, 0, fr, fuel)`.
- `init_entry(p, f, args: Seq<Val>, slots: Seq<Val>) -> Frame` is the frame the theorems quantify over (preflight):
  - for every `Ty::Mut`-typed parameter, it places `Mut(Slot(j), [])` in local `1 + j`, ignoring `args[j]` there;
  - it places `args[j]` in the other parameter locals, and `Unit` everywhere else;
  - `slots` become the frame's slots.

**Events:** `enum Event { Cond(u128), Idx(u128), DivOps(u128, u128), Shamt(u128), Declass(Val), Alloc(u128), Range(u128, u128) }`.

## Leakage model

**Covered.** The attacker observes the event trace and the step count:
- every branch: `switchInt`, including the short-circuit `&&`/`||` MIR makes explicit, and match/`if let`, which are switches on discriminants;
- every assert condition (bounds checks, the divide-by-zero check);
- every array/slice/Vec index, whether read, written or `ConstIndex`-free;
- both operands of `/` and `%` at every width, since u128 lowers to `__udivti3`/`__umodti3` loops;
- the shift amount of `<<`/`>>`;
- allocation sizes;
- subslice bounds;
- declassified values;
- the step count.
- Calls are covered by the callee's summary: the labels of its parameters and its inferred return label, monomorphic per function.

**Assumed public (D7):** the shapes of values, meaning lengths, enum variants and `&mut` targets.

**Not covered** (these sit in the "compiler/CPU preserve CT" row):
- **The compiler below MIR:** MIR passes after the analysed point (the shipped build's MIR inliner) and LLVM, which can turn masks or selects back into branches (watch the u128 mask multiply `x * u128::MAX`) or introduce table lookups.
- **The CPU:** variable-latency instructions other than div and shift, caches beyond the addresses implied by indices, prefetchers, speculation (Spectre-class), power/EM, SMT port contention.
- **Panics and unwinding:** a failed assert is `None`, and the theorem speaks of completed runs. Verus proves the asserts pass.
- **Drop glue** (deallocation). **Interior mutability, and the constructs `unsafe` code needs** (raw pointers, unions, statics, compiler intrinsics), which the translator rejects.

**Overflow:** core arithmetic wraps. The shipped verified crates have no overflow checks (D5), so there are no overflow branches. Verus proves the wrapping never happens in verified code.

## CT typing (`ct.rs`, spec) and theorems

**Labels:** `pub struct FnLab { pub locals: Vec<bool> }` (true = secret). It is an exec type used by the spec through `locals@`, like `Program`, with one per function in `Seq<FnLab>`. The label of slot `j` is that of local `1 + j`.

**Read and write labels.** `rd(pl)` and `wr(pl)` are both `lab(pl.local)`.
- This holds through `Deref` of a `Mut` because the `plc` invariant says a `Mut` local's label equals its target root's label.
- A snapshot's label is that of the local holding it.

**Rules (`ok_*`).** Every read operand is well formed under these rules:

| Construct | Rule |
|---|---|
| `Index(x)` projection, anywhere | `x` public |
| `Bin` Div/Rem | both operands public |
| `Bin` Shl/Shr | rhs public |
| `Len`, `Discr` | public (D7) |
| other `Use`/`Bin`/`Un`/`Cast`/`Aggregate`/`Repeat` | join of their operands |
| `RefShr(pl)` | `rd(pl) ⊑ lab(dst)` |
| `RefMut(pl)` | `lab(dst) == wr(pl)` |
| `Assign(pl, rv)` | `lab(rv) ⊑ wr(pl)`; if the value type contains `Mut`, `==` |
| `Switch`, `Assert` | condition public |
| `Call(Fn(g))` | each arg ⊑ g's param label (`==` for `Mut`-typed params); g's return label ⊑ `wr(dst)` |
| `Call(Intr)` | per-intrinsic: `Declassify` result may be public; `VecWithCapacity` n public; `VecSet`/`VecIndex` i public; `SliceSubrange` lo, hi public; `VecPush`/`VecExtendFromSlice`/`VecSet` value ⊑ target; `VecAsSlice`/`ArrayAsSlice`/`VecIndex`/`SliceSubrange`/`SliceToVec` result ⊒ source; `VecLen` public |
| `Call(Intr(Wrapping(op, ty)))` | as `Bin` (preflight): Div/Rem both operands public, Shl/Shr rhs public, otherwise the join |

**`wf(p)`, the supported subset:**
- `Ty::Mut` only as a top-level local type: not in `Tuple`/`Adt`/`Array`/`Slice`/`Vec`/`Shr`, and not as local 0;
- every `Fn(g)` index is in range;
- block targets are in range;
- arity matches.

**Stricter rules in `ct.rs` (8a Task 3).** These only reject more programs, so they are sound; the real crypto MIR satisfies them, and the translator's output must too.
- **`Mut` flow.** `mut_pl(pl)`: `pl` is an empty-projection place of a `Mut`-typed local. `mut_op(op)`: `op` copies such a place. Only these may hold a `Mut` value.
  - `Assign(pl, Use(op))` with `mut_op(op)` needs `mut_pl(pl)` and `lab(op) == lab(pl)`.
  - `Assign(pl, RefMut(q))` needs `mut_pl(pl)` and `lab(pl) == lab(q.local)`.
  - `refmut_ok`: a `RefMut` of a place rooted at a `Mut`-typed local starts with `Deref` (a reborrow), so a `Mut` never targets a `Mut`-typed local.
  - A `Mut` argument goes only into a `Mut`-typed parameter.
- **No `Mut` operand** (`!mut_op`) in `Aggregate`, `Repeat`, `RefShr` (a snapshot), the `Declassify` argument, the `VecPush`/`VecSet` value, or the `VecAsSlice`/`ArrayAsSlice` source.
- **Intrinsic arities** are exact: `VecNew` 0; `Declassify`, `VecWithCapacity`, `VecAsSlice`, `ArrayAsSlice`, `VecLen`, `SliceToVec` 1; `VecPush`, `VecExtendFromSlice`, `VecIndex`, `Wrapping` 2; `VecSet`, `SliceSubrange` 3.
- **Places** (`ok_place`): the local is in range, and so is every `Index` local.
- **`wf_body`**: at least one block; `nargs < locals.len()`; local 0's type has no `Mut`; every other local has `Mut` only at the top (`wf_local_ty`).
- **`plc` and `args_agree`**: frame locals and slots have the body's lengths; no `Mut` inside non-`Mut` locals, entry arguments or slots (`no_mut`); a `Mut` target's root is a slot or a non-`Mut`-typed local (`root_ok`).
- **`decl_ok`** carries index guards: an over-long `decl[f]` makes it false (fail closed).

`ok_prog(p, ls)` = `wf(p)` ∧ `ls.len() == p.fns.len()` ∧ every `ls[f].locals.len() == p.fns[f].locals.len()` ∧ every body ok under its labels (preflight).

**Agreement.**
- `agree(p, ls, f, fr1, fr2)`: public locals and slots are equal; secret ones are `shape_eq`.
- `shape_eq` is structural: `Arr` lengths equal, `Adt` variants equal, `Mut` locs equal, `Int`s always related.
- `plc(p, ls, f, fr)` is the label-consistency invariant for `Mut` values.

**Theorem** (`ctcore::ni::theorem_ct`, in `ni.rs`; `diverge` and the predicates are in `ct.rs`; the statement a reader trusts). There is no re-export from `lib.rs`: a proof-fn re-export fails `cargo build` with E0432.

```rust
pub open spec fn diverge(t1: Seq<Event>, t2: Seq<Event>) -> bool   // first difference is two Declass events (spike)
pub proof fn theorem_ct(p: Program, ls: Seq<FnLab>, f: nat, a1: Seq<Val>, a2: Seq<Val>,
                        s1: Seq<Val>, s2: Seq<Val>, fuel: nat)
    requires
        ok_prog(p, ls), f < p.fns@.len(),
        args_agree(p, ls, f, a1, a2, s1, s2),          // public params equal; secret params shape_eq
        run_fn(p, f, init_entry(p, f, a1, s1), fuel) is Some,
        run_fn(p, f, init_entry(p, f, a2, s2), fuel) is Some,
    ensures ({
        let (fr1, t1, n1) = run_fn(p, f, init_entry(p, f, a1, s1), fuel).unwrap();
        let (fr2, t2, n2) = run_fn(p, f, init_entry(p, f, a2, s2), fuel).unwrap();
        (t1 == t2 && n1 == n2 && out_agree(p, ls, f, fr1, fr2)) || diverge(t1, t2)
    }),
```

**Reading:** take two runs that both complete at a common fuel, from inputs that agree on public parameters (and on shapes). They produce the results below. The theorem is termination-insensitive, and it says nothing about runs that complete at different fuels (preflight).
- the same leakage trace;
- the same step count;
- publicly-equal outputs (the return value and the `&mut` slots);

unless they first differ at a declassified value.

**Exec checker:** `pub fn check_prog(p: &Program, ls: &Vec<FnLab>) -> (r: bool) ensures r == ok_prog(*p, ls@)`.

**API** (`lib.rs`): `pub fn check_program(p: &Program, decl: &Vec<Option<Vec<bool>>>) -> (r: Result<Vec<FnLab>, Vec<Reject>>) ensures r is Ok ==> ok_prog(*p, r->Ok_0@) && decl_ok(decl@, r->Ok_0@)` (preflight).
- `decl_ok(decl, ls)` (spec, `ct.rs`) is `forall f, j. decl[f] is Some && decl[f]->0@[j] ==> ls[f].locals@[1 + j]` (preflight).
- `decl[f]` has one entry per MIR argument, with `false` for ghost/unit params (preflight).
- It runs inference, then `check_prog`, then a verified exec `decl_ok` check (preflight).
- It returns `Ok` only when both checks returned true.
- On failure, `explain` (exec, unverified) gives the rejection sites.

## Front end (tools/ct-driver; trusted, kept 1:1)

**Invocation.**
- The driver runs as `RUSTC_WORKSPACE_WRAPPER` under `RUSTC_BOOTSTRAP=1 cargo build --release -p <crate>`, with its own target dir.
- For target crates it appends `-Zinline-mir=no`, `--cfg ct_check`, `-Zcrate-attr=feature(register_tool)` and `-Zcrate-attr=register_tool(ct)`.
- `verus!` expands in erase mode, exactly as shipped.

**Items.** The driver works on **monomorphic `Instance`s**: roots, then callees via `Instance::resolve`. It translates `instance.body()`, so trait calls and `const MINIMAL` resolve before translation. It translates only blocks reachable along normal (non-unwind) edges.

**Per-root programs.**
- Each root's reachable closure is translated and checked as **its own `Program`**, by one `check_program` call per root.
- So a rejected or untranslatable root never prevents a verdict on another root, and every `ok` verdict is backed by `check_program`'s ensures for exactly that closure.
- Translation (`translate_closure`) applies no label rule (preflight). Check mode applies the root-label and attribute rules afterwards. So the selftest and 8b's cost mode reuse the same translation.
- During a multi-crate build, the driver keeps only the manifest roots whose crate prefix is the crate being compiled. ct-check.sh asserts that every manifest root got a verdict in some crate.

**Mapping.** Anything not listed here is rejected with its span.

| MIR | core |
|---|---|
| `Assign`, `SetDiscriminant` | `Assign`, `SetDiscr` |
| `StorageLive/Dead`, `Nop`, `FakeRead`, `Retag`, `PlaceMention`, `AscribeUserType`, `Coverage`, `ConstEvalCounter` | dropped |
| `Use`, `BinaryOp` (non-overflow, non-`Offset`), `UnaryOp(Not/Neg)`, `UnaryOp(PtrMetadata)`/`Len` | `Use`, `Bin`, `Un`, `Len` |
| `Cast(IntToInt)`, `Cast(PointerCoercion(Unsize))` | `Cast`, `Use` |
| `Aggregate(Tuple/Array/Adt)`, `Repeat`, `Ref(Shared/Mut)`, `Discriminant`, `CopyForDeref` | same-named core forms |
| `Aggregate(Closure)` | `Lit(Unit)`: ghost closures only; calling a closure is rejected |
| `Cast(PointerCoercion(ClosureFnPointer))` of a closure-ZST constant | `Lit(Unit)`, only when the result flows solely into a `GhostUnit` call: the erased `Ghost(..)` argument residue (spike `encrypt_rk` MIR) (preflight) |
| `Copy`/`Move` operands | `Copy` |
| scalar constants; ZST constants (fn items, unit, `PhantomData`, `Ghost<_>`) | `Const`, `Lit(Unit)` |
| constant refs/arrays of ints (promoteds, `const` arrays) | `Lit(ConstVal)`, decoded little-endian from the allocation |
| projections `Deref`, `Field`, `Index`, `ConstantIndex{from_end: false}`, `Downcast` | same |
| `Goto`, `SwitchInt`, `Assert`, `Return`, `Unreachable` | `Goto`, `Switch`, `Assert`, `Return`, `Abort` |
| `Drop` of a type whose drop glue only frees `Vec` buffers | `Goto` |
| `Call` | `Fn(i)` or `Intr(k)`, by the lookup order below |

- Types map structurally to `Ty`. `Ghost<_>`/`Tracked<_>` map to `Unit`, and so do fn-pointer types, but only for that residue (preflight). `Vec<T>` maps to `Ty::Vec`, and `&T`/`&mut T` to `Shr`/`Mut`.
- Floats, `char`, raw pointers, `Box`, `dyn` and `unsafe` are rejected.

**Callee lookup**, for a resolved Instance's def path:
1. A manifest `intr` line maps it to an intrinsic.
2. Otherwise, the instance has a body and its crate is the target crate or a manifest `translate-crate`: an internal fn.
3. Otherwise: error `unresolved callee <path>`.

**Attributes.**
- Read with `all_tool_attrs()`: `ct::secret(a, ..)`, `ct::public(b, ..)`, and bare `ct::public`.
- Names map to parameters through the body's `var_debug_info` for argument locals. Fallback: `tcx.fn_arg_idents` through `rustc_internal`.
- Unit/ghost-typed parameters are ignored.

**Manifest** (`tools/ct-driver/manifest.txt`): one entry per line, `#` comments.
```
root <def-path>                        # CT root; must resolve and carry a ct:: attribute
intr <def-path> <Intrinsic>[ <BinOp> <IntTy>]
label <def-path> secret(a,b) public(c) # bodies that can't be annotated (third-party); may label a root
translate-crate <crate>                # foreign crates whose bodies may be translated
```
- There is no `exclude` kind (preflight). A path that no root reaches needs no line. A reached callee is either translated, mapped by an `intr` line, or `Unresolved`; it is never skipped.
- The `intr` paths are written from the driver's `census` output. They are never guessed.
- Census lines, manifest matching and report lines all use one key, the ct_key: `Instance::name()` of the resolved instance, with every `::<…>` generic-argument list removed (8a Task 7a ruling).
  - Leaf and intrinsic callees are keyed by def. A type-argument guard requires each such call's instance generic arguments to match the intrinsic's declared types. The Vec/slice intrinsics are u8 only, and any other type argument is `Unsupported` (fail closed; widen when needed).
  - Roots and internal callees are keyed by instance.
  - Ambiguity is an error: a key that matches more than one distinct fn instance fails closed, for roots, internal callees and manifest/`intr` lookups alike.
- `intr` lines need not resolve in a given build (preflight).
- An `intr` path inside the analysed crate is a loader error, except `<crate>::ct::declassify` mapped to `Declassify` (8a Task 7a ruling) and `ct_fixtures::ct::ghost_fallback` mapped to `GhostUnit`, for the fixtures only (8a final review M7). `Declassify` is allowed nowhere else.
- Expected keys include the `Vec::with_capacity`, `push`, `extend_from_slice` and `as_slice` def paths; vstd's `Vec` `set` and `slice_subrange`/`slice_to_vec`; `u32::wrapping_add`; `Ghost::assume_new_fallback`; and `crypto::ct::declassify`.

**Report** (`$CT_OUT/report-<crate>.txt`), one line per item:
```
checked <def-path> secret=<params> ret=<s|p>
declassify <fn def-path>#<k> <file>:<line>
reject <root def-path> <Kind> <file>:<line>
root <def-path> ok
```
- There is one `reject` line per (root, kind, site) (preflight). A secret div or index also trips rustc's div-by-zero or bounds `Assert`, so that site reports both kinds.
- `declassify` lines are keyed by the def path of the fn that contains the call, numbered per fn, and deduplicated across roots (preflight).
- `secret=` is printed from the checked labels, not from the attributes (preflight).

## Labels and declassification

**The 5a/5b crypto code gets attributes in 8a Task 9.** For example:

```rust
#[cfg_attr(ct_check, ct::secret(key, block))]
pub fn aes128_encrypt_block(key: &[u8], block: &[u8]) -> (r: [u8; 16])
```

Roots (manifest), with their labels:
- `aes128_encrypt_block`: secret(key, block)
- `aes128_gcm_seal`: secret(key, pt), public(nonce, aad)
- `aes128_gcm_open`: secret(key), public(nonce, aad, ct)
- `sha256`: secret(msg)
- `hmac_sha256`: secret(key, msg)
- `hkdf_extract`: public(salt), secret(ikm)
- `hkdf_expand`: secret(prk), public(info, len)
- `p256_public_key`: secret(d)
- `p256_ecdh`: secret(d), public(peer)
- `p256_ecdsa_sign`: secret(d), public(msg) (8a Task 9)

No root reaches the RSA path, so it needs no manifest line (preflight).

**Declassify sites.** The list of record is the `ct-declassify:` rows of TRUSTED.md, one per `declassify` line of the crypto report; verify.sh's declassify gate keeps the two, and the source, in sync. Each call sits on its own line (ct-check.sh guards it), because the driver keys sites by file:line.

| Site | What becomes public | Code |
|---|---|---|
| `crypto::gcm::aes128_gcm_open` | the tag-compare outcome (accept/reject) | 5b, **new** in 8a: `if declassify(diff != 0)`, the bit, not the byte (8a final review I1) (the existing `ponytail:` comment already argues it) |
| P-256 (`crypto::p256`, `crypto::ecdsa`) | ct-discipline points 1–5 and the two peer-decode points (B1 below) | 5c Tasks 7/8, placement amended by the 8a Task 9 ruling |

**Binding notes for Phase 5c**, which must reach 5c **before Task 7 starts**:
- **B1.** Write the ruled declassify points with `crate::ct::declassify(..)` from day one, adding `ct.rs` exactly as in D3 if 8a hasn't landed:
  - T7 `p256_public_key`/`p256_ecdh`: `if !declassify(scalar_in_range(d))`;
  - T7 `p256_ecdh`: `declassify(q.inf) == 1`;
  - T8: `if declassify(scalar_in_range(&t))`;
  - T8: the r = 0 / s = 0 outcomes, `declassify(is_zero4(&r)) == 0 && declassify(is_zero4(&s)) == 0` (8a Task 9 ruling: declassifying r/s themselves left `is_zero4`'s result secret, since each fn has one label summary);
  - 8a Task 9 ruling, peer decode in `p256_ecdh`: `declassify(bo)` in `fe_from_be` (x >= p) and `declassify(on_curve_fe(x, y))` in `sec1_decode_exec`, both on peer bytes only and both equal to the fn's own `None` outcome.
- **B2. Void (controller, 2026-10-28).** The post-preflight 5c plan (4812b13, D1 = A) has no branch on `q.inf` in `p256_public_key`: dG ≠ O comes from the Phase 5d lemma `lemma_scalar_mult_g_nonzero`, so the body never tests it.
- **B3.** Turn every `// ct: secret …` line into `#[cfg_attr(ct_check, ct::secret(..), ct::public(..))]` when 8a's driver is available. Then convert the discipline's public-only helper list to nothing: under D4 those are checked as all-public automatically.

## Trust boundary: TRUSTED.md changes (8a Task 10)

New rows:

| Item | File | Why trusted | Removed |
|---|---|---|---|
| CT front end: MIR→core translator, attribute reader, manifest reader | `tools/ct-driver/src/` | unverified, rustc_private. It must map MIR 1:1 per the spec's table and reject everything else. The `&` snapshot and `&mut` copy-in/copy-out semantics rely on rustc's borrow checker. Tested by tools/ct-fixtures and the interpreter self-test, not proved | never |
| CT manifest: each `intr` line asserts a std/vstd fn behaves as its core intrinsic; each `label` line is reviewed (preflight) | `tools/ct-driver/manifest.txt` | std/vstd bodies are not translated | never |
| CT core semantics and leakage model | `crates/ctcore/src/sem.rs`, the spec fns in `ct.rs` | events: branch/assert conditions, indices, div/rem operands (all widths), shift amounts, allocation sizes, subslice bounds, declassified values, steps. Shapes are public. The `binop`/`cast` transcription of Rust release semantics is hand-written | never |
| Compiler and CPU preserve MIR-level CT | (toolchain) | analysis uses `-Zinline-mir=no`, the shipped build doesn't; LLVM may reintroduce branches or tables; variable-latency instructions beyond div/shift, caches beyond indices, speculation. Binary-level (dudect-style) checks are a later item | never |
| ct-declassify: crypto::gcm::aes128_gcm_open#1: tag-compare outcome (accept/reject) is public; the caller learns it anyway | crates/crypto/src/gcm.rs:811 | NI is relative to declassified values (the row text is unbackticked, so the gate's `^| ct-declassify: ` grep matches it) (preflight) | never |

There is one `ct-declassify:` row per report `declassify` line, keyed `<X>#<k>` exactly as the driver prints it. `#k` is 1-based (8a Task 9 ruling) and is a position in the driver's string-sorted site order, so it is unstable when lines move; every row therefore also names the site's `file:line` in its File column, and the gate compares that too. Each row gives the reason the value is public.

Changed rows and lines:
- **The AES/GCM timing row** becomes: "MIR-level constant time proved by `ctcore::ni::theorem_ct` for `crypto::{aes,gcm,sha256,hmac,hkdf}` (scripts/ct-check.sh in verify.sh). Below MIR, see the compiler/CPU row." It also says the claim is modulo the `ct-declassify:` rows and the CT trust-boundary rows.
- **The 5c P-256 timing row** ("… never (known gap; checked by the Phase 8a CT checker)") is reworded the same way, for the roots `p256_public_key`, `p256_ecdh` and `p256_ecdsa_sign`.
- **`tls::server::ct_eq32`** is unchanged. tls is not checked in 8a.
- **The pins paragraph** gains: rustc 1.98.1 via `rust-toolchain.toml` (the build compiler is the verify compiler); the shipped artifact is `cargo build --release`, with overflow checks off for verified crates only (D5).
- **The design spec's non-goal** "proven constant-time execution" is amended to: "proven at MIR level for crypto since Phase 8a; binary level unverified".

**8b adds one row:** "Cost model: steps per core statement/terminator; intrinsic costs (push counted as 1 hides realloc; capacity not modelled); a bound is not wall-clock time and not memory".

## verify.sh integration (8a Task 10)

After the crate loop and `duvet report`, and before the escape gate, verify.sh runs `"$root/scripts/ct-check.sh"`.

Before each analysis build, ct-check.sh deletes the old report and runs `cargo clean --release -p <crate>` in that build's own `--target-dir` (preflight). Cargo skips fresh crates, and manifests and `CT_*` are not cargo inputs.

ct-check.sh, in this order:
1. builds the driver;
2. runs the fixtures and diffs their verdicts against `tools/ct-fixtures/expected.txt`;
3. runs the interpreter selftest over `crypto`;
4. requires one `declassify(` call per line under `crates/crypto/src/` (`ct-check: one declassify per line`);
5. runs it over `crypto` and requires 0 `reject` lines and every manifest root `ok`;
6. runs it over `crypto` with `--cfg ct_negative` and requires **exactly** the one reject `reject crypto::ct_negative::secret_branch SecretSwitch …` (preflight);
7. prints one line per run (preflight): `ct-check: fixtures N/N`, `ct-check: selftest V/V`, `ct-check: crypto ok (F fns, R roots, D declassify)` and `ct-check: negative control rejected`. Every count is derived, none is a literal.

ct-check.sh (and verify.sh's declassify gate, whose per-key loop word-splits) parses report and manifest lines as space-separated `awk` fields, so neither supports def paths containing spaces (for example an `<impl … for …>` root or declassify key). Such a path fails closed (the fixtures diff or the every-root-has-a-verdict check fails). No root has one today; the report format would need a delimiter change first.

verify.sh exports `CT_TARGET_DIR` and `CT_OUT` (with ct-check.sh's defaults) before the call, so the gate reads the report the same run wrote. Then the **declassify gate**:
- every `declassify X#k` report line has a TRUSTED.md row starting `| ct-declassify: X#k: `;
- the row count equals the line count;
- the number of non-comment `declassify(` lines under `crates/crypto/src/` equals that count too (preflight). The search is recursive and excludes `ct.rs`, where the definition is `declassify<T>(`;
- **the lists are equal, not just the counts** (a missing site and an extra one cancel in a count): the sorted `X#k file:line` pairs of the report equal those of the TRUSTED.md rows (File column), and the report's sorted `file:line` sites equal the source lines' `file:line`. Duplicates count.

The final line becomes `verify.sh: all crates verified, duvet ok, ct ok (D declassify), escapes accounted (E)`, where E is main's escape count (preflight).

## Cost analyser (8b)

**Cost model.**
- Steps are `run`'s `nat`: 1 per statement and per terminator, plus the intrinsic extras in the table. Calls cost 1 plus the callee's steps.
- `Repeat`/aggregate moves of fixed-size values count 1.
- This is a model of work, not time. Memory is not bounded. In particular, Vec capacity growth and the Phase 3c-style "copy on every append" can only be bounded when the copying is an intrinsic with a len-cost (extend, to_vec). Repeated `push` reallocations are hidden.

**Bounds.**
- `Poly { monos: Vec<Mono> }` with `Mono { coef: u64, atoms: Vec<Atom> }` (at most 2 atoms), a sum of monomials over atoms (8b preflight I1).
- `Atom = Const(u64) | Val(local, IntTy) | Len(local) | Gap(Box<Atom>, Box<Atom>)`:
  - `Val(x, ty)`: `uval(ty, raw)` for an `Int(raw)`, i.e. the value at the width MIR compares it at; 0 for non-ints (8b preflight C2: frame ints are raw bit patterns, and `binop(Lt, ty, ..)` compares at `ty`);
  - `Len`: the length of the `Arr` behind the local's value, through a `Mut`'s target and then any number of `Shr`; 0 otherwise (`parse` takes `&&[u8]`). `Rvalue::Len` reads one layer, so it is `<=` this atom, not equal;
  - `Gap(a, b)` = max(0, a − b).

  An atom reads its local through `nth`, so an out-of-range local reads as `Unit`, as everywhere in `sem.rs`.
- A function's summary is a `Poly` over its parameter atoms. Example: `huffman_decode: steps <= c0 + c1·len(input)`.

**Certificates** (D9).
- `Cert` = per block `{ facts: Vec<Fact>, pot: Poly }`, with `Fact = Le(Atom, Atom) | Lt(Atom, Atom)`.
- **`cert_sem_ok(p, f, cert, sums)` is semantic.** For every frame satisfying block b's facts, executing b leads to a successor b′ whose facts hold, with `pot_b(fr) >= cost(b, fr) + pot_b′(fr′)`. A return needs `pot_b(fr) >= cost(b)`. A call needs `cost` to include `1 + eval(sums[g], callee entry atoms)`, for *any* callee result within that bound (dst and `&mut` targets are havocked).
- `cert_sem_ok`'s hypotheses are, for all `ls`, `ok_prog(p, ls)` and `plc(p, ls, f, fr)`, plus the block's facts and `frame_len_ok` (every local's and slot's `len_ok`) (8b C1, option B). `ls` stays inside the quantifier because no cost proof reads a label, so `cert_for` and `check_cert` take no labels. `lemma_plc_reachable` composes 8a's per-construct `plc` lemmas into a run-level one.
- **Entry facts must be empty.** The summary is `pot[0]`. `cert_for(p, f, cert, sums)` = `cert_sem_ok` ∧ empty entry facts ∧ `sums[f] == Some(pot[0])`.

**Theorem** (the controller's soundness statement, as amended by the 8b preflight rulings I1 and C2 and by C1 option B):

```rust
pub proof fn theorem_cost(p: Program, ls: Seq<FnLab>, certs: Seq<Cert>, sums: Seq<Option<Poly>>, f: nat,
                          args: Seq<Val>, slots: Seq<Val>, fuel: nat, b: Poly)
    requires
        ok_prog(p, ls), f < p.fns@.len(), certs.len() == p.fns@.len(), sums.len() == p.fns@.len(),
        sums[f as int] == Some(b),
        forall|g: int| 0 <= g < p.fns@.len() && sums[g] is Some ==> cert_for(p, g as nat, certs[g], sums),
        entry_plc(p, f, args, slots),                                // entry frame satisfies plc
        vals_len_ok(args), vals_len_ok(slots),                       // all lengths <= usize::MAX
        run_fn(p, f, init_entry(p, f, args, slots), fuel) is Some,
    ensures
        run_fn(p, f, init_entry(p, f, args, slots), fuel).unwrap().2
            <= poly_val(init_entry(p, f, args, slots), b),
```

- `vals_len_ok(vs)` = `forall|i| 0 <= i < vs.len() ==> len_ok(vs[i])`. It gives `frame_len_ok(init_entry(..))`.
- `poly_val(fr, p)` evaluates `p` with each atom read in `fr`.
- `entry_plc(p, f, args, slots)` = `args.len() == nargs`, `slots.len() == nargs`, `no_mut` on every slot and on every arg whose parameter is not `Mut`-typed. It gives `plc` of `init_entry(..)` for any `ls`.
- **Discharging the premises.** The cost driver runs `check_program` with no declared secrets, so all-public labels; its `Ok(ls)` gives `ok_prog(p, ls)`, a recursion reject gives `none <root> Recursion`, and any other reject gives `none <root> NotTyped`. `entry_plc` and `vals_len_ok` concern the Rust caller's values. As with `theorem_ct`'s `args_agree`, they are not discharged mechanically: `wf_local_ty` shows that a non-`&mut` parameter's type and a `&mut` pointee's type contain no `Mut`, and the claim rests on that.
- The 8a-era statement had a `cert_sem_ok` premise, which never links `sums[f]` to `pot[0]`. It also had `eval_poly(b, fr)`. Both are superseded (I1).

- **The validator** is `pub fn check_cert(p: &Program, f: usize, c: &Cert, sums: &Vec<Option<Poly>>) -> (r: bool) ensures r ==> cert_for(*p, f as nat, *c, sums@)`. It is sound and incomplete.
  - It works by symbolic execution of each block over a small abstract domain: unchanged, `+1`, constant, copy-of, `Len`-alias, unknown. Each block's effect is stated against the successor frame, including the terminator's own writes: an intrinsic's dst, or a call's write-back and dst (I2). A call's or len-cost intrinsic's charge is read at the frame after the block's statements, so it is related to the block's start by the statements' effect alone.
  - **Writes through `Mut` (C1, option B).** Under `plc` only a `Mut`-typed local holds a `Mut`, so the only writers are a `Deref`-first place on such a local and a `Mut`-typed operand passed to push/set/extend or a call. A target's root may be any non-`Mut`-typed local, not just one that was `RefMut`-borrowed, so a writer makes every local unknown. A direct write to a non-`Mut`-typed local also makes every `Mut`-typed local unknown, since its `Len` reads through its target.
  - The `+1` and edge-fact rules are unsigned-only (C2).
  - It then checks inequalities as monomial-wise coefficient dominance, after pulling the successor's potential and the block's charge back to block-start atoms (counter decrement under a `Lt` fact, which earns a credit; upper bounds from `Le` facts; `Gap(a, x) <= a`).
- **The inference** (`loops.rs`, exec, no proof): dominator tree → back edges → natural loops → counted-loop recognition → potentials, with summaries bottom-up and `None` for recursive SCCs. A loop is *counted* when:
  - on every header→latch path, a test `i < N` (or `!(i >= N)`) dominates exactly one `i = i + 1` (or `wrapping_add(i, 1)`);
  - `N` is stable in the loop: a constant, a parameter's `Len`, or a local never assigned in the loop.

**Pre-registered coverage.** These predictions come from reading the code. They are recorded before any run, so the 8b result can be compared against them.

| Target | Loop shape | Prediction |
|---|---|---|
| `wire::varint::exec_len`, `exec_min_len` | none | Some (const) |
| `<QuicVarInt<false>/<true> as Parser>::parse`, `parse_varint` | `i < n`, n from `exec_len`; `!(len < n)` gives `n <= len` | Some (linear in len) |
| `h3::frame::parse_frame_header`, `parse_exact_varint` | calls only | Some |
| `h3::frame::settings_ok` | nested `i < n`, `j < n` | Some (quadratic in len(v)) |
| `h3::frame::parse_settings` | `off = off + n1 + n2` | **None** (non-unit step) |
| `h3::frame::parse_frame_payload` | calls parse_settings | **None** |
| `h3::qpack::int::parse_prefix_int` | `loop` with mid-body exits `i >= len`, `i > MAX`, then `i += 1` | Some |
| `h3::qpack::huffman::lookup`, `feed_bit`, `huffman_decode` | nested `i < len`, `j < 8` | Some (linear) |
| `h3::qpack::field_section::scan_string`, `decode_string`, `decode_field_line` | calls; `SliceToVec` len-cost | Some (if `Le` facts from the length checks are found) |
| `decode_lines`, `decode_lines_bounded`, `decode_field_section(_bounded)` | `pos += consumed` | **None** |
| `quic::frame::vint_at`, `bytes_at`, `stream_data_at`, `parse_reset_stream`, `parse_two_varints`, `parse_crypto`, `parse_stream`, `parse_one_varint`, `parse_new_connection_id`, `parse_path`, `parse_close`, `parse_frame_type` | calls + len checks | Some |
| `quic::ack::parse_ack` | `i < count`, count a parsed varint (bounded only by off-progress) | **None** |
| `parse_frame_fields`, `parse_frame_body`, `parse_frame` | dispatch reaches `parse_ack` | **None** |
| `quic::payload::parse_payload` | `p += consumed` | **None** |

- **Prediction: 27 of the 38 listed functions bounded, 11 `None`.** The real denominator comes from 8b Task 1's census.
- **Denominator after the 8b preflight (I3), recorded before any run: 36, prediction 25 of 36.** The `<QuicVarInt<false>/<true> as Parser>::parse` rows can't be cost roots, for three reasons:
  - the impl is generic, so the driver's root picker takes only monomorphic local fns;
  - `QuicVarInt<true>` has no exec instance at all;
  - `<QuicVarInt<false>>::parse` is counted inside `parse_varint`'s closure.

  The 8b report shows its result against both 27/38 and 25/36, and against the Task 1b re-baseline below.
- **Translator coverage (8b Task 1b).** These are deltas to §Front end, which stays as 8a shipped it. The preflight found that the 8a translator rejects most targets before any cost analysis (I4). Task 1b adds:
  - (i) `str`/`&'static str` as opaque `Unit`;
  - (ii) `-Zalways-encode-mir` for `translate-crate` crates, plus `translate-crate wire`;
  - (iii) per-intrinsic element types where `sem.rs` is element-agnostic. The len-cost intrinsics stay `u8`;
  - (iv) drop glue that frees a bounded number of `Vec<int>` buffers, as `Goto`.

  (v) `copy_from_slice` stays unmapped (a new intrinsic would be a SPEC-CHANGE to 8a), so `parse_path` and its callers are `None`.
- **Re-baseline (8b Task 1b, before Task 2):** 2026-10-29: **23/36 predicted bounded** before the Task 2 Step 0 domain subtraction, which is not yet ruled (Task 2 records the final X′ here, before any proof). The 25 predicted `Some` (I3) less `parse_path` and `parse_new_connection_id`, which both call `copy_from_slice` ((v); the preflight named only `parse_path`). The other 23 translate with 1b's (i)–(iv), allocated ADT constants (vi) and `translate-crate vest_lib` (vii), and pass 8a typing with all-public labels. No predicted-`None` target translates.
- **2026-11-02:** C1 is ruled option B, there is no Task 2 Step 0 any more, and 23/36 is an upper bound. Task 2 Step 4 records the final X′ below, before Tasks 3+.
- **2026-11-02:** Final X′ (8b Task 2, before Task 3): 19/36, from release MIR (`-Zinline-mir=no`) of the 23 and their call closure (31 fns, plus vest_lib's `ParseError::{unexpected_eof, non_canonical, new}`, which do not write) under Task 3's write rule; no cost analysis has run. Lost: `h3::qpack::huffman::huffman_decode`, whose loop counters and input `Len` cross the `feed_bit` call that takes `&mut` args, so every local is `Unknown` there; and its callers `scan_string`, `decode_string`, `decode_field_line` (`CalleeNone`). `feed_bit` also writes through `&mut` but stays bounded: it has no loop and only `lookup`'s constant summary follows its writers. No other function in the closure has a `&mut`.
- **2026-11-02:** Correction to the X′ line above (8b Task 2 fix round): 19/36 is an upper bound, from a hand read of MIR, and it subtracts write-rule losses only. That scan could not see a loss from the atom language: with `len_nat` peeling one `Shr`, `Len` read 0 on `<QuicVarInt<false> as Parser>::parse`'s `&&[u8]` input, which would have taken `parse_varint` and its 10 callers among the targets, leaving at most 8. `len_nat` now reads any number of `Shr`. Re-read under it, the length reaches a parameter `Len` in each of the 19 through the Task 3 and Task 4 rules, which are not yet proved. The inference and validator have not run, so the measured figure can be lower.
- **The structural gap is off-progress loops** (`off += consumed` with `consumed >= 1` from a callee's postcondition). Closing it needs callee return facts. That is 8b's stretch task, behind an explicit go/no-go.

## Risks and fallbacks

- **The memory-model proof (D2) is larger than the spike.** 8a Tasks 3–5 each start with a bounded probe and have a stop rule: escalate if a lemma needs rlimit > 4 after splitting.
- **Release MIR optimizations (GVN, destination propagation) may merge locals of different labels.** Those are false rejects, never unsound. Fallback: report the site, and as a last resort disable that single pass in the analysis build with a recorded trust note.
- **`var_debug_info` missing in release.** Use the `fn_arg_idents` fallback.
- **The lint delta from 1.92 to 1.98.1 versus the 0-warning rule.** 8a Task 1 has a fix scope and a stop rule.
- **`cargo verus` interacting with a root `rust-toolchain.toml`.** 8a Task 1 checks this first. Fallback: the toolchain file pins 1.98.1 (Verus's own), so no conflict is expected.
- **vest_lib bodies under `overflow-checks = true`.** Their MIR keeps `*WithOverflow` asserts, which the translator rejects. If 8b's census needs vest_lib bodies, the options are: a `vest_lib` per-package override plus a TRUSTED note (its proofs are re-checked by `cargo verus verify`), or accept the `None`s. This is a controller ruling at 8b Task 1.
- **Offline rustup.** If `rustup component add rustc-dev` cannot download, use the spike's sha256-checked tarball overlay, documented in ct-check.sh.

- **Known checker limitation: label summaries are context-insensitive**, one per fn. A helper called on both secret and public data is treated as secret everywhere. This forced two extra P-256 declassify sites on peer-only values (`fe_from_be`'s range borrow and the `on_curve_fe` result, 8a Task 9). Future work: label polymorphism or per-call-site summaries, which would remove those two sites.
- **Translation-validation gap (8a Task 8):** no selftest vector exercises a signed or sign-extending cast. Crypto has no signed casts today; add a vector when one appears.

## Evidence

**P1, value-tree recursion probe** (`scratchpad/probe-8a`, pinned Verus, `--rlimit 4`; source not kept, P2 overwrote it):
- `shape_eq`, recursive under `forall` over `Seq<Val>`, plus `shape_refl` and `write_shape` over a recursive `write_path`: 4 verified, 0 errors.
- Gotcha confirmed: on a **fresh target**, `cargo verus verify -- --rlimit 4` also applies the limit to vstd, and vstd's `lemma_indistinguishable_quotients` fails. Build once without `--rlimit`, then re-run with it.

**P2, CFG lockstep NI probe** (same crate, `src/lib.rs` kept):
- Blocks with statements plus `Goto`/`Switch`/`Return`, fuel semantics returning `(state, trace, steps)`, and Div-operand leakage.
- `ni` proves `t1 == t2 && n1 == n2 && agree`: 10 verified, 0 errors. SMT 55 ms total, `ni` 28 ms.
- One fix was needed: a quantifier over `p[b].stmts[k]` needed a named predicate (`ok_block`) as its trigger.

**Spikes:**
- the NI for the structured core with calls: 32 verified at rlimit 4 (0.1 suffices);
- a 50-LOC rustc_public driver under `cargo build --release` as `RUSTC_WORKSPACE_WRAPPER` reads `ct::secret` attributes through `cfg_attr(ct_check, …)`, with Verus unaffected (34 verified).
