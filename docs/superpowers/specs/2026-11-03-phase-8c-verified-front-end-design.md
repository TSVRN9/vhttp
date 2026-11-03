# Phase 8c: a verified MIR front end for the constant-time checker and step-bound analyser — design

## Context

Phases 8a and 8b proved the checkers (`ctcore`: `theorem_ct`, `theorem_cost`, `check_program`,
`check_cert`) over a small core language. Everything that produces the core program is
unverified rustc_private code in `tools/ct-driver`. TRUSTED.md rows 40 and 41, and the glue named
in row 44, trust these parts:

- `translate.rs`, 1015 lines, the MIR→core translator. It handles types, constants decoded from
  layouts, Drop, call resolution, the Ghost residue and statements it drops;
- the manifest reader and the `intr` lines;
- the attribute reader for labels;
- `main.rs`'s `cost_verdict`, `poly_text` and `atom_text`. The text of a `bounded` line comes
  from these, and no code instantiates `theorem_cost`;
- `interp.rs`, the core interpreter behind the selftest. It is unverified, so the selftest tests
  the interpreter, not `sem.rs`.

The user asked for this front end to be proved, reducing the trust base "pretty much as much as
possible until it practically only depends on the same things verus depends on".

Ruling: **prove the translator once, rather than validating each translation**. The translator
is almost 1:1 and its inputs are already trusted rustc data. A Verus translator from a parsed MIR
AST to `ctcore::Program`, proved once to preserve results, events and steps, needs no more
trusted parts than a per-function validator would. It also has no completeness gap, and its proof
follows the code. The earlier chat answer described a validator for each function; this ruling
replaces it. It costs nothing if wrong, since the trusted inputs are the same either way.

## What is trusted at the end (the bar this phase is judged against)

Verus's own trust base:

- rustc, which includes MIR construction, rustc_public's queries and rustc's serde derives;
- Verus's front end (rust_verify reads HIR) and its VIR→SMT encoding;
- Z3;
- vstd's specs of std.

After 8c, the CT and cost results trust only the following. Each item is matched to the Verus
analogue named beside it.

| Trusted after 8c | Verus analogue | Size target |
|---|---|---|
| rustc 1.98.1, rustc_public, serde/serde_json from the sysroot | rustc | — |
| Verus, Z3, vstd | same | — |
| `ct-dump`: rustc_private code that calls rustc_public queries and serializes their answers with rustc's own derives. It decides nothing: no filtering, matching or rejecting | rust_verify's HIR reader | ≤ 300 lines |
| The JSON grammar spec (`print`) and the schema spec (`decode`): how serde writes the rustc_public types this phase reads | — (Verus reads rustc's data in memory) | small, side by side with rustc_public's type definitions |
| The MIR semantics `ctmir::sem`, including the value model, the leakage table, the cost table and the std model. The `&`/`&mut` value model is sound only because borrowck rejects the programs where it would differ | Verus's encoding of Rust semantics, plus vstd's `assume_specification`s for the std model | about the size of `ctcore::sem` |
| Policy inputs: the root list, `ct::secret`/`ct::public` labels and declassify sites. The checker reports them, and `ct-check.sh` pins them | the user's specs | — |
| `main` of the front-end binary: reads files, calls one verified function, prints its result | Verus's driver | ≤ 80 lines |
| Everything below MIR: LLVM and the CPU (row 43, Phase 7a) | rustc codegen, which Verus also trusts | — |

`ctcore::sem` stops being trusted for these results: it becomes an internal step, proved
equivalent to `ctmir::sem` on every translated program. It stays as the reference for
`theorem_ct` and `theorem_cost`.

The phase is judged against this table. An item that cannot reach its row gets a TRUSTED.md row
that says why.

## Goals

1. The translator, the manifest and attribute readers, the verdict and report-line logic, and
   the selftest interpreter are all verified Verus code in a new crate, `crates/ctmir`.
   `tools/ct-driver/src/{translate.rs, interp.rs, manifest.rs}` are deleted, and so is the
   decision logic in `main.rs`.
2. End-to-end theorems are stated over the MIR semantics, with premises in MIR types only:
   - **CT:** if `pipeline(bytes)` reports `ok` for a root, then two runs of that root under
     `ctmir::sem`, on well-typed arguments that agree on public parameters, give the same leakage
     trace, the same steps and publicly equal outputs, up to declassification. This is
     `theorem_ct`'s conclusion carried over the simulation.
   - **Cost:** if `pipeline(bytes)` reports `bounded p` for a root, then every returning run of
     that root under `ctmir::sem`, on well-typed arguments, takes at most `p` steps. This
     discharges `entry_plc` and `vals_len_ok` from the MIR parameter types. The printed text of
     `p` is computed by verified code, which is proved equal to `p`'s spec rendering.
3. An equivalence gate: before anything old is deleted, old and new pipelines must agree on
   everything `ct-check.sh` runs today. The current results are:
   - crypto: ok, 105 fns, 11 roots, 10 declassify;
   - the negative control: rejected;
   - fixtures: as in `tools/ct-fixtures/expected.txt`;
   - cost: 19/36 bounded, `expected-cost.txt` unchanged after coefficients are stripped (as
     `cost_verdicts` already does).

   Any difference is either fixed or justified line by line in the ledger and in the commit that
   changes an expected file. The reconstructed Drop (below) is the one expected source of
   differences.
4. The trusted MIR semantics is tested against rustc. A verified interpreter is proved equal to
   the semantics. It runs the selftest vectors, and also semantic-conformance vectors that native
   execution of the compiled Rust produces.

## Non-goals

- Binary-level CT, the LLVM half of row 43. That is Phase 7a, unchanged.
- Miri. The ground truth for "what the code does" is native execution of the shipped compiler's
  output, and the conformance vectors come from there. Miri's MIR semantics would be a third
  opinion, and it has no leakage notion.
- Widening the accepted language beyond what 8a and 8b accept today, except for the Drop
  reconstruction. A construct the old translator rejects may stay rejected.
- Changing `ctcore`'s existing files. They are frozen; if `ctmir` needs a lemma about `ctcore`,
  it goes in `ctmir`.

## Architecture

```
cargo build (analysis flags) ──RUSTC_WORKSPACE_WRAPPER──▶ ct-dump (rustc_private, decision-free)
        │  writes $CT_OUT/mir-<crate>.json   (rustc_public values, serialized by rustc's serde)
        ▼
ct-front (tools/ct-front: main = I/O only)
        │  bytes, manifest bytes, mode
        ▼
ctmir::pipeline  (verified, crates/ctmir)
   json::parse ─▶ schema::decode ─▶ closure + translate ─▶ ctcore::check_program
                                                         ─▶ ctcore::loops (untrusted) ─▶ ctcore::check_cert
   ─▶ Verdicts (report lines as bytes) with the end-to-end theorems in its ensures
```

The analysis build keeps the flags it has today: `-Zinline-mir=no`, `--cfg ct_check`, the
`register_tool(ct)` crate attributes, and `-Zalways-encode-mir` for the `translate-crate` crates.
`ct-dump` is the old driver with its decision logic removed. Its wrapper protocol (`CT_CRATES`,
`CT_OUT`) stays the same, so `ct-check.sh`'s build plumbing barely changes.

## The dump (`tools/ct-driver`, renamed in place; trusted)

There is one JSON object per analysed crate. Each value marked † is `serde_json::to_string` of a
rustc_public value, written by rustc's own derive. Anything not marked † is a list or record the
dumper builds from query answers, with no conditions.

```
{ "crate": "<name>",
  "items":  [ {"def": <DefId>, "name": <str>, "inst": <InstanceDef>|null, "attrs": [<str>…]} … ],
  "insts":  [ {"id": <InstanceDef>, "def": <DefId>, "name": <str>, "key": <str>, "krate": <str>, "kind": †InstanceKind,
               "body": †Body|null, "fn_sig": †FnSig|null} … ],
  "calls":  [ {"fn_ty": <Ty>, "def": <FnDef>, "def_name": <str>, "args": †GenericArgs, "resolved": <InstanceDef>|null} … ],
  "drops":  [ {"ty": <Ty>, "glue": <InstanceDef>, "empty": <bool>} … ],
  "tys":    [ {"id": <Ty>, "kind": †TyKind} … ],
  "adts":   [ {"ty": <Ty>, "name": <str>, "kind": †AdtKind, "is_box": <bool>,
               "variants": [ {"discr": <u128>|null /* null unless kind is Enum */, "fields": [<Ty>…]} … ]} … ],
  "consts": [ {"id": <TyConstId>, "usize": <u64>|null} … ],
  "layouts":[ {"ty": <Ty>, "shape": †LayoutShape} … ],
  "allocs": [ {"id": <AllocId>, "alloc": †GlobalAlloc} … ],
  "spans":  [ {"id": <Span>, "file": <str>, "line": <u64>} … ] }
```

These are the only queries the dumper makes. Each table key comes from a value the dumper has
already serialized:

| Table | Filled for | Query |
|---|---|---|
| `items` | every local fn item | `all_local_items`, `Instance::try_from(item)`, `item.name()`, `all_tool_attrs` (as strings) |
| `insts` | each instance named by `items` or by a `calls`/`drops` `resolved`/`glue` entry, transitively | `inst.name()`, `ct_key` (kept as a dump-side string function only because the key strips generic args; it is a pure string function, pinned by its existing unit tests), `def.krate().name`, `inst.kind`, `inst.body()`, `inst.fn_abi()`/sig |
| `calls` | each `Call` terminator in a dumped body whose callee operand has type `FnDef` | `Instance::resolve(def, args)` (`null` on error) |
| `drops` | each `Drop` terminator in a dumped body | `place.ty(locals)`, `Instance::resolve_drop_in_place(ty)`, `is_empty_shim()` |
| `tys` | every Ty id reachable from anything above (closure) | `ty.kind()` |
| `adts` | every `RigidTy::Adt` in `tys` | `def.name()`, `def.kind()`, `def.is_box()`, `discriminant_for_variant`, `ty_with_args` per field |
| `consts` | every `TyConst` reachable (array lengths, repeat counts) | `eval_target_usize` (`null` on error) |
| `layouts` | the type of every allocated constant, then the types a value holds, transitively: ADT fields, tuple, array, slice and pattern elements, `Ref`/`RawPtr` pointees; never `FnPtr`, `Dynamic`, `FnDef`, closures or coroutines (`layout_of` ICEs under binders) | `ty.layout().shape()` |
| `allocs` | every provenance target, transitively | `GlobalAlloc::from(id)` |
| `spans` | every Span id reached | `get_filename`, `get_lines().start_line` |

Notes for the consumer:
- `insts[].def` is the identity the key-ambiguity rule uses: one key may name only one def.
- `fn_sig` is `ty().kind().fn_sig().skip_binder()`. For drop glue it is `unsafe fn(*mut T)`,
  while the glue body's argument is `&mut T`.
- Intrinsic instances can carry a fallback body. `ctmir` decides by `kind`, never by
  `body != null`.
- The dumper does not follow `GlobalAlloc::Function` and `Static`. Neither has a table, so a
  constant that reaches one is `Unresolved`/`Unsupported`.

Every place where the old translator decided something (`own_drop`, `drop_bounded`,
`is_internal`, `pick_roots`, `bind_key`, `normal_blocks`, the residue) moves into `ctmir`.
Which bodies to dump is a closure walk, not a decision. It follows every `calls`/`drops` entry
whose instance has a body, in any crate. `ctmir` then decides which of them are "internal", by
the manifest's crate rules.

**Fail-closed:** if a lookup `ctmir` needs is missing from a table, the result is `Unresolved`
or `Unsupported`, never acceptance. If the dump's output size is a problem (crypto's closure is
the largest), the fix is to dump less. Inventing structure is not a fix.

## JSON subset and the reader (`ctmir::json`, verified)

`enum Json { Null, Bool(bool), Num(bool /*neg*/, u128), Str(Vec<u8>), Arr(Vec<Json>), Obj(Vec<(Vec<u8>, Json)>) }`.

The reader accepts exactly what `serde_json::to_string` emits (the compact form):

- no whitespace;
- integers with an optional `-`, no leading zeros, up to u128;
- no floats (rustc_public has none in this subset);
- strings with serde_json's escapes: `\"`, `\\`, `\b`, `\f`, `\n`, `\r`, `\t`, and `\u00XX` for
  other control bytes. Bytes ≥ 0x80 pass through raw; they are UTF-8 and kept as bytes;
- object keys kept in order, with duplicates rejected.

The trusted part is `spec fn print(j: Json) -> Seq<u8>`, serde_json's compact writer as a spec.
The proof obligation:

```
pub fn parse(b: &[u8]) -> (r: Option<Json>)
    ensures r matches Some(j) ==> print(j@) == b@ && depth_ok(j@)
```

Recursion depth is bounded at 256, and deeper input is rejected. There must be no stack overflow
on adversarial nesting. The input is not adversarial (rustc made it), but fail-closed costs
nothing here.

## Schema decode (`ctmir::schema`, verified against a trusted spec)

The MIR AST in `ctmir::mir` is Verus datatypes. They mirror the rustc_public types this phase
reads, with the same names, fields and variant order. Values the semantics never needs, such as
`user_ty`, `source_info.scope` and `Retag`, are kept as raw `Json` fields, so nothing is
silently dropped.

`spec fn decode_*(j: Json) -> Option<T>` follows serde's derive conventions:

- a struct is an object whose keys are in declaration order;
- a newtype struct is its inner value;
- a tuple or a tuple variant is an array;
- an enum is externally tagged: a unit variant is a string, any other variant is
  `{"Variant": payload}`.

An unknown variant name decodes to `None`. A toolchain bump that renames or adds variants then
fails closed.

The exec decoders have the contract `ensures r == decode_*(j)`. This is the second trusted mirror
(spec ↔ rustc_public source). The review checks it side by side with
`$(rustc --print sysroot)/lib/rustlib/rustc-src/rust/compiler/rustc_public/src`.

Allocation bytes are `Vec<Option<u8>>`. A `null` byte is uninitialized, and any constant that
reads one is `Unsupported`.

## MIR semantics (`ctmir::sem`, spec; trusted)

**Independence is the point.** The author of `ctmir::sem` must not read
`tools/ct-driver/src/translate.rs`, the §Front end table of the 8a/8b spec, or `ctcore::sem`'s
statement, terminator and call sections (`ctcore/src/sem.rs` from `place_walk` onward). Otherwise
the translator's decisions (PtrMetadata→Len, Unsize→Use, how Drop is treated, how constants are
lowered) would become spec text, and the proof would be trivial. The author works from:

- the rustc_public type definitions;
- MiniRust (github.com/minirust/minirust) and the rustc dev guide's MIR chapter;
- this section.

The task's reviewer checks independence by reading the semantics against MiniRust, not against
`ctcore::sem`.

Fixed shared vocabulary, so the simulation stays tractable. The author imports these from
`ctcore::sem` and does not redefine them:

- `Val`, `Loc`, `Root`, `PE`, `Frame`, `Event`, `Res`;
- the arithmetic: `bits`, `signed`, `trunc`, `uval`, `ival`, `binop`, `unop`, `cast`;
- the value navigation: `nth`, `pad`, `get`, `put`, `read_at`, `write_at`, `len_ok`.

These are the value domain and Rust's integer arithmetic, already trusted and reviewed.

Fixed modelling decisions (the author implements them and does not choose them):

1. **Shape of a run.** A fuelled big-step run over blocks returns
   `Option<(Frame, Seq<Event>, nat)>`. Each block transition and each call consumes 1 fuel. A run
   that runs out of fuel gives `None`. So do `Unreachable`, `Resume`, `Abort`, a failed
   `Assert`, and any construct outside the subset.
2. **Unwinding is not modelled.** Calls either return normally or the run is `None`. `Resume`
   and every unwind edge give `None`. Only normal successors are followed.
3. **`&` and `&mut`.**
   - `&place` is a snapshot of the value, `Val::Shr`.
   - `&mut place` is a location, `Val::Mut(Loc)`.
   - When a `&mut` argument is passed to a call, its pointee is copied into a callee slot, and
     the slot is written back to the location when the call returns.

   This is sound only for borrowck-accepted programs with no interior mutability. `UnsafeCell`,
   `Box`, unions and raw pointers are outside the subset.
4. **Drop.** `Drop { place, target }` calls `drop_in_place::<T>`. Its MIR is rustc's drop-glue
   body (the dump's `drops` entry), and it runs with `&mut place` as argument 1.
   - A glue that is an empty shim is a no-op.
   - For `std::vec::Vec<E>` with integer `E`, the glue is a std-model leaf (below): the value
     model does not observe memory, so freeing has no effect on values.
   - A glue that calls a user `Drop::drop` runs that user fn like any internal call.

   This replaces `drop_bounded` and `own_drop`. Cost: a Drop costs what the glue's MIR costs.
5. **Constants.** `Operand::Constant` with `ConstantKind::Allocated` decodes the allocation's
   bytes by the constant's type and layout, little-endian x86-64:
   - integers and `bool` from their bytes;
   - arrays element by element at the element size;
   - ADTs by the layout's variant rules (a single variant, a `Direct` tag, or an integer
     `Niche`);
   - a shared reference to an array through the provenance pointer to a `GlobalAlloc::Memory`;
   - a shared reference to a ZST as `Shr` of the ZST's value.

   `ZeroSized` constants are their type's unit-like value. Anything else is outside the subset.
6. **Leakage table.** The events per MIR construct:

   | MIR construct | Event |
   |---|---|
   | `SwitchInt` | `Cond(discr)` |
   | `Assert` | `Cond(cond)` |
   | `Index(local)` projection | `Idx(i)` |
   | `ConstantIndex` | none |
   | `BinaryOp` Div/Rem at any width | `DivOps(a, b)` |
   | Shl/Shr | `Shamt(b)` |
   | std-model calls | their own events (below) |
   | `crypto::ct::declassify` | `Declass(v)` |

   Event order is evaluation order: operands left to right, then the place's projections, then
   the construct's own event. Shapes, meaning lengths and enum variants, are public (spec D7).
7. **Cost table.**
   - Each MIR statement costs 1, except `StorageLive`, `StorageDead`, `Nop`, `FakeRead`,
     `PlaceMention`, `AscribeUserType`, `Coverage` and `ConstEvalCounter`, which cost 0 because
     they generate no code.
   - Each terminator costs 1.
   - Evaluating an allocated ADT constant, or a constant `&ZST`, costs 1 per ADT or reference
     node of its decoded value. This charge is a model choice, deterministic and public. It is
     chosen so that MIR steps equal core steps exactly, and it is recorded as such in TRUSTED.md.
   - A std-model call costs 1 plus its table cost.
   - The callee's steps add to the caller's.
   - A `Drop` costs 1. When its glue is neither an empty shim nor the Vec leaf, the Drop costs 1
     more for passing `&mut place`, plus the glue's own steps. The core image needs a temp for
     the reference, and this charge keeps MIR steps equal to core steps.
8. **Std model.** A trusted table: the callee's `key` and generic args map to an effect, events
   and a cost. It mirrors vstd's specs of the same functions, and each row cites the vstd spec it
   mirrors. The rows are exactly today's `intr` lines, at today's admitted types. The table moves
   from `manifest.txt` into `ctmir::sem` as spec. The manifest keeps only policy: `root`,
   `label`, `cost-root`, `internal-crate` and `translate-crate` lines.

A sanity file, `ctmir/src/sem_sanity.rs`, proves small facts the reviewer can read: a toy body's
run, the event order of a projection, that drop of `Vec<u8>` is a no-op, and that a niche
constant decodes.

## Translator and simulation (`ctmir::lower`, verified)

`pub fn lower(m: &MirCrate, root: InstanceIdx, man: &Policy) -> (r: Result<(ctcore::Program, Vec<FnInfo>), Vec<Reject>>)`.

The translator:

- takes the root's closure: internal callees by the manifest's crate rules, std-model callees
  as intrinsics, and anything else as `Unresolved`;
- keeps MIR locals and blocks 1:1. Blocks outside the normal-edge reachable set `S` become
  `Abort`. `S` is computed exec and proved closed under normal successors, and it contains the
  entry block;
- binds keys uniquely. Two instances under one `ct_key` is a `Reject`;
- reads labels from the dumped attribute strings and the manifest's `label` lines. The grammar
  is a spec fn, `decl_spec`.

**Simulation theorem** (the core of the phase):

```
lower(m, root, man) == Ok((p, infos)) && wt_args(m, f, args, slots)  ==>
   mir_run(m, inst(f), mir_entry(m, f, args, slots), fuel)
     == core_rel(ctcore::run_fn(p, f, ctcore::init_entry(p, f, args', slots'), fuel))
```

Results, event traces and step counts are equal. `args'` relates to `args` by the value
relation, which is identity on the shared `Val` domain except where the translator changes a
representation; each such case is a named lemma. If an exact equality cannot be proved for some
construct, the fallback is equal events, MIR steps ≤ core steps, and same-path step equality. The
plan's simulation task records which form it used.

## Pipeline (`ctmir::pipeline`, verified) and the binary

```
pub fn pipeline(dump: &[u8], manifest: &[u8], mode: Mode) -> (r: Vec<u8> /* report bytes */)
    ensures report_sound(dump@, manifest@, mode, r@)
```

`report_sound` says three things:

- each `root <path> ok` line implies the CT theorem of Goal 2;
- each `bounded <path> deg=… steps <= <text>` line implies the cost theorem, with
  `<text> == poly_text_spec(p)`;
- each `reject` or `none` line is informational.

The report format is today's, byte for byte, so `ct-check.sh`'s parsing is unchanged.

`tools/ct-front/src/main.rs` reads the dump and manifest files, calls `pipeline`, and writes the
report. It contains no `verus!` code and no logic.

## Verified interpreter and conformance tests (`ctmir::interp`, verified)

`pub fn interp(p: &ctcore::Program, f: usize, args: …, fuel: u64) -> (r: Option<…>) ensures r ==
ctcore::run_fn(...) mapped`. The interpreter is exec and works over a concrete value type with a
proved view into `Val`. It interprets core rather than MIR, and the simulation carries the result
to `ctmir::sem`. The selftest mode runs `selftest.txt` through it, and `interp.rs` is deleted.

Conformance: a new fixture crate, `tools/ct-fixtures/semconf`, has one small function per
supported construct:

- each binary operator at each width;
- casts in every direction;
- shifts with large amounts;
- div/rem by 0 and by -1 at MIN;
- slices, `ConstantIndex`, `Repeat`, array and ADT constants, a niche constant;
- `&mut` call write-back;
- drop of a struct with Vec fields and of an `Option<Vec<u8>>`.

Its `#[test]` runs each function natively on 64 pseudo-random inputs from a fixed seed, including
the edge values. It writes `semconf-vectors.txt` in `selftest.txt`'s format. `ct-check.sh`
regenerates the file and runs it through the verified interpreter, and every vector must match.
Regression vectors pin the two front-end bugs found in 8b: Drop of a non-int Vec, and the length
of nested slices.

## Gate and integration

- `crates/ctmir` is in the root workspace and in `verify.sh`'s crate list. Every function must
  verify at `--rlimit 4`, and the escape count stays at 0.
- `ct-check.sh`:
  - builds `ct-dump` and `ct-front`;
  - runs each analysis as dump, then `ct-front`;
  - keeps every existing gate;
  - adds the conformance run and a labels pin. The report lists each root's labels, compared
    against an expected file.
- The equivalence gate (Goal 3) runs once before deletion and its output goes in the ledger.
  After deletion, the expected files are the gate.
- TRUSTED.md:
  - rows 40 and 41 are replaced by rows for the dump, the JSON/schema spec, `ctmir::sem`
    (including the leakage table, the cost table with the constant charge, and the std model)
    and `ct-front`'s main;
  - row 44 loses its "no code instantiates the theorem" and `poly_text`/`atom_text` sentences;
  - row 42 now names `ctmir::sem`; `ctcore::sem` is an internal step.

## Risks and fallbacks

- **The simulation is big.** Fallback order:
  1. Split it per construct, with fuel induction at the top.
  2. If calls with `&mut` write-back resist proof, prove the theorem for call-free fns first and
     land that. Fns with calls then stay in a TRUSTED row as "simulation not proved for calls",
     as a reduced but honest result.
- **JSON size and parse speed on crypto's closure.** Measure in the dump task. The exec parser
  is linear; if it is slow, reduce what is dumped, never the checks.
- **rustc_public's serde format has gaps**, such as a type with a hand-written `Serialize` that
  prints an index: `Ty`, `Span`, `DefId`, `AllocId` and `InstanceDef` do. Those are resolved
  through the tables above. Any other gap found in the dump task gets a table, not a decision.
- **Drop reconstruction changes verdicts or bounds.** Justify each change in the ledger. If a
  root becomes `reject` only because glue now shows a branch on a secret variant, that is a true
  finding under the old row 40's "an unmodelled branch accepted under D7". The finding is ruled
  on in the open: either accept the variant under D7, with the semantics marking `Discr` of glue
  as shape, or fix the code.
- **The independent semantics disagrees with the old translator.** That is the phase working.
  Each disagreement is a finding: either the old translator was wrong, or the semantics is
  wrong, and the conformance tests decide.

## Order of work (the plan refines this)

1. The dump: format, crypto, fixtures and parsers dumped, size measured.
2. `ctmir` scaffold, then the JSON reader.
3. The MIR AST and the schema decode.
4. `ctmir::sem`, written clean-room, with its sanity file.
5. The translator.
6. The simulation proof.
7. The pipeline, the end-to-end theorems, `ct-front`, and the report text.
8. The verified interpreter, selftest and conformance.
9. The equivalence gate, the switch-over and deletion, TRUSTED.md and docs.
