# Phase 5d: The P-256 group law, proved — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove, with zero new escapes, the two lemmas 5c Tasks 6–8 consume from `crate::p256_group`:
- `lemma_scalar_mult_double(j, pt)`: (2j)P = jP + jP;
- `lemma_scalar_mult_g_nonzero(k)`: kG ≠ O for 1 ≤ k < n.

Both are derived from machine-checked primality of p and n, Fermat's little theorem (FLT), the absence of 2-torsion, and associativity of the frozen `point_add`.

**Architecture:**
- **Group law.** `point_add` is related to the Bosma–Lenstra / Renes–Costello–Batina complete projective addition law ("RCB").
  - Associativity of RCB is **one** polynomial identity modulo the curve. A short case analysis maps RCB to the spec's five branches.
- **Identities.** Every polynomial identity is proved by **deterministic grid evaluation**, a verified "vanishes on a big enough grid ⇒ vanishes everywhere" theorem (no randomness).
  - The grid checks run under `compute_only` on small ints mod p, at real curve points with all y-sign choices.
  - The formal polynomials exist only in proofs and are never computed.
- **Primality.** Primality and FLT come from Pratt (Lucas) certificates checked by `compute_only` against a verified Lucas theorem.

**Tech Stack:** Verus 0.2026.10.04.426d8b0 (`~/.local/opt/verus/0.2026.10.04.426d8b0/verus-x86-linux`), vstd `=0.0.0-2026-10-04-0306`, Python 3 stdlib only for the generator (`python3 -I`). No new crates. No Singular.

**Spec:**
- `docs/superpowers/specs/2026-10-27-verified-http3-design.md` (Phase 5);
- 5c plan `docs/superpowers/plans/2026-10-28-phase-5c-p256.md` @ 4812b13: D1 and D9, both ruled A, and the "Consumes (from 5d)" blocks of Tasks 6 and 7;
- the frozen specs in `crates/crypto/src/p256.rs` (`point_add`, `scalar_mult`, `finv`, `fmod`, `on_curve`, the constants) and `crate::rsa::is_prime`.

**Branch:** `phase-5d`, cut from `main` (the 5b merge 60b940d or later; escape count **4**). It merges into `main` before 5c Task 6.
- The only overlap with `phase-5c` is one `mod` line each in `crates/crypto/src/lib.rs`, a trivial conflict.

## Decisions (recorded, with planner probes on the pinned toolchain, 2026-10-28)

All probes live in `<scratch>/probe-5d/`, where `<scratch>` is `/tmp/claude-1000/-home-tavern-Projects-rust-web-server/19d690a3-7cab-4802-bc1f-9aa0173a905e/scratchpad`. `src/` holds the Verus probes, `py/` the Python mirrors, and `py/vt.sh` the timing harness.

- **D1. A2 (no new TCB), not A1. No escalation to Singular is needed.** The A2 route as briefed, a reflective normalizer, fails on evaluator cost. The grid route below replaces it and fits easily.
  - **Evaluator facts measured.** They bind every task:

    | fact | measurement |
    |---|---|
    | per-assert timeout | wall-clock ≈ 0.22 s × rlimit: about 0.87 s at `--rlimit 4` and 9 s at 40 (`tr*.rs`); `#[verifier::rlimit(40)]` on the fn does **not** raise it |
    | recursion depth | 1000 frames pass, 3000 fail (`d.rs`) |
    | memoization | none: `f(k-1) + f(k-1)` is exponential, `let` sharing works (`memo.rs`) |
    | cost per evaluator step | grows with the size of the values touched, superlinearly for bigints: a 1 Mbit int arg costs 27 ms per call, 8 Mbit 630 ms, an 8k-node datatype 1.5 ms, a 10k-element `Seq` 0.7 ms (`bi.rs`, `dt*.rs`, `sq.rs`) |
    | `let` chains | about 25 µs per let at depth 30, 123 µs at depth 300 (`lc.rs`) |
    | trait methods | not evaluated (`tr.rs`) |
    | `--verify-function` | does not isolate compute asserts: every compute in the module runs (`mb.rs`) |
    | `--verify-only-module` | isolates: 0.57 s vs 2.98 s (`mods.rs`) |
    | the modulus via `p256_p()` = `os2ip(P256_P@)` instead of a literal | **60× slower**: about 130 ms per RCB evaluation instead of 2.1 ms (`gr_os.rs`), because `os2ip` is re-run on every mulmod |
  - **A2 as briefed (SHNF normalizer, Russinoff's design) is infeasible.**
    - The Verus SHNF normalizer ran at about 3.6k calls/s: (x0+x1+x2)²⁴ took 72k calls and 19.8 s (`e24.rs`).
    - The Python mirror (`py/shnf.py`, adapted to a = −3, b symbolic) shows that Russinoff's Computation 7 needs 6.3M calls and Computation 10 needs 23.5M. That is hours.
    - Kronecker-packed bigints instead took 285 s for C7 alone (`k_C7.rs`), because each step touches a 256 KiB value.
  - **Grid route (chosen).**
    - The identity's 8 y-components G_S(x0,x1,x2) are formal polynomials over F_p with b fixed to P-256's b. Each has tracked per-variable degree ≤ (9, 12, 9).
    - Vanishing on a 10×13×10 grid of x-values, each with f(x) a nonzero square, implies vanishing everywhere (the univariate root bound, iterated).
    - The 8 components are recovered from plain mod-p evaluations at the 8 sign choices (±y0, ±y1, ±y2) (Hadamard; needs y ≠ 0).
    - Measured:
      - plain mod-p RCB associativity, 2.1 ms per evaluation (`fpr.rs`);
      - a real 80-evaluation chunk, 0.27–0.30 s wall at `--rlimit 4` (`gr.rs`, points from `py/gen_r.py` with real square roots);
      - the negative control (formula coefficient −3 → −2) fails at once. `gr.rs` on disk still holds that −2 control; restore `let w = -3 * …` before re-running it. Re-timed with −3: ≈ 0.10 s per 40-evaluation chunk (preflight).
    - Total: 1300 x-points × 8 signs ≈ 22 s of compute. This holds **only with literal constants**; see the Global Constraints `compute_only` bullet.
  - **No certificates from a CAS are needed for the group law.** The curve equations enter through the y-component representation, and the grid does the rest.
    - sympy (scratch venv, since deleted) served only the planner: to confirm identities and to factor p−1 and n−1. The factorizations are committed as data and re-checked by `compute_only`.
- **D2. Complete formulas instead of Russinoff's case-heavy encoding.**
  - **The formula.** RCB eq. (1) with a = −3, `b3 = 3·b`, fixed (exact copy, all arithmetic mod p):
    ```
    t0 = X1·Z2 + X2·Z1;  y12 = Y1·Y2;  z12 = Z1·Z2;  bz = b3·z12
    u = y12 + 3·t0 − bz;  v = y12 − 3·t0 + bz;  w = −3·X1·X2 + b3·t0 − 9·z12
    s = X1·Y2 + X2·Y1;    r = Y1·Z2 + Y2·Z1;    q = 3·X1·X2 − 3·z12
    X3 = s·u − r·w;       Y3 = v·u + q·w;       Z3 = r·v + s·q
    ```
  - **The associativity identity** is the three 2×2 minors of RCB(RCB(P,Q),R) against RCB(P,RCB(Q,R)), for affine inputs (Z=1).
    - It reduces to 0 modulo the curve (`py/all.py assoc`: zero, 1.7M coefficient multiplies, b symbolic).
    - Its grid cost is 16.2M plain ops. Russinoff's C7+C10 on the same grid would cost 38M + 52M, and Russinoff also needs C1–C11 and an 11-lemma case analysis.
  - **The small identities** (`py/small.py`, `py/res.py`, all reduce to 0). The grid sizes are the tracked x-degrees + 1:

    | id | statement (P=(x1,y1), Q=(x2,y2) affine on the curve; d = x2−x1) | grid |
    |---|---|---|
    | I2 | chord: X3·d² ≡ x3n·Z3, with x3n = (y2−y1)² − (x1+x2)d² | 7×7 |
    | I3 | chord: Y3·d³ ≡ y3n·Z3, with y3n = (y2−y1)(x1·d² − x3n) − y1·d³ | 8×8 |
    | I4 | chord: Z3(P,Q)·Z3(P,−Q) ≡ d³·W(x1,x2) | 7×7 |
    | I5–I6 | doubling (e = 2y1, λ-numerator 3x1²−3): X3·e² ≡ x3n·Z3, Y3·e³ ≡ y3n·Z3 | 8, 10 |
    | I7 | doubling: Z3 ≡ 8·y1·f(x1) | 4 |
    | I8a–c | P+(−P): X3 ≡ 0, Z3 ≡ 0, Y3 ≡ Y3(P,P) | 5, 4, 7 |
    | I10a–b | closure: y3n² ≡ x3n³ − 3·x3n·D² + b·D³, with D = d² (chord) or e² (doubling) | 10×10, 13 |
    | RES1 | 2r0² − (x1+x2)·r0·r1 − (x1x2+3)·r1² ≡ −16·W (no y; 3 vars x1, x2, e) | 7×7 |
    | RES2 | 8·f(e) ≡ q(e)·(4e − 2x1 − 2x2) + r1·e + r0 for all e | 4×4×4 |

    The constants:
    - f(t) = t³ − 3t + b;
    - q(e) = 2e² + (x1+x2)e − (x1x2+3);
    - r1 = 2(x1² + 4x1x2 + x2² − 6);
    - r0 = −2(−4b + x1²x2 + x1x2² + 3x1 + 3x2);
    - W = −8b² + b·x1³ + 9b·x1²x2 + 9b·x1x2² + 6b·x1 + b·x2³ + 6b·x2 + x1³x2³ − 3x1³x2 − 9x1²x2² − 9x1² − 3x1x2³ − 27x1x2 − 9x2² + 27 (= Res_e(f, q), sympy).
  - **Why RCB needs completeness, and how it is proved.** RCB's output is the zero vector only on exceptional pairs.
    - Chord: Z3 ≢ 0 via I4, because d ≢ 0 and W ≢ 0.
    - W ≡ 0 gives a root of f in F_p: e* = −r0/r1 if r1 ≢ 0 (RES1 makes q(e*) ≡ 0, and RES2 then makes f(e*) ≡ 0), else (x1+x2)/2 (r0 ≡ 0 too, so q divides 8f). That contradicts D4.
    - Doubling: Z3 ≡ 8y1³ ≢ 0.
    - P+(−P): Y3 ≡ Y3(P,P) ≡ y(2P)·Z3(P,P) ≢ 0, since y(2P) ≢ 0 by D4.
    - O inputs: RCB((0:Y:0), B) = Y²·B.y·B, with B.y ≢ 0 by D4.
- **D3. Primality and FLT via Lucas/Pratt.**
  - Theorem: if `a^(q−1) ≡ 1`, `q−1 = Π rᵢ^eᵢ` with every rᵢ prime, and `a^((q−1)/rᵢ) ≢ 1`, then:
    - every x ∈ [1, q) is a power of a (order argument plus pigeonhole over vstd `Set` with `lemma_map_size` and `lemma_subset_equality`);
    - hence `is_prime(q)` (`crate::rsa::is_prime`, reused) and FLT for q.
  - The certificate tree has 26 nodes > 2¹⁶ for p and n together (`py/pratt.json`, sympy `factorint` in 1.3 s). Primes < 2¹⁶ use trial division up to √r (recursion ≤ 256 deep).
  - Measured: a 256-bit modexp under compute takes at most about 30 ms (`me.rs`). The preflight re-timing of a 16-op chain chunk, ≈ 0.09 s, puts it nearer 6 ms (preflight).
- **D4. No 2-torsion: f(x) = x³ − 3x + b has no root mod p.**
  - g = x^p mod f is computed by square-and-multiply on quadratics mod (f, p), under compute.
  - Then a Bezout certificate u·f + v·(g − x) ≡ 1 (gcd degree 0; planner Python check).
  - At a root r: r^p ≡ g(r) (evaluation lemma) and r^p ≡ r (FLT, r ≢ 0 since b ≢ 0), so 1 ≡ 0.
  - The spec's own y = 0 doubling case (rule 3) is thereby unreachable on curve points, and completeness (D2) holds.
- **D5. Is there a cheaper route than associativity? No.**
  - The doubling lemma for all j needs P + (aP + bP) = (P + aP) + bP for all a, b.
  - P-256 is cyclic of prime order n (cofactor 1), so {aP} is the whole group for P ≠ O. That is associativity on all point triples.
  - n ≈ 2²⁵⁶ rules out a computational check, and nothing in the frozen spec gives commutativity or associativity for free.
  - What *is* cheaper is the case structure: one complete-law identity instead of Russinoff's Computations 1–11 and Lemmas 7.1–7.11.
  - Prior art:
    - Bartzia–Strub's Picard-group proof and Lean mathlib's class-group proof need commutative-algebra libraries Verus lacks;
    - Théry's and Fiat-Crypto's case splits mirror Russinoff's;
    - Russinoff (EPTCS 249.3, copy in `<scratch>/probe-5d/dl-russinoff/r.txt`) is the template for "computationally surveyable", and the RCB/Bosma–Lenstra law removes the cases.
- **D6. 5d lemma 2 (kG ≠ O) costs little once lemma 1 holds.**
  - nG = O is a spec-level double-and-add chain: 255 doublings plus 166 adds (popcount(n) = 167).
  - It runs on `padd_fast`, `point_add` with `finv` replaced by a `powmod` proven equal, at about 8 ms per point op under compute (`me.rs`; preflight re-timing ≈ 6 ms, modexp included). That is 3.4 s in 32 chunks of 8 bits, with 33 generated checkpoint points as literals.
  - The order argument: kG = O with 1 ≤ k < n, together with FLT for n (k·k^(n−2) = 1 + t·n), gives G = (k·m)G = O. That is a contradiction.
  - **Feasible without new TCB.**
- **D7. Proof-time budget.** The 5d compute total is about 35 s:
  - assoc grid ≈ 25 s in 260 chunks;
  - chain ≈ 3.4 s;
  - Pratt ≈ 2.5 s;
  - small identities ≈ 1 s;
  - torsion ≈ 0.2 s;
  - constants ≈ 0.02 s (preflight: measured ≈ 20 ms per os2ip constant, and one lemma for all of them is fine).

  Z3 proofs are expected to take ≈ 30–60 s more. Crypto's `cargo verus verify` therefore grows by about 1–1.5 min. No single function may exceed 60 s.

## Global Constraints

- **Spec freeze.** No edits to `crates/crypto/src/{p256,ecdsa,rsa,bytes,sha256,aes,gcm,hmac,hkdf}.rs`. 5d adds:
  - `mod p256_group;` in `lib.rs`;
  - the directory `crates/crypto/src/p256_group/`. Its `mod.rs` starts with `#![allow(dead_code)]`: the module is private, and ghost-only types (`Q2`, `MP`, `RF`, `Proj`, …) otherwise make `cargo build` warn (preflight);
  - `scripts/gen_p256_group.py`, `scripts/p256_pratt.json`, `scripts/p256_pratt_factor.py`;
  - one TRUSTED.md row.

  `git diff main -- crates/crypto/src/*.rs` must show only the lib.rs line.
- **Zero new escapes.**
  - No `external_body`, `assume(`, `admit(`, `assume_specification` or `axiom`, not even in comments, and no lemma named `*assume*`/`*axiom*`.
  - `scripts/verify.sh` prints `escapes accounted (4)` after every task.
  - `rlimit`, `spinoff_prover`, `hide`, `reveal_with_fuel` are allowed; each `rlimit` is listed in the report with its time.
- **Exported interface: exact, frozen by 5c Tasks 6–7.** Both lemmas are defined in `crates/crypto/src/p256_group/mod.rs`.
  - Never use `use` to re-export a proof fn: proof fns are erased, so `cargo build` fails with E0432. A lemma proved in a submodule is reached through a `mod.rs` wrapper that calls it (preflight).
  - The statements:
  ```rust
  pub(crate) proof fn lemma_scalar_mult_double(j: nat, pt: SpecPoint)
      requires pt is Infinity || (pt is Affine && on_curve(pt->0, pt->1)),
      ensures scalar_mult((2 * j) as nat, pt) == point_add(scalar_mult(j, pt), scalar_mult(j, pt)),
  pub(crate) proof fn lemma_scalar_mult_g_nonzero(k: nat)
      requires 1 <= k < p256_n(),
      ensures !(scalar_mult(k, p256_g()) is Infinity),
  ```
- **`by (compute_only)`.**
  - **Where it is allowed:**
    - the generated modules (`pratt`, `torsion_cert`, `grid_small`, `grid_assoc_a`…`grid_assoc_d`, `chain`);
    - `field::lemma_group_consts`;
    - `order::lemma_g_curve_pt`;
    - `assoc_id::lemma_assoc_degrees` (preflight);
    - the smoke lemmas named in Tasks 1, 4 and 5.
  - **Where it is never allowed** (preflight):
    - `pow`, `finv`, `point_add` or `scalar_mult`;
    - formal objects built by `rcb_f`/`idf_*`;
    - any Seq longer than about 64.
  - **What it may touch** (preflight): ints < 2⁶⁰⁰, small structs of them, and small literal Seq tables, namely:
    - the factor lists `FS_i` and the Lucas smoke's `seq!`;
    - the degree tables `RD`;
    - the bit strings `BITS_k`;
    - the grid data;
    - the Task 5 smoke's tiny RF.
  - **Literal constants only.** Every spec fn that compute evaluates (`rcb`, `id_*`, `assoc_minor`, the grid cells, `qmul`/`qpow`, `padd_fast`, `chain`, `lucas_ok` inputs) reduces by `% P_LIT()`, uses `B_LIT()` and the literal `G_LIT()`, and never calls `p256_p()`, `p256_b()`, `p256_n()`, `p256_g()`, `fmod` or `on_curve`.
    - `P_LIT`, `N_LIT`, `B_LIT`, `GX_LIT`, `GY_LIT` and `G_LIT` are `pub(crate) open spec fn`s returning int literals, in `field.rs`. Each carries `#[allow(non_snake_case)]`, because Verus warns on uppercase fn names (preflight). Proofs bridge them with `lemma_group_consts`.
    - **Visibility** (preflight): every new open spec fn is `pub(crate)`, because Verus rejects a `pub open spec fn` that references a `pub(crate)` fn. `curve_pt` may stay `pub`, since it uses only `pub` items.
    - Probe: going through `os2ip` is 60× slower (D1).
  - **Shape:** one assert per proof fn.
  - **Chunks to `forall`.** Each chunk's compute assert ensures a recursive range predicate, e.g. `cells_ok(i, j, lo, hi)` (recursion on `hi − lo`). One induction lemma per grid family, written once (`lemma_cells_forall` in `red.rs`, reused by `grid_small.rs` and `assoc_id.rs`), turns the chunk conjunction into the `forall` premise of `lemma_identity`. Never one Z3 query over all chunks.
  - **Timing:** each assert ≤ 0.15 s measured at `--rlimit 4`, a 6× margin under the wall-clock cap, which a loaded machine erodes. Recursion inside compute ≤ 300 deep. Spec fn bodies evaluated by compute have ≤ 30 `let`s. No reliance on memoization.
  - Revert failing compute negative controls at once.
- **Generator.**
  - `scripts/gen_p256_group.py` is stdlib-only, run as `python3 -I scripts/gen_p256_group.py [--check]`.
  - It emits every `@generated` file, each with the header `// @generated by scripts/gen_p256_group.py — do not edit`.
  - `--check` regenerates into a temp dir and fails on any byte difference.
  - Before emitting, it self-checks in Python:
    - each identity is 0 at every grid point and sign;
    - RCB-decoded vs a literal transcription of `point_add` on 200 random P-256 pairs, plus G+G, G+(−G) and G+O;
    - the chain ends at O.
  - Every emitted datum is re-checked in Verus: certificate data by compute, chunk lemmas by the verifier. So the generator is not trusted.
  - `scripts/p256_pratt.json` comes from `scripts/p256_pratt_factor.py` (needs sympy; offline, untrusted, documented in its docstring). The generator only reads it.
- **TRUSTED.md row**, added in Task 2. It must not start with `| crypto::`, so the gate's row count is unchanged:
  ```
  | `by (compute_only)` results (Verus's spec-function interpreter): the 5b S-box chunks and the 5d Pratt certificates, torsion certificate, identity grids and nG chain are accepted from the interpreter's evaluation without a Z3 re-check, so an interpreter bug could make them unsound. Its per-assert timeout is wall-clock (≈0.22 s × rlimit), so a heavily loaded machine can make a chunk fail, never wrongly pass | crates/crypto/src/aes.rs, crates/crypto/src/p256_group/ | part of Verus (already in the trusted base); listed so the reliance is visible | never |
  ```
- **Proof patterns.**
  - `integer_ring` is unavailable. `nonlinear_arith` only with at most one product per side or tiny bodies (the 5c D1 probes).
  - Polynomial identities beyond that go through the grid machinery (Task 5), never inline Z3.
  - `hide(pow)`/`hide(finv)` except in `field.rs` and `order.rs`. `hide(point_add)`/`hide(scalar_mult)` in grid and RCB modules.
  - `#[verifier::spinoff_prover]` on the case lemmas of Task 8 and the induction lemmas of Tasks 1, 4 and 5.
- **`--rlimit 4` on every 5d module, every task:** `cd crates/crypto && cargo verus focus -- --verify-only-module p256_group::<m> --rlimit 4` passes for each module touched.
- **The four checks, every task:**
  1. `scripts/verify.sh` prints `verify.sh: all crates verified, duvet ok, escapes accounted (4)`;
  2. `cargo build && cargo test` pass with 0 warnings;
  3. the escape grep prints only the 4 existing `crates/crypto/src/*.rs:L:#[verifier::external_body]` lines;
  4. `python3 -I scripts/gen_p256_group.py --check` exits 0 (from Task 2 on).
- **Evidence run.**
  - `CARGO_TARGET_DIR=<scratch>/vt-5d-tN scripts/verify.sh` (absolute path), then `rm -rf` the dir.
  - The report lists:
    - the five slowest functions (`--output-json --time-expanded`);
    - the wall time of each touched module at `--rlimit 4`;
    - crypto's total.
  - No function may take ≥ 60 s.
- **Citations** are plain `//` comments (e.g. `// RCB 2016 eq. (1), a = -3`, `// Lucas 1876 / Pratt 1975`). No duvet lines.

## Review Focus

1. **Vacuous proofs.** A theorem can verify because its premise is unsatisfiable or a predicate is trivially true (`fits`, `on3`, `valid`, `rfits` with the −1 zero sentinel). Task 5 adds `lemma_identity_nonvacuous`, and Task 8 runs spot vectors (G+G, G+(−G)) through `dec`/`rcb`. Each must use a premise that is actually satisfied.
2. **Degree tracking too small for its grid.** If `rd_mul` drops the +3 per shared y-bit (the F_i factor) or mishandles the −1 sentinel, the grid would be too small. The `lemma_rfits_mul` proof must reject that. The Task 5 mutation makes `rd_mul` omit the +3 and must fail on `lemma_rfits_mul`, not elsewhere.
3. **Interface drift against 5c.** The exported statements are copied byte for byte. `lemma_5c_interface_smoke` (Task 9) calls both lemmas exactly as 5c Tasks 6–7 will: a doubling step on a ghost `ev`, and `1 <= k < p256_n()` with k: nat.
4. **Compute timeouts under load.** The cap is wall-clock, so verify.sh could fail on a busy machine. Every chunk is ≤ 0.15 s at `--rlimit 4`. The Task 7 report includes a run with four parallel `cargo verus focus` jobs, for each grid module.
5. **The spec's exact branch conditions.** `point_add` compares coordinates with plain `==` and tests `fmod(y1 + y2) == 0` before doubling. The correspondence (Task 8) must split on exactly those conditions, and must prove y2 == y1, as ints in [0, p), in the doubling branch. Spot vector: P + P with y1 ≠ 0, and P + (−P), on G.

---

### Task 1: Elementary number theory and the Lucas theorem (`nt.rs`)

**Files:**
- Create: `crates/crypto/src/p256_group/mod.rs`, whose first line is `#![allow(dead_code)]` (preflight), followed by `mod nt;` and the module docs. Later tasks add their `mod` lines.
- Create: `crates/crypto/src/p256_group/nt.rs`.
- Modify: `crates/crypto/src/lib.rs`, adding `mod p256_group;`.

**Interfaces** (`pub(crate)`, generic in q):
- `open spec fn powmod(a: int, e: nat, q: int) -> int`: square-and-multiply on e/2, `decreases e`, reducing `% q` at every step.
- `proof fn lemma_powmod(a: int, e: nat, q: int)`: requires `q > 1`; ensures `powmod(a, e, q) == pow(a, e) % q`.
- `open spec fn prod_pow(fs: Seq<(nat, nat)>) -> nat`, which is Π rᵢ^eᵢ.
- `open spec fn lucas_ok(q: nat, a: int, fs: Seq<(nat, nat)>) -> bool`, which holds iff all of:
  - `q > 2`;
  - `prod_pow(fs) == q − 1`;
  - `powmod(a, q − 1, q) == 1`;
  - `forall i: fs[i].0 > 1 && (q−1) % fs[i].0 == 0 && powmod(a, (q−1)/fs[i].0, q) != 1`.

  Written so that `compute_only` can evaluate it: recursion over `fs`, not `forall`.
- `open spec fn trial_ok(r: nat) -> bool`: no divisor in [2, ⌊√r⌋], recursion ≤ 256 deep for r < 2¹⁶.
  - `proof fn lemma_trial_prime(r: nat)`: requires `r >= 2`, `trial_ok(r)`; ensures `is_prime(r)`.
- Proof-only lemmas:
  - `lemma_pow_gcd` (aᵈ ≡ 1 ∧ aᵐ ≡ 1 ⇒ a^gcd(d,m) ≡ 1, by Euclid on exponents);
  - `lemma_bezout`;
  - `lemma_euclid_prime` (prime s | ab ⇒ s | a ∨ s | b);
  - `lemma_least_divisor_prime`;
  - `lemma_divisor_hits_factor` (1 < D | prod_pow(fs) with all rᵢ prime ⇒ ∃i. rᵢ | D).
- **`proof fn lemma_lucas(q: nat, a: int, fs: Seq<(nat, nat)>)`:** requires `lucas_ok(q, a, fs)` and `forall i: is_prime(fs[i].0)`. Ensures:
  - `is_prime(q)`;
  - `forall|x: int| x % (q as int) != 0 ==> #[trigger] (pow(x, (q - 1) as nat) % (q as int)) == 1`.

  Proof: order argument, then injectivity of i ↦ aⁱ mod q on [0, q−1), then `lemma_map_size` and `lemma_subset_equality` onto `Set::range(1, q)`.
- `proof fn lemma_lucas_smoke()` (compute): `lucas_ok(7, 3, seq![(2, 1), (3, 1)])`. Then `lemma_lucas` gives `is_prime(7)` and `pow(5, 6) % 7 == 1`.

- [ ] **Step 1:** Write `lemma_lucas_smoke` first. It is RED: nothing is defined.
- [ ] **Step 2:** Implement in the order listed: `powmod`, then gcd and Bezout, then Euclid, then factor hitting, then `lemma_lucas`.
- [ ] **Step 3: Mutations**, each failing on a named postcondition:
  - `powmod` odd step multiplies by `a + 1`;
  - `lucas_ok` drops the `!= 1` checks: `lemma_lucas` must fail, and `lucas_ok(9, 8, seq![(2, 3)])` is the counter-model (8⁸ ≡ 1 mod 9; a = 2 fails the first check, since 2⁸ mod 9 = 4) (preflight);
  - `trial_ok` stops at ⌊√r⌋ − 1.
- [ ] **Step 4:** Run the four checks (generator check n/a) and `--rlimit 4` on `p256_group::nt`. Escape count **4**.
- [ ] **Step 5: Commit:** `feat(crypto): verified Lucas primality theorem and FLT for certified moduli (p256_group::nt)`

**Size:** about 450 lines of proof, comparable to the heaviest 5b task.

---

### Task 2: Pratt certificates for p and n; field facts (`pratt.rs`, `field.rs`)

**Files:**
- Create: `scripts/gen_p256_group.py` (the `pratt` section and `--check`), `scripts/p256_pratt_factor.py` (copy of `<scratch>/probe-5d/py/pratt.py`) and `scripts/p256_pratt.json` (its output, `<scratch>/probe-5d/py/pratt.json`).
- Create: `crates/crypto/src/p256_group/pratt.rs` (@generated) and `crates/crypto/src/p256_group/field.rs`.
- Modify: `mod.rs`; `TRUSTED.md` (the Global Constraints row).

**Interfaces:**
- **`pratt.rs`**, generated:
  - per node q (26 nodes):
    - consts `Q_i`, `A_i` and `FS_i`;
    - one `proof fn lemma_cert_i_k()` per checked power. Each holds one compute assert, ensuring one `powmod(...) == 1` or `!= 1` fact, at ≤ 0.15 s (preflight);
    - `proof fn lemma_cert_i()` ensuring `lucas_ok(Q_i, A_i, FS_i)`. It is assembled from the `lemma_cert_i_k` facts by unfolding the fs-recursion (`reveal_with_fuel`, |fs| ≤ 12), with no compute (preflight);
  - `proof fn lemma_prime_i()` ensuring `is_prime(Q_i)`, from `lemma_lucas` and the children's `lemma_prime_*` or `lemma_trial_prime`, emitted leaves-first;
  - exports `pub(crate) proof fn lemma_p_prime()` and `lemma_n_prime()`, ensuring `is_prime(p256_p() as nat)` and `is_prime(p256_n() as nat)`.
- **`field.rs`:**
  - `pub(crate) open spec fn P_LIT() -> int`, `N_LIT`, `B_LIT`, `GX_LIT`, `GY_LIT` (int literals) and `G_LIT() -> SpecPoint` (`Affine(GX_LIT(), GY_LIT())`).
  - `pub(crate) proof fn lemma_group_consts()` (compute): `p256_p() == P_LIT()`, `p256_n() == N_LIT()`, `p256_b() == B_LIT()`, and `p256_g() == G_LIT()`.
  - `lemma_flt_p(x: int)`: requires `fmod(x) != 0`; ensures `fmod(pow(x, (p256_p() − 1) as nat)) == 1`.
  - `lemma_flt_n(x: int)`: requires `x % p256_n() != 0`; ensures `pow(x, (p256_n() - 1) as nat) % p256_n() == 1` (preflight).
  - `lemma_finv_mul(x: int)`: requires `fmod(x) != 0`; ensures `fmod(x * finv(x)) == 1`.
  - `lemma_finv_unique(x: int, w: int)`: requires `fmod(x * w) == 1`; ensures `finv(x) == fmod(w)`.
  - `lemma_no_zero_div(a: int, b: int)`: requires `fmod(a * b) == 0`; ensures `fmod(a) == 0 || fmod(b) == 0`.
  - `lemma_finv_powmod(x: int)`: ensures `finv(x) == powmod(x % p256_p(), (p256_p() − 2) as nat, p256_p())`.
  - `lemma_finv_one()`: ensures `finv(1) == 1`.
  - `lemma_b_range()`: ensures `0 < p256_b() < p256_p()`.

- [ ] **Step 1:** Write the generator's `pratt` section and emit `pratt.rs`. Verify `p256_group::pratt` alone. Then Python-mutate one witness in a temp copy (`A_p = 5`, a non-generator): the corresponding `lemma_cert` must fail. Revert at once.
- [ ] **Step 2:** Implement `field.rs`.
- [ ] **Step 3: Mutations:**
  - one exponent eᵢ in `FS_p` off by one → `lemma_cert` fails;
  - `lemma_finv_mul` without the `fmod(x) != 0` requires → fails at x = p.
- [ ] **Step 4:** Run the four checks, `--rlimit 4` on `pratt` and `field`, and report `pratt`'s module wall time. Escape count **4**.
- [ ] **Step 5: Commit:** `feat(crypto): P-256 p and n proven prime by checked Pratt certificates; FLT and field facts mod p`

**Size:** about 150 lines hand-written, 150 Python, about 400 generated.

---

### Task 3: No 2-torsion (`torsion.rs`, `torsion_cert.rs`)

**Files:**
- Create: `crates/crypto/src/p256_group/torsion.rs`, plus `torsion_cert.rs` (@generated: the Bezout polynomials u and v, and the compute lemmas).
- Modify: `mod.rs` and the generator (`torsion` section).

**Interfaces:**
- `struct Q2 { c0: int, c1: int, c2: int }`, a quadratic mod f.
- `spec fn qmul(a: Q2, b: Q2) -> Q2`: product reduced by x³ ≡ 3x − B_LIT and x⁴ ≡ 3x² − B_LIT·x, coefficients `% P_LIT()`.
- `spec fn qpow(a: Q2, e: nat) -> Q2`: square-and-multiply, ≤ 256 deep.
- `spec fn qev(a: Q2, r: int) -> int`.
- `lemma_qmul_ev(a, b, r)`: requires `fmod(r*r*r − 3*r + p256_b()) == 0`; ensures `fmod(qev(qmul(a, b), r)) == fmod(qev(a, r) * qev(b, r))`.
- `lemma_qpow_ev(e, r)`: same requires; ensures `fmod(qev(qpow(X, e), r)) == fmod(pow(r, e))`.
- **Generated:**
  - `lemma_xp_mod_f()` (compute): `qpow(X, p) == XP_POLY`, split into ≤ 0.15 s pieces by exponent prefix if needed. It is named `XP_POLY` because `G_LIT` is the generator point (preflight);
  - `lemma_bezout_cert()` (compute): `u·f + v·(XP_POLY − x) ≡ 1`, as a polynomial identity of degree ≤ 4 checked coefficientwise (preflight).
- **Export:** `pub(crate) proof fn lemma_no_2_torsion(x: int)`, ensuring `fmod(x * x * x - 3 * x + p256_b()) != 0`.

- [ ] **Step 1:** Generator section, then the generated file. Verify it alone.
- [ ] **Step 2:** Implement `torsion.rs`: a root r gives r ≢ 0 (b ≢ 0), r^p ≡ r (`lemma_flt_p`), and so 1 ≡ 0.
- [ ] **Step 3: Mutations:**
  - `qmul` reduces x³ ≡ 3x + b → `lemma_qmul_ev` fails;
  - one Bezout coefficient changed → `lemma_bezout_cert` fails (compute; revert at once).
- [ ] **Step 4:** Run the four checks and `--rlimit 4`. Escape count **4**.
- [ ] **Step 5: Commit:** `feat(crypto): P-256 curve has no 2-torsion (x^3 - 3x + b has no root mod p), by checked gcd certificate`

**Size:** about 200 lines plus about 60 generated.

---

### Task 4: Formal polynomials and the grid theorem (`poly.rs`)

**Files:**
- Create: `crates/crypto/src/p256_group/poly.rs`.
- Modify: `mod.rs`.

**Interfaces** (`pub(crate)`; all congruences are mod `p256_p()`; formal objects are proof-only):
- `pub enum MP { K(int), L(Seq<MP>) }`: a constant, or coefficients in the leading variable, each a polynomial in the remaining variables.
- `spec fn ev(a: MP, xs: Seq<int>) -> int`: Horner in `xs[0]` over `ev(cs[j], xs.drop_first())`.
- `spec fn fits(a: MP, ds: Seq<nat>) -> bool`:
  - `K` → true;
  - `L(cs)` → `ds.len() > 0 && cs.len() <= ds[0] + 1 && forall j: fits(cs[j], ds.drop_first())`.
- `spec fn padd`, `pmul`, `pk(c)`, `px(i: nat)`.
  - `pmul` is defined as `a0·Q + x·(tail·Q)` so that its proofs are structural.
- Lemmas:
  - `lemma_ev_add`, `lemma_ev_mul`, `lemma_ev_k`, `lemma_ev_x` (exact over int);
  - `lemma_fits_add` (pointwise max);
  - `lemma_fits_mul` (pointwise sum);
  - `lemma_fits_x`.
- `lemma_roots(cs: Seq<int>, pts: Seq<int>)`:
  - requires `pts.len() >= cs.len()`, pairwise distinct mod p, and `forall t: fmod(horner(cs, pts[t])) == 0`;
  - ensures `forall j: fmod(cs[j]) == 0`;
  - proof: synthetic division by (x − r) plus `lemma_no_zero_div`.
- **`proof fn lemma_grid(a: MP, ds: Seq<nat>, g: Seq<Seq<int>>)`:**
  - requires `fits(a, ds)`, `g.len() == ds.len()`, and `forall k: g[k].len() > ds[k] && distinct_mod_p(g[k])`;
  - requires `forall|xs| in_grid(xs, g) ==> fmod(ev(a, xs)) == 0`;
  - ensures `forall|xs: Seq<int>| xs.len() == ds.len() ==> fmod(ev(a, xs)) == 0`;
  - proof: induction on the number of variables.
- `proof fn lemma_grid_smoke()`:
  - a = (x0 + x1)² − x0² − 2x0x1 − x1², built from `padd`/`pmul`;
  - grid {0, 1, 2}²;
  - the grid premise is discharged by unfolding `ev` on nine literal points (Z3, no compute).

- [ ] **Step 1:** Write `lemma_grid_smoke`. It is RED.
- [ ] **Step 2:** Implement in the order listed.
- [ ] **Step 3: Mutations:**
  - `fits` with `cs.len() <= ds[0] + 2` → `lemma_grid` fails;
  - `lemma_roots` with `pts.len() >= cs.len() − 1` → fails;
  - the smoke grid shrunk to {0, 1} × {0, 1, 2} → its premise fails.
- [ ] **Step 4:** Run the four checks and `--rlimit 4`. Escape count **4**.
- [ ] **Step 5: Commit:** `feat(crypto): formal polynomials over F_p and the grid vanishing theorem (p256_group::poly)`

**Size:** about 500 lines. This is the hardest proof task, a 5b-scale task by itself.

---

### Task 5: Curve-reduced 8-component layer and the identity theorem (`red.rs`)

**Files:**
- Create: `crates/crypto/src/p256_group/red.rs`.
- Modify: `mod.rs`.

**Interfaces:**
- **Component conventions.** Components are indexed by s ∈ [0, 8), a bitmask over {y0, y1, y2}.
  - Indices and masks are `u8`: Verus rejects `^`/`&` on `nat`, while `u8` xor/and evaluate under compute, and `(s ^ r) < 8` holds by `bit_vector` (preflight).
  - `fx(i: nat) -> MP` is the formal x_i³ − 3x_i + B_LIT in 3 variables.
- **Formal ops.** `type RF = Seq<MP>` (length 8).
  - `rf_add`, `rf_k(c)`, `rf_x(i)`, `rf_y(i)`;
  - `rf_mul(a, b)`, whose component r is `Σ_s a[s]·b[s ^ r]·Π_{i ∈ s & (s ^ r)} fx(i)`.
- **Values.**
  - `yw(ys, s) = Π_{i ∈ s} ys[i]`;
  - `rval(a: RF, xs, ys) = Σ_s yw(ys, s)·ev(a[s], xs)`;
  - `on3(xs, ys)`: lengths 3, and `forall i: fmod(ys[i]*ys[i]) == fmod(xs[i]*xs[i]*xs[i] − 3*xs[i] + p256_b())`.
- **Homomorphism.** `lemma_rf_add_hom`, and `lemma_rf_mul_hom(a, b, xs, ys)`: requires `on3`; ensures `fmod(rval(rf_mul(a, b), xs, ys)) == fmod(rval(a, xs, ys) * rval(b, xs, ys))`.
- **Degree tracking**, computable by `compute_only`.
  - `type RD = Seq<Seq<int>>` (8 × 3). A row `[−1, −1, −1]` means "component is the zero polynomial".
  - `rd_add` (max; −1 is the identity), and `rd_mul`, which for component r is the max over s with both inputs non-zero of `da[s] + db[s^r] + 3·[i ∈ s & (s^r)]` per variable i.
  - `rfits(a, d)`, `lemma_rfits_add`, `lemma_rfits_mul`.
  - A sentinel row is evaluative: `forall xs: ev(a[s], xs) == 0`, exactly over int. It can't be structural (`a[s] == K(0)`), because `rf_mul` never produces a structural `K(0)`, and `lemma_rfits_mul` would be unprovable (preflight).
- **Hadamard.** `lemma_hadamard(c: Seq<int>, ys: Seq<int>)`:
  - requires `forall i: fmod(ys[i]) != 0`, and for all 8 sign patterns σ, `fmod(Σ_s χ_σ(s)·yw(ys, s)·c[s]) == 0`;
  - ensures `forall s: fmod(c[s]) == 0`.
- **`proof fn lemma_identity(g: RF, d: RD, gx: Seq<Seq<int>>, gy: Seq<Seq<int>>)`:**
  - requires:
    - `rfits(g, d)`;
    - every non-sentinel `d[s][k] < gx[k].len()`;
    - `gx[k]` distinct mod p;
    - `on3`-style facts at the grid: `fmod(gy[k][t]²) == fmod(f(gx[k][t]))`, both nonzero;
    - `forall` grid indices i, j, l and σ ∈ [0, 8): `fmod(rval(g, [gx0[i], gx1[j], gx2[l]], σ·[gy0[i], gy1[j], gy2[l]])) == 0`;
  - ensures `forall|xs, ys| on3(xs, ys) ==> fmod(rval(g, xs, ys)) == 0`.
  - One- and two-point identities (preflight):
    - each unused variable gets a 1-point grid (degree 0);
    - callers satisfy `on3` with a repeated point, e.g. `xs = [x1, x2, x1]`, so `lemma_g_curve_pt` (Task 10) is never needed earlier.
- **Smoke lemmas:**
  - `lemma_identity_smoke()`: (y0 + y1)² − f(x0) − f(x1) − 2y0y1 ≡ 0 through `lemma_identity`, with a 4×4 grid (x-degree 3). Its grid premise is one inline compute over a 4 × 4 × 8-sign spec fn, about 128 tiny evaluations.
  - `lemma_identity_nonvacuous()`: the grid premises of the smoke lemma hold, `on3` holds at a concrete G-based point, and `rfits` holds for the smoke polynomial.

- [ ] **Step 1:** Write the two smoke lemmas. They are RED.
- [ ] **Step 2:** Implement.
- [ ] **Step 3: Mutations:**
  - `rd_mul` without the +3 → fails at `lemma_rfits_mul` (Review Focus 2);
  - `lemma_hadamard` with 7 sign patterns → fails;
  - `on3` dropping `p256_b()` → `lemma_rf_mul_hom` fails.
- [ ] **Step 4:** Run the four checks and `--rlimit 4`. Escape count **4**.
- [ ] **Step 5: Commit:** `feat(crypto): curve-reduced polynomial layer and grid identity theorem for y^2 = x^3 - 3x + b`

**Size:** about 450 lines.

---

### Task 6: The RCB formula and the small identities (`rcb.rs`, `grid_small.rs`)

**Files:**
- Create: `crates/crypto/src/p256_group/rcb.rs`, plus `grid_small.rs` (@generated: grid data and chunk lemmas for I2–I10 and RES1–2).
- Modify: `mod.rs` and the generator (`grid` section: QR x-values, √ via exponent (p+1)/4, a Python mirror of `rd_*`, self-checks).

**Interfaces:**
- **The plain formula.** `pub struct Proj { pub x: int, pub y: int, pub z: int }`, and `spec fn rcb(a: Proj, b: Proj) -> Proj`: exactly D2's formula, every product and output coordinate reduced `% P_LIT()`, with `b3 = 3·B_LIT()`. The `fmod`-level statements in later tasks get there through `lemma_group_consts`.
- **Its mirrors.**
  - formal: `rcb_f(a: PF, b: PF) -> PF`, where `PF { x: RF, y: RF, z: RF }`;
  - degrees: `rcb_d(a: PD, b: PD) -> PD`, computable;
  - `lemma_rcb_link(...)`: under `on3`, related inputs give related outputs, coordinatewise `fmod(plain) == fmod(rval(formal))`;
  - `lemma_rcb_fits(...)`.
  - Every identity below has a plain spec fn `id_<name>(xs, ys) -> int`, a formal `idf_<name>() -> RF`, a degree table and a link lemma, each built only from `rcb`/`rcb_f`/`rcb_d` and the ring ops.
- **Structural lemmas** (Z3, small steps):
  - `lemma_rcb_symm(a, b)`: `rcb(a, b) == rcb(b, a)`;
  - `lemma_rcb_scale_l(k, a, b)`: `rcb(sc(k, a), b) == sc(k*k, rcb(a, b))` (`sc` scales and `fmod`s all coordinates); and `_r`;
  - `lemma_rcb_inf_l(yv, b)`: `rcb(Proj { x: 0, y: yv, z: 0 }, b) == sc(yv*yv*b.y, b)`.
- **Exported identity lemmas**, each over plain values for all xs, ys with `on3`: `lemma_id_chord_x`, `_chord_y`, `_chord_z`, `_dbl_x`, `_dbl_y`, `_dbl_z`, `_inv_x`, `_inv_z`, `_inv_y`, `_closure_chord`, `_closure_dbl`, each ensuring `fmod(id_<name>(xs, ys)) == 0`.
  - The `id_inv_*` identities (I8) take Q = `Proj { x: x, y: P_LIT() − y, z: 1 }`, so that in the spec's P+(−P) branch y2 == p − y1 holds exactly, and no rcb-congruence lemma is needed (preflight).
  - RES1 and RES2 are y-free and go through `lemma_grid` directly, as `lemma_res1(x1, x2)` and `lemma_res2(x1, x2, e)`.
- **`grid_small.rs`**, generated:
  - grid x-values: the first 13 x ≥ 0 with f(x) a nonzero square mod p, `[0, 5, 6, 8, 9, 12, 13, 17, 23, 24, 25, 26, 29]` (planner check), and their roots;
  - one chunk lemma per identity and grid slice (≤ 0.15 s each);
  - one compute lemma per identity checking its degree table against the grid sizes;
  - `lemma_grid_pts_ok()` (compute, over the 13 literal points with `P_LIT`/`B_LIT`, then bridged by `lemma_group_consts`) discharges `lemma_identity`'s grid premises. Task 7 reuses it (preflight). For every t:
    - `gy(t)² ≡ f(gx(t))`;
    - `gx(t) ≢ 0` and `gy(t) ≢ 0`;
    - the `gx` values are pairwise distinct mod p;
  - `lemma_grid_seq()` states that the `Seq` literals `lemma_identity` takes equal the index fns `gx(i)`/`gy(i)` the chunks evaluate. Task 7 reuses it (preflight);
  - chunks ensure `cells_ok`-style range predicates, glued by `lemma_cells_forall` (Global Constraints).

- [ ] **Step 1:** Generator `grid` section, with the Python self-check printing `all identities zero on grid: 13/13` and `rcb vs point_add: 203/203`. Emit `grid_small.rs`.
- [ ] **Step 2:** Implement `rcb.rs`. Verify `rcb` and then `grid_small` alone.
- [ ] **Step 3: Mutations:**
  - `w = −3·X1·X2` → `−2·…` fails in a named `grid_small` chunk (compute; revert);
  - `rcb_d` adds 1 less to x-degree in `t0` → `lemma_rcb_fits` fails;
  - I4 with d² in place of d³ fails.
- [ ] **Step 4:** Run the four checks, `--rlimit 4`, and the module wall times. Escape count **4**.
- [ ] **Step 5: Commit:** `feat(crypto): complete projective addition (RCB, a = -3) and its correspondence identities, proven by grid evaluation`

**Size:** about 400 lines, plus about 250 Python and about 250 generated.

---

### Task 7: The associativity identity (`assoc_id.rs`, `grid_assoc_{a,b,c,d}.rs`)

**Files:**
- Create: `crates/crypto/src/p256_group/assoc_id.rs`, and the four @generated modules `grid_assoc_a.rs` … `grid_assoc_d.rs`. They split the 10 × 13 (i, j) pairs by i: {0–2}, {3–5}, {6–7}, {8–9}.
- Modify: `mod.rs` and the generator.

**Interfaces:**
- `spec fn assoc_minor(m: nat, xs, ys) -> int` for m ∈ {0, 1, 2}: the m-th 2×2 minor of `rcb(rcb(A0, A1), A2)` against `rcb(A0, rcb(A1, A2))`, with `Ai = Proj { x: xs[i], y: ys[i], z: 1 }`. Its formal and degree mirrors come via Task 6's link and fits lemmas.
- `proof fn lemma_assoc_degrees()` (compute, in `assoc_id.rs`): every non-sentinel degree row of the three minors is ≤ (9, 12, 9).
  - Its cost is unprobed: about 100+ `rd_mul`s, each 64 pairs × 3. Time it first.
  - Fallback if it exceeds 0.15 s: the generator emits each rcb level's degree table as a literal, checked by one compute `rcb_d(lit, lit) == lit` per level (preflight).
- **Generated chunks.**
  - Chunk `lemma_assoc_i_j_h` ensures `assoc_cell(i, j, 5h..5h+5)`: all three minors are 0 at the 5 × 8 sign points. Each body is one compute assert of about 40 plain evaluations, 0.12 s.
  - 260 chunks: grids |S0| = 10, |S1| = 13, |S2| = 10 from the table above.
  - Each chunk ensures `assoc_cells_ok(i, j, lo, hi)`.
  - Each generated `grid_assoc_*` module also emits a glue lemma for its i-range, with one call per chunk (≤ 78 calls).
  - `assoc_id.rs` calls the four glue lemmas, then `lemma_cells_forall`, together with `lemma_grid_pts_ok` and `lemma_grid_seq` from `grid_small`. No single query runs over all chunks (preflight).
- **Export:** `pub(crate) proof fn lemma_rcb_assoc_minors(xs: Seq<int>, ys: Seq<int>)`: requires `on3(xs, ys)`; ensures the three minors ≡ 0.

- [ ] **Step 1:** Generator section; the self-check prints `assoc: 10400/10400 sign-points zero`. Emit the four modules.
- [ ] **Step 2:** Implement `assoc_id.rs`. Verify each grid module alone and record its wall time at `--rlimit 4`. The target is ≤ 10 s per module.
- [ ] **Step 3: Mutations:**
  - right-hand side `rcb(A0, rcb(A1, A1))` (a false identity): the first chunk fails (compute; revert);
  - drop the last grid point of S1 (|S1| = 12): `lemma_identity`'s degree premise fails;
  - `b3 = 2·b` in `rcb`: the first chunk fails.
- [ ] **Step 4:** Run the four checks and the evidence run. Add the load test: run the four grid modules as four parallel `cargo verus focus` jobs, each with its own absolute `CARGO_TARGET_DIR=<scratch>/vt-5d-t7-{a,b,c,d}` (one shared dir would serialize on the cargo lock). All must pass. Report the max chunk time, then `rm -rf` the four dirs. Escape count **4**.
- [ ] **Step 5: Commit:** `feat(crypto): associativity of the complete P-256 addition law as a grid-checked curve identity`

**Size:** about 120 lines, about 80 Python and about 1600 generated. Verify time is dominated by about 25 s of compute.

---

### Task 8: Associativity and closure of the spec's `point_add` (`group.rs`)

**Files:**
- Create: `crates/crypto/src/p256_group/group.rs`.
- Modify: `mod.rs`.

**Interfaces:**
- **Encoding and decoding.**
  - `pub open spec fn curve_pt(p: SpecPoint) -> bool { p is Infinity || (p is Affine && on_curve(p->0, p->1)) }`.
  - `spec fn enc(p: SpecPoint) -> Proj`: Infinity ↦ (0, 1, 0), Affine ↦ (x, y, 1).
  - `spec fn dec(a: Proj) -> SpecPoint`: if `fmod(a.z) != 0` then `Affine(fmod(a.x * finv(a.z)), fmod(a.y * finv(a.z)))`, else Infinity.
  - `spec fn valid(a: Proj) -> bool` (preflight):
    - first, `0 <= a.x < p256_p() && 0 <= a.y < p256_p() && 0 <= a.z < p256_p()`. This range is needed because `lemma_rcb_inf_l` and `lemma_rcb_scale_*` are exact equalities. `enc` of a `curve_pt` and every `rcb` output (`% P_LIT()`) satisfy it;
    - then either (`fmod(a.z) != 0` and `curve_pt(dec(a))`), or (`fmod(a.z) == 0`, `fmod(a.x) == 0` and `fmod(a.y) != 0`).
  - `lemma_dec_enc(p)` and `lemma_enc_valid(p)`.
- **`lemma_w_nonzero(x1: int, x2: int)`:** ensures `fmod(W(x1, x2)) != 0`. Uses RES1, RES2, `lemma_finv_mul` and `lemma_no_2_torsion`, by D2's two cases.
- **`lemma_rcb_correct_aff(p, q)`:** requires both Affine and `curve_pt`; ensures `valid(rcb(enc(p), enc(q)))` and `dec(rcb(enc(p), enc(q))) == point_add(p, q)`. It splits on the spec's exact conditions:
  - `x1 != x2`: chord; I2, I3, I4, `lemma_w_nonzero`, I10a;
  - `x1 == x2 && fmod(y1 + y2) == 0`, in this order (preflight):
    1. `lemma_no_2_torsion(x1)` gives y1 ≢ 0, and with it y2 == p − y1, as I8's `P_LIT() − y` form requires;
    2. I8a–c;
    3. the doubling case on (p, p);
    4. `lemma_no_2_torsion` on 2p;
  - else doubling: prove `y2 == y1` first; then I5–I7 and I10b.
- **`lemma_rcb_correct(a, b)`:** requires `valid(a)` and `valid(b)`; ensures `valid(rcb(a, b))` and `dec(rcb(a, b)) == point_add(dec(a), dec(b))`. It uses `lemma_rcb_inf_l`, `_symm`, `_scale_l`/`_r` and `lemma_rcb_correct_aff`.
- **`lemma_dec_prop(a, b)`:** requires `valid(a)`, `valid(b)` and the three minors ≡ 0; ensures `dec(a) == dec(b)`.
- **Exports:**
  - `pub(crate) proof fn lemma_point_add_closed(p, q)`: requires `curve_pt(p)` and `curve_pt(q)`; ensures `curve_pt(point_add(p, q))`;
  - `pub(crate) proof fn lemma_point_add_assoc(p, q, r)`: requires `curve_pt` for all three; ensures `point_add(point_add(p, q), r) == point_add(p, point_add(q, r))`. Any Infinity is handled by unfolding `point_add`; all-affine goes through `lemma_rcb_assoc_minors`, `lemma_rcb_correct` ×4 and `lemma_dec_prop`.
- **`proof fn lemma_group_spot()`** (no compute on `point_add`): with G from `lemma_group_consts`, show `dec(rcb(enc(G), enc(neg(G)))) is Infinity` and that `valid` holds for `rcb(enc(G), enc(G))`. This guards Review Focus 1 and 5.
  - `spec fn neg(p: SpecPoint) -> SpecPoint` maps `Affine(x, y)` to `Affine(x, P_LIT() − y)` and Infinity to Infinity.
  - The Infinity part is ground Z3 on `rcb(...).z == 0`.
  - `valid` comes from `lemma_rcb_correct_aff(G, G)`, because `dec` involves `finv`, which neither Z3 nor compute may evaluate (preflight).

- [ ] **Step 1:** Write `lemma_group_spot` and the two export signatures. They are RED.
- [ ] **Step 2:** Implement in the order listed, with `#[verifier::spinoff_prover]` on each case lemma.
- [ ] **Step 3: Mutations:**
  - the doubling branch skips the `y2 == y1` step → fails;
  - `valid` without `fmod(a.y) != 0` → `lemma_dec_prop` fails;
  - `lemma_w_nonzero` without `lemma_no_2_torsion` → fails.
- [ ] **Step 4:** Run the four checks, the evidence run and the five slowest functions. Escape count **4**.
- [ ] **Step 5: Commit:** `feat(crypto): associativity and closure of the frozen P-256 point_add (SEC 1 v2 §2.2.1)`

**Size:** about 450 lines.

---

### Task 9: Scalar-multiplication laws and the 5c doubling interface (`mod.rs`)

**Files:**
- Modify: `crates/crypto/src/p256_group/mod.rs`.

**Interfaces:**
- `pub(crate) proof fn lemma_scalar_mult_closed(k: nat, pt: SpecPoint)`: requires `curve_pt(pt)`; ensures `curve_pt(scalar_mult(k, pt))`.
- `pub(crate) proof fn lemma_scalar_mult_add(a: nat, b: nat, pt: SpecPoint)`: requires `curve_pt(pt)`; ensures `scalar_mult(a + b, pt) == point_add(scalar_mult(a, pt), scalar_mult(b, pt))`.
  - Proof: induction on a. The step is `point_add(pt, point_add(aP, bP)) == point_add(point_add(pt, aP), bP)` by `lemma_point_add_assoc`. No commutativity is needed.
- `lemma_scalar_mult_double(j, pt)`: exactly the Global Constraints statement, from `lemma_scalar_mult_add(j, j, pt)`.
- `proof fn lemma_5c_interface_smoke(ev: nat, pt: SpecPoint)` (Review Focus 3): requires the 5c form. It states 5c Task 6's step, `scalar_mult((2 * ev + 1) as nat, pt) == point_add(pt, point_add(scalar_mult(ev, pt), scalar_mult(ev, pt)))`, using the lemma plus one unfold.

- [ ] **Step 1:** Write the smoke lemma. It is RED.
- [ ] **Step 2:** Implement.
- [ ] **Step 3: Mutation:** state the add lemma as `scalar_mult(a + b + 1, …)` → fails at the base case.
- [ ] **Step 4:** Run the four checks. Escape count **4**.
- [ ] **Step 5: Commit:** `feat(crypto): scalar_mult additivity and the doubling law (2j)P = jP + jP, proved`

**Size:** about 120 lines.

---

### Task 10: nG = O and kG ≠ O (`order.rs`, `chain.rs`)

**Files:**
- Create: `crates/crypto/src/p256_group/order.rs`, plus `chain.rs` (@generated).
- Modify: `mod.rs` (its `mod` line and the `lemma_scalar_mult_g_nonzero` wrapper) (preflight) and the generator (`chain` section).

**Interfaces:**
- `proof fn lemma_g_curve_pt()` (compute on literals, via `lemma_group_consts`): ensures `curve_pt(p256_g())`.
- **Fast point addition.**
  - `spec fn finv_fast(x: int) -> int { powmod(x % P_LIT(), (P_LIT() - 2) as nat, P_LIT()) }`.
  - `spec fn finv_fast` and `padd_fast` use `P_LIT()`/`B_LIT()`, not `p256_p()` (Global Constraints).
  - `spec fn padd_fast(a, b)`: `point_add`'s case structure and association order, with `fmod` → `% P_LIT()` and `finv` → `finv_fast`.
  - `lemma_padd_fast(a, b)`: ensures `padd_fast(a, b) == point_add(a, b)`, via `lemma_group_consts` and `lemma_finv_powmod`.
- **The chain.**
  - `spec fn chain(acc: SpecPoint, bits: Seq<bool>) -> SpecPoint`: per bit, `acc = padd_fast(acc, acc)`, then `padd_fast(G_LIT(), acc)` if the bit is set.
  - `lemma_chain(e: nat, bits)`: ensures `chain(scalar_mult(e, G), bits) == scalar_mult(e · 2^|bits| + be_val(bits), G)`. It uses `lemma_scalar_mult_double`, one `scalar_mult` unfold and `lemma_padd_fast`.
- **`chain.rs`**, generated:
  - 33 checkpoint points `PT_k` (PT_0 = G, PT_32 = Infinity) and exponents `E_k`;
  - chunk lemmas `lemma_chain_k()` ensuring `chain(PT_k, BITS_k) == PT_{k+1}` (compute, 8 bits, ≤ 0.15 s; the first chunk has 7 bits, since n's top bit seeds E_0 = 1);
  - `lemma_n_bits()` (compute): `E_32 == N_LIT()`, bridged to `p256_n()` by `lemma_group_consts` (preflight), and `E_{k+1} == E_k · 2^|BITS_k| + be_val(BITS_k)`.
- **Exports:**
  - `pub(crate) proof fn lemma_n_g_inf()`: ensures `scalar_mult(p256_n() as nat, p256_g()) is Infinity`;
  - `lemma_scalar_mult_g_nonzero(k)`: exactly the Global Constraints statement. It is defined in `mod.rs` as a wrapper whose body is `{ order::lemma_g_order(k); }`; there is no `use` re-export (preflight).
  - `pub(crate) proof fn lemma_g_order(k: nat)` in `order.rs`, with the same requires and ensures (preflight).
    - Proof: suppose kG is Infinity. Take m = `powmod(k, n − 2, n)`; by `lemma_flt_n`, k·m = 1 + t·n.
    - `lemma_scalar_mult_add`, by induction on m, gives (k·m)G = O; and (t·n)G = O via `lemma_n_g_inf`.
    - So G = O, contradicting `p256_g() is Affine`.

- [ ] **Step 1:** Generator section; the self-check prints `chain ends at O: True`. Emit `chain.rs`.
- [ ] **Step 2:** Implement `order.rs`.
- [ ] **Step 3: Mutations:**
  - one `BITS_k` bit flipped → that chunk fails (compute; revert);
  - `padd_fast` with exponent p − 3 → `lemma_padd_fast` fails;
  - `lemma_scalar_mult_g_nonzero` with `k <= p256_n()` → fails.
- [ ] **Step 4:** Run the four checks and the evidence run. Report crypto's total verify time before and after 5d; the budget is +90 s. Escape count **4**.
- [ ] **Step 5: Commit:** `feat(crypto): ord(G) = n for P-256 — nG = O by checked chain, kG != O for 1 <= k < n`

**Size:** about 220 lines, plus about 80 Python and about 250 generated.

---

## Size estimate

| task | hand-written Verus | generated | proof difficulty |
|---|---|---|---|
| 1 nt | 450 | — | high (5b-scale) |
| 2 pratt/field | 150 | 400 | low |
| 3 torsion | 200 | 60 | medium |
| 4 poly | 500 | — | high (5b-scale) |
| 5 red | 450 | — | high |
| 6 rcb + small ids | 400 | 250 | medium |
| 7 assoc grid | 120 | 1600 | low (compute-bound) |
| 8 group | 450 | — | high |
| 9 smul | 120 | — | low |
| 10 order | 220 | 250 | medium |

That is about 3000 hand-written lines over 10 tasks, with 4 of them 5b-scale. 5a and 5b were 5 tasks each, so 5d is about **2× 5b**. The 5c D1 guess ("more than 5a + 5b + 5c combined") was for the SHNF route; the grid route is smaller.

## Exit criteria (Phase 5d)

- All four checks pass on the merged tree; `escapes accounted (4)`.
- `crate::p256_group::{lemma_scalar_mult_double, lemma_scalar_mult_g_nonzero}` have exactly the frozen statements, and `lemma_5c_interface_smoke` verifies.
- TRUSTED.md gains only the `compute_only` row, and `| crypto::` rows are unchanged.
- `gen_p256_group.py --check` passes. Every `@generated` file is reproduced byte for byte.
- No 5d function takes ≥ 60 s. Every compute chunk is ≤ 0.15 s at `--rlimit 4`, and the parallel load test passes.
- `phase-5d` is merged into `main`. The controller then amends 5c's Global Constraints `compute_only` bullet so that it governs 5c's files (`p256.rs`, `ecdsa.rs`, `mont.rs`) and names `p256_group` as 5d's scope. This is a wording-only change, which 5c Task 6's preflight records.

## Self-review (done while writing)

- **Coverage of the brief.**
  - Primality of p and FLT: Tasks 1–2.
  - Associativity in the spec's case structure: Tasks 6–8, with D2's case split being exactly the spec's.
  - Induction to the doubling lemma: Task 9.
  - The extra 5c export, kG ≠ O: Task 10, which also gives n prime.
  - Closure: Task 8.
  - Degenerate cases:
    - P + (−P): I8;
    - doubling with y = 0 is impossible: Task 3, used in Task 8;
    - Infinity: by unfolding, Task 8.
  - Generator committed and `--check`ed; TRUSTED note; time budget; `--rlimit 4` everywhere.
- **Probed vs not.**
  - **Probed:**
    - the evaluator limits;
    - SHNF and Kronecker infeasibility;
    - grid chunk speed and correctness on real points, with a negative control;
    - every identity reduces to zero (Python, exact);
    - modexp and spec point-op cost;
    - Pratt factorizations;
    - no 2-torsion numerically;
    - module isolation;
    - trait non-evaluation.
  - **Probed after the advisor's review:** the 60× cost of an `os2ip`-based modulus, which is why the literal-constant rule exists.
  - **Not probed:** the proof effort of Tasks 1, 4, 5 and 8. These are standard inductive developments with no compute, sized by analogy with 5b.
- **Type consistency.** `Proj`, `PF`/`PD`, `RF`/`RD`, `MP`, `curve_pt`, `on3`, `valid`/`dec`/`enc`, `powmod` and `finv_fast` are used with one meaning throughout. The exported names match 5c @ 4812b13.
