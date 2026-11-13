# Phase 9b1: a Frags index (C15) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace `quic::frags::Frags`'s sorted `Vec` of fragments with a verified join-based AVL of chunks, so every
`insert`, `after_insert` and `take_front` call costs O(log n + bytes) worst case, proved by a ghost cost.

**Architecture:** A generic module `quic::avl` (in-order `Seq` view, `join`/`split`/`pop_min`/`get_le`/in-order
consume, each returning a `Ghost<nat>` cost bounded in its ensures). `Frags` is rebuilt on `avl::Tree<Vec<u8>>` with
chunks of at most `CAP` = 256 bytes and the follower rule (`K` = 128). The public `Frags` contract and
`crypto_stream.rs` do not change.

**Tech Stack:** Rust 1.98.1, Verus 0.2026.10.04.426d8b0 (vstd 0.0.0-2026-10-04-0306), pinned; no upgrades.

**Spec:** `docs/superpowers/specs/2026-11-10-phase-9b1-frags-index-design.md` (read it whole before any task; D1-D9
are binding; section numbers below refer to it).

## Global Constraints

- Work only in `.worktrees/wt-9b1` on branch `phase-9b1`. Never /tmp for repo work. Never push, never merge.
- No `assume`, `admit`, `external_body`, `#[verifier::exec_allows_no_decreases_clause]` or new trusted items. Every exec
  fn verified.
- Every fn under the quic rlimit cap: `--rlimit 4` and `rl.py --max 8000000`. Split proofs into lemmas; never raise
  the cap.
- `crates/quic/src/crypto_stream.rs` changes nothing outside tests. Public `Frags` items keep signatures and ensures
  (D1): `view`, `wf`, `held`, `count`, `hi`, `hi_spec`, `lemma_wf`, `new`, `after_insert`, `insert`, `take_front`,
  `capacity`, and the pub
  spec fns/lemmas `run_start`, `starts`, `runs`, `put`, `lemma_runs_le_len`, `lemma_runs_cut`.
- `K: u64 = 128`, `CAP: u64 = 256` (pub consts in frags.rs).
- Cost convention (spec "The bound"): one unit per tree node visited (an empty `None` child included), created or
  relinked, and one per byte copied; accumulated in a ghost local named `work`; every exec fn in avl.rs and frags.rs
  that loops or recurses returns `Ghost<nat>` bounded in its ensures by literal numeric constants (spec fns
  `c_*() -> nat { <literal> }` are fine).
- Node layout: `key: u64, val: V, h: u8, left: Tree<V>, right: Tree<V>`; no exec size field (D7: 56 B node for
  `V = Vec<u8>`).
- Commits: small, message prefix `9b1: `, no attribution lines. Toolchain, ratchet files (only shrink) and
  `crates/crypto` untouched.
- Inner loop: `scripts/quick.sh quic/avl`, `scripts/quick.sh quic/frags`, `scripts/quick.sh quic/avl/FN`; before each
  commit that touches tests or more than one module, `scripts/quick.sh` (no args). Do not run `scripts/verify.sh` (the
  controller does).

## Review Focus

1. A duplicate frame whose held bytes span a head and its follower (`[0,10)`, `[10,138)`, frame `[5,15)`): `insert`
   changes nothing and allocates nothing (D3 step 0). Test in Task 7 (`crypto_alloc.rs`).
2. A frame filling the gap between two chunks that are both shorter than `K` on its two sides: both merge, `wf` holds,
   view correct. Test in Task 7 (`tests/frags.rs`, `frags_gap_small_tails`).
3. `take_front` on a run of many chunks (a head plus followers, e.g. one 16384-byte frame = 64 chunks): returns every
   byte in order and leaves no chunk of the run. Test in Task 7 (`frags_take_front_follower_chain`).
4. One frame larger than `CAP` (16384 bytes at once, and 300 bytes after a 250-byte `Lc`): no chunk over `CAP`, every
   follower at least `K` (checked through `Frags::chunk_lens`, a `#[doc(hidden)]` test accessor). Test in Task 7
   (`frags_big_frame_pieces`).
5. A frame straddling `lo` (`lo > off`): bytes below `lo` are dropped, as today (`frags_lo_cuts_below` exists; add a
   case where `lo` falls inside an existing follower chain). Test in Task 7.

---

### Task 1: The cost test and the measured RCA note

**Files:**
- Create: `crates/quic/tests/crypto_cost.rs`
- Modify: `docs/rca/2026-11-07-audit.md` (§6, a "Measured (9b1 Task 1)" bullet)

**Interfaces:** Produces `crypto_ooo_cost_linear` (un-ignored in Task 7).

- [ ] **Step 1: Write the test.** A per-thread counting allocator as in `tests/crypto_alloc.rs` (alloc, alloc_zeroed,
  realloc counted). Helper `fn cost(frames: &[(u64, Vec<u8>)]) -> (usize /*bytes allocated*/, Duration)` that feeds
  `CryptoStream::on_crypto` (asserting `Ok(())`), timing only the feed loop. Patterns, each at scale `n` ∈
  {1024, 2048, 4096}: runs descending `(2 + 2k, [1])` for k in (0..n).rev(); runs then fill
  (`(2+2k,[1])` for k < n, then `(3+2k,[1])` for k < n−1); grow-down `(o, [1])` for o in (1..4n).rev(); grow-down-full
  `(o, [1; 4n − o])` for o in (1..4n).rev(). Assertions per pattern: `bytes(2n) <= 3 * bytes(n)` and
  `bytes(4n) <= 3 * bytes(2n)`; time: `t(4n) <= 8 * t(n) + 20 ms`. Mark it
  `#[ignore = "9b1: quadratic on the Vec store; un-ignored by Task 7"]`.
- [ ] **Step 2: Show it fails today.** Run: `cargo test -p quic --test crypto_cost -- --ignored`. Expected: FAIL on the
  grow-down patterns (bytes quadratic). Record the failing numbers.
- [ ] **Step 3: RCA note.** In `docs/rca/2026-11-07-audit.md` §6, after the "What remains" bullet, add a bullet
  "Measured (9b1 Task 1, release, bd2708a)" with the spec's table (from "The cost today") and the Step 2 failure line.
- [ ] **Step 4:** `scripts/quick.sh` passes (it runs quic tests; ignored stays ignored). Commit
  `9b1: crypto_ooo_cost_linear (ignored until the index lands; fails on the Vec store) and the measured cost in the RCA`.

### Task 2: `quic::avl` basics

**Files:**
- Create: `crates/quic/src/avl.rs`; Modify: `crates/quic/src/lib.rs` (`pub mod avl;`)

**Interfaces (produces):**
```rust
pub struct Node<V> { pub key: u64, pub val: V, pub h: u8, pub left: Tree<V>, pub right: Tree<V> }
pub type Tree<V> = Option<Box<Node<V>>>;
pub open spec fn ht<V>(t: Tree<V>) -> nat;                 // 0 for None, else node.h
pub open spec fn seq<V>(t: Tree<V>) -> Seq<(u64, V)>;      // in-order
pub open spec fn keys_lt<V>(t: Tree<V>, k: u64) -> bool;   // every key of seq(t) < k
pub open spec fn keys_gt<V>(t: Tree<V>, k: u64) -> bool;   // every key of seq(t) > k
pub open spec fn sorted<V>(s: Seq<(u64, V)>) -> bool;      // strictly increasing keys
pub open spec fn wf<V>(t: Tree<V>) -> bool;  // children wf, keys_lt(left,key), keys_gt(right,key),
                                             // h == 1 + max(ht l, ht r), |ht l − ht r| <= 1, h <= 126
pub proof fn lemma_wf_sorted<V>(t: Tree<V>) requires wf(t) ensures sorted(seq(t));
pub proof fn lemma_height<V>(t: Tree<V>) requires wf(t) ensures seq(t).len() + 1 >= pow2(ht(t) / 2);
pub fn height<V>(t: &Tree<V>) -> (r: u8) ensures r == ht(*t);
pub fn get_le<V>(t: &Tree<V>, k: u64) -> (r: (Option<(u64, &V)>, Ghost<nat>))
    requires wf(*t)
    ensures  r.0 is Some ==> the greatest entry of seq(*t) with key <= k (index-based ensures),
             r.0 is None ==> every key > k,
             r.1 <= c_get() * (ht(*t) + 1);
```
`pow2` from `vstd::arithmetic::power2`. Keep the spike's lesson: state view equations explicitly; prefer `Seq`
concatenation (`seq(l) + seq![(k, v)] + seq(r)`) over maps.

- [ ] **Step 1:** Write the module with `lemma_height` (induction: `N(h) >= 2·N(h−2) + 1`), `height`, `get_le`.
- [ ] **Step 2:** `scripts/quick.sh quic/avl` → `quick: ok`. If `get_le` returning `&V` does not verify, return
  `Option<(u64, usize)>` (key and in-order index are not needed by callers; a key and a separate `get(&t, key) -> &V`
  is the fallback) and record the deviation in the commit message.
- [ ] **Step 3:** Commit `9b1: quic::avl — tree, in-order view, wf, the height lemma, get_le with its cost`.

### Task 3: `join` and `join2`

**Files:** Modify `crates/quic/src/avl.rs`

**Interfaces (produces):**
```rust
pub fn join<V>(a: Tree<V>, k: u64, v: V, b: Tree<V>) -> (r: (Tree<V>, Ghost<nat>))
    requires wf(a), wf(b), keys_lt(a, k), keys_gt(b, k), seq(a).len() + seq(b).len() + 1 < pow2(63)
    ensures wf(r.0), seq(r.0) == seq(a) + seq![(k, v)] + seq(b),
            max(ht(a), ht(b)) <= ht(r.0) <= max(ht(a), ht(b)) + 1,
            r.1 <= c_join() * (|ht(a) − ht(b)| + 1);
pub fn join2<V>(a: Tree<V>, b: Tree<V>) -> (r: (Tree<V>, Ghost<nat>))
    requires wf(a), wf(b), every key of a < every key of b, size bound as above
    ensures wf(r.0), seq(r.0) == seq(a) + seq(b), ht(r.0) <= max(ht(a), ht(b)) + 1,
            r.1 <= c_join2() * (max(ht(a), ht(b)) + 1);
```
`join` descends the taller tree's inner spine (right spine of `a` when `ht(a) > ht(b) + 1`, mirror otherwise), builds
the node where heights differ by at most 1, and rebalances on the way up with single/double rotations (the only fn with
rotations; rotations are private helpers with seq/height ensures). `join2` = `pop_min(b)` then `join` (Task 4
provides `pop_min`; implement `join2` in Task 4 if ordering requires, and note it).

- [ ] **Step 1:** Rotation helpers (`rot_left`, `rot_right`, private) with ensures on `seq` and heights.
- [ ] **Step 2:** `join` with both height ensures and the cost ensures.
- [ ] **Step 3:** `scripts/quick.sh quic/avl` → ok; every fn under the cap (quick prints rl).
- [ ] **Step 4:** Commit `9b1: quic::avl join — rotations, both height bounds, cost c·(|Δh|+1)`.

### Task 4: `split`, `pop_min`, `join2`, the in-order consume

**Files:** Modify `crates/quic/src/avl.rs`

**Interfaces (produces):**
```rust
pub fn split<V>(t: Tree<V>, k: u64) -> (r: (Tree<V>, Tree<V>, Ghost<nat>))
    requires wf(t)
    ensures wf(r.0), wf(r.1), seq(r.0) + seq(r.1) == seq(t), keys_lt(r.0, k), every key of r.1 >= k,
            ht(r.0) <= ht(t), ht(r.1) <= ht(t),
            r.2 <= c_join() * (ht(r.0) + ht(r.1) + 4 * (ht(t) + 1)) + c_split() * (ht(t) + 1);
pub proof fn lemma_split_cost(...) ensures the split cost <= c_split6() * (ht(t) + 1);   // the corollary
pub fn pop_min<V>(t: Tree<V>) -> (r: (Tree<V>, u64, V, Ghost<nat>))
    requires wf(t), t is Some
    ensures wf(r.0), seq![(r.1, r.2)] + seq(r.0) == seq(t), ht(t) − 1 <= ht(r.0) <= ht(t),
            r.3 <= c_pop() * (ht(t) + 1);
pub fn drain<V>(t: Tree<V>, out: &mut Vec<(u64, V)>) -> (r: Ghost<nat>)
    ensures out@ == old(out)@ + seq(t), r <= c_drain() * (2 * seq(t).len() + 1);
```
The split cost proof follows the spec's D4 case analysis (k < x: `R = join(R', x, r)`, cost `c·(h(R) − h(R') + 2)`
from `h(R') <= h(l) <= h(r) + 1` and `h(R) >= h(r)`; k == x; mirror). Split the proof into lemmas per case.

- [ ] **Step 1:** `pop_min` (recursive left descent, rebalance with `join` on the way up).
- [ ] **Step 2:** `join2`, if not done in Task 3.
- [ ] **Step 3:** `split` with the cost ensures and `lemma_split_cost`.
- [ ] **Step 4:** `drain` (recursive, by value).
- [ ] **Step 5:** `scripts/quick.sh quic/avl` → ok. Commit `9b1: quic::avl split (telescoping cost), pop_min, join2, drain`.

### Task 5: Chunks spec and the range walk

**Files:** Create `crates/quic/src/chunks.rs` (temporary home of the new store; Task 7 moves it into frags.rs);
modify `lib.rs` (`mod chunks;`), and make frags.rs's `inf`, `pos`, `at`, `vw`, `sum_len` `pub(crate)` if reused.

**Ruling recorded here (deviation from D4's module split):** the range walk of D3a lives in chunks.rs over
`Tree<Vec<u8>>`, not in generic avl.rs, because a generic walk would need a closure over `V` or a `Vec` of
references; avl.rs supplies only spec helpers it needs (e.g. `seq` slicing lemmas).

**Interfaces (produces):**
```rust
pub struct Chunks { t: Tree<Vec<u8>>, held: u64, count: usize, hi: u64 }
spec fn fs(&self) -> Seq<(nat, Seq<u8>)>;    // seq(t) mapped (key as nat, val@)
pub closed spec fn view(&self) -> Map<nat, u8>;   // vw(fs)
pub closed spec fn wf(&self) -> bool;  // avl::wf, sorted-disjoint (adjacent allowed), every chunk 1..=CAP bytes,
       // follower rule, held == sum_len == view.dom.len, count == runs(view.dom), hi == end of last (0 if none),
       // K·(n − runs) <= held (as a lemma consequence or conjunct)
pub fn new() -> Chunks;  held(); count(); hi()   // same ensures as Frags's
fn after_insert_w(&self, lo: u64, off: u64, data: &[u8]) -> (r: ((u64, usize), Ghost<nat>))
    // Frags::after_insert's ensures on r.0, plus r.1 <= c_walk() * (2 * (ht + 1) + |M| + 2)
    // where |M| is the count of chunks with start in [s, e] (spec fn), and |M| <= d + 1 (lemma)
pub fn after_insert(&self, lo: u64, off: u64, data: &[u8]) -> (r: (u64, usize))  // wrapper, Frags's ensures
```
Walk = `get_le(s − 1)` (when `s > 0`) plus a recursive in-range walk over keys in `[s, e]` that enters a subtree only
if it can hold such a key (two-mode induction: one-sided walk `<= k + h + 1` visits).

- [ ] **Step 1:** Spec + `wf` + the lemmas `K·(n − runs) <= held` and `|M| <= d + 1`.
- [ ] **Step 2:** `new`/`held`/`count`/`hi`, `after_insert_w`, `after_insert`.
- [ ] **Step 3:** `scripts/quick.sh quic/chunks` → ok. Commit `9b1: chunk store spec (follower rule, CAP), range walk with its visit bound`.

### Task 6: `insert_w` and `take_front_w` on `Chunks`

**Files:** Modify `crates/quic/src/chunks.rs`

**Interfaces (produces):** `insert_w(&mut self, lo, off, data) -> Ghost<nat>`, `insert` (wrapper),
`take_front_w(&mut self, end, out) -> (u64, Ghost<nat>)`, `take_front` (wrapper), `capacity(&self) -> usize`
(outside `verus!`, `#[doc(hidden)]`: nodes × `size_of::<Node<Vec<u8>>>()` + each chunk's `Vec` capacity),
`chunk_lens(&self) -> Vec<(u64, usize)>` (outside `verus!`, `#[doc(hidden)]`, test support). All with exactly
`Frags::insert`'s / `Frags::take_front`'s current ensures, plus cost ensures from the spec ("The bound").

D3 steps 0-6 as the spec states them. Step 5's cut, exactly: let `L` be the merged length (computed before any copy).
Piece lengths: `CAP` each, except that if `L mod CAP` is in `1..K` and there are at least two pieces, the last two
take `(CAP + q) / 2` and the rest (`q = L mod CAP`); a single piece takes `L`. Every piece is a fresh
`Vec::with_capacity(len)` filled by exactly `len` counted pushes (`Lc`'s bytes first, then the frame's/held bytes,
then the merged small tails); no `Vec` is ever grown past its initial capacity (no `reserve`, `reserve_exact`,
`append` or `extend` on a chunk), and `Lc`'s old `Vec` is dropped. D3b for `take_front_w`.

- [ ] **Step 1:** `insert_w` steps 0-2 (all-held return before any split; `get_le`; two splits).
- [ ] **Step 2:** steps 3-6 (drain `M`, merge, pop small `B` head, cut, joins), the `put` view proof via lemmas.
- [ ] **Step 3:** `take_front_w`.
- [ ] **Step 4:** `scripts/quick.sh quic/chunks` → ok. Commit `9b1: chunk store insert (one split pair, CAP-cut pieces, joins) and take_front, with cost`.

### Task 7: Swap `Frags` to the chunk store; tests

**Files:** Modify `crates/quic/src/frags.rs` (replace the `Vec` store and its private lemmas with chunks.rs's code under
the name `Frags`; delete what no longer has a caller; remove the `shortcut:` comment), delete `chunks.rs` and its
`mod` line; tests: `crates/quic/tests/frags.rs`, `crates/quic/tests/crypto_alloc.rs`, `crates/quic/tests/crypto_cost.rs`.

- [ ] **Step 1:** Move and rename; `scripts/quick.sh quic` → ok (crypto_stream.rs verifies unchanged).
- [ ] **Step 2: Tests (Review Focus 1-5).**
  - `crypto_alloc.rs` `duplicate_ooo_frames_allocate_nothing`: add one 300-byte frame at offset 2 (the cut gives a
    head `[2,152)` and a follower `[152,302)`; `frags_big_frame_pieces` pins that split through `chunk_lens`), then
    10,000 duplicates of `[147,157)`, which cross the boundary: 0 bytes allocated, time pin unchanged (50 ms).
  - `tests/frags.rs`: `frags_gap_small_tails` (chunks `[0,5)` and `[6,11)`, frame `[5,6)` → one run, `count == 1`,
    `held == 11`, all bytes readable by `take_front(0)`); `frags_take_front_follower_chain` (one 16384-byte frame at 0
    into an empty store, `take_front(0)` returns 16384 bytes equal to the frame, then `held == 0`, `count == 0`);
    `frags_big_frame_pieces` (via `chunk_lens`: every len `<= 256`, every chunk starting at the previous end has len
    `>= 128`, for a 16384-byte frame and for a 250-byte frame followed by a 300-byte frame adjacent above it);
    extend `frags_lo_cuts_below` with `lo` inside a follower chain.
  - Remove the `#[ignore]` from `crypto_ooo_cost_linear`; it passes. Extend its allocator to count `realloc` calls
    separately and assert 0 reallocs on every pattern (none fills from offset 0, so CryptoStream's in-order buffer is
    untouched); check that it fails if a chunk is grown with `push` past `with_capacity`.
- [ ] **Step 3:** `crypto_ooo_capacity_bounded` passes unchanged (bound 266240). If not, STOP and report (D7: owner).
- [ ] **Step 4:** `scripts/quick.sh` (no args) → `quick: ok`. Commit `9b1: Frags is the chunk AVL; cost, follower and dup-across-chunks tests`.

### Task 8: Gate, mutants, docs

**Files:** Create `scripts/cost-charge.sh`; modify `scripts/verify.sh`, `scripts/quick.sh` (cheap-gate list),
`scripts/gate-demos.sh`, `tools/mutants.tsv`, `tools/mutants/*.patch`, `TRUSTED.md`, `docs/carryovers.tsv`,
`docs/roadmap.md`, `docs/rca/catalog.md` (C15 row), and any `docs/requirements.md` row or citation that points at
moved frags.rs lines (the citations gate reports them).

- [ ] **Step 1: Gate** `scripts/cost-charge.sh [ROOT]`: in `crates/quic/src/avl.rs` and `crates/quic/src/frags.rs`,
  inside `verus!`: every `while` has an `invariant` clause mentioning `work`; every exec fn (not `spec`/`proof`) with
  a fn-level `decreases` or a `while` in its body returns a `Ghost<nat>` whose return name appears in its `ensures`.
  Exits non-zero naming file:line. Run from verify.sh and quick.sh where the other cheap gates run. Passes
  `scripts/lint-scripts.sh`.
- [ ] **Step 2: Demos** in gate-demos.sh, in the existing style: a copy with a `while` whose invariant lacks `work`
  → fails naming the line; a recursive exec fn without a `Ghost<nat>` return → fails; the real tree → passes.
- [ ] **Step 3: Mutants.** Regenerate T7-M3b2 (fn `Frags::locate` is gone: retarget "merging disabled" at
  `Frags::insert_w`, e.g. the small-`B`-head pop skipped, expected error a `wf`/view postcondition) and T7-M4
  (`held += data.len()` in `insert_w`). Add: `9b1-M1` a charged extra walk in the range walk (fails cost ensures),
  `9b1-M2` `join` that never rotates (fails balance/`wf`), `9b1-M3` a follower kept without the `K` check (fails
  `wf`), `9b1-M4` a piece cut past `CAP` (fails `wf`). Patches and rows in the registry's format (header of
  `tools/mutants.tsv`); `scripts/mutants.sh check` passes; `scripts/mutants.sh run 9b1-M1 9b1-M2 9b1-M3 9b1-M4
  T7-M3b2 T7-M4` kills all six.
- [ ] **Step 4: Docs.** TRUSTED.md:7's Frags sentences → the chunk layout (chunks of at most 256 bytes, each its own
  `Vec` allocated at its exact length and never grown, nodes `Box`ed, `capacity` checked by
  `crypto_ooo_capacity_bounded`) and the Vec row: std's push-below-capacity guarantee, pinned by the 0-realloc
  assertion in `crypto_ooo_cost_linear` (spec "The bound"). `cat-C15`: owner `9b1`,
  status closed, evidence the cost ensures (`crates/quic/src/frags.rs`), the gate and `crypto_ooo_cost_linear`, in
  the evidence format `scripts/carryovers.sh` accepts. Roadmap: a `9b1` row (status `in progress`; the controller
  sets merged), and row 9b's order cell loses "Task 1 Frags index". catalog.md's C15 row: closed by 9b1.
- [ ] **Step 5:** `scripts/quick.sh` → ok, `scripts/gate-demos.sh` → ok. Commit
  `9b1: cost-charge gate and demos, mutants regenerated and added, TRUSTED/carryovers/roadmap/catalog`.
