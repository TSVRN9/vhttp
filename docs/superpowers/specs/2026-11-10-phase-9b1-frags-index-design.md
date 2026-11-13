# Phase 9b1: a Frags index (C15), design

Roadmap slot: order 4, the first slice of 9b (its Task 1). Carryover `cat-C15` (owner 9b, moved to 9b1 by this phase):
"9a2's sparse CRYPTO store costs ~1.8 s CPU per connection at Initial, pre-authentication (... by arithmetic, not
measured) ... a new byte must cost O(log n + bytes)." Owner decision (2026-11-10): the full bound, worst case, not a
two-level layout or an amortized byte bound (the review of an earlier draft of this spec showed those close the row on a
weaker bound). Second owner decision (2026-11-10): strict per frame, O(log n + bytes) for each call however many gaps the frame
fills, so the tree is join-based (split and join, no per-gap insert).

## The cost today

`quic::frags::Frags` is `v: Vec<(u64, Vec<u8>)>`: sorted, separated fragments, one per run (`count == runs`). Caller
limits (`CryptoStream`): at most `MAX_CRYPTO_BUFFER` = 16384 bytes held, `MAX_CRYPTO_RANGES` = 4096 runs. Per call:

1. **Slot shifting.** `splice_in` inserts a slot or moves the tail down (3 moves per slot, frags.rs:1254-1269);
   `take_front` does `Vec::remove(0)`: up to 4096 slots of 32 bytes, on every in-order fill that meets the front.
2. **Byte copying.** `merged` copies every byte of every touched fragment, one `push` at a time (`push_slice`), into a
   fresh `Vec`: a 1-byte frame joining two 8 KiB fragments copies 16 KiB; growing a fragment downward copies it whole
   per frame.
3. `locate` is a binary search; `after_insert`/`counts`/`bounds` run twice per frame (O(log n + (j − i))).

Measured before the rewrite (2026-11-12, release, `CryptoStream::on_crypto`, a counting allocator; an untracked example
at bd2708a; laptop, other load present):

| pattern | frames | time | live bytes (requested) |
|---|---|---|---|
| 4096 one-byte runs, ascending | 4096 | 0.7 ms | 135168 |
| 4096 one-byte runs, descending (slot shifting) | 4096 | 6.2 ms | 135168 |
| one fragment grown downward a byte at a time to 16383 (byte copying) | 16383 | 108 ms | 16511 |
| the same, each frame re-sending everything above it | 16383 | 96 ms | 16511 |
| 4096 runs, then each gap filled | 8191 | 23.6 ms | 139263 |

Byte copying (2) dominates: about 6.6 µs per frame at 16 KiB held, the same order as the audit's 10-12 µs per frame
(docs/rca/2026-11-07-audit.md §6), so the ~1.8 s per connection at Initial stands as an estimate of the right size.
Task 1 reruns this as a committed test (D6b) and records the table in the RCA.

## The bound this phase proves

Let `n` be the number of chunks (below), `h` the tree height, `d = data.len()`, `r` the bytes `take_front` returns,
`K` = 128 and `CAP` = 2K = 256. Cost is a ghost `nat` that each private worker fn returns (`Ghost<nat>`, D1): one
unit per tree node visited (an empty child included), created or relinked, and per byte copied. Proved, worst case per
call:

- `insert` and `after_insert`: cost at most `c1 · (h + 1) · (d / K + 4) + c2 · (d + 4K)` (the walk, two splits and
  at most `d / K + 4` joins; bytes: `d`, two tails under `K`, and `Lc`'s bytes, at most `CAP`, copied into a fresh
  piece in D3 step 5), which is at most `(c1 + c2) · (d + 4 · (h + 1) + 4K)` since `h + 1 <= K`. The constants are fixed numbers in the ensures.
  `insert_w` also ensures the additive form `112 · (h + 1) + 8 · d + 1207` (from `merge_w`'s `108 · (h + 1) + 6 · d + 1200`
  and the walk's `c_walk() · (2(h + 1) + |M| + 2)` with `|M| <= d + 1`).
- `take_front`: at most `c1 · (h + 1) + c2 · (r + K)`.
- `size + 1 >= 2^(h/2)` (AVL; no `log` in the proofs, vstd's is opaque) and `K · (n − runs) <= held`; the private
  lemma `Frags::lemma_caps_height` proves `n <= 4096 + 128` and `h <= 25` for any wf `Frags` with `held <= 16384` and
  `count <= 4096` (`MAX_CRYPTO_BUFFER` and `MAX_CRYPTO_RANGES`, which `CryptoStream::wf` gives; no caller applies it,
  since `crypto_stream.rs` does not change and the bounds above need only `h + 1 <= 126`). For any store,
  `held <= VARINT_MAX < 2^62` gives `h + 1 <= 126 <= K`, which the bounds above use.

So a frame costs O(log n + d) in the store and `take_front` O(log n + r), worst case per call, with no amortization.
Owner decision 2026-11-12: the per-call rule is O(d + log n) with `d` the bytes the call was given, so a call that
delivers `r` bytes (`on_fill`'s `take_front` when a 1-byte frame closes a gap) does not meet it; lazy delivery of
in-order bytes is 9b2's (`cat-C15-9b2`), and parsing as bytes arrive is 9b5's (`cat-C15-stream-parse`). No chunk
`Vec` ever reallocates (owner request 2026-11-12, after a review found the earlier draft relied on bounded but
uncounted reallocation): every piece D3 step 5 makes is a fresh `Vec::with_capacity(len)` filled by counted pushes of
exactly `len` bytes, and no chunk is grown afterwards, so every byte copy inside `Frags` is in the ghost cost. vstd
models length, not capacity, so "a push below capacity does not reallocate" is std's documented guarantee, trusted
(TRUSTED.md's Vec row), and pinned mechanically: `crypto_ooo_cost_linear` counts `realloc` calls and requires none
on its out-of-order patterns (a gate demo shows it failing when `fill`'s piece is made by `Vec::new()`). `take_front`
appends to `out`; that buffer's growth is the caller's (D10).

## Decisions

- **D1 Public contract unchanged.** `view`, `wf`, `held`, `count`, `hi`, `hi_spec`, `lemma_wf`, `new`, `after_insert`,
  `insert`, `take_front` keep their signatures and ensures; none is weakened. `crypto_stream.rs` does not change, apart from tests. Cost cannot
  be a field (the `&self` fns could not charge it, and `insert`'s all-held return ensures `*final(self) == *old(self)`),
  so each public fn is a one-line wrapper over a private worker (`after_insert_w`, `insert_w`, `take_front_w`, and the
  `avl` ops themselves) that returns its result and a `Ghost<nat>` cost bounded in its ensures; the wrapper asserts the
  bound in its body.
- **D2 Chunks, not fragments.** The store keeps chunks: `(start, Vec<u8>)`, non-empty, at most `CAP` bytes, sorted,
  disjoint, and possibly adjacent. A run may span several chunks. `count` is a field kept equal to
  `runs(view().dom())`, not the number of chunks. Follower rule (invariant): a chunk that starts where another ends (a
  follower) holds at least `K` bytes. Every chunk is a run's first chunk or a follower, so `K · (n − runs) <= held`.
- **D3 One frame, one split, one join.** `insert_w` for a frame `[s, e)`:
  0. The all-held check: the `after_insert_w` walk (D3a); if the held count it returns equals `held`, every position
     of `[s, e)` is held (also when the held range spans several chunks, e.g. a head `[0,10)`, a follower `[10,138)`
     and a frame `[5,15)`), and `insert` returns with `*final(self) == *old(self)`, before any split.
  1. `get_le(s)` finds the chunk `Lc` holding or ending at `s` (if any); `s0` is its start, else `s`.
  2. `split` the tree at `s0` and at `e` into `A` (keys below `s0`), `M` (keys in `[s0, e)`), `B` (keys from `e`).
  3. Consume `M` in order in O(|M|) (an in-order traversal that takes the tree by value, not a `pop_min` loop, which
     would cost `|M| · (h + 1)`); every chunk of `M` but `Lc` starts inside `[s, e)`, so `|M| <= d + 1`. The merged
     bytes are `Lc`'s, then the frame's and held bytes for `[Lc.end, e')`, where `e'` is `e`, or the start of the last
     chunk `Rc` of `M` if it runs past `e`: if `Rc` holds fewer than `K` bytes it is merged whole, else it is kept
     untouched as a follower and the merged bytes stop at `Rc.start`. Held and new bytes in `[s, e)` total at most `d`.
  4. If `B`'s first chunk starts where the merged bytes end and holds fewer than `K` bytes, `pop_min` it and merge it.
  5. Cut the merged bytes into chunks of at most `CAP`, each a fresh `Vec::with_capacity` of its exact length filled
     by counted pushes (`Lc`'s bytes, at most `CAP`, are copied into the first; its old `Vec` is dropped): pieces of
     `CAP`, and if the last piece would hold fewer than `K`, the last two are split evenly (each at least `K`, at most
     `CAP`; lengths are computed before any piece is filled). At most `(d + 2K) / K + 2 <= d / K + 4` chunks result.
  6. Build the pieces into one balanced tree `P` (O(np)), then `join2(A, P)` and one `join` with `Rc` (if kept) and
     `B`: O(h + np). (Joining the pieces one at a time would not do: the accumulator grows taller with each join.)
  The run delta for `count` comes from the walk (runs met in `[s, e)`, plus adjacency at `s − 1` and `e`).
- **D3a `after_insert_w` without mutation.** `&self`: a range walk over the chunks meeting `[s − 1, e]` (recursion
  that enters a subtree only if it can meet the range), proved to cost at most `c_walk() · (2(h + 1) + |M| + 2)`
  with `c_walk() = 2` (empty children count as visits: a one-sided walk over `k` in-range chunks visits at most
  `2k + h + 1`, a two-sided one at most `2k + 2h + 2`, plus `get_le`'s `h + 1`); returns the held and run counts after
  the frame.
- **D3b `take_front_w`.** `pop_min` while the next chunk starts where the taken bytes end (the whole run, never part of
  a chunk): `t` chunks, `t <= 1 + r / K` (every chunk after the first is a follower), so `t · (h + 1) <= h + 1 + r`
  since `h + 1 <= K`. `pop_min` ensures the height does not grow.
- **D4 A verified join-based AVL.** New module `quic::avl`: `Avl<V>` keyed by `u64`, `Box` nodes with a `u8` height,
  ops taking and returning trees by value (`Option::take`, `mem::swap`; no recursion through `&mut`). View: the
  in-order `Seq<(u64, V)>`, sorted by key (rotations, `split` and `join` preserve it by concatenation; the `Map` is
  derived where needed). Size is ghost only (no exec `len` field). Ops: `new`, `get_le(k)`, `split(k)` (keys below
  `k` / the rest), `join(a, (k, v), b)` (all keys of `a` below `k`, all of `b` above; requires a size bound such as
  `size < 2^63`, which keeps heights in `u8`), `join2(a, b)`, `pop_min` and the in-order consume of D3 step 3
  (`drain`). The range walk of D3a is `frags::walk`, not an avl op (ledger ruling: Verus has no closures over `V` to
  make it generic). Ensures on the view, on balance and height, and on cost:
  - `join`: `max(h(a), h(b)) <= h(out) <= max(h(a), h(b)) + 1` (the lower bound is what makes `split` telescope), cost
    at most `c · (|h(a) − h(b)| + 1)` (descending the taller spine; AVL heights drop 1 or 2 per step).
  - `split(T)`: `h(L) <= h(T)`, `h(R) <= h(T)`, cost at most `c · (h(L) + h(R) + 4(h(T) + 1))`, hence at most
    `6c · (h(T) + 1)` (case `k < x`, `R = join(R', x, r)`: from `h(R') <= h(l) <= h(r) + 1` and `h(R) >= h(r)` the
    join costs at most `c · (h(R) − h(R') + 2)`, and `4h(l) + 3 <= 4h(T)`; `k == x` costs `c · (h(r) + 1)`; the
    mirror is symmetric). The hardest proof of the phase.
  - `pop_min`: height does not grow; cost `c · (h + 1)`. `get_le`: `c · (h + 1)`.
  `join` is the only fn with rotations. A generic map, so its proofs do not mention bytes.
- **D5 Frags on the AVL.** `Frags { t: Avl<Vec<u8>>, held: u64, count: usize, hi: u64 }` (`hi` cached as a field, so
  `hi()` stays O(1)). Spec: the in-order chunk sequence; the existing `vw`, `pos`, `at`, `inf` carry over; `sep`
  becomes sorted-and-disjoint (adjacent allowed), the follower rule and the `CAP` bound are local conditions on
  neighbours, and `K · (n − runs) <= held` is an induction over the sequence. Lemmas that assume separated fragments
  (`located`, `lemma_merge*`) are reworked; `put`, `runs`, `starts`, `lemma_runs_*` (the public spec) stay.
- **D6 Catch.** The proved cost ensures are the catch, but cost is charged by hand and the ensures are upper bounds, so
  an uncharged or undercharged loop would still verify. Mechanical guards: (a) a gate (`scripts/cost-charge.sh`, run by
  verify.sh and quick.sh, with gate demos), structural only: in avl.rs and frags.rs every `while` has an invariant
  naming `work` (the ghost accumulator) and a body updating `work = work + E` with `E` not `0`; every exec fn that
  loops or recurses returns a `Ghost<nat>` named in its ensures, and a recursive one's body updates `work` the same
  way; every assignment to `work` is such an update; no callee cost is dropped (each `Ghost<nat>` a callee returns is
  bound as `Ghost(x)` and `x` is charged to `work`, built into the fn's returned `Ghost`, or, in the public wrappers
  `insert`, `after_insert` and `take_front` only, asserted; or the call is a block's tail and passes on); `loop`,
  `for` and the attribute waiving `decreases` are refused. Charging the right amount stays by hand: a semantic check of
  the charge is carryover `cat-C15-semantic-cost` (9b4). Demos: a while without the `work` invariant line, a recursive
  fn returning no cost, fill's ensures not reading its cost, fill's charge deleted or made `+ 0`, take_run's in-loop
  charge deleted, a dropped and a plainly bound callee cost, a `loop`, a `for`; (b) tests: keep `duplicate_ooo_frames_allocate_nothing`'s time pin, add a
  duplicate that crosses a head/follower boundary to it (D3 step 0), and add `crypto_ooo_cost_linear` (the measured
  patterns at 1024, 2048, 4096 runs and 4, 8, 16 KiB: allocations and wall time at most linear, a counting allocator
  for the allocation half). New mutants, each killed by a Verus error: a charged extra walk (visits both subtrees;
  fails the cost ensures), a `join` that never rotates (fails the balance ensures), a follower kept without the `K`
  check (fails `wf`), a chunk extended past `CAP` (fails `wf`).
- **D7 Memory.** Today's worst (4096 one-byte runs): 4096 slots × 32 B + 4096 one-byte `Vec`s = 135168 B requested,
  plus an allocator header per `Vec`. The new node is `key` 8 + `Vec` 24 + two `Box` 16 + a `u8` height, padded to 56 B;
  `Frags::capacity` becomes nodes × (`size_of::<Node>()` + the chunk `Vec`'s capacity), which on that pattern is
  4096 × (56 + 8) = 262144 B, under `crypto_ooo_capacity_bounded`'s 266240 (tests/crypto_stream.rs:150-151) by 4 KiB,
  so the bound stays. A node of 64 B or more fails it (294912): the node must not grow (no exec size field), and if it
  must, raising the bound goes to the owner first. The real malloc footprint rises (each node is its own allocation);
  the test pins requested capacity, as today. TRUSTED.md:7's Frags sentence follows the new layout.
- **D8 Out of scope.** `MAX_CRYPTO_BUFFER` and `MAX_CRYPTO_RANGES` stay byte and run caps (an offset window changes an
  RFC-justified close predicate). `Reassembly` (STREAM data) is untouched. P3 (codec acceptance lemmas) is its own
  later phase.
- **D10 The in-order buffers go to phase 9b2 (owner decision 2026-11-12).** `take_front` appends to `CryptoStream`'s
  `buf`, `CryptoStream::read` appends it to TLS's input, and `tls::HsReader::next_message` drains each message from the
  front with `split_off` (O(unread) per message). All three grow or shift by std's amortized behaviour. Phase 9b2,
  next after 9b1, replaces them with one verified byte queue (de-amortized growth: on reaching half capacity a buffer
  of twice the size is allocated and each append also moves two old bytes, so every append is O(d) worst case with
  every copy counted; front removal copies only the message). Owner decision 2026-11-12: the per-call rule is
  O(d + log n), d the bytes a call was given, so `take_front`'s O(log n + r) delivery of a whole run does not meet it
  either; 9b2 also makes in-order delivery lazy (`cat-C15-9b2`) and 9b5 parses incrementally
  (`cat-C15-stream-parse`). 9b1 closes
  `cat-C15` for the out-of-order store. A sweep (docs/rca/2026-11-12-cost-sweep.md) found about 60 such sites across
  quic, tls, h3 and server; owner decision 2026-11-12: phases 9b2 (quic/tls byte buffers), 9b3 (h3, the quadratic
  cookie merge first) and 9b4 (the rest, and the sweep as a gate) run next, before Phase 6, each with a carryover row.
- **D9 Bookkeeping.** `cat-C15` closes with the `work` ensures, the gate and the test as evidence; the `shortcut:`
  comment at `insert` goes; mutant patches T7-M3b2 and T7-M4 (frags) are regenerated (T7-M6 is `Reassembly`'s and
  stays); roadmap row 9b1 and 9b's text lose Task 1; TRUSTED.md's Vec row names the push-below-capacity guarantee
  and the realloc-count test.

## Task outline (the plan refines)

1. Commit the measurement as a test (the table above) and the RCA note. The throwaway Verus spike is done (2026-11-12,
   untracked, not committed): an `Option<Box<Node>>` tree with a `Map<u64, Seq<u8>>` view, `wf` (order, heights),
   `rotate_right` preserving view and keys, `get_le`, and a recursive `split` (no rebalancing) verify at `--rlimit 4`
   (8 verified, 0 errors; the rotation needs its four view equations spelled out).
2. `quic::avl`: types, sequence view, `wf` (order, balance, `u8` heights, ghost size), `new`, `get_le`, the height lemma.
3. `quic::avl` `join` (rotations, both height ensures) and `join2`, cost ensures.
4. `quic::avl` `split` (the telescoping cost proof), `pop_min`, the in-order consume.
5. `quic::avl` range walk (the visit bound).
6. Frags on the AVL: spec (`sep`, follower rule, `CAP`, `K · (n − runs) <= held`), `wf`, `new`/`held`/`count`/`hi`,
   `after_insert_w` and its wrapper.
7. `insert_w` (D3, steps 0-6) and `take_front_w` (D3b), wrappers.
8. Gate (D6a), tests (D6b), mutants, TRUSTED, carryovers, requirements, roadmap.

Inner loop: `scripts/quick.sh quic/avl`, `scripts/quick.sh quic/frags`. Every fn under the 8,000,000 quic cap; split
proofs, never raise it.
