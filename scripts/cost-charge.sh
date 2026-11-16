#!/bin/sh
set -eu
set -o pipefail
# cost-charge.sh [ROOT]: the cost-charge gate (9b1 D6a; tools/cost_charge.py). In crates/quic/src/avl.rs, frags.rs and
# every crates/byteq/src/*.rs, inside verus!: every `while` has an invariant naming `work` and a body charging `work = work + E` (E not 0), every exec
# fn that loops or recurses (a fn-level decreases) returns a Ghost<nat> cost its ensures read (a recursive one charges
# work too), and every callee's Ghost<nat> cost is bound and mentioned in a charge, the returned cost or (frags.rs's public
# wrappers Frags::insert, after_insert, take_front) an assert (a callee is `NAME(`, `path::NAME(` or `.NAME(` on any receiver, NAME a cost fn of these files; std methods of
# other names, such as `out.append(..)`, are not); `loop`, `for` and unchecked recursion in fn bodies are refused.
# crypto_stream.rs is gated whole (CryptoStream::on_fill a wrapper); conn.rs and quictls's server.rs per fn: their
# Ghost<nat>-returning fns are callees and every fn there keeps the callee costs it gets, but for the listed exclusion
# drops (DROPS). A cost fn binds no ghost but work to a literal (a stubbed callee cost) and, in the per-fn files, builds
# no literal Ghost(N) after its first callee cost or charge (a stubbed return).
# Structural only: the amount charged is not checked, and per-path use, built-then-discarded Ghosts and `+=` are not
# seen (cat-C15-semantic-cost). ROOT (default: the repo) holds crates/; scripts/gate-demos.sh feeds it temp copies. Prints `cost-charge: N ...` on success.
root=${1:-$(cd "$(dirname "$0")/.." && pwd)}
python3 -I "$(cd "$(dirname "$0")/../tools" && pwd)/cost_charge.py" "$root"
