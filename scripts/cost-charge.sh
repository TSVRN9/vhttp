#!/bin/sh
set -eu
set -o pipefail
# cost-charge.sh [ROOT]: the cost-charge gate (9b1 D6a; tools/cost_charge.py). In crates/byteq/src/avl.rs, quic's frags.rs and
# every crates/byteq/src/*.rs, inside verus!: every `while` has an invariant naming `work` and a body charging `work = work + E` (E not 0), every exec
# fn that loops or recurses (a fn-level decreases) returns a Ghost<nat> cost its ensures read (a recursive one charges
# work too), and every callee's Ghost<nat> cost is bound and mentioned in a charge, the returned cost or (frags.rs's public
# wrappers Frags::insert, after_insert, take_front) an assert (a callee is `NAME(`, `path::NAME(` or `.NAME(` on any receiver, NAME a cost fn of these files; std methods of
# other names, such as `out.append(..)`, are not); `loop`, `for` and unchecked recursion in fn bodies are refused.
# crypto_stream.rs is gated whole (CryptoStream::on_crypto a wrapper); conn.rs, pipeline.rs and quictls's server.rs per
# fn: their Ghost<nat>-returning fns are callees and every fn there keeps the callee costs it gets, with no allowed drop
# (9b2 Task 10d), but for NOT_COSTS's keyed calls that only share a cost fn's name (each naming the fn it is, which must
# return no Ghost<nat>); a cost fn imported under another name (`use .. as`) is refused. streams.rs and recv_stream.rs
# are callee-only: their cost fns are callees of the checked files, their bodies unchecked (calls among them unseen:
# cat-C15-semantic-cost, 9b4). In every file work is assigned only as work = work + E and bound once per fn; a cost fn binds no ghost
# but work to a literal (a stubbed callee cost) and builds no literal Ghost(N) after its first callee cost or charge (a
# stubbed return), but for avl::bal, frags::walk and frags::walk_run (LITERAL_OK, cat-C15-semantic-cost's).
# Structural only: the amount charged is not checked, and per-path use, built-then-discarded Ghosts and `+=` are not
# seen, nor a stub helper cost fn (a literal Ghost(N) returned before any call, bound and charged by its caller) (cat-C15-semantic-cost). ROOT (default: the repo) holds crates/; scripts/gate-demos.sh feeds it temp copies. Prints `cost-charge: N ...` on success.
root=${1:-$(cd "$(dirname "$0")/.." && pwd)}
python3 -I "$(cd "$(dirname "$0")/../tools" && pwd)/cost_charge.py" "$root"
