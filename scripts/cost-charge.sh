#!/bin/sh
set -eu
set -o pipefail
# cost-charge.sh [ROOT]: the cost-charge gate (9b1 D6a; tools/cost_charge.py). In crates/quic/src/avl.rs and frags.rs,
# inside verus!: every `while` has an invariant naming `work`, and every exec fn that loops or recurses (a fn-level
# decreases) returns a Ghost<nat> cost its ensures read; `loop`, `for` and unchecked recursion are refused. ROOT
# (default: the repo) holds crates/; scripts/gate-demos.sh feeds it temp copies. Prints `cost-charge: N ...` on success.
root=${1:-$(cd "$(dirname "$0")/.." && pwd)}
python3 -I "$(cd "$(dirname "$0")/../tools" && pwd)/cost_charge.py" "$root"
