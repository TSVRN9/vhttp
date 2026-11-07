#!/bin/sh
set -eu
set -o pipefail
# test-gate.sh DIR LOG [CARGO TEST ARGS..]: `cargo test --locked -q` in DIR (verify.sh passes
# --workspace for the repo root), output in LOG, shown on failure. A build failure, a failing test
# or a run that passed no test at all is a failure.
[ $# -ge 2 ] || { echo "usage: test-gate.sh DIR LOG [cargo test args..]" >&2; exit 1; }
dir=$1 log=$2
shift 2
fail() { echo "test-gate: $*" >&2; exit 1; }
[ -d "$dir" ] || fail "no directory $dir"
(cd "$dir" && cargo test --locked -q "$@" > "$log" 2>&1) || { cat "$log"; fail "cargo test failed"; }
n=$(sed -n 's/^test result: ok\. \([0-9][0-9]*\) passed.*/\1/p' "$log" | awk '{ s += $1 } END { print s + 0 }')
[ "$n" -gt 0 ] || { cat "$log"; fail "cargo test passed no test"; }
echo "test-gate: $n tests passed"
