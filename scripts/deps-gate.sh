#!/bin/sh
set -eu
set -o pipefail
# deps-gate.sh [ROOT [TREEFILE]]: crypto's normal dependencies are exactly vstd. TREEFILE holds
# `cargo tree -p crypto -e normal --depth 1 --prefix none` output; without it the script runs
# that in ROOT (default: the repo). A missing, empty or failed tree is a failure.
root=${1:-$(cd "$(dirname "$0")/.." && pwd)}
fail() { echo "deps-gate: $*" >&2; exit 1; }
if [ $# -ge 2 ]; then
    [ -f "$2" ] || fail "no $2"
    tree=$(cat "$2") || fail "cannot read $2"
else
    tree=$(cd "$root" && cargo tree -p crypto -e normal --depth 1 --prefix none) || fail "cargo tree failed"
fi
[ -n "$tree" ] || fail "empty cargo tree output"
[ "$(printf '%s\n' "$tree" | sed 1d | cut -d' ' -f1)" = vstd ] || fail "crypto's normal deps are not exactly vstd"
echo "deps-gate: crypto's normal deps are exactly vstd"
