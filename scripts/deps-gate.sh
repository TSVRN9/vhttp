#!/bin/sh
set -eu
set -o pipefail
# deps-gate.sh [ROOT [TREEDIR]]: every crate under ROOT/crates has a line `CRATE: DEP ..` in tools/deps-allow.txt and its normal
# depth-1 deps (first token of each `cargo tree` line after the root, sorted) equal that line exactly; a line without a crate fails.
# TREEDIR holds one canned `cargo tree -p C -e normal --depth 1 --prefix none --locked` output per crate as C.txt; without it the
# script runs cargo in ROOT. A missing, empty or failed tree is a failure.
root=${1:-$(cd "$(dirname "$0")/.." && pwd)}
allow=$root/tools/deps-allow.txt
fail() { echo "deps-gate: $*" >&2; exit 1; }
[ -s "$allow" ] || fail "no or empty $allow"
n=0
crates=
for d in "$root"/crates/*/; do
    [ -f "$d/Cargo.toml" ] || continue
    c=$(basename "$d"); crates="$crates $c"
    if [ $# -ge 2 ]; then
        [ -f "$2/$c.txt" ] || fail "no $2/$c.txt"
        tree=$(cat "$2/$c.txt") || fail "cannot read $2/$c.txt"
    else
        tree=$(cd "$root" && cargo tree -p "$c" -e normal --depth 1 --prefix none --locked) || fail "cargo tree failed for $c"
    fi
    [ -n "$tree" ] || fail "empty cargo tree output for $c"
    got=$(printf '%s\n' "$tree" | sed 1d | cut -d' ' -f1 | LC_ALL=C sort | tr '\n' ' ' | sed 's/ $//')
    want=$(grep "^$c:" "$allow" | sed 's/^[^:]*: *//') || fail "crate $c has no line in tools/deps-allow.txt"
    [ "$(grep -c "^$c:" "$allow")" = 1 ] || fail "crate $c has several lines in tools/deps-allow.txt"
    [ "$got" = "$want" ] || fail "crate $c: deps '$got' differ from tools/deps-allow.txt '$want'"
    n=$((n + 1))
done
[ "$n" -gt 0 ] || fail "no crate under $root/crates"
for l in $(cut -d: -f1 "$allow"); do
    case " $crates " in *" $l "*) ;; *) fail "tools/deps-allow.txt lists $l, which is not a crate under crates/" ;; esac
done
echo "deps-gate: $n crates match tools/deps-allow.txt"
