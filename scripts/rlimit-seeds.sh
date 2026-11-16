#!/bin/sh
set -eu
set -o pipefail
# rlimit-seeds.sh CRATE [N]: C11 PROOF-BUDGET FRAGILITY, the seed gate (RCA docs/rca/2026-11-16-smt-order-fragility.md).
# Verifies crates/CRATE whole (`cargo verus focus`, its dependencies type-checked only) at `--rlimit 4` under Z3 seeds
# 0..N-1 (default 5), one run at a time, and fails (tools/rlseeds.py) if any fn fails under any seed or a fn of CRATE
# exceeds its tools/rlimit-ceilings.txt line, or 8,000,000 when it has none, under any seed. A proof that verifies only
# under seed 0 depends on the solver's path, which unrelated edits (a vstd declaration order, a new requires) move.
# Logs go to target/rlimit-seeds/CRATE/seed-<i>.json (RS_OUT overrides target/rlimit-seeds).
root=$(cd "$(dirname "$0")/.." && pwd)
tools=$root/tools
fail() { echo "rlimit-seeds: $*" >&2; exit 1; }
[ $# -ge 1 ] && [ $# -le 2 ] || fail "usage: rlimit-seeds.sh CRATE [N]"
crate=$1
n=${2:-5}
case $n in '' | *[!0-9]* | 0*) fail "N must be a positive integer, got '$n'" ;; esac
[ -d "$root/crates/$crate/src" ] || fail "no crates/$crate"
verus_ver=$(sed -n 's/^version //p' "$tools/verus-pin.txt")
[ -n "$verus_ver" ] || fail "no version line in tools/verus-pin.txt"
VERUS_HOME="${VERUS_HOME:-$HOME/.local/opt/verus/$verus_ver/verus-x86-linux}"
PATH="$VERUS_HOME:$PATH"
out=${RS_OUT:-$root/target/rlimit-seeds}/$crate
mkdir -p "$out"
rm -f "$out"/seed-*.json "$out"/seed-*.err
cd "$root"
tdir=$(cargo metadata --no-deps --format-version 1 | python3 -I -c 'import json, sys; print(json.load(sys.stdin)["target_directory"])') || fail "cargo metadata gave no target_directory"
set --
i=0
while [ "$i" -lt "$n" ]; do
    # cargo does not fingerprint verus args: clean the crate, else a cached build verifies nothing.
    cargo clean -q -p "$crate" --target-dir "$tdir/verus-partial" || fail "cargo clean -p $crate failed"
    # A failing seed still writes its JSON (FAIL rows); rlseeds.py reads every seed before it judges.
    (cd "crates/$crate" && cargo verus focus -- --rlimit 4 --smt-option smt.random_seed="$i" --output-json --time-expanded) \
        > "$out/seed-$i.json" 2> "$out/seed-$i.err" || echo "rlimit-seeds: seed $i: verus exited non-zero (see $out/seed-$i.err)" >&2
    set -- "$@" "$out/seed-$i.json"
    i=$((i + 1))
done
python3 -I "$tools/rlseeds.py" "$crate" --pin "$tools/verus-pin.txt" --ceilings "$tools/rlimit-ceilings.txt" "$@"
