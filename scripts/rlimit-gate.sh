#!/bin/sh
set -eu
set -o pipefail
# rlimit-gate.sh [ROOT]: verify every crate under ROOT/crates at `--rlimit 4` (the gate replaces the default
# `cargo verus verify` loop) and fail on any FAIL row, a run that left no JSON, or (quic, quictls) a fn above
# 8,000,000, and every fn above 8,000,000 in any other crate must be in the shrink-only tools/rlimit-ceilings.txt. C11 PROOF-BUDGET FRAGILITY. Measured on a fresh target: `-- --rlimit 4` reaches vstd, whose
# lemma_indistinguishable_quotients needs more than 4, so vstd is built first at the default limit (via the
# smallest crate); and cargo does not fingerprint verus args, so each crate is cleaned before its rlimit-4 run
# (otherwise a cached crate verifies nothing and prints no JSON). `server` is unverified shell code (cargo verus
# only type-checks it, no rows), so it is the one crate named as ungated; rlimit-ceilings.sh fails if its src has proofs.
root=${1:-$(cd "$(dirname "$0")/.." && pwd)}
tools=$(cd "$(dirname "$0")/../tools" && pwd)
verus_ver=$(sed -n 's/^version //p' "$tools/verus-pin.txt")
[ -n "$verus_ver" ] || { echo "rlimit-gate: no version line in tools/verus-pin.txt" >&2; exit 1; }
VERUS_HOME="${VERUS_HOME:-$HOME/.local/opt/verus/$verus_ver/verus-x86-linux}"
PATH="$VERUS_HOME:$PATH"
ungated=server
cap=8000000
out=${RL_OUT:-$root/target/rlimit}
mkdir -p "$out"
rm -f "$out"/*.json  # no log of a removed crate survives into the ceilings check
fail() { echo "rlimit-gate: $*" >&2; exit 1; }
cd "$root"
# Dependency order, so a crate is verified once (its dependencies are already built and cached); a crate dir missing from
# this list, or a name here with no dir, fails.
order="wire crypto ctcore ctmir h3 tls quic quictls server"
have=$(for d in crates/*/; do [ -d "$d" ] && basename "$d"; done | LC_ALL=C sort | tr '\n' ' ')
want=$(printf '%s\n' $order | LC_ALL=C sort | tr '\n' ' ')
[ -n "$have" ] || fail "no crates under crates/"
[ "$have" = "$want" ] || fail "crates/ holds [$have] but the dependency order lists [$want]; update order in scripts/rlimit-gate.sh"
set --
for n in $order; do set -- "$@" "crates/$n/"; done
(cd "$root" && cargo verus verify -p wire > "$out/warm.log" 2>&1) || { cat "$out/warm.log"; fail "default-limit warm-up of vstd and wire failed"; }
best=0 bestfn=
for c in "$@"; do
    n=$(basename "$c")
    cargo clean -p "$n" > /dev/null 2>&1 || fail "cargo clean -p $n failed"
    if [ "$n" = "$ungated" ]; then
        (cd "$c" && cargo verus verify) || fail "$n (ungated, type-check only) failed"
        continue
    fi
    (cd "$c" && cargo verus verify -- --rlimit 4 --output-json --time-expanded > "$out/$n.json" 2> "$out/$n.err") || { cat "$out/$n.err"; fail "$n failed at rlimit 4 (see $out/$n.json)"; }
    case $n in quic|quictls) lim="--max $cap" ;; *) lim= ;; esac
    # shellcheck disable=SC2086
    line=$(python3 -I "$tools/rl.py" --gate "$n" --pin "$root/tools/verus-pin.txt" $lim "$out/$n.json") || exit 1
    echo "$line"
    v=${line##* }
    if [ "$v" -gt "$best" ]; then best=$v; bestfn=$(printf '%s\n' "$line" | cut -d' ' -f4); fi
done
[ -n "$bestfn" ] || fail "no crate produced rows"
"$root/scripts/rlimit-ceilings.sh" "$root" "$out" || exit 1
echo "rlimit-gate: ok (max $bestfn $best)"
