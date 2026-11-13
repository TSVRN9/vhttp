#!/bin/sh
set -eu
set -o pipefail
# quick.sh [TARGET..]: the inner loop. NOT a gate: it never prints verify.sh's line and vouches for no commit; only a clean
# scripts/verify.sh run does. Dirty trees are fine. Verus runs through `cargo verus focus` (the crate's own fns, its
# dependencies type-checked only, target/verus-partial) at --rlimit 4, the full gate's limit.
#   quick.sh                      every crate changed since `git merge-base HEAD main` (commits, edits, untracked files)
#                                 and its dependents (tools/quick.py scope): Verus per crate (tools/rl.py --gate, the 8,000,000
#                                 cap on quic and quictls), their tests, the cheap gates, and, when the paths call for them,
#                                 ct-check + declassify, ct-binary, interop and gate-demos.
#   quick.sh CRATE[/MOD[/FN]]..   Verus only, on each target: a whole crate, one module (--verify-only-module, e.g. quic/frags)
#                                 or one fn in it (--verify-function, e.g. quic/conn/Connection::accept).
root=$(cd "$(dirname "$0")/.." && pwd)
tools=$root/tools
verus_ver=$(sed -n 's/^version //p' "$tools/verus-pin.txt")
[ -n "$verus_ver" ] || { echo "quick: no version line in tools/verus-pin.txt" >&2; exit 1; }
VERUS_HOME="${VERUS_HOME:-$HOME/.local/opt/verus/$verus_ver/verus-x86-linux}"
PATH="$VERUS_HOME:$PATH"
out=${QUICK_OUT:-$root/target/quick}
mkdir -p "$out"
fail() { echo "quick: $*" >&2; exit 1; }
cd "$root"
t0=$(date +%s)
# step NAME CMD..: run CMD, print its time; its failure ends the run.
step() {
    s=$1
    shift
    t=$(date +%s)
    "$@" || fail "$s failed"
    echo "quick: $s ok ($(($(date +%s) - t)) s)"
}
# verus CRATE [MOD [FN]]: cargo does not fingerprint verus args, so the crate is cleaned first (else a cached crate verifies nothing).
verus() {
    b=$out/$(printf '%s' "$*" | tr ' :' '._')
    cargo clean -q -p "$1" --target-dir "$root/target/verus-partial" || return 1
    case $# in
        1) a= ;;
        2) a="--verify-only-module $2" ;;
        *) a="--verify-only-module $2 --verify-function $3" ;;
    esac
    # shellcheck disable=SC2086 # $a is a word list
    (cd "crates/$1" && cargo verus focus -- --rlimit 4 $a --output-json --time-expanded) > "$b.json" 2> "$b.log" || { cat "$b.log" >&2; return 1; }
    if [ $# -eq 1 ]; then
        case $1 in quic|quictls) lim="--max 8000000" ;; *) lim= ;; esac
        # shellcheck disable=SC2086
        python3 -I "$tools/rl.py" --gate "$1" --pin "$tools/verus-pin.txt" $lim "$b.json"
    else
        python3 -I "$tools/quick.py" check "$b"
    fi
}

if [ $# -gt 0 ]; then
    for t in "$@"; do
        # CRATE/MOD/FN into words (MOD and FN keep their ::)
        IFS=/
        # shellcheck disable=SC2086
        set -- $t
        unset IFS
        [ $# -le 3 ] && [ -n "${1-}" ] && [ -d "crates/$1" ] || fail "bad target $t (targets are CRATE, CRATE/MOD or CRATE/MOD/FN)"
        [ "$1" != server ] || fail "server has no proofs (cargo test -p server tests it)"
        step "verus $t" verus "$@"
    done
    echo "quick: ok ($(($(date +%s) - t0)) s; Verus only) - not a verify.sh run, vouches for no commit"
    exit 0
fi

base=$(git merge-base HEAD main) || fail "cannot resolve the merge-base of HEAD and main"
paths=$(git diff --name-only "$base"; git ls-files --others --exclude-standard)
cargo metadata --no-deps --locked --format-version 1 > "$out/meta.json" || fail "cargo metadata --locked failed"
# shellcheck disable=SC2086 # one path per word (no tracked path has a space)
sc=$(python3 -I "$tools/quick.py" scope "$out/meta.json" $paths) || exit 1
crates=$(printf '%s\n' "$sc" | sed -n 1p)
extra=$(printf '%s\n' "$sc" | sed -n 2p)
echo "quick: since $(git rev-parse --short "$base"): crates [$crates], extra [$extra]"
has() { case " $extra " in *" $1 "*) return 0 ;; esac; return 1; }

for c in $crates; do
    [ "$c" = server ] || step "verus $c" verus "$c"
done
if [ -n "$crates" ]; then
    pk=$(printf ' -p %s' $crates)
    # shellcheck disable=SC2086
    step "tests$pk" "$root/scripts/test-gate.sh" "$root" "$out/cargo-test.log" $pk
fi
step duvet duvet report
step deps "$root/scripts/deps-gate.sh" "$root"
step escape "$root/scripts/escape-gate.sh" "$root"
step cost-charge "$root/scripts/cost-charge.sh" "$root"
step quotes "$root/scripts/check-quotes.sh"
step acceptance "$root/scripts/acceptance.sh"
step citations python3 -I "$tools/citations.py" cite "$root"
step closes python3 -I "$tools/citations.py" closes "$root" "$tools/mutants.tsv"
step rfc-quantity "$root/scripts/rfc-quantity.sh"
step mutants-check "$root/scripts/mutants.sh" check
step carryovers "$root/scripts/carryovers.sh" "$root"
step requirements "$root/scripts/requirements.sh" "$root"
step lint "$root/scripts/lint-scripts.sh"
if has ct; then
    export CT_TARGET_DIR="${CT_TARGET_DIR:-$root/target/ct}"
    export CT_OUT="${CT_OUT:-$CT_TARGET_DIR/out}"
    mkdir -p "$CT_OUT"
    step ct-check sh -c '"$1/scripts/ct-check.sh" > "$2/ct-check.log" || { cat "$2/ct-check.log"; exit 1; }' - "$root" "$CT_OUT"
    step declassify "$root/scripts/declassify-gate.sh" "$root" "$CT_OUT/crypto/report-crypto.txt" "$CT_OUT/gate"
fi
if has binary; then step ct-binary "$root/scripts/ct-binary.sh"; fi
if has interop; then step interop "$root/scripts/interop.sh" "$root"; fi
if has demos; then step gate-demos "$root/scripts/gate-demos.sh"; fi
echo "quick: ok ($(($(date +%s) - t0)) s; crates [$crates], extra [$extra]) - not a verify.sh run, vouches for no commit"
