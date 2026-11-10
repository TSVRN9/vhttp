#!/bin/sh
set -eu
set -o pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
# A green run must describe a commit: a dirty tree stops here unless VERIFY_DIRTY=1 (then the final line says it vouches for no commit).
pfx="verify.sh:"
head=$(git -C "$root" rev-parse HEAD) || { echo "verify.sh: git rev-parse HEAD failed" >&2; exit 1; }
"$root/scripts/clean-tree.sh" "$root" || {
    [ "${VERIFY_DIRTY:-}" = 1 ] || exit 1
    echo "verify.sh: tree dirty, not a main-tip run"; pfx="verify.sh (DIRTY TREE, vouches for no commit):"
}
# A Cargo.lock that cargo would rewrite fails here, so every later cargo call can rely on it.
(cd "$root" && cargo metadata --locked --format-version 1 > /dev/null) || { echo "verify.sh: cargo metadata --locked failed" >&2; exit 1; }
verus_ver=$(sed -n 's/^version //p' "$root/tools/verus-pin.txt")
[ -n "$verus_ver" ] || { echo "verify.sh: no version line in tools/verus-pin.txt" >&2; exit 1; }
VERUS_HOME="${VERUS_HOME:-$HOME/.local/opt/verus/$verus_ver/verus-x86-linux}"
PATH="$VERUS_HOME:$PATH"
# Every crate verified at --rlimit 4 (replaces the default per-crate run); quic/quictls fns must stay under 8,000,000.
"$root/scripts/rlimit-gate.sh" "$root" || exit 1
(cd "$root" && duvet report)
# Constant-time check; its crypto report is read by the declassify gate, so pin where it goes.
export CT_TARGET_DIR="${CT_TARGET_DIR:-$root/target/ct}"
export CT_OUT="${CT_OUT:-$CT_TARGET_DIR/out}"
mkdir -p "$CT_OUT"
"$root/scripts/ct-check.sh" > "$CT_OUT/ct-check.log" || { cat "$CT_OUT/ct-check.log"; exit 1; }
cat "$CT_OUT/ct-check.log"
cost=$(sed -n 's/^ct-check: cost \([0-9]*\/[0-9]*\) bounded$/\1/p' "$CT_OUT/ct-check.log")
[ -n "$cost" ] || { echo "verify.sh: no cost line in ct-check's output" >&2; exit 1; }
# Declassify gate (scripts/declassify-gate.sh): the report's declassify sites, TRUSTED.md's ct-declassify rows and the
# declassify( lines of crates/crypto/src/ are the same lists.
decl=$("$root/scripts/declassify-gate.sh" "$root" "$CT_OUT/crypto/report-crypto.txt" "$CT_OUT/gate") || exit 1
echo "$decl"
d=$(printf '%s\n' "$decl" | sed -n 's/^declassify-gate: \([0-9]*\) declassify sites accounted$/\1/p')
[ -n "$d" ] || { echo "verify.sh: no count in declassify-gate's output" >&2; exit 1; }
# Deps gate (scripts/deps-gate.sh): every crate's normal depth-1 dependencies equal its line in tools/deps-allow.txt.
"$root/scripts/deps-gate.sh" "$root" || exit 1
cd "$root"
# Escape gate (scripts/escape-gate.sh): every escape hatch in crates/ is an accounted external_body.
esc=$("$root/scripts/escape-gate.sh" "$root") || exit 1
echo "$esc"
attrs=$(printf '%s\n' "$esc" | sed -n 's/^escape-gate: \([0-9]*\) escapes accounted$/\1/p')
[ -n "$attrs" ] || { echo "verify.sh: no count in escape-gate's output" >&2; exit 1; }
# Binary gate: crates/crypto's shipped object code must match docs/crypto-binary-digests.txt.
bin=$("$root/scripts/ct-binary.sh") || exit 1
bin=$(printf '%s\n' "$bin" | sed -n 's/^ct-binary: ok (\([0-9]*\) fns)$/\1/p')
[ -n "$bin" ] || { echo "verify.sh: no ok line in ct-binary's output" >&2; exit 1; }
# Quote gate: duvet report exits 0 on a `//#` quote that is not in the RFC text.
"$root/scripts/check-quotes.sh" || exit 1
# Acceptance ratchet: every error-returning exec fn in verus! carries an allowed_ clause or is in the shrinking baseline.
"$root/scripts/acceptance.sh" || exit 1
# Citation gate (C1): every allowed_*err predicate, close-code fn and code-mapping spec fn carries an RFC citation with a quote
# (the quote text is checked by check-quotes above), and every close-code fn is named by a row of tools/mutants.tsv.
python3 -I "$root/tools/citations.py" cite "$root" || exit 1
python3 -I "$root/tools/citations.py" closes "$root" "$root/tools/mutants.tsv" || exit 1
# RFC-quantity gate (C8): every read in an allowed_*err predicate's body and the spec fns it calls is vouched for as an RFC
# quantity (a `// rfc-quantity:` line, or tools/rfc-quantity-allow.txt, a digest-pinned list) or listed in the shrinking tools/rfc-quantity-open.txt.
"$root/scripts/rfc-quantity.sh" || exit 1
# Mutant registry (C6): every tools/mutants/ patch applies exactly and every allowed_*err predicate has a row; at main's
# tip, tools/mutants-last-run.txt must name this commit's crates/, root Cargo files and pinned Verus with every mutant
# killed, and a fresh full run there (about 10 minutes) must reproduce it.
"$root/scripts/mutants.sh" verify || exit 1
# Carryover gate (C3, scripts/carryovers.sh): every docs/carryovers.tsv owner is a docs/roadmap.md phase, closed rows'
# evidence resolves, no merged phase owns an open row, TRUSTED.md removal cells name a phase or never (reason), no tracked
# evidence cites an untracked path; rows are closed, never deleted.
"$root/scripts/carryovers.sh" "$root" || exit 1
# Requirements status (C1, scripts/requirements.sh): every docs/requirements.md row has a Status; a ticked row is proved:
# by a verified fn with an ensures, tested-only rows are open work with an owner phase.
"$root/scripts/requirements.sh" "$root" || exit 1
# Script hygiene: every scripts/*.sh has set -eu and pipefail.
"$root/scripts/lint-scripts.sh" || exit 1
# Gate demos: each cheap gate rejects its canned bad input.
"$root/scripts/gate-demos.sh" || exit 1
# Tests: the unverified shell (crates/server) has no proofs, so its tests are its only guard.
"$root/scripts/test-gate.sh" "$root" "$CT_OUT/cargo-test.log" --workspace || exit 1
# The test floor only grows (a deleted test cannot hide behind the others), and every present external client fetches (F13).
"$root/scripts/test-floor.sh" "$root" || exit 1
"$root/scripts/interop.sh" "$root" || exit 1
# The tree must still be the one the run started on: an edit or a commit made mid-run leaves the clean line unearned.
"$root/scripts/clean-tree.sh" "$root" "$head" || {
    [ "${VERIFY_DIRTY:-}" = 1 ] || exit 1
    pfx="verify.sh (DIRTY TREE, vouches for no commit):"
}
echo "$pfx all crates verified, duvet ok, ct ok ($d declassify), cost $cost, escapes accounted ($attrs), binary ok ($bin fns)"
