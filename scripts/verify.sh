#!/bin/sh
set -eu
VERUS_HOME="${VERUS_HOME:-$HOME/.local/opt/verus/0.2026.10.04.426d8b0/verus-x86-linux}"
PATH="$VERUS_HOME:$PATH"
root=$(cd "$(dirname "$0")/.." && pwd)
for c in "$root"/crates/*/; do
    [ -d "$c" ] || { echo "verify.sh: no crates under crates/" >&2; exit 1; }
    (cd "$c" && cargo verus verify)
done
(cd "$root" && duvet report)
# Escape gate: no escape token anywhere in crates/ (Phase 3 reintroduces per-hit accounting).
rc=0
grep -rnE 'admit\(|assume\(|external_body|assume_specification|verifier::external|verifier\(external|\baxiom\b' "$root/crates" --include='*.rs' || rc=$?
[ "$rc" -eq 1 ] || { echo "verify.sh: escape found in crates/ (or grep failed, rc=$rc)" >&2; exit 1; }
echo "verify.sh: all crates verified, duvet ok, no escapes"
