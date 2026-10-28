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
# Escape accounting: every file in crates/ holding an escape token must be named in TRUSTED.md.
hits=$(grep -rlE 'admit\(|assume\(|external_body|assume_specification|verifier::external|axiom fn' "$root/crates" --include='*.rs' || true)
for f in $hits; do
    rel=${f#"$root"/}
    grep -qF "$rel" "$root/TRUSTED.md" || { echo "verify.sh: escape in $rel has no TRUSTED.md entry" >&2; exit 1; }
done
echo "verify.sh: all crates verified, duvet ok, escapes accounted"
