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
# Escape gate, per hit: every hit must be a bare #[verifier::external_body] line in
# crates/crypto/src/; each one must precede a fn named by a `| crypto::<mod>::<fn>: ` row in
# TRUSTED.md, and the attribute count must equal the number of `| crypto::` rows.
fail() { echo "verify.sh: escape gate: $*" >&2; exit 1; }
rc=0
hits=$(grep -rnE 'admit[[:space:]]*\(|assume[[:space:]]*\(|external_body|assume_specification|verifier[[:space:]]*(::|\()[[:space:]]*external|\baxiom\b' "$root/crates" --include='*.rs') || rc=$?
[ "$rc" -le 1 ] || fail "grep failed (rc=$rc)"
bad=$(printf '%s\n' "$hits" | awk -v pre="$root/crates/crypto/src/" 'NF { f=$0; sub(/:[0-9]+:.*/, "", f); t=$0; sub(/^[^:]*:[0-9]+:[ \t]*/, "", t); if (index(f, pre) != 1 || t != "#[verifier::external_body]") print }')
[ -z "$bad" ] || fail "unaccounted escape:
$bad"
attrs=$(printf '%s\n' "$hits" | grep -c . || true)
named=0
for f in "$root"/crates/crypto/src/*.rs; do
    [ -f "$f" ] || continue
    mod=$(basename "$f" .rs)
    for fn in $(awk '/^[ \t]*#\[verifier::external_body\]/ { p = 1; next } p && /^[ \t]*\/\// { next } p && /(proof|spec)[ \t]+fn / { print "NOT-EXEC-FN"; p = 0; next } p && match($0, /fn [A-Za-z_0-9]+/) { print substr($0, RSTART + 3, RLENGTH - 3); p = 0 }' "$f"); do
        [ "$fn" != NOT-EXEC-FN ] || fail "$mod.rs: external_body on a proof/spec fn"
        named=$((named + 1))
        grep -qF "| crypto::$mod::$fn: " "$root/TRUSTED.md" || fail "crypto::$mod::$fn has no TRUSTED.md row"
    done
done
rows=$(grep -c '^| crypto::' "$root/TRUSTED.md" || true)
[ "$attrs" -eq "$named" ] || fail "$attrs attributes but $named name a following fn"
[ "$attrs" -eq "$rows" ] || fail "$attrs attributes but $rows TRUSTED.md crypto rows"
echo "verify.sh: all crates verified, duvet ok, escapes accounted ($attrs)"
