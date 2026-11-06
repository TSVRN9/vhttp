#!/bin/sh
set -eu
set -o pipefail
# escape-gate.sh [ROOT]: the escape gate of verify.sh, runnable alone (scripts/gate-demos.sh feeds it
# a temp tree). ROOT (default: the repo) holds crates/ and TRUSTED.md. Prints
# `escape-gate: N escapes accounted` on success.
root=${1:-$(cd "$(dirname "$0")/.." && pwd)}
[ -d "$root/crates" ] && [ -f "$root/TRUSTED.md" ] || { echo "escape-gate: no $root/crates or $root/TRUSTED.md" >&2; exit 1; }
fail() { echo "escape-gate: $*" >&2; exit 1; }
# Escape gate, per hit: every hit must be a bare #[verifier::external_body] line in
# crates/crypto/src/; each one must precede a fn named by a `| crypto::<mod>::<fn>: ` row in
# TRUSTED.md, and the attribute count must equal the number of `| crypto::` rows.
rc=0
hits=$(grep -rnE 'admit[[:space:]]*\(|assume[[:space:]]*\(|external_body|assume_specification|external_type_specification|external_trait_specification|verifier[[:space:]]*(::|\()[[:space:]]*external|\baxiom\b' "$root/crates" --include='*.rs') || rc=$?
[ "$rc" -le 1 ] || fail "grep failed (rc=$rc)"
# Escapes split across lines (e.g. `assume` newline `(`), which the line-based grep misses.
rc=0
ml=$(grep -rlPz '\b(admit|assume)\s*\(' "$root/crates" --include='*.rs') || rc=$?
[ "$rc" -le 1 ] || fail "grep -P failed (rc=$rc)"
[ "$rc" -eq 1 ] || fail "escape across lines in: $ml"
bad=$(printf '%s\n' "$hits" | awk -v pre="$root/crates/crypto/src/" 'NF { f=$0; sub(/:[0-9]+:.*/, "", f); t=$0; sub(/^[^:]*:[0-9]+:[ \t]*/, "", t); if (index(f, pre) != 1 || t != "#[verifier::external_body]") print }')
[ -z "$bad" ] || fail "unaccounted escape:
$bad"
attrs=$(printf '%s\n' "$hits" | { grep -c . || [ $? -eq 1 ]; })
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
echo "escape-gate: $attrs escapes accounted"
