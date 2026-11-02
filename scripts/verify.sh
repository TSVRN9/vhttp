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
# Constant-time check; its crypto report is read by the declassify gate, so pin where it goes.
export CT_TARGET_DIR="${CT_TARGET_DIR:-$root/target/ct}"
export CT_OUT="${CT_OUT:-$CT_TARGET_DIR/out}"
mkdir -p "$CT_OUT"
"$root/scripts/ct-check.sh" > "$CT_OUT/ct-check.log" || { cat "$CT_OUT/ct-check.log"; exit 1; }
cat "$CT_OUT/ct-check.log"
cost=$(sed -n 's/^ct-check: cost \([0-9]*\/[0-9]*\) bounded$/\1/p' "$CT_OUT/ct-check.log")
[ -n "$cost" ] || { echo "verify.sh: no cost line in ct-check's output" >&2; exit 1; }
# Declassify gate: the report's `declassify <X>#<k> <file>:<line>` sites, the TRUSTED.md
# `| ct-declassify: <X>#<k>: ... | <file>:<line> |` rows and the non-comment `declassify(` lines
# of crates/crypto/src/ (ct.rs holds the definition) must be the same lists, duplicates included.
gate=declassify
fail() { echo "verify.sh: $gate gate: $*" >&2; exit 1; }
cd "$root"
report=$CT_OUT/crypto/report-crypto.txt
[ -f "$report" ] || fail "no $report"
# The fe_from_be/sec1_decode_exec ct-declassify rows rely on these fns having no secret param.
for f in fe_from_be sec1_decode_exec; do
    grep -q "^checked crypto::p256::$f secret= ret=" "$report" || fail "crypto::p256::$f has a secret-labelled param (its ct-declassify row says none)"
done
grep -q '^checked crypto::rsa::rsa_pss_sign_inner secret=d,msg,salt ret=' "$report" || fail "rsa_pss_sign_inner lost its secret labels"
grep -q '^checked crypto::rsa::mod_pow_ct secret=[^ ]*\be\b' "$report" || fail "mod_pow_ct's exponent is not secret"
grep -q '^checked crypto::rsa::modulus_bits secret= ret=' "$report" || fail "modulus_bits has a secret-labelled param"
if cargo tree -p crypto -e normal --prefix none | grep -qE '^(rsa|sha2|crypto-bigint) '; then fail "RustCrypto in crypto's normal deps"; fi
g=$CT_OUT/gate
mkdir -p "$g"
awk '$1 == "declassify" { s = $NF; $1 = ""; $NF = ""; gsub(/^ +| +$/, ""); print $0, s }' "$report" | LC_ALL=C sort > "$g/report"
awk -F'|' '/^\| ct-declassify: / { k = $2; sub(/^ ct-declassify: /, "", k); sub(/: .*/, "", k); s = $3; gsub(/^ +| +$/, "", s); print k, s }' TRUSTED.md | LC_ALL=C sort > "$g/trusted"
grep -rn --include='*.rs' 'declassify(' crates/crypto/src | grep -v '/ct\.rs:' | grep -vE '^[^:]*:[0-9]+:[[:space:]]*//' | cut -d: -f1,2 | LC_ALL=C sort > "$g/source"
awk '{ print $NF }' "$g/report" | LC_ALL=C sort > "$g/report-sites"
d=$(wc -l < "$g/report" | tr -d ' ')
for k in $(awk '{ $NF = ""; print }' "$g/report"); do
    grep -qF "| ct-declassify: $k: " TRUSTED.md || fail "$k has no TRUSTED.md ct-declassify row"
done
n=$(grep -c '^| ct-declassify: ' TRUSTED.md || true)
[ "$n" -eq "$d" ] || fail "$d report sites but $n TRUSTED.md ct-declassify rows"
n=$(wc -l < "$g/source" | tr -d ' ')
[ "$n" -eq "$d" ] || fail "$d report sites but $n declassify( lines in crates/crypto/src"
diff "$g/report" "$g/trusted" >&2 || fail "report sites and TRUSTED.md rows differ (diff above: < report, > TRUSTED.md)"
diff "$g/report-sites" "$g/source" >&2 || fail "report sites and declassify( lines differ (diff above: < report, > source)"
# Escape gate, per hit: every hit must be a bare #[verifier::external_body] line in
# crates/crypto/src/; each one must precede a fn named by a `| crypto::<mod>::<fn>: ` row in
# TRUSTED.md, and the attribute count must equal the number of `| crypto::` rows.
gate=escape
rc=0
hits=$(grep -rnE 'admit[[:space:]]*\(|assume[[:space:]]*\(|external_body|assume_specification|external_type_specification|external_trait_specification|verifier[[:space:]]*(::|\()[[:space:]]*external|\baxiom\b' "$root/crates" --include='*.rs') || rc=$?
[ "$rc" -le 1 ] || fail "grep failed (rc=$rc)"
# Escapes split across lines (e.g. `assume` newline `(`), which the line-based grep misses.
ml=$(grep -rlPz '\b(admit|assume)\s*\(' "$root/crates" --include='*.rs') && fail "escape across lines in: $ml"
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
echo "verify.sh: all crates verified, duvet ok, ct ok ($d declassify), cost $cost, escapes accounted ($attrs)"
