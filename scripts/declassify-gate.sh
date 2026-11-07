#!/bin/sh
set -eu
set -o pipefail
# declassify-gate.sh ROOT REPORT GATEDIR: the declassify gate of verify.sh, runnable alone
# (scripts/gate-demos.sh feeds it a temp tree). REPORT is ct-check's crypto report; ROOT holds
# TRUSTED.md and crates/crypto/src; GATEDIR gets the sorted lists. The report's
# `declassify <X>#<k> <file>:<line>` sites, the TRUSTED.md
# `| ct-declassify: <X>#<k>: ... | <file>:<line> |` rows and the non-comment `declassify(` lines
# of crates/crypto/src/ (ct.rs holds the definition) must be the same lists, duplicates included.
# Prints `declassify-gate: N declassify sites accounted` on success.
[ $# -eq 3 ] || { echo "usage: declassify-gate.sh ROOT REPORT GATEDIR" >&2; exit 1; }
root=$1 report=$2 g=$3
fail() { echo "declassify-gate: $*" >&2; exit 1; }
[ -d "$root/crates/crypto/src" ] && [ -f "$root/TRUSTED.md" ] || fail "no $root/crates/crypto/src or $root/TRUSTED.md"
cd "$root"
[ -f "$report" ] || fail "no $report"
[ -s "$report" ] || fail "$report is empty"
# The fe_from_be/sec1_decode_exec ct-declassify rows rely on these fns having no secret param.
for f in fe_from_be sec1_decode_exec; do
    grep -q "^checked crypto::p256::$f secret= ret=" "$report" || fail "crypto::p256::$f has a secret-labelled param (its ct-declassify row says none)"
done
grep -q '^checked crypto::rsa::rsa_pss_sign_inner secret=d,msg,salt ret=' "$report" || fail "rsa_pss_sign_inner lost its secret labels"
grep -q '^checked crypto::rsa::mod_pow_ct secret=[^ ]*\be\b' "$report" || fail "mod_pow_ct's exponent is not secret"
grep -q '^checked crypto::rsa::modulus_bits secret= ret=' "$report" || fail "modulus_bits has a secret-labelled param"
mkdir -p "$g"
awk '$1 == "declassify" { s = $NF; $1 = ""; $NF = ""; gsub(/^ +| +$/, ""); print $0, s }' "$report" | LC_ALL=C sort > "$g/report"
awk -F'|' '/^\| ct-declassify: / { k = $2; sub(/^ ct-declassify: /, "", k); sub(/: .*/, "", k); s = $3; gsub(/^ +| +$/, "", s); print k, s }' TRUSTED.md | LC_ALL=C sort > "$g/trusted"
{ grep -rn --include='*.rs' 'declassify(' crates/crypto/src || [ $? -eq 1 ]; } | { grep -v '/ct\.rs:' || [ $? -eq 1 ]; } | { grep -vE '^[^:]*:[0-9]+:[[:space:]]*//' || [ $? -eq 1 ]; } | cut -d: -f1,2 | LC_ALL=C sort > "$g/source"
awk '{ print $NF }' "$g/report" | LC_ALL=C sort > "$g/report-sites"
d=$(wc -l < "$g/report" | tr -d ' ')
[ "$d" -gt 0 ] || fail "no declassify site in $report"
for k in $(awk '{ $NF = ""; print }' "$g/report"); do
    grep -qF "| ct-declassify: $k: " TRUSTED.md || fail "$k has no TRUSTED.md ct-declassify row"
done
n=$(grep -c '^| ct-declassify: ' TRUSTED.md || true)
[ "$n" -eq "$d" ] || fail "$d report sites but $n TRUSTED.md ct-declassify rows"
n=$(wc -l < "$g/source" | tr -d ' ')
[ "$n" -eq "$d" ] || fail "$d report sites but $n declassify( lines in crates/crypto/src"
diff "$g/report" "$g/trusted" >&2 || fail "report sites and TRUSTED.md rows differ (diff above: < report, > TRUSTED.md)"
diff "$g/report-sites" "$g/source" >&2 || fail "report sites and declassify( lines differ (diff above: < report, > source)"
echo "declassify-gate: $d declassify sites accounted"
