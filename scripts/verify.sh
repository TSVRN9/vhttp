#!/bin/sh
set -eu
set -o pipefail
VERUS_HOME="${VERUS_HOME:-$HOME/.local/opt/verus/0.2026.10.04.426d8b0/verus-x86-linux}"
PATH="$VERUS_HOME:$PATH"
root=$(cd "$(dirname "$0")/.." && pwd)
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
tree=$(cargo tree -p crypto -e normal --depth 1 --prefix none) || fail "cargo tree failed"
[ "$(printf '%s\n' "$tree" | sed 1d | cut -d' ' -f1)" = vstd ] || fail "crypto's normal deps are not exactly vstd"
g=$CT_OUT/gate
mkdir -p "$g"
awk '$1 == "declassify" { s = $NF; $1 = ""; $NF = ""; gsub(/^ +| +$/, ""); print $0, s }' "$report" | LC_ALL=C sort > "$g/report"
awk -F'|' '/^\| ct-declassify: / { k = $2; sub(/^ ct-declassify: /, "", k); sub(/: .*/, "", k); s = $3; gsub(/^ +| +$/, "", s); print k, s }' TRUSTED.md | LC_ALL=C sort > "$g/trusted"
{ grep -rn --include='*.rs' 'declassify(' crates/crypto/src || [ $? -eq 1 ]; } | { grep -v '/ct\.rs:' || [ $? -eq 1 ]; } | { grep -vE '^[^:]*:[0-9]+:[[:space:]]*//' || [ $? -eq 1 ]; } | cut -d: -f1,2 | LC_ALL=C sort > "$g/source"
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
# Mutant registry (C6): every tools/mutants/ patch applies exactly and every allowed_*err predicate has a row; at main's
# tip, tools/mutants-last-run.txt must name this commit's crates/ and root Cargo files with every mutant killed.
"$root/scripts/mutants.sh" verify || exit 1
# Script hygiene: every scripts/*.sh has set -eu and pipefail.
"$root/scripts/lint-scripts.sh" || exit 1
# Gate demos: each cheap gate rejects its canned bad input.
"$root/scripts/gate-demos.sh" || exit 1
# Tests: the unverified shell (crates/server) has no proofs, so its tests are its only guard.
(cd "$root" && cargo test --workspace --locked -q > "$CT_OUT/cargo-test.log" 2>&1) || { cat "$CT_OUT/cargo-test.log"; echo "verify.sh: cargo test failed" >&2; exit 1; }
echo "verify.sh: all crates verified, duvet ok, ct ok ($d declassify), cost $cost, escapes accounted ($attrs), binary ok ($bin fns)"
