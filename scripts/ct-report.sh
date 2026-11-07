#!/bin/sh
set -eu
set -o pipefail
# ct-report.sh REPORT MANIFEST LABELS OUTDIR: ct-check.sh's reader of the crypto report (runnable
# alone; scripts/gate-demos.sh feeds it canned reports). No `reject` line, a verdict for every
# MANIFEST root, and the report's `checked` lines equal to LABELS. Verdicts and labels go to OUTDIR.
[ $# -eq 4 ] || { echo "usage: ct-report.sh REPORT MANIFEST LABELS OUTDIR" >&2; exit 1; }
report=$1 cm=$2 labels=$3 out=$4
CT_OUT=${CT_OUT:-$out}
fail() { echo "ct-check: $*" >&2; exit 1; }
. "$(dirname "$0")/ct-lib.sh"
[ -f "$report" ] || fail "crypto: no report $report"
[ -s "$report" ] || fail "crypto: empty report $report"
[ -f "$cm" ] && [ -f "$labels" ] || fail "crypto: no manifest $cm or labels $labels"
[ "$(grep -c '^root ' "$cm" || true)" -gt 0 ] || fail "crypto: no root in $cm"
mkdir -p "$out"
grep '^reject ' "$report" >&2 && fail "crypto: rejects (above)"
got=$out/verdicts.txt
verdicts "$report" > "$got"
no_missing "$cm" "$got"
grep '^checked ' "$report" > "$out/labels.txt" || true
diff -u "$labels" "$out/labels.txt" || fail "crypto: checked lines differ from tools/ct-driver/expected-labels.txt"
