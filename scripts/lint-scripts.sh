#!/bin/sh
set -eu
set -o pipefail
# lint-scripts.sh [DIR]: every DIR/*.sh (default: this directory) must have `set -eu` and
# `set -o pipefail` (or `set -euo pipefail`) among its leading `set` lines, before the first other
# command. Comments and blank lines are skipped. Also rejects grep used as a verdict (`grep .. && fail`,
# `if grep ..`, `! grep ..`, `while grep ..`): grep exits 2 on a missing file, which those read as "no match";
# use grep_hits (scripts/ct-lib.sh), or `grep .. || fail` for a required match. Fails closed: no *.sh file is a failure.
dir=${1:-$(dirname "$0")}
n=0
bad=0
for f in "$dir"/*.sh; do
    [ -f "$f" ] || continue
    n=$((n + 1))
    miss=$(awk '
        /^[ \t]*(#|$)/ { next }
        /^set -(eu|ue)$/ { eu = 1; next }
        /^set -o pipefail$/ { pf = 1; next }
        /^set -(euo|ueo) pipefail$/ { eu = pf = 1; next }
        /^set -[a-z]+$/ { next }
        { exit }
        END { if (!eu) printf " set-eu"; if (!pf) printf " pipefail" }' "$f")
    idiom=$({ grep -nE '(^|[^_[:alnum:]])grep[[:space:]][^|;]*&&[[:space:]]*(fail|die|err|exit)\b|(^|[[:space:];({])(if|while|until|!)[[:space:]]+grep[[:space:]]' "$f" || [ $? -eq 1 ]; } | { grep -vE '^[0-9]+:[[:space:]]*#' || [ $? -eq 1 ]; })
    if [ -n "$idiom" ]; then
        echo "lint-scripts: $f uses grep as a verdict (exit 2 reads as no match; use grep_hits):" >&2
        printf '%s\n' "$idiom" >&2
        bad=$((bad + 1))
    fi
    if [ -n "$miss" ]; then
        echo "lint-scripts: $f lacks:$miss before its first command" >&2
        bad=$((bad + 1))
    fi
done
[ "$n" -gt 0 ] || { echo "lint-scripts: no *.sh in $dir" >&2; exit 1; }
[ "$bad" -eq 0 ] || exit 1
echo "lint-scripts: $n scripts have set -eu and pipefail"
