#!/bin/sh
set -eu
set -o pipefail
# lint-scripts.sh [DIR]: every DIR/*.sh (default: this directory) must have `set -eu` and
# `set -o pipefail` (or `set -euo pipefail`) among its leading `set` lines, before the first other
# command. Comments and blank lines are skipped. Fails closed: no *.sh file is a failure.
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
    if [ -n "$miss" ]; then
        echo "lint-scripts: $f lacks:$miss before its first command" >&2
        bad=$((bad + 1))
    fi
done
[ "$n" -gt 0 ] || { echo "lint-scripts: no *.sh in $dir" >&2; exit 1; }
[ "$bad" -eq 0 ] || exit 1
echo "lint-scripts: $n scripts have set -eu and pipefail"
