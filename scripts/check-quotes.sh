#!/bin/sh
set -eu
set -o pipefail
# check-quotes.sh [CRATES_DIR [SPEC_DIR]]: every Duvet `//#` quote in every .rs under CRATES_DIR (default:
# crates/) must occur in its RFC section (`duvet report` exits 0 even when it does not). Needs
# .duvet/specifications, which is git-ignored: a missing directory, no .rs file or no citation is
# a failure, not a skip.
root=$(cd "$(dirname "$0")/.." && pwd)
src=${1:-$root/crates}
spec=${2:-$root/.duvet/specifications}
[ -d "$spec" ] || { echo "check-quotes: no $spec" >&2; exit 1; }
[ -d "$src" ] || { echo "check-quotes: no $src" >&2; exit 1; }
out=$(find "$src" -name '*.rs' -not -path '*/target/*' -print0 | sort -z | xargs -0 python3 -I "$root/tools/check_quotes.py" --spec-dir "$spec") || {
    printf '%s\n' "$out" >&2
    echo "check-quotes: bad quotes (above)" >&2
    exit 1
}
echo "check-quotes: $out"
