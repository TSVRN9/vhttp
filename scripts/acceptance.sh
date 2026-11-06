#!/bin/sh
set -eu
set -o pipefail
# acceptance.sh [--root DIR] [--baseline FILE] [--old-baseline FILE]: the error-path acceptance
# ratchet. Every error-returning exec fn inside verus! must carry an allowed_*err clause in its
# ensures or be listed in tools/acceptance-baseline.txt, which only shrinks: it is capped by
# MAX_BASELINE in tools/acceptance.py and, with the default root, no line may be absent from the
# baseline at the merge-base with main (skipped, and said so, when that commit has no baseline;
# an unresolvable merge-base or main is a failure). The number of fn items the parser examined
# must equal an independent awk count of fn tokens in the verus! blocks (col-0 `verus! {` to
# col-0 `} // verus!`). See tools/acceptance.py for the parser's limits.
here=$(cd "$(dirname "$0")/.." && pwd)
root=$here
prev=
for a in "$@"; do
    [ "$prev" != --root ] || root=$a
    prev=$a
done
have_old=0
for a in "$@"; do [ "$a" != --old-baseline ] || have_old=1; done
extra=
if [ "$root" = "$here" ] && [ "$have_old" -eq 0 ]; then
    mb=$(git -C "$root" merge-base HEAD main) || { echo "acceptance: cannot resolve the merge-base of HEAD and main" >&2; exit 1; }
    if git -C "$root" cat-file -e "$mb:tools/acceptance-baseline.txt" 2>/dev/null; then
        old=$(mktemp)
        trap 'rm -f "$old"' EXIT
        git -C "$root" show "$mb:tools/acceptance-baseline.txt" > "$old"
        extra="--old-baseline $old"
    else
        echo "acceptance: skipping the merge-base baseline check: $mb has no tools/acceptance-baseline.txt" >&2
    fi
fi
# shellcheck disable=SC2086 # $extra is `--old-baseline FILE` or empty
python3 -I "$here/tools/acceptance.py" "$@" $extra
parsed=$(python3 -I "$here/tools/acceptance.py" --count "$@" | tail -n 1)
indep=$(find "$root/crates" -name '*.rs' -not -path '*/target/*' -not -path "$root/crates/crypto/src/*" | LC_ALL=C sort | xargs -r awk '
    /^verus! *\{/ { on = 1; next }
    /^\} *\/\/ *verus!/ { on = 0; next }
    on { sub(/\/\/.*/, ""); gsub(/"[^"]*"/, ""); n += gsub(/(^|[^A-Za-z0-9_])fn[ \t]+[A-Za-z_]/, "&") }
    END { print n + 0 }')
[ "$parsed" = "$indep" ] || { echo "acceptance: the parser examined $parsed fns but an independent scan counts $indep fn tokens in verus! blocks" >&2; exit 1; }
