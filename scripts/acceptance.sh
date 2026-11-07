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
# col-0 `} // verus!`). Known limit: the cross-count checks lexing and block discovery only (the
# parser reaches every fn token by construction), so it cannot see a fn credited with the wrong
# clause text; the parser's raise on a body brace not indented under its fn covers that.
# On main the baseline is walked first-parent from the commit that introduced it (tools/ratchet_walk.py: no step may grow it) (and the working tree); a git error fails the gate. See tools/acceptance.py for the parser's limits.
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
walk=0
if [ "$(cd "$root" && pwd -P)" = "$(cd "$here" && pwd -P)" ] && [ "$have_old" -eq 0 ]; then
    die() { echo "acceptance: $*" >&2; exit 1; }
    head=$(git -C "$root" rev-parse HEAD) || die "cannot resolve HEAD"
    cmp=$(git -C "$root" merge-base HEAD main) || die "cannot resolve the merge-base of HEAD and main"
    if [ "$cmp" = "$head" ]; then walk=1; fi  # on main (or main == HEAD): walk the whole first-parent history and the working tree
    present=$(git -C "$root" ls-tree --name-only "$cmp" -- tools/acceptance-baseline.txt) || die "git ls-tree $cmp failed"
    if [ "$walk" -eq 1 ]; then
        :
    elif [ -n "$present" ]; then
        old=$(mktemp)
        trap 'rm -f "$old"' EXIT
        git -C "$root" show "$cmp:tools/acceptance-baseline.txt" > "$old" || die "git show $cmp:tools/acceptance-baseline.txt failed"
        extra="--old-baseline $old"
    else
        echo "acceptance: skipping the merge-base baseline check: $cmp has no tools/acceptance-baseline.txt" >&2
    fi
fi
[ "$walk" -eq 0 ] || python3 -I "$here/tools/ratchet_walk.py" "$root" tools/acceptance-baseline.txt lines
# shellcheck disable=SC2086 # $extra is `--old-baseline FILE` or empty
python3 -I "$here/tools/acceptance.py" "$@" $extra
parsed=$(python3 -I "$here/tools/acceptance.py" --count "$@" | tail -n 1)
indep=$(find "$root/crates" -name '*.rs' -not -path '*/target/*' -not -path "$root/crates/crypto/src/*" | LC_ALL=C sort | xargs -r -d '\n' awk '
    FNR == 1 { on = 0 }
    /^verus! *\{/ { on = 1; next }
    /^\} *\/\/ *verus!/ { on = 0; next }
    on { sub(/\/\/.*/, ""); gsub(/"[^"]*"/, ""); n += gsub(/(^|[^A-Za-z0-9_])fn[ \t]+[A-Za-z_]/, "&") }
    END { print n + 0 }')
[ "$parsed" = "$indep" ] || { echo "acceptance: the parser examined $parsed fns but an independent scan counts $indep fn tokens in verus! blocks" >&2; exit 1; }
