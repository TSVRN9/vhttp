#!/bin/sh
set -eu
set -o pipefail
# rfc-quantity.sh [--root DIR] [--allow FILE] [--open FILE] [--old-open FILE] [--allow-lines N]: the RFC-quantity
# gate (C8, tools/rfc_quantity.py). Every read in an allowed_*err predicate's body, and in the spec fns it calls, is
# vouched for as an RFC quantity (a `// rfc-quantity:` line, tools/rfc-quantity-allow.txt) or is a known open item in
# tools/rfc-quantity-open.txt, which only shrinks: with the default root, no line (or larger count) may be absent from
# the open file at the merge-base with main, or at HEAD^1 on main (acceptance.sh's scheme; skipped, and said so, when
# that commit has no open file; a git error fails the gate).
here=$(cd "$(dirname "$0")/.." && pwd)
root=$here
prev=
have_old=0
for a in "$@"; do
    [ "$prev" != --root ] || root=$a
    [ "$a" != --old-open ] || have_old=1
    prev=$a
done
die() { echo "rfc-quantity: $*" >&2; exit 1; }
extra=
if [ "$(cd "$root" && pwd -P)" = "$(cd "$here" && pwd -P)" ] && [ "$have_old" -eq 0 ]; then
    head=$(git -C "$root" rev-parse HEAD) || die "cannot resolve HEAD"
    cmp=$(git -C "$root" merge-base HEAD main) || die "cannot resolve the merge-base of HEAD and main"
    if [ "$cmp" = "$head" ]; then  # on main (or main == HEAD): compare with the previous commit
        cmp=$(git -C "$root" rev-parse "HEAD^1") || die "HEAD is main and has no parent to compare the open ratchet with"
    fi
    present=$(git -C "$root" ls-tree --name-only "$cmp" -- tools/rfc-quantity-open.txt) || die "git ls-tree $cmp failed"
    if [ -n "$present" ]; then
        old=$(mktemp)
        trap 'rm -f "$old"' EXIT
        git -C "$root" show "$cmp:tools/rfc-quantity-open.txt" > "$old" || die "git show $cmp:tools/rfc-quantity-open.txt failed"
        extra="--old-open $old"
    else
        echo "rfc-quantity: skipping the merge-base open-ratchet check: $cmp has no tools/rfc-quantity-open.txt" >&2
    fi
fi
# shellcheck disable=SC2086 # $extra is `--old-open FILE` or empty
python3 -I "$here/tools/rfc_quantity.py" "$@" $extra
