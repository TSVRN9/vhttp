#!/bin/sh
set -eu
set -o pipefail
# clean-tree.sh ROOT [HEAD]: exit 0 iff `git -C ROOT status --porcelain` is empty (a green run then describes HEAD); a git error fails.
# With HEAD (verify.sh's start-of-run `git rev-parse HEAD`) it also fails when HEAD has moved, so an end-of-run call catches a commit or an edit made mid-run.
root=${1:?usage: clean-tree.sh ROOT [HEAD]}
st=$(git -C "$root" status --porcelain) || { echo "clean-tree: git status failed in $root" >&2; exit 1; }
[ -z "$st" ] || { echo "clean-tree: tree dirty ($(printf '%s\n' "$st" | wc -l) paths)" >&2; exit 1; }
if [ -n "${2:-}" ]; then
    now=$(git -C "$root" rev-parse HEAD) || { echo "clean-tree: git rev-parse failed in $root" >&2; exit 1; }
    [ "$now" = "$2" ] || { echo "clean-tree: HEAD moved during the run ($2 -> $now)" >&2; exit 1; }
fi
