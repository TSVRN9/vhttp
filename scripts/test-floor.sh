#!/bin/sh
set -eu
set -o pipefail
# test-floor.sh ROOT: tools/test-floor.txt only grows. On a branch it is compared with the merge-base with main's copy (no value
# lower, no line removed; skipped, and said so, when that commit has no file); on main by the first-parent walk of
# tools/ratchet_walk.py (floors): HEAD's copy and the working tree stay at or above each key's highest earlier value.
root=${1:?root}
tools=$(cd "$(dirname "$0")/../tools" && pwd)
die() { echo "test-floor: $*" >&2; exit 1; }
{ [ -d "$root/.git" ] || [ -f "$root/.git" ]; } || die "$root is not a git checkout; cannot compare the floor with history"
head=$(git -C "$root" rev-parse HEAD) || die "cannot resolve HEAD"
cmp=$(git -C "$root" merge-base HEAD main) || die "cannot resolve the merge-base of HEAD and main"
present=$(git -C "$root" ls-tree --name-only "$cmp" -- tools/test-floor.txt) || die "git ls-tree $cmp failed"
if [ "$cmp" = "$head" ]; then
    python3 -I "$tools/ratchet_walk.py" "$root" tools/test-floor.txt floors
elif [ -n "$present" ]; then
    python3 -I "$tools/ratchet_walk.py" "$root" tools/test-floor.txt floors "$cmp"
else
    echo "test-floor: skipping the merge-base check: $cmp has no tools/test-floor.txt" >&2
fi
