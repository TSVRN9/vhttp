#!/bin/sh
set -eu
set -o pipefail
# carryovers.sh ROOT: docs/roadmap.md, docs/carryovers.tsv and TRUSTED.md agree (tools/carryovers.py check: owners are
# roadmap ids, closed rows' evidence resolves, no merged phase owns an open row, TRUSTED removal cells name a phase or
# `never (reason)`, merged phases name an ancestor commit and match the `Merge phase-<id>` commits, no tracked evidence
# cites an untracked path). Rows are never deleted, only closed, and a merged phase stays merged: on a branch the tsv and
# the roadmap keep every id (and merged id) of the merge-base with main's copy (skipped, and said so, when that commit has
# none); on main tools/ratchet_walk.py (ids, merged) keeps those of every first-parent copy.
root=${1:?root}
tools=$(cd "$(dirname "$0")/../tools" && pwd)
die() { echo "carryovers: $*" >&2; exit 1; }
{ [ -d "$root/.git" ] || [ -f "$root/.git" ]; } || die "$root is not a git checkout; cannot compare the carryovers with history"
python3 -I "$tools/carryovers.py" check "$root"
head=$(git -C "$root" rev-parse HEAD) || die "cannot resolve HEAD"
cmp=$(git -C "$root" merge-base HEAD main) || die "cannot resolve the merge-base of HEAD and main"
# walk FILE MODE: the merge-base copy on a branch, the first-parent history on main.
walk() {
    present=$(git -C "$root" ls-tree --name-only "$cmp" -- "$1") || die "git ls-tree $cmp failed"
    if [ "$cmp" = "$head" ]; then
        python3 -I "$tools/ratchet_walk.py" "$root" "$1" "$2"
    elif [ -n "$present" ]; then
        python3 -I "$tools/ratchet_walk.py" "$root" "$1" "$2" "$cmp"
    else
        echo "carryovers: skipping the merge-base check: $cmp has no $1" >&2
    fi
}
walk docs/carryovers.tsv ids
walk docs/roadmap.md merged
