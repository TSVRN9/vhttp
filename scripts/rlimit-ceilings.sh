#!/bin/sh
set -eu
set -o pipefail
# rlimit-ceilings.sh ROOT LOGDIR: the ceilings ratchet over the per-crate JSON logs in LOGDIR (see tools/rl.py --ceilings):
# every fn above 8,000,000 in any crate is listed in ROOT/tools/rlimit-ceilings.txt at no more than its listed value, the
# file only shrinks (compared with the merge-base with main, or HEAD^1 on main, exactly as scripts/acceptance.sh does for
# its baseline; skipped, and said so, when that commit has no file), and the unverified-shell exemption of crates/server
# holds only while crates/server/src has no verus! and no #[verifier.
root=${1:?root}
logs=${2:?logdir}
tools=$(cd "$(dirname "$0")/../tools" && pwd)
die() { echo "rlimit-gate: $*" >&2; exit 1; }
if [ -d "$root/crates/server/src" ]; then
    hits=$(grep -rnE 'verus!|#\[verifier' "$root/crates/server/src" || [ $? -eq 1 ])
    [ -z "$hits" ] || die "crates/server is exempt as unverified shell code but has proofs:
$hits"
fi
set -- "$logs"/*.json
[ -f "$1" ] || die "no JSON logs in $logs"
extra=
if [ -d "$root/.git" ] || [ -f "$root/.git" ]; then
    head=$(git -C "$root" rev-parse HEAD) || die "cannot resolve HEAD"
    cmp=$(git -C "$root" merge-base HEAD main) || die "cannot resolve the merge-base of HEAD and main"
    if [ "$cmp" = "$head" ]; then
        cmp=$(git -C "$root" rev-parse "HEAD^1") || die "HEAD is main and has no parent to compare the ceilings with"
    fi
    present=$(git -C "$root" ls-tree --name-only "$cmp" -- tools/rlimit-ceilings.txt) || die "git ls-tree $cmp failed"
    if [ -n "$present" ]; then
        old=$(mktemp)
        trap 'rm -f "$old"' EXIT
        git -C "$root" show "$cmp:tools/rlimit-ceilings.txt" > "$old" || die "git show $cmp:tools/rlimit-ceilings.txt failed"
        extra="--old $old"
    else
        echo "rlimit-gate: skipping the merge-base ceilings check: $cmp has no tools/rlimit-ceilings.txt" >&2
    fi
else
    die "$root is not a git checkout; cannot compare the ceilings with history"
fi
# shellcheck disable=SC2086 # $extra is `--old FILE` or empty
python3 -I "$tools/rl.py" --ceilings "$root/tools/rlimit-ceilings.txt" $extra "$@"
