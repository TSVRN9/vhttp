#!/bin/sh
set -eu
set -o pipefail
# clean-tree.sh ROOT: exit 0 iff `git -C ROOT status --porcelain` is empty (a green run then describes HEAD); a git error fails.
st=$(git -C "${1:?usage: clean-tree.sh ROOT}" status --porcelain) || { echo "clean-tree: git status failed in $1" >&2; exit 1; }
[ -z "$st" ] || { echo "clean-tree: tree dirty ($(printf '%s\n' "$st" | wc -l) paths)" >&2; exit 1; }
