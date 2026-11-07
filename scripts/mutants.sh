#!/bin/sh
set -eu
set -o pipefail
# mutants.sh check|run [id..]|verify: the mutant registry (C6 MUST ONLY TEST-PINNED). tools/mutants.tsv rows are
# `id crate module fn tests regex origin` (tab-separated); tools/mutants/<id>.patch is one deliberate bug.
#   check   every row is well formed and has a patch touching only crates/<crate>/, no orphan patch, no duplicate id,
#           the tsv is non-empty, and every patch `git apply --check`s against this tree.
#   run     in a throwaway `git worktree` of HEAD (never the caller's tree), for each row: the unmutated fn verifies
#           and its named tests pass; then with the patch applied alone, `cargo verus focus -- --verify-only-module
#           <module> --verify-function <fn>` reports >= 1 error and a postcondition/precondition/assertion block
#           matching <regex> with no rlimit text, and every named test prints `test <name> ... FAILED`. `focus`
#           verifies only the crate (plain `verify -- ARGS` passes ARGS to the dependencies too). A full run (no ids)
#           writes tools/mutants-last-run.txt; a run of some ids only prints. Last step on a branch before merging.
#   verify  what verify.sh runs: `check`, and on main at a merge commit the merge gate (tools/mutants.py gate).
root=$(cd "$(dirname "$0")/.." && pwd)
VERUS_HOME="${VERUS_HOME:-$HOME/.local/opt/verus/0.2026.10.04.426d8b0/verus-x86-linux}"
PATH="$VERUS_HOME:$PATH"
tsv=$root/tools/mutants.tsv
pdir=$root/tools/mutants
mpy() { python3 -I "$root/tools/mutants.py" "$@"; }
fail() { echo "mutants: $*" >&2; exit 1; }

check() {
    [ -f "$tsv" ] || fail "no $tsv"
    [ -d "$pdir" ] || fail "no $pdir"
    rows=$(mpy rows "$tsv" "$pdir") || exit 1
    n=0
    for id in $(printf '%s\n' "$rows" | cut -f1); do
        e=$(git -C "$root" apply --check "$pdir/$id.patch" 2>&1) || fail "$id.patch does not apply to this tree (regenerate it with git diff): $e"
        n=$((n + 1))
    done
    [ "$n" -gt 0 ] || fail "no rows"
    echo "mutants: check ok ($n mutants, every patch applies)"
}

# one BASE CRATE MODULE FN: run Verus on FN alone in the worktree; its JSON goes to BASE.json, its stderr to BASE.log.
one() {
    # cargo verus decides freshness by content (blake3) and ignores verus args, so an unchanged crate would be a cached
    # no-op that verifies nothing: clean it first (tools/mutants.py also fails a log without a results line).
    (cd "$wt" && cargo clean -q -p "$2" --target-dir "$wt/target/verus-partial") < /dev/null > "$1.clean-cargo.log" 2>&1 || { : > "$1.json"; echo "cargo clean -p $2 failed" > "$1.log"; return 0; }
    (cd "$wt/crates/$2" && cargo verus focus -- --verify-only-module "$3" --verify-function "$4" --output-json --time-expanded) \
        < /dev/null > "$1.json" 2> "$1.log" || true
}

# tests LOGBASE CRATE TESTS WANT: each target:name of TESTS must print `test name ... WANT` (ok or FAILED).
tests() {
    [ "$3" = - ] && return 0
    for t in $(printf '%s\n' "$3" | tr ',' ' '); do
        (cd "$wt" && cargo test -p "$2" --test "${t%%:*}" -- --exact "${t#*:}") < /dev/null > "$1.${t#*:}.log" 2>&1 || true
        grep -qxF "test ${t#*:} ... $4" "$1.${t#*:}.log" || { echo "test ${t#*:} did not print '... $4' ($1.${t#*:}.log)"; return 1; }
    done
}

run() {
    check > /dev/null
    [ -z "$(git -C "$root" status --porcelain -- crates tools/mutants tools/mutants.tsv)" ] \
        || fail "crates/ or the registry has uncommitted changes; the run uses HEAD, so commit first"
    rows=$(mpy rows "$tsv" "$pdir") || exit 1
    full=1
    if [ $# -gt 0 ]; then
        full=0
        sel=
        for id in "$@"; do
            r=$(printf '%s\n' "$rows" | awk -F'\t' -v i="$id" '$1 == i') || true
            [ -n "$r" ] || fail "no row $id"
            sel="$sel$r
"
        done
        rows=$(printf '%s' "$sel")
    fi
    common=$(git -C "$root" rev-parse --path-format=absolute --git-common-dir) || fail "not a git repo"
    parent=$(dirname "$common")/.worktrees
    mkdir -p "$parent"
    wt=$(mktemp -d "$parent/mutants-XXXXXX")
    trap 'git -C "$root" worktree remove --force "$wt" > /dev/null 2>&1 || rmdir "$wt" 2> /dev/null || true; git -C "$root" worktree prune' EXIT
    trap 'exit 1' INT TERM HUP
    git -C "$root" worktree add -q --detach "$wt" HEAD || fail "git worktree add failed"
    out=${MUTANTS_OUT:-$root/target/mutants}
    mkdir -p "$out"
    rm -f "$out"/*.log "$out"/*.json
    crates=$(git -C "$wt" rev-parse HEAD:crates)
    tsvblob=$(git -C "$wt" rev-parse HEAD:tools/mutants.tsv)
    res="# tools/mutants-last-run.txt: written by scripts/mutants.sh run on $(date -u +%Y-%m-%dT%H:%MZ); verify.sh's merge gate reads it
crates $crates
tsv $tsvblob"
    bad=0
    tab=$(printf '\t')
    while IFS=$tab read -r id crate mod fn tst rx; do
        t0=$(date +%s)
        git -C "$wt" reset -q --hard HEAD && git -C "$wt" clean -fdq -- crates || fail "cannot reset the worktree"
        why=
        one "$out/$id.clean" "$crate" "$mod" "$fn"
        if ! why=$(mpy clean "$out/$id.clean" "$crate" "$mod" "$fn" 2>&1); then :
        elif ! why=$(tests "$out/$id.clean" "$crate" "$tst" ok); then why="unmutated: $why"
        elif ! why=$(git -C "$wt" apply "$wt/tools/mutants/$id.patch" 2>&1); then why="patch does not apply: $why"
        else
            one "$out/$id" "$crate" "$mod" "$fn"
            if ! why=$(mpy killed "$out/$id" "$crate" "$mod" "$fn" "$rx" 2>&1); then :
            elif ! why=$(tests "$out/$id" "$crate" "$tst" FAILED); then why="mutant: $why"
            else why=; fi
        fi
        if [ -z "$why" ]; then
            echo "mutants: $id: killed ($crate $mod::$fn, $(($(date +%s) - t0))s)"
            res="$res
$id pass $(git -C "$wt" rev-parse "HEAD:tools/mutants/$id.patch")"
        else
            echo "mutants: $id: FAILED: $why" >&2
            res="$res
$id fail $(git -C "$wt" rev-parse "HEAD:tools/mutants/$id.patch")"
            bad=$((bad + 1))
        fi
    done <<EOF
$rows
EOF
    if [ "$full" -eq 1 ]; then
        printf '%s\n' "$res" > "$root/tools/mutants-last-run.txt"
        echo "mutants: wrote tools/mutants-last-run.txt (crates tree $crates)"
    fi
    [ "$bad" -eq 0 ] || fail "$bad mutants not killed (logs in $out)"
    echo "mutants: run ok ($(printf '%s\n' "$rows" | wc -l | tr -d ' ') mutants killed)"
}

verify() {
    check
    branch=$(git -C "$root" symbolic-ref -q --short HEAD) || branch=
    if [ "$branch" = main ] && git -C "$root" rev-parse -q --verify HEAD^2 > /dev/null; then
        mpy gate "$root" || exit 1
    else
        echo "mutants: not a merge commit on main (${branch:-detached}): merge gate not applicable, check only"
    fi
}

case ${1:-} in
check) check ;;
run) shift; run "$@" ;;
verify) verify ;;
*) fail "usage: mutants.sh check | run [id..] | verify" ;;
esac
