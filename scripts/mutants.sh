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
#   verify  what verify.sh runs: `check`, and at main's tip (every commit there, merge or not) the gate
#           (tools/mutants.py gate): the committed run file names this commit's crates/ + root Cargo.toml, Cargo.lock,
#           rust-toolchain.toml with every id passing. check also fails on an allowed_*err predicate with no row.
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
    mpy allowed "$root" "$tsv" > /dev/null || exit 1
    n=0
    for id in $(printf '%s\n' "$rows" | cut -f1); do
        e=$(git -C "$root" apply --check -v "$pdir/$id.patch" 2>&1) || fail "$id.patch does not apply to this tree (regenerate it with git diff): $e"
        # a hunk found at another line may be an identical-looking spot (T6-M2 has three near-identical hunks)
        if printf '%s\n' "$e" | grep -qiE 'offset|fuzz'; then fail "$id.patch applies only with an offset (regenerate it with git diff): $e"; fi
        n=$((n + 1))
    done
    [ "$n" -gt 0 ] || fail "no rows"
    echo "mutants: check ok ($n mutants, every patch applies exactly, every allowed_*err predicate has a row)"
}

# one BASE CRATE MODULE FN: run Verus on FN alone in the worktree; its JSON goes to BASE.json, its stderr to BASE.log.
one() {
    # cargo verus decides freshness by content (blake3) and ignores verus args, so an unchanged crate would be a cached
    # no-op that verifies nothing: clean it first (tools/mutants.py also fails a log without a results line).
    (cd "$wt" && cargo clean -q -p "$2" --target-dir "${CARGO_TARGET_DIR:-$wt/target}/verus-partial") < /dev/null > "$1.clean-cargo.log" 2>&1 || { : > "$1.json"; echo "cargo clean -p $2 failed" > "$1.log"; return 0; }
    (cd "$wt/crates/$2" && cargo verus focus -- --verify-only-module "$3" --verify-function "$4" --output-json --time-expanded) \
        < /dev/null > "$1.json" 2> "$1.log" || true
}

# tests LOGBASE CRATE TESTS WANT: each [package/]target:name of TESTS (package defaults to CRATE) must print
# `test name ... WANT` (ok or FAILED); a misspelt name runs 0 tests and prints neither.
tests() {
    [ "$3" = - ] && return 0
    for t in $(printf '%s\n' "$3" | tr ',' ' '); do
        p=$2 name=${t#*:} tgt=${t%%:*}
        case $tgt in */*) p=${tgt%%/*} tgt=${tgt#*/} ;; esac
        (cd "$wt" && cargo test -p "$p" --test "$tgt" -- --exact "$name") < /dev/null > "$1.$name.log" 2>&1 || true
        grep -qxF "test $name ... $4" "$1.$name.log" || { echo "test $p/$tgt:$name did not print '... $4' ($1.$name.log)"; return 1; }
    done
}

run() {
    check > /dev/null
    st=$(git -C "$root" status --porcelain -- crates tools/mutants tools/mutants.tsv tools/mutants.py scripts/mutants.sh) || fail "git status failed"
    [ -z "$st" ] || fail "crates/, the registry or the mutants tools have uncommitted changes; the run uses HEAD, so commit first"
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
    # the worktree's own target dir, not a CARGO_TARGET_DIR shared with other worktrees; MUTANTS_TARGET_DIR (gate-demos
    # only) keeps vstd built across the demos' throwaway repos
    unset CARGO_TARGET_DIR
    [ -z "${MUTANTS_TARGET_DIR:-}" ] || export CARGO_TARGET_DIR="$MUTANTS_TARGET_DIR"
    out=${MUTANTS_OUT:-$root/target/mutants}
    mkdir -p "$out"
    rm -f "$out"/*.log "$out"/*.json
    crates=$(git -C "$wt" rev-parse HEAD:crates)
    runtree=$(mpy tree "$wt" HEAD) || exit 1
    tsvblob=$(git -C "$wt" rev-parse HEAD:tools/mutants.tsv)
    res="# tools/mutants-last-run.txt: written by scripts/mutants.sh run on $(date -u +%Y-%m-%dT%H:%MZ); verify.sh's main gate reads it
crates $crates
tree $runtree
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
    head=$(git -C "$root" rev-parse HEAD) || fail "git rev-parse HEAD failed"
    # main's tip (checked out as main, or detached as in a CI checkout), merge or not: a fast-forward or a squash is
    # gated like a merge. No main is a failure, not a skipped gate.
    main=$(git -C "$root" rev-parse -q --verify refs/heads/main) || fail "cannot resolve main (refs/heads/main): the gate cannot tell whether HEAD is main's tip"
    if [ "$head" = "$main" ]; then
        mpy gate "$root" || exit 1
    else
        echo "mutants: HEAD is not main's tip: main gate not applicable, check only"
    fi
}

# One braced block, parsed whole before it runs: sh reads a script as it goes, so an edit to this file during a long
# run would otherwise be executed from the middle (seen in the first full run).
{
    case ${1:-} in
    check) check ;;
    run) shift; run "$@" ;;
    verify) verify ;;
    *) fail "usage: mutants.sh check | run [id..] | verify" ;;
    esac
    exit
}
