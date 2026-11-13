#!/bin/sh
set -eu
set -o pipefail
# mutants.sh check|run [--out FILE] [id..]|verify: the mutant registry (C6 MUST ONLY TEST-PINNED). tools/mutants.tsv rows are
# `id crate module fn tests regex origin` (tab-separated); tools/mutants/<id>.patch is one deliberate bug.
#   check   every row is well formed and has a patch touching only crates/<crate>/ and its path dependencies, no orphan
#           patch, no duplicate id,
#           the tsv is non-empty, and every patch `git apply --check`s against this tree.
#   run     in throwaway `git worktree`s of HEAD (never the caller's tree; MUTANTS_JOBS of them, default 4, each taking
#           every MUTANTS_JOBS-th row), for each row: the unmutated fn verifies
#           and its named tests pass; then with the patch applied alone, each path dependency it touches still verifies
#           whole on its own (`cargo verus focus` in that crate: 0 errors, no rlimit text; otherwise a patch breaking the
#           dependency's proof would pass as a kill here), `cargo verus focus -- --verify-only-module
#           <module> --verify-function <fn>` reports >= 1 error and a postcondition/precondition/assertion/loop-invariant
#           block matching <regex> with no rlimit text, and every named test prints `test <name> ... FAILED`. `focus`
#           verifies only the crate (plain `verify -- ARGS` passes ARGS to the dependencies too). `verus --version`
#           must name the pinned version (tools/verus-pin.txt) and every Verus JSON must carry the pinned version, commit
#           and toolchain (tools/mutants.py). A full run (no ids) writes tools/mutants-last-run.txt (or FILE), its `#`
#           line naming the pinned Verus; a run of some ids only prints. Last step on a branch before merging.
#   verify  what verify.sh runs: `check`, and at main's tip (every commit there, merge or not) the gate
#           (tools/mutants.py gate): the committed run file names this commit's crates/ + root Cargo.toml, Cargo.lock,
#           rust-toolchain.toml and the pinned Verus with every id passing; then a full `run --out` and `mutants.py same`
#           against the committed file, since git alone can produce a file the gate accepts (audit F4). On a branch, the
#           gate once crates/, the root Cargo files or the registry differ from the merge-base's (tools/mutants.py
#           gate-branch), and no run. check also fails on an allowed_*err predicate with no row.
root=$(cd "$(dirname "$0")/.." && pwd)
verus_ver=$(sed -n 's/^version //p' "$root/tools/verus-pin.txt")
[ -n "$verus_ver" ] || { echo "mutants.sh: no version line in tools/verus-pin.txt" >&2; exit 1; }
VERUS_HOME="${VERUS_HOME:-$HOME/.local/opt/verus/$verus_ver/verus-x86-linux}"
PATH="$VERUS_HOME:$PATH"
tsv=$root/tools/mutants.tsv
pdir=$root/tools/mutants
out=${MUTANTS_OUT:-$root/target/mutants}
mpy() { python3 -I "$root/tools/mutants.py" "$@"; }
fail() { echo "mutants: $*" >&2; exit 1; }

check() {
    [ -f "$tsv" ] || fail "no $tsv"
    [ -d "$pdir" ] || fail "no $pdir"
    rows=$(mpy rows "$root" "$tsv" "$pdir") || exit 1
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

# deps BASE DEPS: each crate of DEPS (comma-separated, - for none), a patched path dependency, verifies whole on its own;
# focus's own run of the row's crate only rebuilds it.
deps() {
    [ "$2" = - ] && return 0
    for d in $(printf '%s\n' "$2" | tr ',' ' '); do
        (cd "$wt" && cargo clean -q -p "$d" --target-dir "${CARGO_TARGET_DIR:-$wt/target}/verus-partial") < /dev/null > "$1.dep-$d.clean-cargo.log" 2>&1 || { echo "cargo clean -p $d failed"; return 1; }
        (cd "$wt/crates/$d" && cargo verus focus -- --output-json) < /dev/null > "$1.dep-$d.json" 2> "$1.dep-$d.log" || true
        mpy depok "$1.dep-$d" "$d" 2>&1 || return 1
    done
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

# worker WT ROWS RES: each row of file ROWS in worktree WT (one, deps and tests read $wt), one `<id> pass|fail <patch blob>`
# line per row appended to RES. run starts each as `mutants.sh worker ..` in its own session (setsid), as its direct child
# (MUTANTS_RUN is run's pid): a setsid that forked would leave run waiting on the wrong pid and killing the wrong group.
worker() {
    [ "$(ps -o sid= -p $$ | tr -d ' ')" = "$$" ] || fail "worker: not a session leader (run starts workers with setsid)"
    [ "$PPID" = "${MUTANTS_RUN:-}" ] || fail "worker: not started by mutants.sh run (parent $PPID, MUTANTS_RUN '${MUTANTS_RUN:-}')"
    wt=$1
    tab=$(printf '\t')
    while IFS=$tab read -r id crate mod fn tst dep rx; do
        t0=$(date +%s)
        git -C "$wt" reset -q --hard HEAD && git -C "$wt" clean -fdq -- crates || fail "cannot reset the worktree $wt"
        why=
        one "$out/$id.clean" "$crate" "$mod" "$fn"
        if ! why=$(mpy clean "$out/$id.clean" "$crate" "$mod" "$fn" 2>&1); then :
        elif ! why=$(tests "$out/$id.clean" "$crate" "$tst" ok); then why="unmutated: $why"
        elif ! why=$(git -C "$wt" apply "$wt/tools/mutants/$id.patch" 2>&1); then why="patch does not apply: $why"
        elif ! why=$(deps "$out/$id" "$dep"); then why="dependency: $why"
        else
            one "$out/$id" "$crate" "$mod" "$fn"
            if ! why=$(mpy killed "$out/$id" "$crate" "$mod" "$fn" "$rx" 2>&1); then :
            elif ! why=$(tests "$out/$id" "$crate" "$tst" FAILED); then why="mutant: $why"
            else why=; fi
        fi
        blob=$(git -C "$wt" rev-parse "HEAD:tools/mutants/$id.patch") || fail "git rev-parse HEAD:tools/mutants/$id.patch failed"
        if [ -z "$why" ]; then
            echo "mutants: $id: killed ($crate $mod::$fn, $(($(date +%s) - t0))s)"
            echo "$id pass $blob" >> "$3"
        else
            echo "mutants: $id: FAILED: $why" >&2
            echo "$id fail $blob" >> "$3"
        fi
    done < "$2"
}

# addwt: one more worktree of $rev in $parent, its path appended to $wts.
addwt() {
    w=$(mktemp -d "$parent/mutants-XXXXXX") || fail "mktemp in $parent failed"
    wts="$wts $w"
    git -C "$root" worktree add -q --detach "$w" "$rev" || fail "git worktree add failed"
}

# stop (run's EXIT trap): a stopped run stops its workers' sessions (TERM, then KILL after 10 s) before their worktrees go,
# else a cargo or Verus still writing in one makes its removal fail.
stop() {
    for p in $pids; do kill -- "-$p" 2> /dev/null || true; done
    for p in $pids; do
        wait "$p" 2> /dev/null || true  # the worker itself; a zombie would keep its group alive below
        i=0
        while kill -0 -- "-$p" 2> /dev/null && [ "$i" -lt 100 ]; do sleep 0.1; i=$((i + 1)); done
        kill -KILL -- "-$p" 2> /dev/null || true
    done
    for w in $wts; do git -C "$root" worktree remove --force "$w" > /dev/null 2>&1 || rmdir "$w" 2> /dev/null || true; done
    git -C "$root" worktree prune || true
}

run() {
    dest=$root/tools/mutants-last-run.txt
    if [ "${1:-}" = --out ]; then
        [ $# -ge 2 ] || fail "run --out needs a FILE"
        dest=$2
        shift 2
    fi
    check > /dev/null
    st=$(git -C "$root" status --porcelain -- crates tools/mutants tools/mutants.tsv tools/mutants.py tools/verus-pin.txt scripts/mutants.sh) || fail "git status failed"
    [ -z "$st" ] || fail "crates/, the registry or the mutants tools have uncommitted changes; the run uses HEAD, so commit first"
    # VERUS_HOME is env-overridable and a missing one falls back to PATH; tools/mutants.py checks each JSON's verus object too
    vv=$(verus --version 2>&1) || fail "verus --version failed (VERUS_HOME=$VERUS_HOME): $vv"
    got=$(printf '%s\n' "$vv" | sed -n 's/^ *Version: //p')
    [ "$got" = "$verus_ver" ] || fail "verus --version names ${got:-no version}, tools/verus-pin.txt says $verus_ver (VERUS_HOME=$VERUS_HOME)"
    jobs=${MUTANTS_JOBS:-4}
    case $jobs in '' | *[!0-9]* | 0*) fail "MUTANTS_JOBS must be a positive integer, not '$jobs'" ;; esac
    # one run per output dir: workers outlive a SIGKILLed run (their own sessions) and would write into the next run's
    # files; they and their cargo and Verus inherit fd 9, so the lock lasts until the last of them exits
    mkdir -p "$out"
    exec 9> "$out/.lock"
    flock -n 9 || fail "another mutants run, or the orphaned workers of a killed one, still holds $out/.lock"
    set +m  # job control off: setsid then never forks, so $! is the worker and its session
    common=$(git -C "$root" rev-parse --path-format=absolute --git-common-dir) || fail "not a git repo"
    parent=$(dirname "$common")/.worktrees
    mkdir -p "$parent"
    rev=$(git -C "$root" rev-parse HEAD) || fail "git rev-parse HEAD failed"
    wts= pids=
    trap stop EXIT
    trap 'exit 1' INT TERM HUP
    # MUTANTS_JOBS workers (default 4), each with its own worktree of one HEAD and its own target dir, take every
    # MUTANTS_JOBS-th row; the mutants are independent, so the run file is the one a single worker writes. The rows come
    # from the first worktree, so they and the patches the workers apply are of one commit.
    addwt
    wt=${wts# }
    rows=$(mpy rows "$wt" "$wt/tools/mutants.tsv" "$wt/tools/mutants") || exit 1
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
    nrows=$(printf '%s\n' "$rows" | wc -l | tr -d ' ')
    [ "$jobs" -le "$nrows" ] || jobs=$nrows
    k=1
    while [ "$k" -lt "$jobs" ]; do
        addwt
        k=$((k + 1))
    done
    # each worktree's own target dir, not a CARGO_TARGET_DIR shared with other worktrees; MUTANTS_TARGET_DIR (gate-demos
    # only) keeps vstd built across the demos' throwaway repos, one subdir per worker (parallel cargo cleans cannot share one)
    unset CARGO_TARGET_DIR
    rm -f "$out"/*.log "$out"/*.json "$out"/shard-*
    crates=$(git -C "$wt" rev-parse HEAD:crates)
    runtree=$(mpy tree "$wt" HEAD) || exit 1
    tsvblob=$(git -C "$wt" rev-parse HEAD:tools/mutants.tsv)
    res="# tools/mutants-last-run.txt: written by scripts/mutants.sh run on $(date -u +%Y-%m-%dT%H:%MZ) under Verus $verus_ver; verify.sh's main gate reads it
crates $crates
tree $runtree
tsv $tsvblob"
    k=0 resf=
    printf '%s\n' "$rows" > "$out/shard-all.rows"
    export MUTANTS_RUN=$$
    for w in $wts; do
        awk -v j="$jobs" -v k="$k" '(NR - 1) % j == k' "$out/shard-all.rows" > "$out/shard-$k.rows"
        : > "$out/shard-$k.res"
        resf="$resf $out/shard-$k.res"
        # its own session, so the trap's kill of the group reaches the worker's cargo and Verus too
        if [ -n "${MUTANTS_TARGET_DIR:-}" ]; then
            CARGO_TARGET_DIR="$MUTANTS_TARGET_DIR/w$k" setsid "$root/scripts/mutants.sh" worker "$w" "$out/shard-$k.rows" "$out/shard-$k.res" &
        else
            setsid "$root/scripts/mutants.sh" worker "$w" "$out/shard-$k.rows" "$out/shard-$k.res" &
        fi
        pids="$pids $!"
        k=$((k + 1))
    done
    dead=0
    for p in $pids; do wait "$p" || dead=$((dead + 1)); done
    # a dead worker's group may still hold its cargo or Verus: the trap kills it. Live ones exited after their last row.
    [ "$dead" -eq 0 ] || fail "$dead of $jobs mutant workers died (logs in $out)"
    pids=
    # the run file lists the rows in registry order, whichever worker ran them
    # shellcheck disable=SC2086 # one path per word
    lines=$(mpy assemble "$out/shard-all.rows" $resf) || exit 1
    bad=$(printf '%s\n' "$lines" | awk '$2 != "pass"' | wc -l | tr -d ' ')
    res="$res
$lines"
    if [ "$full" -eq 1 ]; then
        printf '%s\n' "$res" > "$dest" || fail "cannot write $dest"
        echo "mutants: wrote ${dest#"$root"/} (crates tree $crates)"
    fi
    [ "$bad" -eq 0 ] || fail "$bad mutants not killed (logs in $out)"
    echo "mutants: run ok ($(printf '%s\n' "$rows" | wc -l | tr -d ' ') mutants killed)"
}

verify() {
    check
    head=$(git -C "$root" rev-parse HEAD) || fail "git rev-parse HEAD failed"
    # main's tip (checked out as main, or detached as in a CI checkout). Merges to main are --no-ff only; whatever else
    # lands at main's tip is gated all the same. No main is a failure, not a skipped gate.
    main=$(git -C "$root" rev-parse -q --verify refs/heads/main) || fail "cannot resolve main (refs/heads/main): the gate cannot tell whether HEAD is main's tip"
    if [ "$head" = "$main" ]; then
        mpy gate "$root" || exit 1
        # the gate only reads text that git alone can produce (audit F4): at main's tip every mutant is run again
        fresh=$out/mutants-fresh.txt
        rm -f "$fresh"
        run --out "$fresh"
        git -C "$root" show HEAD:tools/mutants-last-run.txt > "$out/mutants-committed.txt" || fail "git show HEAD:tools/mutants-last-run.txt failed"
        mpy same "$out/mutants-committed.txt" "$fresh" || exit 1
        echo "mutants: fresh run at main's tip matches the committed run file ($(awk '$2 == "pass"' "$fresh" | wc -l | tr -d ' ') mutants)"
    else
        mpy gate-branch "$root" || exit 1  # a stale run file shows before the merge, not after
    fi
}

# One braced block, parsed whole before it runs: sh reads a script as it goes, so an edit to this file during a long
# run would otherwise be executed from the middle (seen in the first full run).
{
    case ${1:-} in
    check) check ;;
    run) shift; run "$@" ;;
    worker) [ $# -eq 4 ] || fail "usage: mutants.sh worker WT ROWS RES (run's own)"; shift; worker "$@" ;;
    verify) verify ;;
    *) fail "usage: mutants.sh check | run [--out FILE] [id..] | verify" ;;
    esac
    exit
}
