#!/bin/sh
set -eu
set -o pipefail
# test-gate.sh DIR LOG [CARGO TEST ARGS..]: `cargo test --locked -q` in DIR (verify.sh passes
# --workspace for the repo root), output in LOG, shown on failure. A build failure, a failing test
# or a run that passed no test at all is a failure. --workspace also holds each crate to DIR/tools/test-floor.txt (CRATE COUNT):
# fewer passed tests than the floor, a crate with tests and no floor line, or a line naming no crate fails (the file itself only
# grows: scripts/test-floor.sh).
[ $# -ge 2 ] || { echo "usage: test-gate.sh DIR LOG [cargo test args..]" >&2; exit 1; }
dir=$1 log=$2
shift 2
fail() { echo "test-gate: $*" >&2; exit 1; }
required="server"  # crates that must pass a test whatever they hold (crates/server's tests are its only guard)
is_required() { for r in $required; do [ "$r" != "$1" ] || return 0; done; return 1; }
[ -d "$dir" ] || fail "no directory $dir"
# --workspace is run one member at a time, so each member's passed count is its own: a member with a tests/ dir or a
# #[test], and every crate in $required, must pass at least one test (crates/server's tests are its only guard and cannot vanish behind the others').
if [ "${1-}" = --workspace ] && [ $# -eq 1 ] && [ -d "$dir/crates" ]; then
    : > "$log"
    total=0
    floor=$dir/tools/test-floor.txt
    [ -s "$floor" ] || fail "$floor is missing or empty"
    seen=
    for r in $required; do [ -f "$dir/crates/$r/Cargo.toml" ] || fail "required-tests crate $r is missing"; done
    for m in "$dir"/crates/*/; do
        [ -f "$m/Cargo.toml" ] || continue
        name=$(basename "$m")
        (cd "$dir" && cargo test --locked -q -p "$name" > "$log.m" 2>&1) || { cat "$log.m"; fail "cargo test -p $name failed"; }
        cat "$log.m" >> "$log"
        n=$(sed -n 's/^test result: ok\. \([0-9][0-9]*\) passed.*/\1/p' "$log.m" | awk '{ s += $1 } END { print s + 0 }')
        has=$(grep -rl --include='*.rs' '#\[test\]' "$m" || [ $? -eq 1 ])
        if [ -d "$m/tests" ] || [ -n "$has" ] || is_required "$name"; then
            [ "$n" -gt 0 ] || { cat "$log.m"; fail "crate $name has tests but passed no test"; }
        fi
        f=$(awk -v c="$name" '$1 == c { print $2 }' "$floor")
        case $f in *[!0-9]*) fail "$floor has a bad or duplicate line for $name" ;; esac
        if [ -n "$f" ]; then
            [ "$n" -ge "$f" ] || { cat "$log.m"; fail "crate $name passed $n tests, below its floor $f in tools/test-floor.txt"; }
        elif [ "$n" -gt 0 ] || [ -d "$m/tests" ] || [ -n "$has" ]; then
            fail "crate $name has tests but no line in tools/test-floor.txt"
        fi
        echo "test-gate: $name $n"
        seen="$seen $name"
        total=$((total + n))
    done
    for c in $(awk '!/^#/ && NF { print $1 }' "$floor"); do
        case " $seen " in *" $c "*) ;; *) fail "tools/test-floor.txt names $c, which is not a crate under crates/" ;; esac
    done
    rm -f "$log.m"
    [ "$total" -gt 0 ] || fail "cargo test passed no test"
    echo "test-gate: $total tests passed"
    exit 0
fi
(cd "$dir" && cargo test --locked -q "$@" > "$log" 2>&1) || { cat "$log"; fail "cargo test failed"; }
n=$(sed -n 's/^test result: ok\. \([0-9][0-9]*\) passed.*/\1/p' "$log" | awk '{ s += $1 } END { print s + 0 }')
[ "$n" -gt 0 ] || { cat "$log"; fail "cargo test passed no test"; }
echo "test-gate: $n tests passed"
