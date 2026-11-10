#!/bin/sh
set -eu
set -o pipefail
# interop.sh ROOT: runs crates/server/tests/interop.rs's ignored tests for each external HTTP/3 client that is present, with
# INTEROP_STRICT=1, and requires `test NAME ... ok`. curl is present when `curl --version` lists HTTP3; quiche when $QUICHE_CLIENT
# is set, else <main checkout>/.worktrees/ext-quiche/src/target/release/quiche-client is executable. An absent client is said so.
root=${1:?root}
die() { echo "interop: $*" >&2; exit 1; }
[ -f "$root/crates/server/tests/interop.rs" ] || die "no crates/server/tests/interop.rs under $root"
qs="skipped (no client)"
cs="skipped (no HTTP3)"
if curl --version 2>/dev/null | grep -q HTTP3; then cs=ok; fi
q=${QUICHE_CLIENT:-}
if [ -z "$q" ]; then
    gc=$(git -C "$root" rev-parse --path-format=absolute --git-common-dir) || die "cannot find the git common dir of $root"
    q=$(dirname "$gc")/.worktrees/ext-quiche/src/target/release/quiche-client
    [ -x "$q" ] || q=
fi
[ -z "$q" ] || [ -x "$q" ] || die "QUICHE_CLIENT $q is not executable"
[ -z "$q" ] || qs=ok
run() { # run NAME: the test must print `test NAME ... ok`
    out=$(cd "$root" && INTEROP_STRICT=1 QUICHE_CLIENT=$q cargo test --locked -p server --test interop -- --ignored --exact "$1" 2>&1) || { printf '%s\n' "$out" >&2; die "$1 failed"; }
    printf '%s\n' "$out" | grep -q "^test $1 \.\.\. ok" || { printf '%s\n' "$out" >&2; die "$1 did not print ok"; }
}
[ "$cs" != ok ] || { run curl_fetches; run curl_two_requests; }
[ "$qs" != ok ] || run quiche_fetches
echo "interop: curl $cs, quiche $qs"
