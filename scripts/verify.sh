#!/bin/sh
set -e
VERUS_HOME="${VERUS_HOME:-$HOME/.local/opt/verus/0.2026.10.04.426d8b0/verus-x86-linux}"
PATH="$VERUS_HOME:$PATH"
root=$(cd "$(dirname "$0")/.." && pwd)
for c in "$root"/crates/*/; do
    (cd "$c" && cargo verus verify)
done
