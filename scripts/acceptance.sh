#!/bin/sh
set -eu
set -o pipefail
# acceptance.sh [--root DIR] [--baseline FILE]: the error-path acceptance ratchet. Every error-returning
# exec fn inside verus! must carry an `allowed_` clause in its ensures or be listed in
# tools/acceptance-baseline.txt, which only shrinks. See tools/acceptance.py for the parser's limits.
exec python3 -I "$(dirname "$0")/../tools/acceptance.py" "$@"
