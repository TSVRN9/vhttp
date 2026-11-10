#!/bin/sh
set -eu
set -o pipefail
# requirements.sh ROOT: every row of docs/requirements.md's RFC tables has a Status (tools/requirements.py check): proved:
# names resolve to a verified fn with an ensures, tested: names to #[test] fns and come with an open: owner, false (ID) is
# an open TRUSTED.md carryover with its owner, open: names an unmerged roadmap phase with a req- carryover row, and a ticked
# row is proved: alone.
root=${1:?root}
python3 -I "$(cd "$(dirname "$0")/../tools" && pwd)/requirements.py" check "$root"
