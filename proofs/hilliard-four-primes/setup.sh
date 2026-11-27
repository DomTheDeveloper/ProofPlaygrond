#!/bin/bash
# Fetches the two dependencies into .lake/packages, each at a pinned commit and unmodified, then the Mathlib cache:
#   - https://github.com/lsernau/grh-lean (the Lean proof of RH and of GRH for Dirichlet L-functions)
#   - https://github.com/AndrewVSutherland/schoenfeld-rh-lean (Schoenfeld's bound is equivalent to RH)
set -euo pipefail
cd "$(dirname "$0")"
fetch() {  # name url commit
  [ -d ".lake/packages/$1" ] || git clone "$2" ".lake/packages/$1"
  git -C ".lake/packages/$1" checkout --quiet "$3"
  test "$(git -C ".lake/packages/$1" rev-parse HEAD)" = "$3"
  test -z "$(git -C ".lake/packages/$1" status --porcelain)"
}
mkdir -p .lake/packages
fetch grh-lean https://github.com/lsernau/grh-lean 72fead102f663d5c7a407964a13dc0cf9d977207
fetch schoenfeld-rh-lean https://github.com/AndrewVSutherland/schoenfeld-rh-lean 0e52d7b1a83fb548f6395546828a923a2e3d9627
lake exe cache get
echo "Dependencies ready. Run lake build."
