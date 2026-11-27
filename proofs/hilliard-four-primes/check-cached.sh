#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
ulimit -s unlimited

# setup.sh supplies the pinned original sources and their Mathlib dependencies.
proof_dir=$PWD
temporary=$(mktemp -d)
trap 'rm -rf -- "$temporary"' EXIT
cache_checkout="$temporary/cache-source"
cache_commit=5ba920829cb7286b51f4d233b493f5b1287bf51b

from_source() {
  echo "$1. Compiling the pinned original sources." >&2
  lake build --fail-fast
  lake env lean Hilliard.lean
}

git init -q "$cache_checkout"
if ! git -C "$cache_checkout" fetch -q --depth=1 \
    https://github.com/leanprover-community/riemann-hypothesis.git "$cache_commit"; then
  from_source "RH cache metadata is unavailable"
  exit 0
fi
git -C "$cache_checkout" checkout -q --detach "$cache_commit"
rh_project="$cache_checkout/grh-compact"
published_tree=$(git -C "$cache_checkout" rev-parse 'HEAD:grh-compact/src')
pinned_tree=$(git -C .lake/packages/grh-lean rev-parse 'HEAD:grh-compact/src')
if [[ "$published_tree" != "$pinned_tree" ]]; then
  echo "The published RH sources differ from the pinned source tree." >&2
  exit 1
fi
cmp lean-toolchain "$rh_project/lean-toolchain"

mkdir -p "$rh_project/.lake"
ln -s "$proof_dir/.lake/packages" "$rh_project/.lake/packages"
echo "Verifying the published modules for RH source tree $published_tree"
cache_status=0
python3 "$rh_project/scripts/ci-cache-get.py" --project "$rh_project" --jobs 4 || cache_status=$?
case "$cache_status" in
  0) ;;
  3) from_source "There is no published record for these sources"; exit 0 ;;
  *) exit "$cache_status" ;;
esac

# Compile the application and the Schoenfeld library against the pinned Mathlib.
lake build --fail-fast +CubeProof:olean @SchoenfeldRH/+SchoenfeldRH.Main:olean
output_dir="$temporary/application"
mkdir -p "$output_dir"
project_paths=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$output_dir:$rh_project/.lake/build/lib/lean:$project_paths"
lean_bin=$(elan which lean)
"$lean_bin" -o "$output_dir/BoundSolution.olean" BoundSolution.lean
"$lean_bin" -o "$output_dir/Hilliard.olean" Hilliard.lean
