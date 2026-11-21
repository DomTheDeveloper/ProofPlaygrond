#!/usr/bin/env bash
set -euo pipefail

source_root="$(cd -- "$(dirname -- "$0")" && pwd)"
archive="$(realpath "${1:?Pass the pinned archive checkout with Mathlib installed}")"
objects="$(realpath "${2:?Pass the directory containing the compiled modules from the archive}")"
scratch_root="$(mktemp -d)"
trap 'rm -rf -- "$scratch_root"' EXIT
cd "$archive"
bin="$(lake env lean --print-prefix)/bin"
export PATH="$bin:$PATH"
"$bin/lean" --version | grep -F 'version 4.33.1,'
deps="$(lake env printenv LEAN_PATH)"
export LEAN_PATH="$scratch_root:$objects:$deps"
export LEAN_ABORT_ON_PANIC=1
for module in PrincipalWindows OrdinaryRH; do
  "$bin/lean" -j2 --trust=0 --tstack=400000 -DwarningAsError=true \
    -DmaxHeartbeats=4000000 -DautoImplicit=false -DrelaxedAutoImplicit=false \
    -DmaxSynthPendingDepth=3 --root="$source_root" \
    -o "$scratch_root/$module.olean" "$source_root/$module.lean"
  "$bin/leanchecker" -v "$module"
done
