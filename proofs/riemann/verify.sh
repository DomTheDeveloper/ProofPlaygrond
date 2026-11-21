#!/usr/bin/env bash
set -euo pipefail

source_root="$(cd -- "$(dirname -- "$0")" && pwd)"
archive="$(realpath "${1:?Pass the pinned archive checkout with Mathlib installed}")"
objects="$(realpath "${2:?Pass the directory containing the compiled archive modules}")"
mode="${4:-both}"
case "$mode" in
  compile|replay|both) ;;
  *) echo "Choose compile, replay or both." >&2; exit 2 ;;
esac

if [[ -n "${3:-}" ]]; then
  mkdir -p -- "$3"
  output="$(realpath "$3")"
else
  output="$(mktemp -d)"
  trap 'rm -rf -- "$output"' EXIT
fi

cd "$archive"
bin="$(lake env lean --print-prefix)/bin"
export PATH="$bin:$PATH"
"$bin/lean" --version | grep -F 'version 4.33.1,'
deps="$(lake env printenv LEAN_PATH)"
export LEAN_PATH="$output:$objects:$deps"
export LEAN_ABORT_ON_PANIC=1

if [[ "$mode" != replay ]]; then
  "$bin/lean" -j2 --trust=0 --tstack=400000 -DwarningAsError=true \
    -DmaxHeartbeats=4000000 -DautoImplicit=false -DrelaxedAutoImplicit=false \
    -DmaxSynthPendingDepth=3 --root="$source_root" \
    -o "$output/CompactRH.olean" -i "$output/CompactRH.ilean" "$source_root/CompactRH.lean"
fi
if [[ "$mode" != compile ]]; then
  "$bin/leanchecker" -v CompactRH
fi
