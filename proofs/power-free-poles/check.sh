#!/usr/bin/env bash
set -euo pipefail

project=$(cd "${1:?Pass the pinned compact RH project or Mathlib project directory}" && pwd)
src=$(cd "$(dirname "$0")" && pwd)
mode=${2:-full}
output=$(mktemp -d)
trap 'rm -rf -- "$output"' EXIT
cd "$project"
case "$mode" in
  full)
    export POWERFREE_RH_OLEAN="$project/.lake/build/lib/lean/Main.olean"
    if [[ ! -f "$POWERFREE_RH_OLEAN" ]]; then lake exe cache get; fi
    lake build +Main
    ;;
  --interface-only)
    export POWERFREE_RH_OLEAN="$src/verification/upstream/Main.olean"
    python3 - "$POWERFREE_RH_OLEAN" <<'PY'
import hashlib
import pathlib
import sys
path = pathlib.Path(sys.argv[1])
expected = '0fa731cf77514371b6bed2b575e126fd95bb3e2229e10bfbc77756e7460ccf89'
if hashlib.sha256(path.read_bytes()).hexdigest() != expected:
    raise SystemExit('Unexpected upstream Main.olean SHA-256')
PY
    ;;
  *) echo 'Choose full or --interface-only' >&2; exit 2 ;;
esac
lake env bash -euc '
  src=$1
  output=$2
  mode=$3
  export LEAN_PATH="$output:${LEAN_PATH:-}"
  cd "$src"
  for mod in PoleDescent FreePoles PowerFreeCounting PowerFreeGlobal; do
    lean -R "$src" -o "$output/$mod.olean" "$src/$mod.lean"
  done
  lean -R "$src/verification" -o "$output/DeclaredTargets.olean" "$src/verification/DeclaredTargets.lean"
  lean -R "$src/verification" "$src/verification/PoleAudit.lean"
  if [[ "$mode" == full ]]; then
    for mod in PowerFreePoles PowerFreeResidues; do
      lean -R "$src" -o "$output/$mod.olean" "$src/$mod.lean"
    done
    lean -R "$src" "$src/Audit.lean"
  fi
  lean -R "$src/examples" -o "$output/PowerFreeSieve.olean" "$src/examples/PowerFreeSieve.lean"
  lean -R "$src/examples" "$src/examples/SieveChecks.lean"
' bash "$src" "$output" "$mode"
