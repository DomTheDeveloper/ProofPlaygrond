#!/usr/bin/env bash
set -euo pipefail

# Run from the pinned repository root using "lake env bash /path/to/replay.sh".
bundle=$(cd "$(dirname "$0")" && pwd -P)
target=FormalConjectures/OEIS/86766.lean
expected_blob=33fcfc5183a380f0137a343d5a19ccd6b0404651
[[ "$(git hash-object "$target")" == "$expected_blob" ]] || {
  echo 'Upstream problem file differs from the audited revision.' >&2
  exit 1
}
build=$(mktemp -d)
trap 'rm -rf -- "$build"' EXIT
cp "$bundle/FiroozbakhtCounterexample.lean" "$bundle/CheckDeepMind.lean" "$build/"
IFS=: read -r -a entries <<< "$LEAN_PATH"
absolute=()
for entry in "${entries[@]}"; do
  case "$entry" in
    /*) absolute+=("$entry") ;;
    *) absolute+=("$PWD/${entry:-.}") ;;
  esac
done
export LEAN_PATH="$build:$(IFS=:; echo "${absolute[*]}")"
cd "$build"
lean --version
for module in FiroozbakhtCounterexample CheckDeepMind; do
  lean -j1 -DwarningAsError=true -o "$module.olean" "$module.lean"
done
leanchecker -v FiroozbakhtCounterexample CheckDeepMind
