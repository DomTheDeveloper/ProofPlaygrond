#!/usr/bin/env bash
# usage: build.sh <lean-bin-dir> <lake-workspace-for-LEAN_PATH> <src-root> <out-dir> <module>...
set -uo pipefail
LEANBIN=$1; WS=$2; SRC=$3; OUT=$4; shift 4
export PATH="$LEANBIN:$PATH"
BASE_LEAN_PATH=$(cd "$WS" && lake env printenv LEAN_PATH)
export LEAN_PATH="$OUT:$BASE_LEAN_PATH"
rc=0
for m in "$@"; do
  rel=$(echo "$m" | tr . /)
  mkdir -p "$(dirname "$OUT/$rel")"
  echo "=== $m"
  start=$(date +%s)
  lean ${LEAN_EXTRA_ARGS:-} --root="$SRC" -o "$OUT/$rel.olean" -i "$OUT/$rel.ilean" "$SRC/$rel.lean" 2>&1 | head -${MAXLINES:-120}
  r=${PIPESTATUS[0]}
  echo "--- exit $r ($(( $(date +%s) - start ))s)"
  if [ "$r" -ne 0 ]; then rc=$r; break; fi
done
exit $rc
