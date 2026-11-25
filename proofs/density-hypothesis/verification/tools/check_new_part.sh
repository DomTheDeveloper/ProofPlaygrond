#!/usr/bin/env bash
# Checks that need no build of the Riemann Hypothesis proof: the part of this project that rests on
# Mathlib alone (the implication RH => Density Hypothesis, and the unconditional zero count).
#
#   check_new_part.sh <project-dir> <rh-checkout> <out-dir-of-build_437.sh> <results-dir>
#
# `lean`, `lake`, `leanexport`, `leanchecker`, `con-leche`, `con-ron` must be the v4.37.0-rc1 ones
# (PATH), and `bwrap` (bubblewrap) must be installed: `lake comparator` refuses to run without it.
set -uo pipefail
PROJ=$(realpath "$1"); RH=$(realpath "$2"); OUT=$(realpath "$3"); RES=$(realpath -m "$4")
TOOLS="$PROJ/verification/tools"
mkdir -p "$RES"
# Mathlib and its dependencies only: the RH proof's own modules are not on this search path
BASE=$(cd "$RH" && lake env printenv LEAN_PATH | tr ':' '\n' | grep -v "^$RH/.lake/build" | paste -sd:)
L="$OUT/lib/DensityHypothesis"; C="$OUT/catalog"; fail=0

{
echo "## Challenge.lean vs the library (Defs + Main)"
lean --run "$TOOLS/Compare.lean" "$OUT/challenge/Challenge.olean" "$L/Defs.olean,$L/Main.olean" || fail=1
echo
echo "## comparator/CatalogChallenge.lean vs the catalog's unmodified files compiled in this toolchain"
lean --run "$TOOLS/Compare.lean" "$OUT/challenge/CatalogChallenge.olean" \
  "$C/FormalConjecturesForMathlib/NumberTheory/RiemannZetaZeros.olean,$C/FormalConjectures/Wikipedia/DensityHypothesis.olean" || fail=1
echo
echo "## the catalog's unmodified files vs the library (Defs + Unconditional)"
lean --run "$TOOLS/Compare.lean" \
  "$C/FormalConjecturesForMathlib/NumberTheory/RiemannZetaZeros.olean,$C/FormalConjectures/Wikipedia/DensityHypothesis.olean" \
  "$L/Defs.olean,$L/Unconditional.olean" || fail=1
} > "$RES/statement-comparison.txt" 2>&1
echo "statement comparison: $([ $fail = 0 ] && echo identical || echo MISMATCH) (see statement-comparison.txt)"

W=$(mktemp -d)
LEAN_PATH="$OUT/challenge:$BASE" leanexport Challenge -- $(cat "$PROJ/export-targets.txt") > "$W/challenge.export" || fail=1
LEAN_PATH="$OUT/lib:$BASE" leanexport Solution -- $(cat "$PROJ/export-targets.txt") > "$W/solution.export" || fail=1
(cd "$W" && sha256sum challenge.export solution.export && wc -c challenge.export solution.export) > "$RES/exports.txt"

mkdir -p "$W/run" && cp "$PROJ/comparator.json" "$W/run/"
(cd "$W/run" && lake comparator --config comparator.json \
   --challenge-from-export ../challenge.export --solution-from-export ../solution.export) > "$RES/lake-comparator.txt" 2>&1
rc=$?; echo "exit code $rc" >> "$RES/lake-comparator.txt"; [ $rc = 0 ] || fail=1
echo "lake comparator: exit $rc"

for k in con-leche con-ron; do
  $k --jobs=2 "$W/solution.export" > "$RES/$k.txt" 2>&1
  rc=$?; echo "exit code $rc" >> "$RES/$k.txt"; [ $rc = 0 ] || fail=1
  echo "$k: exit $rc: $(grep -m1 accepted "$RES/$k.txt")"
done

LEAN_PATH="$OUT/lib:$BASE" leanchecker DensityHypothesis.Defs DensityHypothesis.ZeroCount DensityHypothesis.Main > "$RES/leanchecker.txt" 2>&1
rc=$?; echo "exit code $rc" >> "$RES/leanchecker.txt"; [ $rc = 0 ] || fail=1
echo "leanchecker: exit $rc"
rm -rf "$W"
exit $fail
