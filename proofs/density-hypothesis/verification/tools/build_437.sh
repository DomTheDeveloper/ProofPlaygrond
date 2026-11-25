#!/usr/bin/env bash
# Compile everything of this project that lives in the toolchain of the Riemann Hypothesis proof
# (Lean v4.37.0-rc1, Mathlib 31ce06e), with plain `lean`, from the files of this repository.
#
#   build_437.sh <project-dir> <rh-checkout> <catalog-checkout> <out-dir>
#
#   <project-dir>       proofs/density-hypothesis of this repository
#   <rh-checkout>       leanprover-community/riemann-hypothesis with Mathlib's cache fetched and the
#                       public parts of its own modules restored in .lake/build/lib/lean (pass 1)
#   <catalog-checkout>  google-deepmind/formal-conjectures at 9097e2f (only four source files are read)
#   <out-dir>           receives lib/ (the library), challenge/ (the statement-only files) and
#                       catalog/ (the catalog's files and InSituUnconditional)
#
# `lean` must be the v4.37.0-rc1 binary (PATH). Nothing is written outside <out-dir>.
set -euo pipefail
PROJ=$(realpath "$1"); RH=$(realpath "$2"); FC=$(realpath "$3"); OUT=$(realpath -m "$4")
TOOLS="$PROJ/verification/tools"
BASE_LEAN_PATH=$(cd "$RH" && lake env printenv LEAN_PATH)
RHLIB="$RH/.lake/build/lib/lean"
mkdir -p "$OUT/lib" "$OUT/challenge" "$OUT/catalog" "$OUT/src-catalog"

compile() {   # compile <src-root> <out-root> <module> [extra lean args...]
  local src=$1 out=$2 mod=$3; shift 3
  local rel=${mod//./\/}
  mkdir -p "$(dirname "$out/$rel")"
  lean "$@" --root="$src" -o "$out/$rel.olean" -i "$out/$rel.ilean" "$src/$rel.lean"
  echo "built $mod"
}
compile_setup() {   # compile_setup <src-file> <out-root> <module>: only public parts of the RH modules are loaded
  local file=$1 out=$2 mod=$3
  local rel=${mod//./\/}
  mkdir -p "$(dirname "$out/$rel")"
  python3 -I "$TOOLS/mksetup.py" "$mod" "$RHLIB" "$OUT/rh_modules.tsv" "$OUT/setup_$mod.json" > /dev/null
  lean --setup="$OUT/setup_$mod.json" -o "$out/$rel.olean" -i "$out/$rel.ilean" "$file"
  echo "built $mod (against the compiled Riemann Hypothesis proof)"
}

# every module of the RH build that has a public .olean on disk
(cd "$RHLIB" && find . -name '*.olean' | sed 's|^\./||; s|\.olean$||; s|/|.|g' | sort) > "$OUT/rh_modules.tsv"
echo "$(wc -l < "$OUT/rh_modules.tsv") modules of the Riemann Hypothesis build found"

# 1. the library and the solution module
export LEAN_PATH="$OUT/lib:$BASE_LEAN_PATH"
for m in DensityHypothesis.Defs DensityHypothesis.ZeroCount DensityHypothesis.Main DensityHypothesis Solution; do
  compile "$PROJ" "$OUT/lib" "$m" -DautoImplicit=false
done
# 2. the unconditional theorem
compile_setup "$PROJ/DensityHypothesis/Unconditional.lean" "$OUT/lib" DensityHypothesis.Unconditional

# 3. the statement-only files (they declare the same names as the library: separate directory)
export LEAN_PATH="$OUT/challenge:$BASE_LEAN_PATH"
compile "$PROJ" "$OUT/challenge" Challenge -DautoImplicit=false
cp "$PROJ/comparator/CatalogChallenge.lean" "$OUT/src-catalog/CatalogChallenge.lean"
compile "$OUT/src-catalog" "$OUT/challenge" CatalogChallenge -DautoImplicit=false

# 4. the catalog's own files, unmodified, plus the reduced aggregator, and the in-situ proof
S="$OUT/src-catalog"
mkdir -p "$S/FormalConjecturesUtil/Attributes" "$S/FormalConjecturesForMathlib/NumberTheory" "$S/FormalConjectures/Wikipedia"
cp "$FC/FormalConjecturesUtil/Attributes/AMS.lean" "$FC/FormalConjecturesUtil/Attributes/Basic.lean" "$S/FormalConjecturesUtil/Attributes/"
cp "$FC/FormalConjecturesForMathlib/NumberTheory/RiemannZetaZeros.lean" "$S/FormalConjecturesForMathlib/NumberTheory/"
cp "$FC/FormalConjectures/Wikipedia/DensityHypothesis.lean" "$S/FormalConjectures/Wikipedia/"
cp "$PROJ/verification/catalog-in-rh-toolchain/FormalConjecturesUtil.lean" "$S/FormalConjecturesUtil.lean"
export LEAN_PATH="$OUT/catalog:$BASE_LEAN_PATH"
for m in FormalConjecturesUtil.Attributes.AMS FormalConjecturesUtil.Attributes.Basic \
         FormalConjecturesForMathlib.NumberTheory.RiemannZetaZeros FormalConjecturesUtil \
         FormalConjectures.Wikipedia.DensityHypothesis; do
  compile "$S" "$OUT/catalog" "$m" -DautoImplicit=false
done
compile_setup "$PROJ/InSituUnconditional.lean" "$OUT/catalog" InSituUnconditional

(cd "$OUT" && find lib challenge catalog -name '*.olean*' | sort | xargs sha256sum) > "$OUT/olean.sha256"
echo "done: $(wc -l < "$OUT/olean.sha256") compiled files listed in $OUT/olean.sha256"
