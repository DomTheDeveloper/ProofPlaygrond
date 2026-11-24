#!/usr/bin/env python3
"""Regenerate InSitu.lean from DensityHypothesis/ZeroCount.lean.

InSitu.lean is the proof text of DensityHypothesis/ZeroCount.lean, unchanged except that its
import lines are replaced by a single import of the unmodified catalog module
`FormalConjectures.Wikipedia.DensityHypothesis`. It is meant to be compiled inside a checkout of
google-deepmind/formal-conjectures (see README.md).

usage: make_insitu.py <path to ZeroCount.lean> <output path>
"""
import pathlib
import sys

proof_path, out_path = sys.argv[1:3]
lines = pathlib.Path(proof_path).read_text(encoding="utf-8").splitlines()
body = "\n".join(line for line in lines if not line.startswith("import "))
# formal-conjectures' style linter allows one module docstring per file; the generated header
# below is that one, so the proof's own `/-! ... -/` blocks become ordinary comments.
body = body.replace("/-!", "/-")

HEADER = """import FormalConjectures.Wikipedia.DensityHypothesis

/-!
GENERATED FILE: do not edit. Produced by `make_insitu.py` from `DensityHypothesis/ZeroCount.lean`.
Compile it inside a checkout of google-deepmind/formal-conjectures; see `README.md`.
-/
"""

FOOTER = """
namespace DensityHypothesis

/-- The catalog statement `DensityHypothesis.density_hypothesis_zeta_zeros`, from the Riemann
Hypothesis. Its type is taken from the catalog theorem itself by `type_of%`. -/
theorem density_hypothesis_zeta_zeros_of_riemannHypothesis (hRH : RiemannHypothesis) :
    type_of% @density_hypothesis_zeta_zeros :=
  fun ε hε => DensityHypothesisProof.density_hypothesis_of_riemannHypothesis hRH ε hε

/-- The catalog statement `DensityHypothesis.guth_maynard_zero_density`, from the Riemann
Hypothesis. Its type is taken from the catalog theorem itself by `type_of%`. -/
theorem guth_maynard_zero_density_of_riemannHypothesis (hRH : RiemannHypothesis) :
    type_of% @guth_maynard_zero_density :=
  fun ε hε => DensityHypothesisProof.guth_maynard_zero_density_of_riemannHypothesis hRH ε hε

end DensityHypothesis

#print axioms DensityHypothesis.density_hypothesis_zeta_zeros_of_riemannHypothesis
#print axioms DensityHypothesis.guth_maynard_zero_density_of_riemannHypothesis
#print axioms DensityHypothesisProof.zeroCountOn_strip_le_mul_log
"""

pathlib.Path(out_path).write_text(HEADER + body.lstrip("\n") + "\n" + FOOTER, encoding="utf-8")
print(f"wrote {out_path}")
