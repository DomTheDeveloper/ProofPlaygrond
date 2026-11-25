#!/usr/bin/env python3
"""Regenerate InSitu.lean from DensityHypothesis/ZeroCount.lean.

InSitu.lean is the proof text of DensityHypothesis/ZeroCount.lean with three mechanical changes:
its import lines are replaced by a single `public import` of the unmodified catalog module
`FormalConjectures.Wikipedia.DensityHypothesis`; a generated header is put in front; and its
`/-! ... -/` section comments become ordinary `/- ... -/` comments (the catalog's linter allows
one module docstring per file). Two theorems whose types are taken from the catalog by `type_of%`
are appended. Like the catalog's files it is a `module`. It is meant to be compiled inside a
checkout of google-deepmind/formal-conjectures (see README.md).

With `--unconditional` the generated file additionally imports `Main` of
leanprover-community/riemann-hypothesis and proves the two catalog statements with no hypothesis;
that file can only be compiled where both the catalog's statement file and a build of the Riemann
Hypothesis proof are available (see `verification/README.md`).

usage: make_insitu.py <path to ZeroCount.lean> <output path> [--unconditional]
"""
import pathlib
import sys

proof_path, out_path = sys.argv[1:3]
unconditional = "--unconditional" in sys.argv[3:]
lines = pathlib.Path(proof_path).read_text(encoding="utf-8").splitlines()
assert lines[0] == "module", "ZeroCount.lean is expected to be a `module`"
body = "\n".join(line for line in lines[1:] if not line.startswith(("import ", "public import ")))
# formal-conjectures' style linter allows one module docstring per file; the generated header
# below is that one, so the proof's own `/-! ... -/` blocks become ordinary comments.
body = body.replace("/-!", "/-")

HEADER = """module

public import FormalConjectures.Wikipedia.DensityHypothesis

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

HEADER_UNCONDITIONAL = """module

public import FormalConjectures.Wikipedia.DensityHypothesis
import Main

/-!
GENERATED FILE: do not edit. Produced by `make_insitu.py --unconditional` from
`DensityHypothesis/ZeroCount.lean`. `Main` is the module of
leanprover-community/riemann-hypothesis that contains `riemannHypothesis`.
-/
"""

FOOTER_UNCONDITIONAL = """
namespace DensityHypothesis

/-- The catalog statement `DensityHypothesis.density_hypothesis_zeta_zeros`, with no hypothesis.
Its type is taken from the catalog theorem itself by `type_of%`. -/
theorem density_hypothesis_zeta_zeros_proved : type_of% @density_hypothesis_zeta_zeros :=
  fun ε hε => DensityHypothesisProof.density_hypothesis_of_riemannHypothesis riemannHypothesis ε hε

/-- The catalog statement `DensityHypothesis.guth_maynard_zero_density`, with no hypothesis, as a
corollary of the Riemann Hypothesis. Its type is taken from the catalog theorem by `type_of%`. -/
theorem guth_maynard_zero_density_proved : type_of% @guth_maynard_zero_density :=
  fun ε hε =>
    DensityHypothesisProof.guth_maynard_zero_density_of_riemannHypothesis riemannHypothesis ε hε

end DensityHypothesis

#print axioms DensityHypothesis.density_hypothesis_zeta_zeros_proved
#print axioms DensityHypothesis.guth_maynard_zero_density_proved
#check @DensityHypothesis.density_hypothesis_zeta_zeros_proved
"""

if unconditional:
    HEADER, FOOTER = HEADER_UNCONDITIONAL, FOOTER_UNCONDITIONAL
pathlib.Path(out_path).write_text(HEADER + body.lstrip("\n") + "\n" + FOOTER, encoding="utf-8")
print(f"wrote {out_path}")
