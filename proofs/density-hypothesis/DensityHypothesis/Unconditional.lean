module

public import DensityHypothesis.Main
import Main

/-!
# The Density Hypothesis for the Riemann zeta function

This file can only be compiled inside a build of `leanprover-community/riemann-hypothesis`: its
second import, `Main`, is that repository's module containing
`theorem riemannHypothesis : RiemannHypothesis`.

The two statements are, word for word, `DensityHypothesis.density_hypothesis_zeta_zeros` and
`DensityHypothesis.guth_maynard_zero_density` of `google-deepmind/formal-conjectures`
(`FormalConjectures/Wikipedia/DensityHypothesis.lean`, commit
`9097e2f90e66d2f6244209cb1c07f7120d17ec53`), with no hypothesis.
-/

@[expose] public section

namespace DensityHypothesis

/-- **The Density Hypothesis**: for every `ε > 0` there is `C > 0` such that
`N(σ, T) ≤ C T ^ (2 (1 - σ) + ε)` for all `1/2 ≤ σ ≤ 1` and `T ≥ 2`. -/
theorem density_hypothesis_zeta_zeros (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → 2 ≤ T →
      (zetaZeroCount σ T : ℝ) ≤ C * T ^ (2 * (1 - σ) + ε) :=
  density_hypothesis_zeta_zeros_of_riemannHypothesis riemannHypothesis ε hε

/-- The zero-density bound with exponent `30/13` (the statement the catalog names after Guth and
Maynard), here as a corollary of the Riemann Hypothesis; Guth and Maynard's unconditional argument
is not formalised here. -/
theorem guth_maynard_zero_density (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → 2 ≤ T →
      (zetaZeroCount σ T : ℝ) ≤ C * T ^ ((30 / 13 : ℝ) * (1 - σ) + ε) :=
  guth_maynard_zero_density_of_riemannHypothesis riemannHypothesis ε hε

end DensityHypothesis
