import DensityHypothesis.Endpoint
import Main

/-! The density hypothesis for the exact multiplicity-weighted count in Formal Conjectures. -/

namespace DensityHypothesis

/-- For every positive ε, one constant works on the whole closed strip and for all T ≥ 2. -/
theorem density_hypothesis_zeta_zeros (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → 2 ≤ T →
      (zetaZeroCount σ T : ℝ) ≤ C * T ^ (2 * (1 - σ) + ε) :=
  density_of_endpoint riemannHypothesis ε (critical_line_estimate ε hε)

#print axioms density_hypothesis_zeta_zeros

end DensityHypothesis
