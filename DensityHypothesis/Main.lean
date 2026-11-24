import DensityHypothesis.ZeroCount

/-!
# The Density Hypothesis for the Riemann zeta function follows from the Riemann Hypothesis

`DensityHypothesis.density_hypothesis_zeta_zeros_of_riemannHypothesis` is, word for word, the
statement `DensityHypothesis.density_hypothesis_zeta_zeros` of
`google-deepmind/formal-conjectures` (`FormalConjectures/Wikipedia/DensityHypothesis.lean`, commit
`9097e2f90e66d2f6244209cb1c07f7120d17ec53`), with Mathlib's `RiemannHypothesis` as its only
hypothesis.

The proof has two ingredients.

* For `σ > 1/2` the Riemann Hypothesis leaves no zeros to count.
* For `σ = 1/2` one needs `N(1/2, T) ≪ T ^ (1 + ε)`. This is the classical unconditional
  Riemann–von Mangoldt upper bound, proved in `DensityHypothesis.ZeroCount` from Jensen's
  inequality (`DensityHypothesisProof.zeroCountOn_strip_le_rpow`, and in the sharper form
  `O(T log T)` as `DensityHypothesisProof.zeroCountOn_strip_le_mul_log`).
-/

namespace DensityHypothesis

/-- **The Density Hypothesis, assuming the Riemann Hypothesis**: for every `ε > 0` there is
`C > 0` such that `N(σ, T) ≤ C T ^ (2 (1 - σ) + ε)` for all `1/2 ≤ σ ≤ 1` and `T ≥ 2`. -/
theorem density_hypothesis_zeta_zeros_of_riemannHypothesis (hRH : RiemannHypothesis)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → 2 ≤ T →
      (zetaZeroCount σ T : ℝ) ≤ C * T ^ (2 * (1 - σ) + ε) :=
  DensityHypothesisProof.density_hypothesis_of_riemannHypothesis hRH ε hε

/-- Assuming the Riemann Hypothesis, the zero-density bound with the Guth–Maynard exponent
`30/13` (the statement `DensityHypothesis.guth_maynard_zero_density` of formal-conjectures). -/
theorem guth_maynard_zero_density_of_riemannHypothesis (hRH : RiemannHypothesis)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → 2 ≤ T →
      (zetaZeroCount σ T : ℝ) ≤ C * T ^ ((30 / 13 : ℝ) * (1 - σ) + ε) :=
  DensityHypothesisProof.guth_maynard_zero_density_of_riemannHypothesis hRH ε hε

/-- **Unconditional**: the zeros of `ζ` in `1/2 ≤ Re s ≤ 1`, `0 < Im s ≤ T`, counted with
multiplicity, number at most `C T log T`. -/
theorem zetaZeroCount_half_le_mul_log :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → (zetaZeroCount (1 / 2) T : ℝ) ≤ C * T * Real.log T :=
  DensityHypothesisProof.zeroCountOn_strip_le_mul_log

end DensityHypothesis
