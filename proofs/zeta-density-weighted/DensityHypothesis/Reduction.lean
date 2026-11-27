module

public import DensityHypothesis.Count
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-! Reduction of the closed-strip density hypothesis to the count on its left boundary. -/
@[expose] public section

namespace DensityHypothesis

/-- At positive imaginary height, RH puts every zero on the critical line. -/
theorem count_eq_zero_of_RH (hRH : RiemannHypothesis) {σ : ℝ} (hσ : 1 / 2 < σ) (T : ℝ) :
    zetaZeroCount σ T = 0 := by
  apply Complex.zeroCountOn_eq_zero_of_forall_ne_zero
  rintro z ⟨hzσ, _, him, _⟩ hzero
  have hz1 : z ≠ 1 := by
    rintro rfl
    simp at him
  have htriv : ¬ ∃ n : ℕ, z = -2 * (n + 1) := by
    rintro ⟨n, rfl⟩
    simp [Complex.mul_im] at him
  exact (not_lt_of_ge hzσ) ((hRH z hzero htriv hz1) ▸ hσ)

/-- A single endpoint estimate gives one constant for the whole closed strip. -/
theorem density_of_endpoint (hRH : RiemannHypothesis) (ε : ℝ)
    (h : ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaZeroCount (1 / 2) T : ℝ) ≤ C * T ^ (1 + ε)) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → 2 ≤ T →
      (zetaZeroCount σ T : ℝ) ≤ C * T ^ (2 * (1 - σ) + ε) := by
  obtain ⟨C, hC, hbound⟩ := h
  refine ⟨C, hC, fun σ T hlo _ hT ↦ ?_⟩
  rcases eq_or_lt_of_le hlo with rfl | hσ
  · rw [show (2 : ℝ) * (1 - 1 / 2) = 1 by norm_num]
    exact hbound T hT
  · rw [count_eq_zero_of_RH hRH hσ, Nat.cast_zero]
    exact mul_nonneg hC.le (Real.rpow_nonneg (by linarith) _)

end DensityHypothesis
