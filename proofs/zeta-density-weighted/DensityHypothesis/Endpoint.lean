module

public import DensityHypothesis.Weighted
public import Zeta.Hadamard.ZeroSummability
import Mathlib.Tactic.NormNum

/-! Apply the summability theorem for the divisor of ξ to the multiplicities of ζ. -/
@[expose] public section

namespace DensityHypothesis

private theorem order_eq_xi_divisor {z : ℂ} (hpos : 0 < z.re) (hlt : z.re < 1) :
    (analyticOrderNatAt riemannZeta z : ℝ) =
      ((MeromorphicOn.divisor riemannXi ⊤ z : ℤ) : ℝ) := by
  have hz1 : z ≠ 1 := by rintro rfl; norm_num at hlt
  have hζ : AnalyticAt ℂ riemannZeta z := analyticOn_riemannZeta z hz1
  have h : MeromorphicOn.divisor riemannXi ⊤ z = (analyticOrderNatAt riemannZeta z : ℤ) := by
    rw [MeromorphicOn.divisor_apply analyticOnNhd_riemannXi.meromorphicOn (Set.mem_univ z),
      meromorphicOrderAt_riemannXi_eq_riemannZeta hpos hlt, hζ.meromorphicOrderAt_eq]
    change ((analyticOrderAt riemannZeta z).map (Nat.cast : ℕ → ℤ)).untop₀ =
      ((analyticOrderAt riemannZeta z).toNat : ℤ)
    generalize analyticOrderAt riemannZeta z = n
    induction n using ENat.recTopCoe <;> simp
  rw [h]
  norm_cast

theorem critical_line_estimate (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaZeroCount (1 / 2) T : ℝ) ≤ C * T ^ (1 + ε) :=
  endpoint_of_weighted_sum ε hε _ divisor_riemannXi_cast_nonneg
    (fun _ hpos hlt ↦ order_eq_xi_divisor hpos hlt) (summable_one_div_riemannZeta_zero_rpow hε)

#print axioms critical_line_estimate

end DensityHypothesis
