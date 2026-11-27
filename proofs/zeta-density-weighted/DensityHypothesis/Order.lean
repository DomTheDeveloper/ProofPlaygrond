module

public import DensityHypothesis.Count
public import Zeta.RiemannXi
public import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Tactic.NormNum

/-! Apply the summability theorem for the divisor of ξ to the multiplicities of ζ. -/
@[expose] public section

namespace DensityHypothesis

theorem order_eq_xi_divisor {z : ℂ} (hpos : 0 < z.re) (hlt : z.re < 1) :
    (analyticOrderNatAt riemannZeta z : ℝ) =
      ((MeromorphicOn.divisor riemannXi ⊤ z : ℤ) : ℝ) := by
  have hz1 : z ≠ 1 := by rintro rfl; norm_num at hlt
  have hζ : AnalyticAt ℂ riemannZeta z := analyticOn_riemannZeta z hz1
  have h : MeromorphicOn.divisor riemannXi ⊤ z = (analyticOrderNatAt riemannZeta z : ℤ) := by
    change MeromorphicOn.divisor riemannXi Set.univ z = (analyticOrderNatAt riemannZeta z : ℤ)
    rw [MeromorphicOn.divisor_apply analyticOnNhd_riemannXi.meromorphicOn (Set.mem_univ z),
      meromorphicOrderAt_riemannXi_eq_riemannZeta hpos hlt, hζ.meromorphicOrderAt_eq]
    change ((analyticOrderAt riemannZeta z).map (Nat.cast : ℕ → ℤ)).untop₀ =
      ((analyticOrderAt riemannZeta z).toNat : ℤ)
    generalize analyticOrderAt riemannZeta z = n
    induction n using ENat.recTopCoe <;> simp
  rw [h] <;> norm_cast

end DensityHypothesis
