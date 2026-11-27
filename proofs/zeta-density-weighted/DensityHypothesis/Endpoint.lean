module

public import DensityHypothesis.Order
public import DensityHypothesis.Weighted
public import Zeta.Hadamard.ZeroSummability

/-! The weighted estimate specialized to the divisor of ξ. -/
@[expose] public section

namespace DensityHypothesis

theorem critical_line_estimate (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaZeroCount (1 / 2) T : ℝ) ≤ C * T ^ (1 + ε) :=
  endpoint_of_weighted_sum ε hε _ divisor_riemannXi_cast_nonneg
    (fun _ hpos hlt ↦ order_eq_xi_divisor hpos hlt) (summable_one_div_riemannZeta_zero_rpow hε)

#print axioms critical_line_estimate

end DensityHypothesis
