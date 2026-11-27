module

public import DensityHypothesis.Reduction
public import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Deduce the endpoint count directly from a summable weighted multiplicity. -/
@[expose] public section

namespace DensityHypothesis

/-- Each term in the counting rectangle has norm at most `2T`. Extracting this
power from a finite subsum gives a bound uniform in the height. -/
theorem endpoint_of_weighted_sum (ε : ℝ) (hε : 0 < ε) (m : ℂ → ℝ)
    (hm : ∀ z, 0 ≤ m z)
    (hmult : ∀ z : ℂ, 0 < z.re → z.re < 1 → (analyticOrderNatAt riemannZeta z : ℝ) = m z)
    (hsum : Summable fun z : ℂ ↦ m z * ‖z‖ ^ (-(1 + ε))) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaZeroCount (1 / 2) T : ℝ) ≤ C * T ^ (1 + ε) := by
  classical
  let p := 1 + ε
  let w := fun z : ℂ ↦ m z * ‖z‖ ^ (-p)
  have hw (z : ℂ) : 0 ≤ w z := mul_nonneg (hm z) (Real.rpow_nonneg (norm_nonneg _) _)
  have hp : 0 < p := by dsimp [p]; linarith
  have htotal : 0 ≤ ∑' z, w z := tsum_nonneg hw
  refine ⟨1 + 2 ^ p * ∑' z, w z, by positivity, fun T hT ↦ ?_⟩
  have ht : 0 < T := by linarith
  let S := {z : ℂ | 1 / 2 ≤ z.re ∧ z.re ≤ 1 ∧ 0 < z.im ∧ z.im ≤ T}
  let Z := {z ∈ S | riemannZeta z = 0}
  have hnorm {z : ℂ} (hz : z ∈ S) : ‖z‖ ≤ 2 * T := by
    obtain ⟨ha, hb, hc, hd⟩ := hz
    calc
      ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ ≤ 2 * T := by rw [abs_of_nonneg (by linarith : 0 ≤ z.re), abs_of_pos hc]; linarith
  have hZ : Z.Finite := (isCompact_closedBall (0 : ℂ) (2 * T)).inter_riemannZetaZeros_finite.subset
    fun z hz ↦ ⟨by simpa [Metric.mem_closedBall, dist_zero_right] using hnorm hz.1, hz.2⟩
  change (Complex.zeroCountOn riemannZeta S : ℝ) ≤ _
  rw [← Complex.zeroCountOn_sep_eq_zero, Complex.zeroCountOn, Nat.cast_finsum_mem hZ,
    finsum_mem_eq_finite_toFinset_sum _ hZ]
  calc
    _ ≤ ∑ z ∈ hZ.toFinset, (2*T)^p * w z := by
      apply Finset.sum_le_sum
      intro z hz
      have hz' : z ∈ Z := hZ.mem_toFinset.mp hz
      have hpos : 0 < z.re := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/2) hz'.1.1
      have hn : 0 < ‖z‖ := norm_pos_iff.mpr (Complex.ne_zero_of_re_pos hpos)
      rw [hmult z hpos (lt_of_not_ge fun h ↦ riemannZeta_ne_zero_of_one_le_re h hz'.2)]
      dsimp only [w]
      rw [Real.rpow_neg hn.le, ← div_eq_mul_inv, ← mul_div_assoc, le_div_iff₀ (Real.rpow_pos_of_pos hn _)]
      simpa [mul_comm] using mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow hn.le (hnorm hz'.1) hp.le) (hm z)
    _ = (2*T)^p * ∑ z ∈ hZ.toFinset, w z := (Finset.mul_sum ..).symm
    _ ≤ (2*T)^p * ∑' z, w z := by
      exact mul_le_mul_of_nonneg_left (hsum.sum_le_tsum _ (fun z _ ↦ hw z)) (by positivity)
    _ ≤ (1 + 2 ^ p * ∑' z, w z) * T ^ p := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) ht.le]
      nlinarith [Real.rpow_pos_of_pos ht p]

end DensityHypothesis
