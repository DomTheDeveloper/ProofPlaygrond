import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic
import DensityHypothesis.Defs

/-!
# Counting the zeros of the Riemann zeta function, and the density hypothesis

This file proves, on top of Mathlib only:

* `DensityHypothesisProof.norm_riemannZeta₁_le`: polynomial growth of the entire function
  `(s - 1) ζ(s)` on the half-plane `Re s ≥ 1/5`, via the series
  `(s - 1) ζ(s) = 1 - ∑ₙ ((1 - s) (n+1)^(-s) - ((n+2)^(1-s) - (n+1)^(1-s)))`,
  which converges locally uniformly on `Re s > 0`;
* `DensityHypothesisProof.zeroCountOn_strip_le_mul_log` and
  `DensityHypothesisProof.zeroCountOn_strip_le_rpow`: the unconditional bound `O(T log T)` for
  the number of zeros with `1/2 ≤ Re s ≤ 1`, `0 < Im s ≤ T`, counted with multiplicity, from
  Jensen's inequality on discs centred at `2 + i (k + 1/2)`. This is only the easy upper-bound
  half of the Riemann–von Mangoldt formula, and only for the right half of the critical strip;
* `DensityHypothesisProof.density_hypothesis_of_riemannHypothesis`: the Riemann Hypothesis
  implies the Density Hypothesis `N(σ, T) ≪ T ^ (2 (1 - σ) + ε)`, uniformly in `1/2 ≤ σ ≤ 1`.
-/
open Complex Filter Topology Metric Set MeromorphicOn

noncomputable section

namespace DensityHypothesisProof

/-! ## Part 1: the correction series for `(s - 1) ζ(s)` on `Re s > 0` -/

/-- `cterm n s = (1 - s) (n+1)^{-s} - ((n+2)^{1-s} - (n+1)^{1-s})`. -/
def cterm (n : ℕ) (s : ℂ) : ℂ :=
  (1 - s) * ((n : ℂ) + 1) ^ (-s) - (((n : ℂ) + 2) ^ (1 - s) - ((n : ℂ) + 1) ^ (1 - s))

lemma norm_cpow_neg_sub_le {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 0 < s.re) {y : ℝ}
    (hy : y ∈ Icc a (a + 1)) :
    ‖(y : ℂ) ^ (-s) - (a : ℂ) ^ (-s)‖ ≤ ‖s‖ * a ^ (-s.re - 1) * (y - a) := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs
  have hderiv : ∀ x ∈ Icc a (a + 1),
      HasDerivWithinAt (fun t : ℝ => (t : ℂ) ^ (-s)) (-s * (x : ℂ) ^ (-s - 1))
        (Icc a (a + 1)) x := by
    intro x hx
    have hx0 : x ≠ 0 := (ha.trans_le hx.1).ne'
    exact (hasDerivAt_ofReal_cpow_const hx0 (neg_ne_zero.mpr hs0)).hasDerivWithinAt
  have hbound : ∀ x ∈ Icc a (a + 1), ‖-s * (x : ℂ) ^ (-s - 1)‖ ≤ ‖s‖ * a ^ (-s.re - 1) := by
    intro x hx
    have hx0 : 0 < x := ha.trans_le hx.1
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hre : (-s - 1).re = -s.re - 1 := by simp
    rw [hre]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos ha hx.1 (by linarith)) (norm_nonneg _)
  have h := (convex_Icc a (a + 1)).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (left_mem_Icc.mpr (by linarith)) hy
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hy.1)] at h
  exact h

lemma norm_cterm_le (n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    ‖cterm n s‖ ≤ ‖s‖ * ‖1 - s‖ * ((n : ℝ) + 1) ^ (-s.re - 1) := by
  by_cases h1 : s = 1
  · subst h1
    simp [cterm]
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  set a : ℝ := (n : ℝ) + 1 with ha_def
  have ha : 0 < a := by positivity
  set c : ℂ := (1 - s) * (a : ℂ) ^ (-s) with hc_def
  -- ψ(t) = t^{1-s} - (t - a) • c
  have hderiv : ∀ x ∈ Icc a (a + 1),
      HasDerivWithinAt (fun t : ℝ => (t : ℂ) ^ (1 - s) - (t - a) • c)
        ((1 - s) * (x : ℂ) ^ (1 - s - 1) - (1 : ℝ) • c) (Icc a (a + 1)) x := by
    intro x hx
    have hx0 : x ≠ 0 := (ha.trans_le hx.1).ne'
    have e1 := hasDerivAt_ofReal_cpow_const hx0 h1s
    have e2 : HasDerivAt (fun t : ℝ => (t - a) • c) ((1 : ℝ) • c) x :=
      ((hasDerivAt_id x).sub_const a).smul_const c
    exact (e1.sub e2).hasDerivWithinAt
  have hbound : ∀ x ∈ Icc a (a + 1),
      ‖(1 - s) * (x : ℂ) ^ (1 - s - 1) - (1 : ℝ) • c‖ ≤ ‖s‖ * ‖1 - s‖ * a ^ (-s.re - 1) := by
    intro x hx
    have e : (1 - s) * (x : ℂ) ^ (1 - s - 1) - (1 : ℝ) • c
        = (1 - s) * ((x : ℂ) ^ (-s) - (a : ℂ) ^ (-s)) := by
      have : (1 : ℂ) - s - 1 = -s := by ring
      rw [this, one_smul, hc_def]
      ring
    rw [e, norm_mul]
    have h2 := norm_cpow_neg_sub_le ha hs hx
    have h3 : x - a ≤ 1 := by linarith [hx.2]
    have h4 : 0 ≤ ‖s‖ * a ^ (-s.re - 1) := by positivity
    calc ‖1 - s‖ * ‖(x : ℂ) ^ (-s) - (a : ℂ) ^ (-s)‖
        ≤ ‖1 - s‖ * (‖s‖ * a ^ (-s.re - 1) * (x - a)) :=
          mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ ≤ ‖1 - s‖ * (‖s‖ * a ^ (-s.re - 1) * 1) := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          exact mul_le_mul_of_nonneg_left h3 h4
      _ = ‖s‖ * ‖1 - s‖ * a ^ (-s.re - 1) := by ring
  have h := (convex_Icc a (a + 1)).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (left_mem_Icc.mpr (by linarith)) (right_mem_Icc.mpr (by linarith))
  have hnorm : ‖(a + 1 : ℝ) - a‖ = 1 := by simp
  rw [hnorm, mul_one] at h
  have hkey : ((fun t : ℝ => (t : ℂ) ^ (1 - s) - (t - a) • c) (a + 1)
      - (fun t : ℝ => (t : ℂ) ^ (1 - s) - (t - a) • c) a) = -cterm n s := by
    have ea : ((a : ℝ) : ℂ) = (n : ℂ) + 1 := by simp [ha_def]
    have ea1 : ((a + 1 : ℝ) : ℂ) = (n : ℂ) + 2 := by
      simp only [ha_def]; push_cast; ring
    simp only [cterm, hc_def, sub_self, zero_smul, sub_zero, add_sub_cancel_left, one_smul]
    rw [ea1, ea]
    ring
  rw [hkey, norm_neg] at h
  exact h

lemma summable_rpow_add_one {p : ℝ} (hp : p < -1) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ p) := by
  have h := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr hp)
  simpa using h

lemma summable_norm_cterm {s : ℂ} (hs : 0 < s.re) : Summable (fun n : ℕ => ‖cterm n s‖) := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => norm_cterm_le n hs) ?_
  exact (summable_rpow_add_one (by linarith)).mul_left _

lemma differentiable_cterm (n : ℕ) : Differentiable ℂ (cterm n) := by
  have h1 : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
  have h2 : ((n : ℂ) + 2) ≠ 0 := by
    have := Nat.cast_add_one_ne_zero (R := ℂ) (n + 1)
    push_cast at this
    intro h
    apply this
    rw [← h]; ring
  intro s
  have d1 : DifferentiableAt ℂ (fun s : ℂ => ((n : ℂ) + 1) ^ (-s)) s :=
    (differentiableAt_id.neg).const_cpow (Or.inl h1)
  have d2 : DifferentiableAt ℂ (fun s : ℂ => ((n : ℂ) + 2) ^ (1 - s)) s :=
    ((differentiableAt_const 1).sub differentiableAt_id).const_cpow (Or.inl h2)
  have d3 : DifferentiableAt ℂ (fun s : ℂ => ((n : ℂ) + 1) ^ (1 - s)) s :=
    ((differentiableAt_const 1).sub differentiableAt_id).const_cpow (Or.inl h1)
  have d0 : DifferentiableAt ℂ (fun s : ℂ => (1 : ℂ) - s) s :=
    (differentiableAt_const 1).sub differentiableAt_id
  exact (d0.mul d1).sub (d2.sub d3)

/-- The series `∑ cterm n s` is holomorphic on the right half-plane. -/
lemma differentiableOn_tsum_cterm :
    DifferentiableOn ℂ (fun s : ℂ => ∑' n : ℕ, cterm n s) {s : ℂ | 0 < s.re} := by
  intro s₀ hs₀
  have hs₀' : 0 < s₀.re := hs₀
  set σ₀ : ℝ := s₀.re / 2 with hσ₀
  set B : ℝ := ‖s₀‖ + 1 with hB
  have hσ₀pos : 0 < σ₀ := half_pos hs₀'
  set U : Set ℂ := {s : ℂ | σ₀ < s.re} ∩ ball 0 B with hU
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ball
  have hs₀U : s₀ ∈ U := by
    refine ⟨?_, ?_⟩
    · show σ₀ < s₀.re
      rw [hσ₀]; linarith
    · rw [mem_ball_zero_iff, hB]; linarith
  have hBpos : 0 ≤ B := by rw [hB]; positivity
  have hu : Summable (fun n : ℕ => B * (1 + B) * ((n : ℝ) + 1) ^ (-σ₀ - 1)) :=
    (summable_rpow_add_one (by linarith)).mul_left _
  have hle : ∀ (n : ℕ) (w : ℂ), w ∈ U → ‖cterm n w‖ ≤ B * (1 + B) * ((n : ℝ) + 1) ^ (-σ₀ - 1) := by
    intro n w hw
    have hwre : σ₀ < w.re := hw.1
    have hwB : ‖w‖ < B := by simpa [mem_ball_zero_iff] using hw.2
    have h1 := norm_cterm_le n (hσ₀pos.trans hwre)
    have h2 : ‖1 - w‖ ≤ 1 + B := by
      calc ‖1 - w‖ ≤ ‖(1 : ℂ)‖ + ‖w‖ := norm_sub_le _ _
        _ ≤ 1 + B := by rw [norm_one]; linarith
    have h3 : ((n : ℝ) + 1) ^ (-w.re - 1) ≤ ((n : ℝ) + 1) ^ (-σ₀ - 1) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by linarith)
    have h4 : 0 ≤ ((n : ℝ) + 1) ^ (-w.re - 1) := by positivity
    calc ‖cterm n w‖ ≤ ‖w‖ * ‖1 - w‖ * ((n : ℝ) + 1) ^ (-w.re - 1) := h1
      _ ≤ B * (1 + B) * ((n : ℝ) + 1) ^ (-σ₀ - 1) := by
          exact mul_le_mul (mul_le_mul hwB.le h2 (norm_nonneg _) hBpos) h3 h4
            (mul_nonneg hBpos (by linarith))
  have hdiff := differentiableOn_tsum_of_summable_norm hu
    (fun n => (differentiable_cterm n).differentiableOn) hUopen hle
  exact (hdiff.differentiableAt (hUopen.mem_nhds hs₀U)).differentiableWithinAt

/-- For `Re s > 1` the series sums to `(1 - s) ζ(s) + 1`. -/
lemma tsum_cterm_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    ∑' n : ℕ, cterm n s = (1 - s) * riemannZeta s + 1 := by
  have hs0 : 0 < s.re := by linarith
  -- the zeta series
  have hzsum : Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s) := by
    have h := (summable_nat_add_iff 1).mpr (Complex.summable_one_div_nat_cpow.mpr hs)
    simpa using h
  have hz : HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s) (riemannZeta s) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
    exact hzsum.hasSum
  -- the telescoping part
  set f : ℕ → ℂ := fun k => ((k : ℂ) + 1) ^ (1 - s) with hf
  have hterm : ∀ n : ℕ, cterm n s = (1 - s) * (1 / ((n : ℂ) + 1) ^ s) - (f (n + 1) - f n) := by
    intro n
    have e : ((n + 1 : ℕ) : ℂ) + 1 = (n : ℂ) + 2 := by push_cast; ring
    simp only [cterm, hf, e, Complex.cpow_neg, one_div]
  have hcsum : Summable (fun n : ℕ => cterm n s) := (summable_norm_cterm hs0).of_norm
  have htel_summable : Summable (fun n : ℕ => f (n + 1) - f n) := by
    have := (hzsum.mul_left (1 - s)).sub hcsum
    refine this.congr (fun n => ?_)
    rw [hterm n]; ring
  have hf0 : Tendsto f atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hnorm : ∀ k : ℕ, ‖f k‖ = ((k : ℝ) + 1) ^ (-(s.re - 1)) := by
      intro k
      have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have : ((k : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
      simp only [hf]
      rw [this, Complex.norm_cpow_eq_rpow_re_of_pos hk]
      congr 1
      simp
    simp only [hnorm]
    exact (tendsto_rpow_neg_atTop (by linarith : 0 < s.re - 1)).comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have htel : HasSum (fun n : ℕ => f (n + 1) - f n) (0 - f 0) := by
    rw [htel_summable.hasSum_iff_tendsto_nat]
    simp only [Finset.sum_range_sub]
    exact hf0.sub_const _
  have hf00 : f 0 = 1 := by simp [hf]
  have hsum : HasSum (fun n : ℕ => cterm n s) ((1 - s) * riemannZeta s - (0 - f 0)) := by
    have h := (hz.mul_left (1 - s)).sub htel
    have hfun : (fun n : ℕ => cterm n s)
        = fun n : ℕ => (1 - s) * (1 / ((n : ℂ) + 1) ^ s) - (f (n + 1) - f n) := funext hterm
    rw [hfun]
    exact h
  rw [hsum.tsum_eq, hf00]; ring

/-- `riemannZeta₁ s = (s - 1) ζ(s)` for `s ≠ 1`. -/
lemma riemannZeta₁_eq {s : ℂ} (hs : s ≠ 1) : riemannZeta₁ s = (s - 1) * riemannZeta s := by
  have h := riemannZeta_eq_inv_sub_mul hs
  have hne : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  rw [h, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]

/-- On the right half-plane, `(s - 1) ζ(s) = 1 - ∑ cterm n s`. -/
lemma riemannZeta₁_eq_one_sub_tsum {s : ℂ} (hs : 0 < s.re) :
    riemannZeta₁ s = 1 - ∑' n : ℕ, cterm n s := by
  have hUopen : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hf : AnalyticOnNhd ℂ riemannZeta₁ {s : ℂ | 0 < s.re} :=
    fun z _ => differentiable_riemannZeta₁.analyticAt z
  have hg : AnalyticOnNhd ℂ (fun s : ℂ => 1 - ∑' n : ℕ, cterm n s) {s : ℂ | 0 < s.re} :=
    ((differentiableOn_const 1).sub differentiableOn_tsum_cterm).analyticOnNhd hUopen
  have hconn : IsPreconnected {s : ℂ | 0 < s.re} := (convex_halfSpace_re_gt 0).isPreconnected
  have h2 : (2 : ℂ) ∈ {s : ℂ | 0 < s.re} := by simp
  have heq : riemannZeta₁ =ᶠ[𝓝 (2 : ℂ)] (fun s : ℂ => 1 - ∑' n : ℕ, cterm n s) := by
    have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (by simp : (2 : ℂ) ∈ {s : ℂ | 1 < s.re})] with z hz
    have hz' : 1 < z.re := hz
    have hz1 : z ≠ 1 := by
      rintro rfl
      simp at hz'
    show riemannZeta₁ z = 1 - ∑' n : ℕ, cterm n z
    rw [riemannZeta₁_eq hz1, tsum_cterm_of_one_lt_re hz']
    ring
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hconn h2 heq hs

/-- The constant `K = ∑ (n+1)^{-6/5}`. -/
def K : ℝ := ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(6 / 5 : ℝ))

lemma K_nonneg : 0 ≤ K := tsum_nonneg fun n => by positivity

/-- Polynomial growth of `(s - 1) ζ(s)` on `Re s ≥ 1/5`. -/
lemma norm_riemannZeta₁_le {s : ℂ} (hs : 1 / 5 ≤ s.re) :
    ‖riemannZeta₁ s‖ ≤ 1 + ‖s‖ * ‖1 - s‖ * K := by
  have hs0 : 0 < s.re := by linarith
  rw [riemannZeta₁_eq_one_sub_tsum hs0]
  have hK : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-(6 / 5 : ℝ))) :=
    summable_rpow_add_one (by norm_num)
  have h1 : ‖∑' n : ℕ, cterm n s‖ ≤ ∑' n : ℕ, ‖cterm n s‖ :=
    norm_tsum_le_tsum_norm (summable_norm_cterm hs0)
  have h2 : ∑' n : ℕ, ‖cterm n s‖
      ≤ ∑' n : ℕ, ‖s‖ * ‖1 - s‖ * ((n : ℝ) + 1) ^ (-(6 / 5 : ℝ)) := by
    refine Summable.tsum_le_tsum (fun n => ?_) (summable_norm_cterm hs0) (hK.mul_left _)
    refine (norm_cterm_le n hs0).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) n])
      (by linarith)
  have h3 : ∑' n : ℕ, ‖s‖ * ‖1 - s‖ * ((n : ℝ) + 1) ^ (-(6 / 5 : ℝ)) = ‖s‖ * ‖1 - s‖ * K := by
    rw [tsum_mul_left]; rfl
  calc ‖1 - ∑' n : ℕ, cterm n s‖ ≤ ‖(1 : ℂ)‖ + ‖∑' n : ℕ, cterm n s‖ := norm_sub_le _ _
    _ ≤ 1 + ‖s‖ * ‖1 - s‖ * K := by rw [norm_one]; linarith

/-! ## Part 2: a lower bound for `ζ` on the line `Re s = 2` -/

lemma one_third_le_norm_riemannZeta {s : ℂ} (hs : s.re = 2) : 1 / 3 ≤ ‖riemannZeta s‖ := by
  have hs1 : 1 < s.re := by rw [hs]; norm_num
  have hzsum : Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s) := by
    have h := (summable_nat_add_iff 1).mpr (Complex.summable_one_div_nat_cpow.mpr hs1)
    simpa using h
  have hzeta : riemannZeta s = 1 + ∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℂ) + 1) ^ s := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs1, hzsum.tsum_eq_zero_add]
    simp
  have hnorm : ∀ n : ℕ, ‖1 / (((n + 1 : ℕ) : ℂ) + 1) ^ s‖ = 1 / ((n + 2 : ℕ) : ℝ) ^ 2 := by
    intro n
    have e : (((n + 1 : ℕ) : ℂ) + 1) = ((n + 2 : ℕ) : ℂ) := by push_cast; ring
    rw [e, norm_div, norm_one, Complex.norm_natCast_cpow_of_pos (by omega), hs, Real.rpow_two]
  have h2 : HasSum (fun n : ℕ => 1 / ((n + 2 : ℕ) : ℝ) ^ 2) (Real.pi ^ 2 / 6 - 1) := by
    have h := (hasSum_nat_add_iff' 2).mpr hasSum_zeta_two
    simpa [Finset.sum_range_succ] using h
  have htail : ‖∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℂ) + 1) ^ s‖ ≤ Real.pi ^ 2 / 6 - 1 := by
    have hsn : Summable (fun n : ℕ => ‖1 / (((n + 1 : ℕ) : ℂ) + 1) ^ s‖) := by
      simp only [hnorm]; exact h2.summable
    refine (norm_tsum_le_tsum_norm hsn).trans ?_
    simp only [hnorm]
    exact h2.tsum_eq.le
  have hpi : Real.pi ^ 2 / 6 - 1 ≤ 2 / 3 := by
    have h1 : Real.pi < 3.15 := Real.pi_lt_d2
    have h0 : 0 < Real.pi := Real.pi_pos
    nlinarith [mul_pos (sub_pos.mpr h1) (by linarith : (0 : ℝ) < 3.15 + Real.pi)]
  have h1le : (1 : ℝ) ≤ ‖riemannZeta s‖ + ‖∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℂ) + 1) ^ s‖ := by
    have h := norm_sub_le (riemannZeta s) (∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℂ) + 1) ^ s)
    have e : riemannZeta s - ∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℂ) + 1) ^ s = 1 := by
      rw [hzeta]; ring
    rw [e, norm_one] at h
    exact h
  linarith

/-! ## Part 3: Jensen's inequality on a disc centred at `2 + iτ` -/

/-- Centre of the disc at height `τ`. -/
def ctr (τ : ℝ) : ℂ := 2 + τ * I

lemma ctr_re (τ : ℝ) : (ctr τ).re = 2 := by simp [ctr]

lemma ctr_im (τ : ℝ) : (ctr τ).im = τ := by simp [ctr]

lemma norm_riemannZeta₁_ctr (τ : ℝ) : 1 / 3 ≤ ‖riemannZeta₁ (ctr τ)‖ := by
  have hne : ctr τ ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    rw [ctr_re] at this
    norm_num at this
  rw [riemannZeta₁_eq hne, norm_mul]
  have h1 : 1 ≤ ‖ctr τ - 1‖ := by
    have := Complex.abs_re_le_norm (ctr τ - 1)
    rw [Complex.sub_re, ctr_re] at this
    norm_num at this
    exact this
  have h2 := one_third_le_norm_riemannZeta (ctr_re τ)
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]

lemma norm_riemannZeta₁_le_of_mem_sphere (τ : ℝ) {z : ℂ} (hz : z ∈ sphere (ctr τ) (9 / 5)) :
    ‖riemannZeta₁ z‖ ≤ 1 + (|τ| + 4) ^ 2 * K := by
  have hdist : ‖z - ctr τ‖ = 9 / 5 := by
    rw [← dist_eq_norm]; exact hz
  have hre : 1 / 5 ≤ z.re := by
    have := Complex.abs_re_le_norm (z - ctr τ)
    rw [hdist, Complex.sub_re, ctr_re] at this
    linarith [(abs_le.mp this).1]
  have hc : ‖ctr τ‖ ≤ 2 + |τ| := by
    have := Complex.norm_le_abs_re_add_abs_im (ctr τ)
    rw [ctr_re, ctr_im] at this
    simpa using this
  have hc1 : ‖1 - ctr τ‖ ≤ 1 + |τ| := by
    have := Complex.norm_le_abs_re_add_abs_im (1 - ctr τ)
    rw [Complex.sub_re, Complex.sub_im, ctr_re, ctr_im] at this
    norm_num at this
    exact this
  have hz1 : ‖z‖ ≤ |τ| + 4 := by
    have : ‖z‖ ≤ ‖z - ctr τ‖ + ‖ctr τ‖ := by
      simpa using norm_add_le (z - ctr τ) (ctr τ)
    linarith
  have hz2 : ‖1 - z‖ ≤ |τ| + 4 := by
    have : ‖1 - z‖ ≤ ‖1 - ctr τ‖ + ‖ctr τ - z‖ := by
      have := norm_add_le (1 - ctr τ) (ctr τ - z)
      simpa using this
    rw [norm_sub_rev (ctr τ) z, hdist] at this
    linarith
  have h := norm_riemannZeta₁_le hre
  have hK := K_nonneg
  have hmul : ‖z‖ * ‖1 - z‖ ≤ (|τ| + 4) ^ 2 := by
    rw [sq]
    exact mul_le_mul hz1 hz2 (norm_nonneg _) (by positivity)
  linarith [mul_le_mul_of_nonneg_right hmul hK]

/-- Jensen's inequality: the number of zeros of `(s-1)ζ(s)` in the disc of radius `8/5`
around `2 + iτ` is `O(log (|τ| + 4))`. -/
lemma finsum_divisor_le (τ : ℝ) :
    ((∑ᶠ u, divisor riemannZeta₁ (closedBall (ctr τ) (8 / 5)) u : ℤ) : ℝ)
      ≤ Real.log (3 * (1 + (|τ| + 4) ^ 2 * K)) / Real.log (9 / 8) := by
  set M : ℝ := 1 + (|τ| + 4) ^ 2 * K with hM
  have hK := K_nonneg
  have hM1 : 1 ≤ M := by
    rw [hM]; nlinarith [mul_nonneg (sq_nonneg (|τ| + 4)) hK]
  have e8 : |(8 / 5 : ℝ)| = 8 / 5 := abs_of_pos (by norm_num)
  have e9 : |(9 / 5 : ℝ)| = 9 / 5 := abs_of_pos (by norm_num)
  have hc0 := norm_riemannZeta₁_ctr τ
  have hcne : riemannZeta₁ (ctr τ) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hc0
    norm_num at hc0
  have h := AnalyticOnNhd.sum_divisor_le (c := ctr τ) (r := 8 / 5) (R := 9 / 5) (M := M)
    (f := riemannZeta₁) (by rw [e8]; norm_num) (by rw [e8, e9]; norm_num) hM1
    (fun z _ => differentiable_riemannZeta₁.analyticAt z) hcne
    (fun z hz => by rw [e9] at hz; exact norm_riemannZeta₁_le_of_mem_sphere τ hz)
  rw [e8] at h
  refine h.trans ?_
  have hlog98 : (9 / 5 : ℝ) / (8 / 5) = 9 / 8 := by norm_num
  rw [hlog98]
  have hpos : 0 < Real.log (9 / 8) := Real.log_pos (by norm_num)
  apply div_le_div_of_nonneg_right _ hpos.le
  have hnpos : 0 < ‖riemannZeta₁ (ctr τ)‖ := norm_pos_iff.mpr hcne
  have hMpos : 0 < M := by linarith
  apply Real.log_le_log (div_pos hMpos hnpos)
  rw [div_le_iff₀ hnpos]
  nlinarith [mul_nonneg hMpos.le (by linarith : (0 : ℝ) ≤ 3 * ‖riemannZeta₁ (ctr τ)‖ - 1)]

/-! ## Part 4: from divisors of `(s-1)ζ(s)` to `Complex.zeroCountOn riemannZeta` -/

lemma enat_map_untop₀ (n : ℕ∞) :
    ((n.map (Nat.cast : ℕ → ℤ)).untop₀ : ℤ) = (n.toNat : ℤ) := by
  induction n using ENat.recTopCoe with
  | top => simp
  | coe m => simp

lemma analyticOrderAt_riemannZeta₁ {u : ℂ} (hu : u ≠ 1) :
    analyticOrderAt riemannZeta₁ u = analyticOrderAt riemannZeta u := by
  have h1 : riemannZeta₁ =ᶠ[𝓝 u] ((fun s : ℂ => s - 1) * riemannZeta) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (show u ∈ ({1} : Set ℂ)ᶜ from hu)] with z hz
    simp only [Pi.mul_apply]
    exact riemannZeta₁_eq hz
  have hid : AnalyticAt ℂ (fun s : ℂ => s - 1) u := analyticAt_id.sub analyticAt_const
  rw [analyticOrderAt_congr h1, analyticOrderAt_mul hid (analyticOn_riemannZeta u hu)]
  have h0 : analyticOrderAt (fun s : ℂ => s - 1) u = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr (sub_ne_zero.mpr hu))
  rw [h0, zero_add]

lemma divisor_riemannZeta₁_eq {c : ℂ} {r : ℝ} {u : ℂ} (hu : u ∈ closedBall c r) (hu1 : u ≠ 1) :
    divisor riemannZeta₁ (closedBall c r) u = (analyticOrderNatAt riemannZeta u : ℤ) := by
  have han : AnalyticOnNhd ℂ riemannZeta₁ (closedBall c r) :=
    fun z _ => differentiable_riemannZeta₁.analyticAt z
  rw [han.divisor_apply hu, analyticOrderAt_riemannZeta₁ hu1, enat_map_untop₀]
  rfl

lemma support_analyticOrderNatAt_subset :
    Function.support (fun s : ℂ => analyticOrderNatAt riemannZeta s) ⊆ riemannZetaZeros := by
  intro s hs
  by_contra h
  exact hs (Complex.analyticOrderNatAt_eq_zero_of_ne_zero h)

lemma finite_inter_support {S : Set ℂ} (hS : Bornology.IsBounded S) :
    (S ∩ Function.support (fun s : ℂ => analyticOrderNatAt riemannZeta s)).Finite := by
  refine (hS.finite_riemannZeta_zeros).subset ?_
  rintro s ⟨hsS, hs⟩
  exact ⟨hsS, support_analyticOrderNatAt_subset hs⟩

lemma zeroCountOn_union {S T : Set ℂ} (hd : Disjoint S T) (hS : Bornology.IsBounded S)
    (hT : Bornology.IsBounded T) :
    zeroCountOn riemannZeta (S ∪ T) = zeroCountOn riemannZeta S + zeroCountOn riemannZeta T :=
  finsum_mem_union' hd (finite_inter_support hS) (finite_inter_support hT)

lemma zeroCountOn_mono {S T : Set ℂ} (hST : S ⊆ T) (hT : Bornology.IsBounded T) :
    zeroCountOn riemannZeta S ≤ zeroCountOn riemannZeta T := by
  have h : S ∪ (T \ S) = T := by
    ext x
    constructor
    · rintro (hx | hx)
      · exact hST hx
      · exact hx.1
    · intro hx
      by_cases hxS : x ∈ S
      · exact Or.inl hxS
      · exact Or.inr ⟨hx, hxS⟩
  rw [← h, zeroCountOn_union disjoint_sdiff_right (hT.subset hST)
    (hT.subset fun x hx => hx.1)]
  exact Nat.le_add_right _ _

lemma zeroCountOn_le_finsum_divisor {c : ℂ} {r : ℝ} {Q : Set ℂ} (hQ : Q ⊆ closedBall c r)
    (h1 : (1 : ℂ) ∉ Q) :
    ((zeroCountOn riemannZeta Q : ℕ) : ℤ) ≤ ∑ᶠ u, divisor riemannZeta₁ (closedBall c r) u := by
  classical
  set g : ℂ → ℕ := fun s => analyticOrderNatAt riemannZeta s with hg
  have han : AnalyticOnNhd ℂ riemannZeta₁ (closedBall c r) :=
    fun z _ => differentiable_riemannZeta₁.analyticAt z
  have hQb : Bornology.IsBounded Q := isBounded_closedBall.subset hQ
  have hQfin : (Q ∩ Function.support g).Finite := finite_inter_support hQb
  have hDfin : (Function.support (divisor riemannZeta₁ (closedBall c r))).Finite :=
    (divisor riemannZeta₁ (closedBall c r)).finiteSupport (isCompact_closedBall c r)
  have hDeq : ∀ u ∈ Q, divisor riemannZeta₁ (closedBall c r) u = (g u : ℤ) := by
    intro u hu
    exact divisor_riemannZeta₁_eq (hQ hu) (fun h => h1 (h ▸ hu))
  have hDnn : ∀ u, 0 ≤ divisor riemannZeta₁ (closedBall c r) u := fun u => by
    simpa using han.divisor_nonneg u
  have e1 : zeroCountOn riemannZeta Q = ∑ s ∈ hQfin.toFinset, g s := finsum_mem_eq_sum g hQfin
  have e2 : ∑ᶠ u, divisor riemannZeta₁ (closedBall c r) u
      = ∑ u ∈ hDfin.toFinset, divisor riemannZeta₁ (closedBall c r) u :=
    finsum_eq_sum_of_support_subset _ (by simp)
  rw [e1, e2, Nat.cast_sum]
  have hsub : hQfin.toFinset ⊆ hDfin.toFinset := by
    intro u hu
    rw [Set.Finite.mem_toFinset] at hu ⊢
    obtain ⟨huQ, hsupp⟩ := hu
    rw [Function.mem_support] at hsupp ⊢
    rw [hDeq u huQ]
    exact_mod_cast hsupp
  calc ∑ s ∈ hQfin.toFinset, (g s : ℤ)
      = ∑ s ∈ hQfin.toFinset, divisor riemannZeta₁ (closedBall c r) s := by
        refine Finset.sum_congr rfl (fun u hu => ?_)
        rw [Set.Finite.mem_toFinset] at hu
        exact (hDeq u hu.1).symm
    _ ≤ ∑ u ∈ hDfin.toFinset, divisor riemannZeta₁ (closedBall c r) u :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun u _ _ => hDnn u)

/-! ## Part 5: boxes, strips and the summation -/

/-- The `k`-th unit box of the half-strip `1/2 ≤ Re s ≤ 1`. -/
def box (k : ℕ) : Set ℂ := {s : ℂ | 1 / 2 ≤ s.re ∧ s.re ≤ 1 ∧ (k : ℝ) < s.im ∧ s.im ≤ k + 1}

/-- The region counted by `zetaZeroCount (1/2) x`. -/
def strip (x : ℝ) : Set ℂ := {s : ℂ | 1 / 2 ≤ s.re ∧ s.re ≤ 1 ∧ 0 < s.im ∧ s.im ≤ x}

lemma box_subset_closedBall (k : ℕ) : box k ⊆ closedBall (ctr ((k : ℝ) + 1 / 2)) (8 / 5) := by
  intro s hs
  obtain ⟨h1, h2, h3, h4⟩ := hs
  rw [mem_closedBall, dist_eq_norm]
  have hsq : ‖s - ctr ((k : ℝ) + 1 / 2)‖ ^ 2 ≤ (8 / 5 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, ctr_re, ctr_im]
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2),
      mul_nonneg (sub_nonneg.mpr h3.le) (sub_nonneg.mpr h4)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by norm_num) two_ne_zero).mp hsq

lemma one_notMem_box (k : ℕ) : (1 : ℂ) ∉ box k := by
  rintro ⟨_, _, h3, _⟩
  have h : (k : ℝ) < 0 := by simpa using h3
  exact absurd h (not_lt.mpr (Nat.cast_nonneg k))

lemma isBounded_strip (x : ℝ) : Bornology.IsBounded (strip x) := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨1 + |x|, fun s hs => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hs
  have := Complex.norm_le_abs_re_add_abs_im s
  have hre : |s.re| ≤ 1 := abs_le.mpr ⟨by linarith, h2⟩
  have him : |s.im| ≤ |x| := by
    rw [abs_of_pos h3]; exact h4.trans (le_abs_self x)
  linarith

lemma box_subset_strip (k : ℕ) : box k ⊆ strip ((k : ℝ) + 1) := by
  rintro s ⟨h1, h2, h3, h4⟩
  exact ⟨h1, h2, lt_of_le_of_lt (Nat.cast_nonneg k) h3, h4⟩

lemma strip_succ (m : ℕ) : strip ((m : ℝ) + 1) = strip m ∪ box m := by
  ext s
  simp only [strip, box, mem_union]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    by_cases h : s.im ≤ m
    · exact Or.inl ⟨h1, h2, h3, h⟩
    · exact Or.inr ⟨h1, h2, not_le.mp h, h4⟩
  · rintro (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩)
    · exact ⟨h1, h2, h3, by linarith⟩
    · exact ⟨h1, h2, lt_of_le_of_lt (Nat.cast_nonneg m) h3, h4⟩

lemma disjoint_strip_box (m : ℕ) : Disjoint (strip m) (box m) := by
  rw [Set.disjoint_left]
  rintro s ⟨_, _, _, h4⟩ ⟨_, _, h3', _⟩
  linarith

/-- The per-box bound, as a function of a real upper bound `X` for the height. -/
def Lr (X : ℝ) : ℝ := Real.log (3 * (1 + (X + 5) ^ 2 * K)) / Real.log (9 / 8)

lemma Lr_nonneg (X : ℝ) : 0 ≤ Lr X := by
  have hK := K_nonneg
  have hpos : 0 < Real.log (9 / 8) := Real.log_pos (by norm_num)
  apply div_nonneg _ hpos.le
  apply Real.log_nonneg
  nlinarith [mul_nonneg (sq_nonneg (X + 5)) hK]

lemma zeroCountOn_box_le (k : ℕ) {X : ℝ} (hkX : (k : ℝ) ≤ X) :
    (zeroCountOn riemannZeta (box k) : ℝ) ≤ Lr X := by
  have h1 := zeroCountOn_le_finsum_divisor (box_subset_closedBall k) (one_notMem_box k)
  have h2 := finsum_divisor_le ((k : ℝ) + 1 / 2)
  have h3 : ((zeroCountOn riemannZeta (box k) : ℕ) : ℝ)
      ≤ ((∑ᶠ u, divisor riemannZeta₁ (closedBall (ctr ((k : ℝ) + 1 / 2)) (8 / 5)) u : ℤ) : ℝ) := by
    exact_mod_cast h1
  refine (h3.trans h2).trans ?_
  have hK := K_nonneg
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have habs : |(k : ℝ) + 1 / 2| = (k : ℝ) + 1 / 2 := abs_of_nonneg (by linarith)
  rw [habs, Lr]
  have hpos : 0 < Real.log (9 / 8) := Real.log_pos (by norm_num)
  apply div_le_div_of_nonneg_right _ hpos.le
  have hsq : ((k : ℝ) + 1 / 2 + 4) ^ 2 ≤ (X + 5) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hsqK := mul_le_mul_of_nonneg_right hsq hK
  have hposl : 0 < 3 * (1 + ((k : ℝ) + 1 / 2 + 4) ^ 2 * K) := by
    nlinarith [mul_nonneg (sq_nonneg ((k : ℝ) + 1 / 2 + 4)) hK]
  apply Real.log_le_log hposl
  linarith

lemma zeroCountOn_strip_nat_le (X : ℝ) : ∀ m : ℕ, (m : ℝ) ≤ X + 1 →
    (zeroCountOn riemannZeta (strip m) : ℝ) ≤ m * Lr X := by
  intro m
  induction m with
  | zero =>
    intro _
    have h0 : zeroCountOn riemannZeta (strip (0 : ℝ)) = 0 := by
      apply zeroCountOn_eq_zero_of_forall_ne_zero
      rintro s ⟨_, _, h3, h4⟩
      exact absurd h3 (not_lt.mpr h4)
    simp only [Nat.cast_zero, zero_mul]
    rw [h0]
    simp
  | succ m ih =>
    intro hm
    have hm' : (m : ℝ) ≤ X := by push_cast at hm; linarith
    have e : strip ((m + 1 : ℕ) : ℝ) = strip m ∪ box m := by
      push_cast; exact strip_succ m
    rw [e, zeroCountOn_union (disjoint_strip_box m) (isBounded_strip m)
      ((isBounded_strip _).subset (box_subset_strip m))]
    have h1 := ih (by linarith)
    have h2 := zeroCountOn_box_le m hm'
    have e2 : ((m + 1 : ℕ) : ℝ) * Lr X = m * Lr X + Lr X := by push_cast; ring
    rw [e2]
    push_cast
    linarith

lemma zeroCountOn_strip_le {T : ℝ} (hT : 2 ≤ T) :
    (zeroCountOn riemannZeta (strip T) : ℝ) ≤ (T + 1) * Lr T := by
  have hT0 : 0 ≤ T := by linarith
  have hceil : ((⌈T⌉₊ : ℕ) : ℝ) < T + 1 := Nat.ceil_lt_add_one hT0
  have hsub : strip T ⊆ strip ((⌈T⌉₊ : ℕ) : ℝ) := by
    rintro s ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, h3, h4.trans (Nat.le_ceil T)⟩
  have h1 : zeroCountOn riemannZeta (strip T) ≤ zeroCountOn riemannZeta (strip ((⌈T⌉₊ : ℕ) : ℝ)) :=
    zeroCountOn_mono hsub (isBounded_strip _)
  have h2 := zeroCountOn_strip_nat_le T ⌈T⌉₊ hceil.le
  have h3 : ((zeroCountOn riemannZeta (strip T) : ℕ) : ℝ)
      ≤ ((zeroCountOn riemannZeta (strip ((⌈T⌉₊ : ℕ) : ℝ)) : ℕ) : ℝ) := by exact_mod_cast h1
  have hL : 0 ≤ Lr T := Lr_nonneg T
  calc (zeroCountOn riemannZeta (strip T) : ℝ)
      ≤ ((⌈T⌉₊ : ℕ) : ℝ) * Lr T := h3.trans h2
    _ ≤ (T + 1) * Lr T := mul_le_mul_of_nonneg_right hceil.le hL

/-- **Zero count, unconditional**: the number of zeros of `ζ`, counted with multiplicity, in
`1/2 ≤ Re s ≤ 1`, `0 < Im s ≤ T` is `O_ε(T^{1+ε})`. -/
theorem zeroCountOn_strip_le_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zeroCountOn riemannZeta (strip T) : ℝ) ≤ C * T ^ (1 + ε) := by
  have hK := K_nonneg
  set A : ℝ := 3 * (1 + 16 * K) with hA
  have hApos : 0 < A := by rw [hA]; linarith
  have hlog : 0 < Real.log (9 / 8) := Real.log_pos (by norm_num)
  have hAε : 0 < A ^ (ε / 2) := Real.rpow_pos_of_pos hApos _
  refine ⟨4 * A ^ (ε / 2) / (ε * Real.log (9 / 8)),
    div_pos (mul_pos (by norm_num) hAε) (mul_pos hε hlog), fun T hT => ?_⟩
  have hT0 : 0 < T := by linarith
  have h1 := zeroCountOn_strip_le hT
  have hinner : 3 * (1 + (T + 5) ^ 2 * K) ≤ A * T ^ 2 := by
    rw [hA]
    have h5 : (T + 5) ^ 2 ≤ 16 * T ^ 2 := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 3 * T - 5) (by linarith : (0 : ℝ) ≤ 5 * T + 5)]
    have h6 : (1 : ℝ) ≤ T ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right h5 hK]
  have hinner_pos : 0 < 3 * (1 + (T + 5) ^ 2 * K) := by
    nlinarith [mul_nonneg (sq_nonneg (T + 5)) hK]
  have hlogle : Real.log (3 * (1 + (T + 5) ^ 2 * K)) ≤ (2 / ε) * A ^ (ε / 2) * T ^ ε := by
    calc Real.log (3 * (1 + (T + 5) ^ 2 * K))
        ≤ Real.log (A * T ^ 2) := Real.log_le_log hinner_pos hinner
      _ ≤ (A * T ^ 2) ^ (ε / 2) / (ε / 2) :=
          Real.log_le_rpow_div (mul_nonneg hApos.le (sq_nonneg T)) (by linarith)
      _ = (2 / ε) * A ^ (ε / 2) * T ^ ε := by
          rw [Real.mul_rpow hApos.le (sq_nonneg T), ← Real.rpow_natCast T 2,
            ← Real.rpow_mul hT0.le]
          have e : ((2 : ℕ) : ℝ) * (ε / 2) = ε := by push_cast; ring
          rw [e]
          field_simp
  have hLr : Lr T ≤ (2 / ε) * A ^ (ε / 2) * T ^ ε / Real.log (9 / 8) := by
    rw [Lr]
    exact div_le_div_of_nonneg_right hlogle hlog.le
  have hTε : 0 < T ^ ε := Real.rpow_pos_of_pos hT0 ε
  have hLr0 : 0 ≤ Lr T := Lr_nonneg T
  have hε' : ε ≠ 0 := hε.ne'
  have hlog' : Real.log (9 / 8) ≠ 0 := hlog.ne'
  calc (zeroCountOn riemannZeta (strip T) : ℝ)
      ≤ (T + 1) * Lr T := h1
    _ ≤ (2 * T) * ((2 / ε) * A ^ (ε / 2) * T ^ ε / Real.log (9 / 8)) :=
        mul_le_mul (by linarith) hLr hLr0 (by linarith)
    _ = 4 * A ^ (ε / 2) / (ε * Real.log (9 / 8)) * T ^ (1 + ε) := by
        rw [Real.rpow_add hT0, Real.rpow_one]
        field_simp
        ring

/-- **Zero count, unconditional, logarithmic form**: the number of zeros of `ζ`, counted with
multiplicity, in `1/2 ≤ Re s ≤ 1`, `0 < Im s ≤ T` is `O(T log T)`. -/
theorem zeroCountOn_strip_le_mul_log :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zeroCountOn riemannZeta (strip T) : ℝ) ≤ C * T * Real.log T := by
  have hK := K_nonneg
  set A : ℝ := 3 * (1 + 16 * K) with hA
  have hA1 : 1 ≤ A := by rw [hA]; linarith
  have hApos : 0 < A := by linarith
  have hlog : 0 < Real.log (9 / 8) := Real.log_pos (by norm_num)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg hA1
  set D : ℝ := Real.log A / Real.log 2 + 2 with hD
  have hDpos : 0 < D := by
    rw [hD]; exact add_pos_of_nonneg_of_pos (div_nonneg hlogA hlog2.le) two_pos
  refine ⟨2 * D / Real.log (9 / 8), div_pos (mul_pos two_pos hDpos) hlog, fun T hT => ?_⟩
  have hT0 : 0 < T := by linarith
  have h1 := zeroCountOn_strip_le hT
  have hlogT : Real.log 2 ≤ Real.log T := Real.log_le_log two_pos hT
  have hlogT0 : 0 < Real.log T := lt_of_lt_of_le hlog2 hlogT
  have hinner : 3 * (1 + (T + 5) ^ 2 * K) ≤ A * T ^ 2 := by
    rw [hA]
    have h5 : (T + 5) ^ 2 ≤ 16 * T ^ 2 := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 3 * T - 5) (by linarith : (0 : ℝ) ≤ 5 * T + 5)]
    have h6 : (1 : ℝ) ≤ T ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right h5 hK]
  have hinner_pos : 0 < 3 * (1 + (T + 5) ^ 2 * K) := by
    nlinarith [mul_nonneg (sq_nonneg (T + 5)) hK]
  have hlogle : Real.log (3 * (1 + (T + 5) ^ 2 * K)) ≤ D * Real.log T := by
    have e : Real.log (A * T ^ 2) = Real.log A + 2 * Real.log T := by
      rw [Real.log_mul hApos.ne' (pow_ne_zero 2 hT0.ne'), Real.log_pow]
      push_cast
      ring
    have hA2 : Real.log A ≤ Real.log A / Real.log 2 * Real.log T := by
      have h := mul_le_mul_of_nonneg_left hlogT (div_nonneg hlogA hlog2.le)
      rwa [div_mul_cancel₀ _ hlog2.ne'] at h
    calc Real.log (3 * (1 + (T + 5) ^ 2 * K))
        ≤ Real.log (A * T ^ 2) := Real.log_le_log hinner_pos hinner
      _ = Real.log A + 2 * Real.log T := e
      _ ≤ D * Real.log T := by rw [hD]; linarith
  have hLr : Lr T ≤ D * Real.log T / Real.log (9 / 8) := by
    rw [Lr]
    exact div_le_div_of_nonneg_right hlogle hlog.le
  have hLr0 : 0 ≤ Lr T := Lr_nonneg T
  have hlog' : Real.log (9 / 8) ≠ 0 := hlog.ne'
  calc (zeroCountOn riemannZeta (strip T) : ℝ)
      ≤ (T + 1) * Lr T := h1
    _ ≤ (2 * T) * (D * Real.log T / Real.log (9 / 8)) :=
        mul_le_mul (by linarith) hLr hLr0 (by linarith)
    _ = 2 * D / Real.log (9 / 8) * T * Real.log T := by
        field_simp

/-! ## Part 6: the Density Hypothesis from the Riemann Hypothesis -/

/-- **The Density Hypothesis follows from the Riemann Hypothesis.**
The conclusion is verbatim the statement of
`DensityHypothesis.density_hypothesis_zeta_zeros` in `google-deepmind/formal-conjectures`
(with the abbreviation `zetaZeroCount` unfolded). -/
theorem density_hypothesis_of_riemannHypothesis (hRH : RiemannHypothesis) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → 2 ≤ T →
      (zeroCountOn riemannZeta {s : ℂ | σ ≤ s.re ∧ s.re ≤ 1 ∧ 0 < s.im ∧ s.im ≤ T} : ℝ)
        ≤ C * T ^ (2 * (1 - σ) + ε) := by
  obtain ⟨C, hC, hbound⟩ := zeroCountOn_strip_le_rpow ε hε
  refine ⟨C, hC, fun σ T hσ hσ1 hT => ?_⟩
  have hT0 : 0 < T := by linarith
  rcases eq_or_lt_of_le hσ with h | h
  · subst h
    have e : 2 * (1 - (1 / 2 : ℝ)) + ε = 1 + ε := by ring
    rw [e]
    exact hbound T hT
  · have hz : zeroCountOn riemannZeta
        {s : ℂ | σ ≤ s.re ∧ s.re ≤ 1 ∧ 0 < s.im ∧ s.im ≤ T} = 0 := by
      apply zeroCountOn_eq_zero_of_forall_ne_zero
      rintro s ⟨h1, h2, h3, h4⟩ hzero
      have hre : s.re = 1 / 2 := by
        refine hRH s hzero ?_ ?_
        · rintro ⟨n, hn⟩
          have him := congrArg Complex.im hn
          simp at him
          linarith
        · rintro rfl
          simp at h3
      linarith
    rw [hz]
    simp only [Nat.cast_zero]
    exact mul_nonneg hC.le (Real.rpow_nonneg hT0.le _)

/-- Under the Riemann Hypothesis the zero-density bound with exponent `30/13` is an immediate
consequence of the Density Hypothesis, because `30/13 ≥ 2`. The conclusion is verbatim the
statement of `DensityHypothesis.guth_maynard_zero_density` in
`google-deepmind/formal-conjectures`, whose name this declaration follows. This is not Guth and
Maynard's theorem: theirs is unconditional and deep, and nothing of it is proved here. -/
theorem guth_maynard_zero_density_of_riemannHypothesis (hRH : RiemannHypothesis) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → 2 ≤ T →
      (zeroCountOn riemannZeta {s : ℂ | σ ≤ s.re ∧ s.re ≤ 1 ∧ 0 < s.im ∧ s.im ≤ T} : ℝ)
        ≤ C * T ^ ((30 / 13 : ℝ) * (1 - σ) + ε) := by
  obtain ⟨C, hC, hbound⟩ := density_hypothesis_of_riemannHypothesis hRH ε hε
  refine ⟨C, hC, fun σ T hσ hσ1 hT => (hbound σ T hσ hσ1 hT).trans ?_⟩
  refine mul_le_mul_of_nonneg_left ?_ hC.le
  exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by nlinarith)

end DensityHypothesisProof
