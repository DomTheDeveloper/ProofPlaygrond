/-
Copyright 2026 The Formal Conjectures Authors. Licensed under Apache 2.0.
Formal Conjectures definitions and target: google-deepmind/formal-conjectures at 9097e2f90e66.
Transfer by @domthedeveloper. Three-point bound by Thomas Lince (2026 Zeta Lab, MIT).
-/
import Mathlib
import ThreePoint.Main

namespace Complex

/-- The multiplicity-weighted count of zeros of `f : ℂ → ℂ` in `S : Set ℂ`, summing
`analyticOrderNatAt f s` over `s ∈ S`. Points where `f s ≠ 0` or `f` is not analytic contribute
`0`. -/
noncomputable def zeroCountOn (f : ℂ → ℂ) (S : Set ℂ) : ℕ :=
  ∑ᶠ s ∈ S, analyticOrderNatAt f s

end Complex

namespace ZetaZeros

/-- The nontrivial zeros of `f` (those in the critical strip `0 < re s < 1`) with imaginary part
in `(T₁, T₂]`. -/
def nontrivialZeros (f : ℂ → ℂ) (T₁ T₂ : ℝ) : Set ℂ :=
  {s | f s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ T₁ < s.im ∧ s.im ≤ T₂}

/-- `N(T₁, T₂)`: the nontrivial zeros of `f` with imaginary part in `(T₁, T₂]`, counted with
multiplicity. -/
noncomputable def N (f : ℂ → ℂ) (T₁ T₂ : ℝ) : ℕ :=
  Complex.zeroCountOn f (nontrivialZeros f T₁ T₂)

/-- `Ns(T₁, T₂)`: the number of simple zeros of `f` on the critical line with imaginary part in
`(T₁, T₂]`. -/
noncomputable def Ns (f : ℂ → ℂ) (T₁ T₂ : ℝ) : ℕ :=
  {s ∈ nontrivialZeros f T₁ T₂ | s.re = 1 / 2 ∧ analyticOrderAt f s = 1}.ncard

/-- The Montgomery–Taylor constant `c_MT = √2 tan(1/√2) / (1 + tan(1/√2)/√2)`, so that
`c_MT⁻¹ = 1/2 + cot(1/√2)/√2 = 1.3274…`. -/
noncomputable def montgomeryTaylorConst : ℝ := √2 * (1 / √2).tan / (1 + (1 / √2).tan / √2)

end ZetaZeros

namespace SimplePropLtProof

open Filter ZetaZeros Zeta23

private noncomputable def H : ℝ :=
  3 / 2 - (Real.sqrt 2)⁻¹ * (Real.cos (Real.sqrt 2)⁻¹ / Real.sin (Real.sqrt 2)⁻¹)

private theorem zeros_eq (a b : ℝ) :
    zerosIn a b = nontrivialZeros riemannZeta a b := by
  ext z
  simp [zerosIn, IsNontrivialZero, nontrivialZeros, and_assoc]

private theorem total_eq (a b : ℝ) : Ncount a b = N riemannZeta a b := by
  unfold Ncount N Complex.zeroCountOn
  rw [zeros_eq]
  rfl

private theorem simple_eq (a b : ℝ) : N0simple a b = Ns riemannZeta a b := by
  unfold N0simple Ns
  rw [zeros_eq]
  congr 1
  ext z
  change ((z ∈ nontrivialZeros riemannZeta a b ∧ z.re = 1 / 2) ∧
    (analyticOrderAt riemannZeta z).toNat = 1) ↔
    z ∈ nontrivialZeros riemannZeta a b ∧ z.re = 1 / 2 ∧ analyticOrderAt riemannZeta z = 1
  simp only [ENat.toNat_eq_iff_eq_natCast, Nat.cast_one, and_assoc]

private theorem constant_eq_and_lower :
    H = 2 - montgomeryTaylorConst⁻¹ ∧ (1/2 : ℝ) < H := by
  let r := Real.sqrt 2
  let x := r⁻¹
  have hr : 0 < r := Real.sqrt_pos.2 (by norm_num)
  have hr₂ : r ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hx : 0 < x := inv_pos.mpr hr
  have hπ : x < Real.pi / 2 := by
    have : x ≤ 1 := inv_le_one_of_one_le₀ Real.one_lt_sqrt_two.le
    linarith [Real.pi_gt_three]
  have ht := Real.lt_tan hx hπ
  have heq : H = 3 / 2 - x / x.tan := by
    dsimp only [H, x, r]
    rw [Real.tan_eq_sin_div_cos, div_div_eq_mul_div, mul_div_assoc]
  rw [heq]
  constructor
  · unfold montgomeryTaylorConst
    simp only [one_div]
    change 3 / 2 - r⁻¹ / x.tan = 2 - (r * x.tan / (1 + x.tan / r))⁻¹
    rw [inv_div]
    have ht0 : 0 < x.tan := hx.trans ht
    field_simp
    nlinarith [congrArg (fun y : ℝ => y * x.tan) hr₂]
  · have hlt : x / x.tan < 1 := (div_lt_one (hx.trans ht)).2 ht
    linarith

theorem _root_.riemannZeta.simple_prop_lt :
    ∃ c > 2 - montgomeryTaylorConst⁻¹, ∃ o : ℝ → ℝ,
    o =o[atTop] (1 : ℝ → ℝ) ∧
      ∀ T > 0, (c - o T) * N riemannZeta T (2 * T) ≤ Ns riemannZeta T (2 * T) := by
  let B := (149000000 * H - 99200) / 148800133
  have hHB : H < B := by dsimp [B]; linarith [constant_eq_and_lower.2]
  obtain ⟨c, hc, hcB⟩ := exists_between hHB
  obtain ⟨T₀, hT₀⟩ := Zeta23Ext.Bridge.ThreePoint.three_point_bound (B - c) (sub_pos.mpr hcB)
  rw [Zeta23.ThmD.HD_one] at hT₀
  refine ⟨c, constant_eq_and_lower.1 ▸ hc, fun T => if T₀ ≤ T then 0 else c, ?_, ?_⟩
  · apply (Asymptotics.isLittleO_zero (1 : ℝ → ℝ) atTop).congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [eventually_ge_atTop T₀] with T hT using (if_pos hT).symm
  · intro T _
    by_cases hT : T₀ ≤ T
    · simpa [hT, B, H, total_eq, simple_eq] using hT₀ T hT
    · simp [hT]

end SimplePropLtProof

#print axioms riemannZeta.simple_prop_lt
