/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
https://www.apache.org/licenses/LICENSE-2.0
-/
import Mathlib

/-!
# Transfer of the registered three-point estimate to Formal Conjectures

The zero counts and target follow Google DeepMind's `FormalConjectures/Paper/RiemannZetaZeros.lean`
and `Complex.zeroCountOn` at `f606af160664c5a10952e9a957b100a1cd45bbeb` (Apache 2.0).
The registered input is Thomas Lince's unconditional three-point theorem, Palomar
`PALOMAR-2026-08-25-000005`. Its counting definitions and constant are reproduced below
under a local namespace from `teal-sea/zeta-lab` at
`84312e4477dfeb7e0d8a91c38897f225f5a52f19` (MIT, © 2026 Zeta Lab).

This file checks the implication with Mathlib alone. `SimplePropLt.lean` supplies the
registered proof to obtain the unconditional conclusion.
-/

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

/- MIT License

Copyright (c) 2026 Thomas Lince

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

noncomputable section
namespace SimplePropLtProof.Registered

/-! ### Counting the zeros of ζ -/

/-- `ρ` is a nontrivial zero of `ζ`: a zero in the open critical strip. -/
def IsNontrivialZero (ρ : ℂ) : Prop := riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1

/-- `m_ρ`, the multiplicity of `ρ`: the order of vanishing of `ζ` at `ρ`, via
Mathlib's `analyticOrderAt`. -/
def zeroMult (ρ : ℂ) : ℕ := (analyticOrderAt riemannZeta ρ).toNat

/-- `{ρ nontrivial zero : T₁ < γ ≤ T₂}`, with `γ = Im ρ`. -/
def zerosIn (T₁ T₂ : ℝ) : Set ℂ := {ρ | IsNontrivialZero ρ ∧ T₁ < ρ.im ∧ ρ.im ≤ T₂}

/-- `N(T₁,T₂)`: the number of nontrivial zeros with `T₁ < γ ≤ T₂`, counted with
multiplicity. -/
def Ncount (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosIn T₁ T₂, zeroMult ρ

/-- `N₀ˢ(T₁,T₂)`: the number of `ρ` with `T₁ < γ ≤ T₂`, `β = 1/2` and `m_ρ = 1`,
that is the simple zeros on the critical line in the window. -/
def N0simple (T₁ T₂ : ℝ) : ℕ :=
  (zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2} ∩ {ρ | zeroMult ρ = 1}).ncard

def H : ℝ := 3 / 2 - (Real.sqrt 2)⁻¹ * (Real.cos (Real.sqrt 2)⁻¹ / Real.sin (Real.sqrt 2)⁻¹)


end SimplePropLtProof.Registered
end

namespace SimplePropLtProof

open Filter ZetaZeros Registered

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

theorem of_three_point (three_point :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((149000000 * H - 99200) / 148800133 - ε) * (Ncount T (2 * T) : ℝ)
        ≤ N0simple T (2 * T)) :
    ∃ c > 2 - montgomeryTaylorConst⁻¹, ∃ o : ℝ → ℝ,
    o =o[atTop] (1 : ℝ → ℝ) ∧
      ∀ T > 0, (c - o T) * N riemannZeta T (2 * T) ≤ Ns riemannZeta T (2 * T) := by
  let B := (149000000 * H - 99200) / 148800133
  have hHB : H < B := by dsimp [B]; linarith [constant_eq_and_lower.2]
  obtain ⟨c, hc, hcB⟩ := exists_between hHB
  obtain ⟨T₀, hT₀⟩ := three_point (B - c) (sub_pos.mpr hcB)
  refine ⟨c, constant_eq_and_lower.1 ▸ hc, fun T => if T₀ ≤ T then 0 else c, ?_, ?_⟩
  · apply (Asymptotics.isLittleO_zero (1 : ℝ → ℝ) atTop).congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [eventually_ge_atTop T₀] with T hT using (if_pos hT).symm
  · intro T _
    by_cases hT : T₀ ≤ T
    · simpa [hT, B, total_eq, simple_eq] using hT₀ T hT
    · simp [hT]

end SimplePropLtProof

#print axioms SimplePropLtProof.of_three_point
