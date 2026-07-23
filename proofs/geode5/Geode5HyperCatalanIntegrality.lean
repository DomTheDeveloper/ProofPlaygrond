/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Arxiv.«2508.10245».Geode5Proof.MultinomialDivisibility

/-!
# Integrality of the five-variable hyper-Catalan quotient

This completes the natural-number/rational bridge needed to rewrite the
`Nat.div` in `hyperCatalan5` as the exact factorial quotient used by the Geode
moment proof.
-/

namespace Arxiv.«2508.10245».Geode5Proof

/-- Denominator shared by the hyper-Catalan and full multinomial quotients. -/
def hyperDenominator (m₁ m₂ m₃ m₄ m₅ : ℕ) : ℕ :=
  Nat.factorial (hyperLongIndex m₁ m₂ m₃ m₄ m₅) *
    Nat.factorial m₁ * Nat.factorial m₂ * Nat.factorial m₃ *
    Nat.factorial m₄ * Nat.factorial m₅

/-- The natural hyper-Catalan quotient is the full multinomial divided by length. -/
theorem hyperCatalan5_eq_hyperMultinomial_div_length
    (m₁ m₂ m₃ m₄ m₅ : ℕ) :
    hyperCatalan5 m₁ m₂ m₃ m₄ m₅ =
      hyperMultinomial m₁ m₂ m₃ m₄ m₅ /
        (hyperNumeratorIndex m₁ m₂ m₃ m₄ m₅ + 1) := by
  let N := hyperNumeratorIndex m₁ m₂ m₃ m₄ m₅
  let L := N + 1
  let D := hyperDenominator m₁ m₂ m₃ m₄ m₅
  have hL : 0 < L := by simp [L]
  rw [hyperMultinomial_eq_factorial_quotient]
  simp only [hyperCatalan5, hyperNumeratorIndex, hyperLongIndex,
    hyperDenominator] at ⊢
  change Nat.factorial N / D =
    (Nat.factorial L / D) / L
  rw [Nat.div_div_eq_div_mul]
  have hfac : Nat.factorial L = L * Nat.factorial N := by
    simp [L, Nat.factorial_succ]
  rw [hfac]
  calc
    (L * Nat.factorial N) / (D * L) =
        (Nat.factorial N * L) / (D * L) := by rw [Nat.mul_comm]
    _ = Nat.factorial N / D := by
      exact Nat.mul_div_mul_right _ _ hL

/-- The full multinomial is exactly length times the hyper-Catalan number. -/
theorem hyperMultinomial_eq_length_mul_hyperCatalan5
    (m₁ m₂ m₃ m₄ m₅ : ℕ) :
    hyperMultinomial m₁ m₂ m₃ m₄ m₅ =
      (hyperNumeratorIndex m₁ m₂ m₃ m₄ m₅ + 1) *
        hyperCatalan5 m₁ m₂ m₃ m₄ m₅ := by
  rw [hyperCatalan5_eq_hyperMultinomial_div_length]
  exact (Nat.mul_div_cancel' (hyper_word_length_dvd_multinomial
    m₁ m₂ m₃ m₄ m₅)).symm

/-- Cast of `hyperCatalan5` equals its exact rational factorial quotient. -/
theorem cast_hyperCatalan5_eq_qHyperCatalan5
    (m₁ m₂ m₃ m₄ m₅ : ℕ) :
    (hyperCatalan5 m₁ m₂ m₃ m₄ m₅ : ℚ) =
      qHyperCatalan5 m₁ m₂ m₃ m₄ m₅ := by
  rw [hyperCatalan5_eq_hyperMultinomial_div_length]
  rw [Nat.cast_div (hyper_word_length_dvd_multinomial m₁ m₂ m₃ m₄ m₅)]
  rw [qHyperCatalan5_eq_fullMultinomial_div_length]
  congr 1
  rw [hyperMultinomial_eq_factorial_quotient]
  simp [qHyperFullMultinomial, qFactorial, hyperDenominator]

#print axioms hyper_word_length_dvd_multinomial
#print axioms cast_hyperCatalan5_eq_qHyperCatalan5

end Arxiv.«2508.10245».Geode5Proof
