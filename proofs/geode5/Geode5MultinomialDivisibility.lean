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

import Mathlib.Data.Nat.Choose.Multinomial
import FormalConjectures.Arxiv.«2508.10245».Geode5Proof.IntegralityReduction

/-!
# Multinomial divisibility for the Geode hyper-Catalan quotient

For every symbol `a`, the total word length divides
`count a * multinomial`. The Geode counts then supply an explicit coefficient-one
linear relation, so the word length divides the multinomial coefficient itself.
-/

namespace Arxiv.«2508.10245».Geode5Proof

open scoped BigOperators

/-- The sum of the counts divides each count times the multinomial coefficient. -/
theorem sum_dvd_apply_mul_multinomial {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℕ) {a : α} (ha : a ∈ s) :
    (∑ i ∈ s, f i) ∣ f a * Nat.multinomial s f := by
  by_cases hfa : f a = 0
  · simp [hfa]
  let g := Function.update f a (f a - 1)
  have hfa_pos : 0 < f a := Nat.pos_of_ne_zero hfa
  have hga : g a + 1 = f a := by
    simp [g, Nat.sub_add_cancel hfa_pos]
  have hupdate : Function.update g a (g a).succ = f := by
    funext x
    by_cases hxa : x = a
    · subst x
      simp [hga]
    · simp [g, hxa]
  have hsum_erase :
      ∑ x ∈ s.erase a, g x = ∑ x ∈ s.erase a, f x := by
    apply Finset.sum_congr rfl
    intro x hx
    have hxa : x ≠ a := ne_of_mem_erase hx
    simp [g, hxa]
  have hsum :
      (∑ x ∈ s, g x).succ = ∑ x ∈ s, f x := by
    rw [← Finset.sum_erase_add _ ha, ← Finset.sum_erase_add _ ha]
    rw [hsum_erase]
    omega
  have hmul := Nat.succ_mul_multinomial (s := s) (f := g) ha
  refine ⟨Nat.multinomial s g, ?_⟩
  calc
    f a * Nat.multinomial s f =
        (g a).succ *
          Nat.multinomial s (Function.update g a (g a).succ) := by
            rw [hupdate]
    _ = (∑ x ∈ s, g x).succ * Nat.multinomial s g := hmul.symm
    _ = (∑ x ∈ s, f x) * Nat.multinomial s g := by rw [hsum]

/-- The six symbols in the Raney-word interpretation. -/
inductive HyperLetter
  | negative | one | two | three | four | five
  deriving DecidableEq, Fintype

/-- Multiplicities of the six Raney-word symbols. -/
def hyperCounts (m₁ m₂ m₃ m₄ m₅ : ℕ) : HyperLetter → ℕ
  | .negative => hyperLongIndex m₁ m₂ m₃ m₄ m₅
  | .one => m₁
  | .two => m₂
  | .three => m₃
  | .four => m₄
  | .five => m₅

/-- The sum of all six counts is the numerator index plus one. -/
theorem sum_hyperCounts (m₁ m₂ m₃ m₄ m₅ : ℕ) :
    ∑ a : HyperLetter, hyperCounts m₁ m₂ m₃ m₄ m₅ a =
      hyperNumeratorIndex m₁ m₂ m₃ m₄ m₅ + 1 := by
  simp [hyperCounts, hyperLongIndex, hyperNumeratorIndex]
  omega

/-- The full multinomial coefficient for the six Raney-word symbol counts. -/
def hyperMultinomial (m₁ m₂ m₃ m₄ m₅ : ℕ) : ℕ :=
  Nat.multinomial Finset.univ (hyperCounts m₁ m₂ m₃ m₄ m₅)

/--
The word length divides the full multinomial coefficient. This is the exact
integrality statement required for the five-variable hyper-Catalan number.
-/
theorem hyper_word_length_dvd_multinomial (m₁ m₂ m₃ m₄ m₅ : ℕ) :
    hyperNumeratorIndex m₁ m₂ m₃ m₄ m₅ + 1 ∣
      hyperMultinomial m₁ m₂ m₃ m₄ m₅ := by
  let c := hyperCounts m₁ m₂ m₃ m₄ m₅
  let L := hyperNumeratorIndex m₁ m₂ m₃ m₄ m₅ + 1
  let M := hyperMultinomial m₁ m₂ m₃ m₄ m₅
  have hsum : (∑ a : HyperLetter, c a) = L := by
    simpa [c, L] using sum_hyperCounts m₁ m₂ m₃ m₄ m₅
  have hdiv (a : HyperLetter) : L ∣ c a * M := by
    rw [← hsum]
    exact sum_dvd_apply_mul_multinomial Finset.univ c (Finset.mem_univ a)
  have hneg := hdiv HyperLetter.negative
  have h₁ := hdiv HyperLetter.one
  have h₂ := hdiv HyperLetter.two
  have h₃ := hdiv HyperLetter.three
  have h₄ := hdiv HyperLetter.four
  have h₅ := hdiv HyperLetter.five
  have hweighted :
      L ∣ (m₁ + 2 * m₂ + 3 * m₃ + 4 * m₄ + 5 * m₅) * M := by
    dsimp [c, M] at h₁ h₂ h₃ h₄ h₅
    exact (((h₁.add (h₂.mul_left 2)).add (h₃.mul_left 3)).add
      (h₄.mul_left 4)).add (h₅.mul_left 5)
  have hrelation :
      hyperLongIndex m₁ m₂ m₃ m₄ m₅ * M =
        M + (m₁ + 2 * m₂ + 3 * m₃ + 4 * m₄ + 5 * m₅) * M := by
    simp [hyperLongIndex]
    ring
  dsimp [c] at hneg
  rw [hrelation] at hneg
  exact (dvd_add_iff_left hweighted).mp hneg

/-- The natural full multinomial has exactly the expected factorial quotient. -/
theorem hyperMultinomial_eq_factorial_quotient (m₁ m₂ m₃ m₄ m₅ : ℕ) :
    hyperMultinomial m₁ m₂ m₃ m₄ m₅ =
      Nat.factorial (hyperNumeratorIndex m₁ m₂ m₃ m₄ m₅ + 1) /
        (Nat.factorial (hyperLongIndex m₁ m₂ m₃ m₄ m₅) *
          Nat.factorial m₁ * Nat.factorial m₂ * Nat.factorial m₃ *
          Nat.factorial m₄ * Nat.factorial m₅) := by
  simp [hyperMultinomial, Nat.multinomial, hyperCounts, sum_hyperCounts]

#print axioms sum_dvd_apply_mul_multinomial
#print axioms hyper_word_length_dvd_multinomial

end Arxiv.«2508.10245».Geode5Proof
