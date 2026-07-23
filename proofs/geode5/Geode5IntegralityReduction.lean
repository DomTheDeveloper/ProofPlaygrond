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

import FormalConjectures.Arxiv.«2508.10245».Geode5Proof.Reduction

/-!
# Integrality reduction for the five-variable hyper-Catalan quotient

The hyper-Catalan factorial quotient is a Raney/cycle-lemma number. This file
isolates the exact algebraic reduction: it is the full multinomial count of a
word with one negative step type and five nonnegative step types, divided by the
word length. The remaining integrality theorem is therefore the freeness of the
cyclic rotation action (equivalently, the cycle lemma).
-/

namespace Arxiv.«2508.10245».Geode5Proof

/-- Numerator index in the five-variable hyper-Catalan quotient. -/
def hyperNumeratorIndex (m₁ m₂ m₃ m₄ m₅ : ℕ) : ℕ :=
  2 * m₁ + 3 * m₂ + 4 * m₃ + 5 * m₄ + 6 * m₅

/-- Number of negative unit steps in the corresponding Raney word. -/
def hyperLongIndex (m₁ m₂ m₃ m₄ m₅ : ℕ) : ℕ :=
  1 + m₁ + 2 * m₂ + 3 * m₃ + 4 * m₄ + 5 * m₅

/-- Total number of nonnegative steps. -/
def hyperPositiveCount (m₁ m₂ m₃ m₄ m₅ : ℕ) : ℕ :=
  m₁ + m₂ + m₃ + m₄ + m₅

/-- The word length is the hyper-Catalan numerator index plus one. -/
theorem hyper_word_length_identity (m₁ m₂ m₃ m₄ m₅ : ℕ) :
    hyperNumeratorIndex m₁ m₂ m₃ m₄ m₅ + 1 =
      hyperLongIndex m₁ m₂ m₃ m₄ m₅ +
        hyperPositiveCount m₁ m₂ m₃ m₄ m₅ := by
  omega

/-- The full multinomial factorial quotient over `ℚ`. -/
def qHyperFullMultinomial (m₁ m₂ m₃ m₄ m₅ : ℕ) : ℚ :=
  qFactorial (hyperNumeratorIndex m₁ m₂ m₃ m₄ m₅ + 1) /
    (qFactorial (hyperLongIndex m₁ m₂ m₃ m₄ m₅) *
      qFactorial m₁ * qFactorial m₂ * qFactorial m₃ *
      qFactorial m₄ * qFactorial m₅)

/--
The hyper-Catalan rational quotient is the full multinomial count divided by
its total word length.
-/
theorem qHyperCatalan5_eq_fullMultinomial_div_length
    (m₁ m₂ m₃ m₄ m₅ : ℕ) :
    qHyperCatalan5 m₁ m₂ m₃ m₄ m₅ =
      qHyperFullMultinomial m₁ m₂ m₃ m₄ m₅ /
        (hyperNumeratorIndex m₁ m₂ m₃ m₄ m₅ + 1 : ℚ) := by
  simp only [qHyperCatalan5, qHyperFullMultinomial,
    hyperNumeratorIndex, hyperLongIndex, qFactorial, Nat.factorial_succ]
  field_simp
  ring

/-- The associated step multiset has total sum `-1`. -/
theorem raney_step_sum (m₁ m₂ m₃ m₄ m₅ : ℕ) :
    (m₁ : ℤ) + 2 * m₂ + 3 * m₃ + 4 * m₄ + 5 * m₅ -
        hyperLongIndex m₁ m₂ m₃ m₄ m₅ = -1 := by
  simp [hyperLongIndex]
  omega

#print axioms qHyperCatalan5_eq_fullMultinomial_div_length
#print axioms raney_step_sum

end Arxiv.«2508.10245».Geode5Proof
