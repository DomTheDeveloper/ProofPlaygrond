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

import FormalConjectures.Arxiv.«2508.10245».Geode5Proof.HyperCatalanIntegrality

/-!
# Cast bridges from the benchmark definition to the rational Geode proof
-/

namespace Arxiv.«2508.10245».Geode5Proof

open scoped BigOperators

inductive FourLetter
  | first | second | third | fourth
  deriving DecidableEq, Fintype

/-- Four symbol multiplicities used for the ordinary multinomial coefficient. -/
def fourCounts (a b c d : ℕ) : FourLetter → ℕ
  | .first => a
  | .second => b
  | .third => c
  | .fourth => d

/-- The denominator in `multinomial4` divides its factorial numerator. -/
theorem multinomial4_denominator_dvd (a b c d : ℕ) :
    Nat.factorial a * Nat.factorial b * Nat.factorial c * Nat.factorial d ∣
      Nat.factorial (a + b + c + d) := by
  simpa [fourCounts, mul_assoc, add_assoc, add_comm, add_left_comm] using
    (Nat.multinomial_dvd_factorial (s := Finset.univ) (fourCounts a b c d))

/-- Cast of `multinomial4` equals the exact rational factorial quotient. -/
theorem cast_multinomial4_eq_qMultinomial4 (a b c d : ℕ) :
    (multinomial4 a b c d : ℚ) = qMultinomial4 a b c d := by
  rw [multinomial4, Nat.cast_div (multinomial4_denominator_dvd a b c d)]
  simp [qMultinomial4, qFactorial]

/-- Rational version of the original alternating-sum definition. -/
def qGeode5Diagonal (n : ℕ) : ℚ :=
  ∑ j₂ ∈ Finset.range (n + 1),
    ∑ j₃ ∈ Finset.range (n + 1),
      ∑ j₄ ∈ Finset.range (n + 1),
        ∑ j₅ ∈ Finset.range (n + 1),
          (-1 : ℚ) ^ (j₂ + j₃ + j₄ + j₅) *
            qMultinomial4 j₂ j₃ j₄ j₅ *
              qHyperCatalan5 (n + 1 + j₂ + j₃ + j₄ + j₅)
                (n - j₂) (n - j₃) (n - j₄) (n - j₅)

/-- Casting the exact benchmark definition gives the rational alternating sum. -/
theorem cast_geode5Diagonal_eq_qGeode5Diagonal (n : ℕ) :
    (geode5Diagonal n : ℚ) = qGeode5Diagonal n := by
  simp only [geode5Diagonal, qGeode5Diagonal, Int.cast_sum, Int.cast_mul,
    Int.cast_pow, Int.cast_neg, Int.cast_one, Nat.cast_ofNat]
  apply Finset.sum_congr rfl
  intro j₂ hj₂
  apply Finset.sum_congr rfl
  intro _ _
  apply Finset.sum_congr rfl
  intro _ _
  apply Finset.sum_congr rfl
  intro j₅ hj₅
  rw [cast_multinomial4_eq_qMultinomial4,
    cast_hyperCatalan5_eq_qHyperCatalan5]
  norm_num

#print axioms cast_multinomial4_eq_qMultinomial4
#print axioms cast_geode5Diagonal_eq_qGeode5Diagonal

end Arxiv.«2508.10245».Geode5Proof
