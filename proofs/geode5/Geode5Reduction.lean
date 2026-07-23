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

import FormalConjectures.Arxiv.«2508.10245».Geode5

/-!
# Factorial reduction for the five-dimensional Geode

This module formalizes the purely algebraic reduction of an individual term in
the four-dimensional alternating sum to the binomial form used in the moment
integral. It intentionally works over `ℚ`; the separate generalized-Catalan
integrality layer will connect the natural-number quotient in `hyperCatalan5`
to this rational expression.
-/

namespace Arxiv.«2508.10245».Geode5Proof

/-- A natural factorial viewed in `ℚ`. -/
def qFactorial (n : ℕ) : ℚ := Nat.factorial n

/-- The factorial quotient representing a binomial coefficient over `ℚ`. -/
def qBinomial (n k : ℕ) : ℚ :=
  qFactorial n / (qFactorial k * qFactorial (n - k))

/-- The four-way multinomial factorial quotient over `ℚ`. -/
def qMultinomial4 (a b c d : ℕ) : ℚ :=
  qFactorial (a + b + c + d) /
    (qFactorial a * qFactorial b * qFactorial c * qFactorial d)

/-- The hyper-Catalan factorial quotient before natural-number division. -/
def qHyperCatalan5 (m₁ m₂ m₃ m₄ m₅ : ℕ) : ℚ :=
  qFactorial (2 * m₁ + 3 * m₂ + 4 * m₃ + 5 * m₄ + 6 * m₅) /
    (qFactorial (1 + m₁ + 2 * m₂ + 3 * m₃ + 4 * m₄ + 5 * m₅) *
      qFactorial m₁ * qFactorial m₂ * qFactorial m₃ *
      qFactorial m₄ * qFactorial m₅)

/-- One rational summand in the original alternating Geode formula. -/
def qAlternatingSummand (n a b c d : ℕ) : ℚ :=
  (-1 : ℚ) ^ (a + b + c + d) * qMultinomial4 a b c d *
    qHyperCatalan5 (n + 1 + a + b + c + d)
      (n - a) (n - b) (n - c) (n - d)

/-- The same summand after collecting factorials as in the ZIP proof. -/
def qReducedSummand (n a b c d : ℕ) : ℚ :=
  let r := a + b + c + d
  let q := a + 2 * b + 3 * c + 4 * d
  qFactorial (5 * n) / qFactorial n ^ 4 *
    ((-1 : ℚ) ^ r * qFactorial r / qFactorial (n + r + 1) *
      qBinomial n a * qBinomial n b * qBinomial n c * qBinomial n d *
      qBinomial (20 * n + 2 - q) (5 * n))

/-- The numerator index in the specialized hyper-Catalan term. -/
theorem specialized_numerator_index (n a b c d : ℕ)
    (ha : a ≤ n) (hb : b ≤ n) (hc : c ≤ n) (hd : d ≤ n) :
    2 * (n + 1 + a + b + c + d) + 3 * (n - a) + 4 * (n - b) +
        5 * (n - c) + 6 * (n - d) =
      20 * n + 2 - (a + 2 * b + 3 * c + 4 * d) := by
  omega

/-- The long-factorial index in the specialized hyper-Catalan term. -/
theorem specialized_long_index (n a b c d : ℕ)
    (ha : a ≤ n) (hb : b ≤ n) (hc : c ≤ n) (hd : d ≤ n) :
    1 + (n + 1 + a + b + c + d) + 2 * (n - a) + 3 * (n - b) +
        4 * (n - c) + 5 * (n - d) =
      15 * n + 2 - (a + 2 * b + 3 * c + 4 * d) := by
  omega

/-- The complementary binomial index is the hyper-Catalan long index. -/
theorem specialized_binomial_complement (n a b c d : ℕ)
    (ha : a ≤ n) (hb : b ≤ n) (hc : c ≤ n) (hd : d ≤ n) :
    (20 * n + 2 - (a + 2 * b + 3 * c + 4 * d)) - 5 * n =
      15 * n + 2 - (a + 2 * b + 3 * c + 4 * d) := by
  omega

/--
The factorial identity at the heart of the alternating-sum-to-moment reduction.
No combinatorics or analysis is used here.
-/
theorem qAlternatingSummand_eq_qReducedSummand (n a b c d : ℕ)
    (ha : a ≤ n) (hb : b ≤ n) (hc : c ≤ n) (hd : d ≤ n) :
    qAlternatingSummand n a b c d = qReducedSummand n a b c d := by
  have hnum := specialized_numerator_index n a b c d ha hb hc hd
  have hlong := specialized_long_index n a b c d ha hb hc hd
  have hcomp := specialized_binomial_complement n a b c d ha hb hc hd
  simp only [qAlternatingSummand, qReducedSummand, qHyperCatalan5,
    qMultinomial4, qBinomial]
  rw [hnum, hlong, hcomp]
  field_simp [qFactorial]
  ring

#print axioms qAlternatingSummand_eq_qReducedSummand

end Arxiv.«2508.10245».Geode5Proof
