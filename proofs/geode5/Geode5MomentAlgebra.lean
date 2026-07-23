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

import Mathlib

/-!
# Symbolic moment algebra for the five-dimensional Geode

This file formalizes the symbolic source of the five-state recurrence from the
Geode certificate. The large sparse tables used by the C++ evaluator are not
trusted as primitive data: they are generated from the single polynomial

`P_y(t) = ∏ w ∈ {0,1,2,3,4}, (y^w - t)`.

For `k = 1, ..., 5`, the quotient in the Euclidean division of
`t^k * ∂P/∂t` by `P` is expressed by the power sums
`1 + y^d + y^(2d) + y^(3d) + y^(4d)`. The corresponding remainders have
`t`-degree at most four, which is exactly why five moments suffice.
-/

namespace Arxiv.«2508.10245».Geode5Proof

open scoped BigOperators

/-- Polynomials in the parameter `y`. -/
abbrev YPoly := Polynomial ℤ

/-- Polynomials in `t` whose coefficients are polynomials in `y`. -/
abbrev TYPoly := Polynomial YPoly

private def y : YPoly := Polynomial.X
private def t : TYPoly := Polynomial.X

/-- `1 + y^d + y^(2d) + y^(3d) + y^(4d)`. -/
def powerSum (d : ℕ) : YPoly :=
  ∑ w ∈ Finset.range 5, y ^ (d * w)

/-- The polynomial `P_y(t) = ∏_{w=0}^4 (y^w - t)`. -/
def geodeKernel : TYPoly :=
  ∏ w ∈ Finset.range 5, (Polynomial.C (y ^ w) - t)

/--
The quotient predicted by Newton's identities for the division of
`t^k P_y'(t)` by `P_y(t)`.
-/
def momentQuotient (k : ℕ) : TYPoly :=
  ∑ ell ∈ Finset.range k,
    Polynomial.C (powerSum (k - 1 - ell)) * t ^ ell

/-- The remainder generated from the quotient, rather than copied from a table. -/
def momentRemainder (k : ℕ) : TYPoly :=
  t ^ k * geodeKernel.derivative - momentQuotient k * geodeKernel

/-- The defining quotient/remainder identity. -/
theorem moment_division_identity (k : ℕ) :
    t ^ k * geodeKernel.derivative =
      momentQuotient k * geodeKernel + momentRemainder k := by
  simp only [momentRemainder]
  ring

/-- The zero-th power sum is the constant five. -/
theorem powerSum_zero : powerSum 0 = 5 := by
  native_decide

/-- The five quotient rows used by the lower-triangular recurrence. -/
theorem momentQuotient_rows :
    momentQuotient 1 = 5 ∧
    momentQuotient 2 =
      Polynomial.C (powerSum 1) + 5 * t ∧
    momentQuotient 3 =
      Polynomial.C (powerSum 2) +
        Polynomial.C (powerSum 1) * t + 5 * t ^ 2 ∧
    momentQuotient 4 =
      Polynomial.C (powerSum 3) +
        Polynomial.C (powerSum 2) * t +
        Polynomial.C (powerSum 1) * t ^ 2 + 5 * t ^ 3 ∧
    momentQuotient 5 =
      Polynomial.C (powerSum 4) +
        Polynomial.C (powerSum 3) * t +
        Polynomial.C (powerSum 2) * t ^ 2 +
        Polynomial.C (powerSum 1) * t ^ 3 + 5 * t ^ 4 := by
  native_decide

/-- Every one of the five generated remainders has `t`-degree below five. -/
theorem momentRemainder_degree_bounds :
    (momentRemainder 1).natDegree < 5 ∧
    (momentRemainder 2).natDegree < 5 ∧
    (momentRemainder 3).natDegree < 5 ∧
    (momentRemainder 4).natDegree < 5 ∧
    (momentRemainder 5).natDegree < 5 := by
  native_decide

/-- The constant-in-`t` coefficients satisfy the sparse evaluator's degree bounds. -/
theorem momentRemainder_y_degree_bounds :
    (momentRemainder 1).coeff 0 |>.natDegree ≤ 10 ∧
    (momentRemainder 2).coeff 0 |>.natDegree ≤ 14 ∧
    (momentRemainder 3).coeff 0 |>.natDegree ≤ 18 ∧
    (momentRemainder 4).coeff 0 |>.natDegree ≤ 22 ∧
    (momentRemainder 5).coeff 0 |>.natDegree ≤ 26 := by
  native_decide

/-- Diagonal coefficient in recurrence row `i`, where `i = 0, ..., 4`. -/
def recurrenceDiagonal (n i : ℕ) : ℕ := 5 * n + 6 + i

/-- Every diagonal coefficient is positive, so forward substitution is valid in characteristic zero. -/
theorem recurrenceDiagonal_pos (n i : ℕ) : 0 < recurrenceDiagonal n i := by
  omega

/-- Product of the five diagonal entries, matching the symbolic determinant. -/
theorem recurrenceDiagonal_product (n : ℕ) :
    ∏ i ∈ Finset.range 5, recurrenceDiagonal n i =
      5 * (n + 2) * (5 * n + 6) * (5 * n + 7) *
        (5 * n + 8) * (5 * n + 9) := by
  simp [recurrenceDiagonal]
  ring

/-- Through level 1000, every diagonal is at most 5010. -/
theorem recurrenceDiagonal_le_5010
    (n i : ℕ) (hn : n < 1000) (hi : i < 5) :
    recurrenceDiagonal n i ≤ 5010 := by
  omega

#print axioms moment_division_identity
#print axioms momentQuotient_rows
#print axioms momentRemainder_degree_bounds
#print axioms recurrenceDiagonal_product

end Arxiv.«2508.10245».Geode5Proof
