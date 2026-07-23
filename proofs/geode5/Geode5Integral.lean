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

import Geode5MomentAlgebra

/-!
# Formal polynomial integration for the Geode moment recurrence

The moment proof only needs integration of a polynomial in `t` from zero to one.
We define that operation algebraically, coefficient by coefficient, over
`Polynomial ℚ`. This avoids importing analytic integration and makes the
integration-by-parts argument available over exact rational coefficients.
-/

namespace Arxiv.«2508.10245».Geode5Proof

noncomputable section

/-- Polynomials in `y` with rational coefficients. -/
abbrev QYPoly := Polynomial ℚ

/-- Polynomials in `t` with coefficients in `QYPoly`. -/
abbrev TQYPoly := Polynomial QYPoly

/-- Multiplication by `1 / (n + 1)` on `QYPoly`. -/
def integralWeight (n : ℕ) : QYPoly →ₗ[ℚ] QYPoly where
  toFun a := ((n + 1 : ℚ)⁻¹) • a
  map_add' a b := by simp [smul_add]
  map_smul' c a := by simp [smul_smul, mul_comm]

/-- Algebraic integral from zero to one in the variable `t`. -/
def integral01 : TQYPoly →ₗ[ℚ] QYPoly :=
  Polynomial.lsum integralWeight

@[simp]
theorem integralWeight_apply (n : ℕ) (a : QYPoly) :
    integralWeight n a = ((n + 1 : ℚ)⁻¹) • a := rfl

@[simp]
theorem integral01_monomial (n : ℕ) (a : QYPoly) :
    integral01 (Polynomial.monomial n a) = ((n + 1 : ℚ)⁻¹) • a := by
  simp [integral01, integralWeight]

/-- The algebraic fundamental theorem for polynomial derivatives. -/
theorem integral01_derivative (p : TQYPoly) :
    integral01 p.derivative = p.eval 1 - p.eval 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp [Polynomial.derivative_add, hp, hq, sub_add_sub_comm]
  | monomial n a =>
      cases n with
      | zero => simp [Polynomial.derivative_monomial]
      | succ n =>
          rw [Polynomial.derivative_monomial_succ, integral01_monomial]
          have hn : (n + 1 : ℚ) ≠ 0 := by positivity
          simp [Polynomial.eval_monomial, Algebra.smul_def, hn, mul_comm]

#print axioms integral01_derivative

end

end Arxiv.«2508.10245».Geode5Proof
