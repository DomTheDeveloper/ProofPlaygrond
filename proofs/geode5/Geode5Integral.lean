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

import FormalConjectures.Arxiv.«2508.10245».Geode5Proof.MomentAlgebra

/-!
# Formal polynomial integration for the Geode moment recurrence

The moment proof only needs integration of a polynomial in `t` from zero to one.
We define that operation algebraically, coefficient by coefficient, over
`Polynomial ℚ`. The map is linear over the coefficient ring `Polynomial ℚ`, so
polynomial coefficients in `y` factor through the integral exactly.
-/

namespace Arxiv.«2508.10245».Geode5Proof

noncomputable section

/-- Polynomials in `y` with rational coefficients. -/
abbrev QYPoly := Polynomial ℚ

/-- Polynomials in `t` with coefficients in `QYPoly`. -/
abbrev TQYPoly := Polynomial QYPoly

/-- Multiplication by the constant polynomial `1 / (n + 1)` on `QYPoly`. -/
def integralWeight (n : ℕ) : QYPoly →ₗ[QYPoly] QYPoly where
  toFun a := Polynomial.C ((n + 1 : ℚ)⁻¹) * a
  map_add' a b := by simp [mul_add]
  map_smul' c a := by
    simp only [smul_eq_mul, RingHom.id_apply]
    ring

/-- Algebraic integral from zero to one in the variable `t`. -/
def integral01 : TQYPoly →ₗ[QYPoly] QYPoly :=
  Polynomial.lsum integralWeight

@[simp]
theorem integralWeight_apply (n : ℕ) (a : QYPoly) :
    integralWeight n a = Polynomial.C ((n + 1 : ℚ)⁻¹) * a := rfl

@[simp]
theorem integral01_monomial (n : ℕ) (a : QYPoly) :
    integral01 (Polynomial.monomial n a) =
      Polynomial.C ((n + 1 : ℚ)⁻¹) * a := by
  simp [integral01, integralWeight]

/-- The algebraic fundamental theorem for polynomial derivatives. -/
theorem integral01_derivative (p : TQYPoly) :
    integral01 p.derivative = p.eval 1 - p.eval 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp [Polynomial.derivative_add, hp, hq, sub_add_sub_comm]
  | monomial n a =>
      cases n with
      | zero => simp
      | succ n =>
          rw [Polynomial.derivative_monomial_succ, integral01_monomial]
          have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
          have hcast :
              (n : QYPoly) + 1 = Polynomial.C ((n : ℚ) + 1) := by
            norm_num
          have hprod :
              ((n : QYPoly) + 1) * Polynomial.C (((n : ℚ) + 1)⁻¹) = 1 := by
            rw [hcast, ← Polynomial.C_mul]
            simp [hn]
          have hboundary :
              Polynomial.eval 1 (Polynomial.monomial (n + 1) a) -
                  Polynomial.eval 0 (Polynomial.monomial (n + 1) a) = a := by
            simp [Polynomial.eval_monomial]
          rw [hboundary]
          calc
            Polynomial.C (((n : ℚ) + 1)⁻¹) *
                (a * ((n : QYPoly) + 1)) =
              a * (((n : QYPoly) + 1) *
                Polynomial.C (((n : ℚ) + 1)⁻¹)) := by ring
            _ = a := by rw [hprod, mul_one]

#print axioms integral01_derivative

end

end Arxiv.«2508.10245».Geode5Proof
