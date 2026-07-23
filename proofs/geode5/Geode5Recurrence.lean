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

import FormalConjectures.Arxiv.«2508.10245».Geode5Proof.Integral

/-!
# The exact five-state Geode moment recurrence

This file proves the integration-by-parts recurrence used by the computational
certificate. The quotient and remainder polynomials are generated symbolically;
no sparse C++ table is assumed.
-/

namespace Arxiv.«2508.10245».Geode5Proof

open scoped BigOperators

noncomputable section

private def qy : QYPoly := Polynomial.X
private def qt : TQYPoly := Polynomial.X

/-- Rational version of `1 + y^d + ... + y^(4d)`. -/
def qPowerSum (d : ℕ) : QYPoly :=
  ∑ w ∈ Finset.range 5, qy ^ (d * w)

/-- Rational Geode kernel `P_y(t)`. -/
def qKernel : TQYPoly :=
  ∏ w ∈ Finset.range 5, (Polynomial.C (qy ^ w) - qt)

/-- Quotient in the division of `t^k P_y'(t)` by `P_y(t)`. -/
def qMomentQuotient (k : ℕ) : TQYPoly :=
  ∑ ell ∈ Finset.range k,
    Polynomial.C (qPowerSum (k - 1 - ell)) * qt ^ ell

/-- Generated remainder in the same division. -/
def qMomentRemainder (k : ℕ) : TQYPoly :=
  qt ^ k * qKernel.derivative - qMomentQuotient k * qKernel

/-- The quotient/remainder identity over rational coefficient polynomials. -/
theorem qMoment_division_identity (k : ℕ) :
    qt ^ k * qKernel.derivative =
      qMomentQuotient k * qKernel + qMomentRemainder k := by
  simp only [qMomentRemainder]
  ring

/-- Evaluation at `t = 1` vanishes because the `w = 0` factor is `1 - t`. -/
theorem qKernel_eval_one : qKernel.eval 1 = 0 := by
  simp [qKernel, qy, qt, Finset.prod_range_succ]

/-- Evaluation at `t = 0` is `y^(0+1+2+3+4) = y^10`. -/
theorem qKernel_eval_zero : qKernel.eval 0 = qy ^ 10 := by
  simp [qKernel, qy, qt, Finset.prod_range_succ]
  ring

/-- The exact polynomial moment `J_{n,k}(y)`. -/
def qMoment (n k : ℕ) : QYPoly :=
  integral01 (qt ^ k * qKernel ^ n)

/-- Initial moment vector `(1, 1/2, ..., 1/5)`. -/
theorem qMoment_zero (k : ℕ) :
    qMoment 0 k = Polynomial.C ((k + 1 : ℚ)⁻¹) := by
  simp [qMoment, qt, integral01_monomial, Polynomial.X_pow_eq_monomial]

/--
Integration by parts followed by the generated quotient/remainder identity.
This is the recurrence before expanding the quotient and remainder coefficients.
-/
theorem qMoment_recurrence_raw (n k : ℕ) (hk : 0 < k) :
    (k : QYPoly) * qMoment (n + 1) (k - 1) +
        (n + 1 : QYPoly) *
          integral01 (qMomentQuotient k * qKernel ^ (n + 1)) =
      -(n + 1 : QYPoly) *
        integral01 (qMomentRemainder k * qKernel ^ n) := by
  have hboundary :
      integral01 ((qt ^ k * qKernel ^ (n + 1)).derivative) = 0 := by
    rw [integral01_derivative]
    simp [Polynomial.eval_mul, qt, qKernel_eval_one, hk.ne']
  have hderiv :
      (qt ^ k * qKernel ^ (n + 1)).derivative =
        (k : QYPoly) • (qt ^ (k - 1) * qKernel ^ (n + 1)) +
          (n + 1 : QYPoly) •
            (qMomentQuotient k * qKernel ^ (n + 1) +
              qMomentRemainder k * qKernel ^ n) := by
    rw [Polynomial.derivative_mul]
    simp only [qt, Polynomial.derivative_X_pow,
      Polynomial.derivative_pow_succ]
    have hdiv := qMoment_division_identity k
    simp only [qt] at hdiv
    simp only [Polynomial.smul_eq_C_mul]
    calc
      Polynomial.C (k : QYPoly) * Polynomial.X ^ (k - 1) *
            qKernel ^ (n + 1) +
          Polynomial.X ^ k *
            (Polynomial.C (n + 1 : QYPoly) * qKernel ^ n *
              qKernel.derivative) =
        Polynomial.C (k : QYPoly) *
            (Polynomial.X ^ (k - 1) * qKernel ^ (n + 1)) +
          Polynomial.C (n + 1 : QYPoly) *
            ((Polynomial.X ^ k * qKernel.derivative) * qKernel ^ n) := by
              ring
      _ = Polynomial.C (k : QYPoly) *
            (Polynomial.X ^ (k - 1) * qKernel ^ (n + 1)) +
          Polynomial.C (n + 1 : QYPoly) *
            ((qMomentQuotient k * qKernel + qMomentRemainder k) *
              qKernel ^ n) := by rw [hdiv]
      _ = Polynomial.C (k : QYPoly) *
            (Polynomial.X ^ (k - 1) * qKernel ^ (n + 1)) +
          Polynomial.C (n + 1 : QYPoly) *
            (qMomentQuotient k * qKernel ^ (n + 1) +
              qMomentRemainder k * qKernel ^ n) := by ring
  rw [hderiv] at hboundary
  simp only [map_add, map_smul, smul_eq_mul] at hboundary
  change
    (k : QYPoly) * integral01 (qt ^ (k - 1) * qKernel ^ (n + 1)) +
        (n + 1 : QYPoly) *
          integral01 (qMomentQuotient k * qKernel ^ (n + 1)) =
      -(n + 1 : QYPoly) *
        integral01 (qMomentRemainder k * qKernel ^ n)
  linear_combination hboundary

#print axioms qMoment_recurrence_raw

end

end Arxiv.«2508.10245».Geode5Proof
