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

import FormalConjectures.Arxiv.«2508.10245».Geode5Proof.Recurrence
import FormalConjectures.Arxiv.«2508.10245».Geode5Proof.RemainderTables

/-!
# Expanded sparse Geode5 moment recurrence

This module proves the generic bridge from the symbolic integration-by-parts
identity to the sparse table update used by the modular evaluator.
-/

namespace Arxiv.«2508.10245».Geode5Proof

open scoped BigOperators

noncomputable section

private def qy : QYPoly := Polynomial.X
private def qt : TQYPoly := Polynomial.X

/-- Interpret an integer sparse table in the rational nested polynomial ring. -/
def qSparsePolynomial (terms : List SparseTerm) : TQYPoly :=
  terms.foldr (fun a p =>
    Polynomial.C (Polynomial.C (a.coefficient : ℚ) * qy ^ a.shift) *
      qt ^ a.source + p) 0

/-- The corresponding sparse linear combination of the five moments. -/
def qSparseMomentSum (terms : List SparseTerm) (n : ℕ) : QYPoly :=
  terms.foldr (fun a p =>
    (Polynomial.C (a.coefficient : ℚ) * qy ^ a.shift) *
      qMoment n a.source + p) 0

/-- Polynomial integration converts a sparse polynomial row into its sparse moment sum. -/
theorem integral01_qSparsePolynomial_mul (terms : List SparseTerm) (n : ℕ) :
    integral01 (qSparsePolynomial terms * qKernel ^ n) =
      qSparseMomentSum terms n := by
  induction terms with
  | nil => simp [qSparsePolynomial, qSparseMomentSum]
  | cons a terms ih =>
      simp only [qSparsePolynomial, qSparseMomentSum, List.foldr_cons]
      rw [add_mul, map_add, ih]
      change
        integral01
            (Polynomial.C
                (Polynomial.C (a.coefficient : ℚ) * qy ^ a.shift) *
              (qt ^ a.source * qKernel ^ n)) +
            qSparseMomentSum terms n =
          (Polynomial.C (a.coefficient : ℚ) * qy ^ a.shift) *
              qMoment n a.source + qSparseMomentSum terms n
      rw [← Polynomial.smul_eq_C_mul, map_smul]
      rfl

/-- Expansion of the Newton power-sum quotient against the moment vector. -/
theorem integral01_qMomentQuotient_mul (n k : ℕ) :
    integral01 (qMomentQuotient k * qKernel ^ n) =
      ∑ ell ∈ Finset.range k,
        qPowerSum (k - 1 - ell) * qMoment n ell := by
  simp only [qMomentQuotient, Finset.sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro ell hell
  rw [mul_assoc]
  change
    integral01
        (Polynomial.C (qPowerSum (k - 1 - ell)) *
          (qt ^ ell * qKernel ^ n)) =
      qPowerSum (k - 1 - ell) * qMoment n ell
  rw [← Polynomial.smul_eq_C_mul, map_smul]
  rfl

/--
Generic sparse recurrence row. Supplying a certified equality between the
symbolic remainder and one of the exact `R0`, ..., `R4` tables yields the same
update equation used by the modular evaluator.
-/
theorem qMoment_recurrence_sparse (n k : ℕ) (hk : 0 < k)
    (terms : List SparseTerm)
    (hrem : qMomentRemainder k = qSparsePolynomial terms) :
    (k : QYPoly) * qMoment (n + 1) (k - 1) +
        (n + 1 : QYPoly) *
          (∑ ell ∈ Finset.range k,
            qPowerSum (k - 1 - ell) * qMoment (n + 1) ell) =
      -(n + 1 : QYPoly) * qSparseMomentSum terms n := by
  rw [← integral01_qMomentQuotient_mul]
  rw [← integral01_qSparsePolynomial_mul]
  rw [← hrem]
  exact qMoment_recurrence_raw n k hk

#print axioms integral01_qSparsePolynomial_mul
#print axioms integral01_qMomentQuotient_mul
#print axioms qMoment_recurrence_sparse

end

end Arxiv.«2508.10245».Geode5Proof
