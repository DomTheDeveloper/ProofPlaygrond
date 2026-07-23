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
# Sparse remainder tables for the Geode5 recurrence

The five lists below are the exact `R0`, ..., `R4` tables from the supplied C++
certificate. Each entry `(src, shift, coefficient)` represents
`coefficient * y^shift * t^src`. The table metadata is checked by computation,
and the generated polynomial is proved equal to the symbolic remainder.
-/

namespace Arxiv.«2508.10245».Geode5Proof

noncomputable section

structure SparseTerm where
  source : ℕ
  shift : ℕ
  coefficient : ℤ
  deriving DecidableEq, Repr

private def y : YPoly := Polynomial.X
private def t : TYPoly := Polynomial.X

/-- Interpret a sparse C++ table as a nested polynomial. -/
def sparsePolynomial (terms : List SparseTerm) : TYPoly :=
  terms.foldr (fun a p =>
    Polynomial.C (a.coefficient * y ^ a.shift) * t ^ a.source + p) 0

/-- Sparse remainder table `R0` from the certificate. -/
def r0Terms : List SparseTerm := [
  ⟨0, 10, -5⟩, ⟨1, 10, 4⟩, ⟨1, 9, 4⟩, ⟨1, 8, 4⟩, ⟨1, 7, 4⟩,
  ⟨1, 6, 4⟩, ⟨2, 9, -3⟩, ⟨2, 8, -3⟩, ⟨2, 7, -6⟩, ⟨2, 6, -6⟩,
  ⟨2, 5, -6⟩, ⟨2, 4, -3⟩, ⟨2, 3, -3⟩, ⟨3, 7, 2⟩, ⟨3, 6, 2⟩,
  ⟨3, 5, 4⟩, ⟨3, 4, 4⟩, ⟨3, 3, 4⟩, ⟨3, 2, 2⟩, ⟨3, 1, 2⟩,
  ⟨4, 4, -1⟩, ⟨4, 3, -1⟩, ⟨4, 2, -1⟩, ⟨4, 1, -1⟩, ⟨4, 0, -1⟩]

/-- Sparse remainder table `R1` from the certificate. -/
def r1Terms : List SparseTerm := [
  ⟨0, 14, -1⟩, ⟨0, 13, -1⟩, ⟨0, 12, -1⟩, ⟨0, 11, -1⟩, ⟨0, 10, -1⟩,
  ⟨1, 14, 1⟩, ⟨1, 13, 2⟩, ⟨1, 12, 3⟩, ⟨1, 11, 4⟩, ⟨1, 9, 4⟩,
  ⟨1, 8, 3⟩, ⟨1, 7, 2⟩, ⟨1, 6, 1⟩, ⟨2, 13, -1⟩, ⟨2, 12, -2⟩,
  ⟨2, 11, -4⟩, ⟨2, 10, -2⟩, ⟨2, 9, -4⟩, ⟨2, 8, -4⟩, ⟨2, 7, -4⟩,
  ⟨2, 6, -2⟩, ⟨2, 5, -4⟩, ⟨2, 4, -2⟩, ⟨2, 3, -1⟩, ⟨3, 11, 1⟩,
  ⟨3, 10, 2⟩, ⟨3, 9, 1⟩, ⟨3, 8, 3⟩, ⟨3, 7, 2⟩, ⟨3, 6, 2⟩,
  ⟨3, 5, 2⟩, ⟨3, 4, 3⟩, ⟨3, 3, 1⟩, ⟨3, 2, 2⟩, ⟨3, 1, 1⟩,
  ⟨4, 8, -1⟩, ⟨4, 6, -1⟩, ⟨4, 4, -1⟩, ⟨4, 2, -1⟩, ⟨4, 0, -1⟩]

/-- Sparse remainder table `R2` from the certificate. -/
def r2Terms : List SparseTerm := [
  ⟨0, 18, -1⟩, ⟨0, 16, -1⟩, ⟨0, 14, -1⟩, ⟨0, 12, -1⟩, ⟨0, 10, -1⟩,
  ⟨1, 18, 1⟩, ⟨1, 17, 1⟩, ⟨1, 16, 2⟩, ⟨1, 15, 2⟩, ⟨1, 14, 2⟩,
  ⟨1, 13, 1⟩, ⟨1, 12, 2⟩, ⟨1, 11, 1⟩, ⟨1, 10, 2⟩, ⟨1, 9, 2⟩,
  ⟨1, 8, 2⟩, ⟨1, 7, 1⟩, ⟨1, 6, 1⟩, ⟨2, 17, -1⟩, ⟨2, 16, -1⟩,
  ⟨2, 15, -3⟩, ⟨2, 14, -2⟩, ⟨2, 13, -3⟩, ⟨2, 12, -1⟩, ⟨2, 11, -2⟩,
  ⟨2, 10, -4⟩, ⟨2, 9, -2⟩, ⟨2, 8, -1⟩, ⟨2, 7, -3⟩, ⟨2, 6, -2⟩,
  ⟨2, 5, -3⟩, ⟨2, 4, -1⟩, ⟨2, 3, -1⟩, ⟨3, 15, 1⟩, ⟨3, 14, 1⟩,
  ⟨3, 13, 2⟩, ⟨3, 12, 1⟩, ⟨3, 11, 1⟩, ⟨3, 10, 2⟩, ⟨3, 9, 2⟩,
  ⟨3, 7, 2⟩, ⟨3, 6, 2⟩, ⟨3, 5, 1⟩, ⟨3, 4, 1⟩, ⟨3, 3, 2⟩,
  ⟨3, 2, 1⟩, ⟨3, 1, 1⟩, ⟨4, 12, -1⟩, ⟨4, 9, -1⟩, ⟨4, 6, -1⟩,
  ⟨4, 3, -1⟩, ⟨4, 0, -1⟩]

/-- Sparse remainder table `R3` from the certificate. -/
def r3Terms : List SparseTerm := [
  ⟨0, 22, -1⟩, ⟨0, 19, -1⟩, ⟨0, 16, -1⟩, ⟨0, 13, -1⟩, ⟨0, 10, -1⟩,
  ⟨1, 22, 1⟩, ⟨1, 21, 1⟩, ⟨1, 20, 1⟩, ⟨1, 19, 2⟩, ⟨1, 18, 1⟩,
  ⟨1, 17, 1⟩, ⟨1, 16, 1⟩, ⟨1, 15, 2⟩, ⟨1, 13, 2⟩, ⟨1, 12, 1⟩,
  ⟨1, 11, 1⟩, ⟨1, 10, 1⟩, ⟨1, 9, 2⟩, ⟨1, 8, 1⟩, ⟨1, 7, 1⟩,
  ⟨1, 6, 1⟩, ⟨2, 21, -1⟩, ⟨2, 20, -1⟩, ⟨2, 19, -2⟩, ⟨2, 18, -2⟩,
  ⟨2, 17, -2⟩, ⟨2, 16, -1⟩, ⟨2, 15, -2⟩, ⟨2, 14, -1⟩, ⟨2, 13, -2⟩,
  ⟨2, 12, -2⟩, ⟨2, 11, -2⟩, ⟨2, 10, -1⟩, ⟨2, 9, -2⟩, ⟨2, 8, -1⟩,
  ⟨2, 7, -2⟩, ⟨2, 6, -2⟩, ⟨2, 5, -2⟩, ⟨2, 4, -1⟩, ⟨2, 3, -1⟩,
  ⟨3, 19, 1⟩, ⟨3, 18, 1⟩, ⟨3, 17, 1⟩, ⟨3, 16, 2⟩, ⟨3, 14, 1⟩,
  ⟨3, 13, 1⟩, ⟨3, 12, 2⟩, ⟨3, 11, 1⟩, ⟨3, 9, 1⟩, ⟨3, 8, 2⟩,
  ⟨3, 7, 1⟩, ⟨3, 6, 1⟩, ⟨3, 4, 2⟩, ⟨3, 3, 1⟩, ⟨3, 2, 1⟩,
  ⟨3, 1, 1⟩, ⟨4, 16, -1⟩, ⟨4, 12, -1⟩, ⟨4, 8, -1⟩, ⟨4, 4, -1⟩,
  ⟨4, 0, -1⟩]

/-- Sparse remainder table `R4` from the certificate. -/
def r4Terms : List SparseTerm := [
  ⟨0, 26, -1⟩, ⟨0, 22, -1⟩, ⟨0, 18, -1⟩, ⟨0, 14, -1⟩, ⟨0, 10, -1⟩,
  ⟨1, 26, 1⟩, ⟨1, 25, 1⟩, ⟨1, 24, 1⟩, ⟨1, 23, 1⟩, ⟨1, 22, 1⟩,
  ⟨1, 21, 1⟩, ⟨1, 20, 1⟩, ⟨1, 18, 2⟩, ⟨1, 17, 1⟩, ⟨1, 15, 1⟩,
  ⟨1, 14, 2⟩, ⟨1, 12, 1⟩, ⟨1, 11, 1⟩, ⟨1, 10, 1⟩, ⟨1, 9, 1⟩,
  ⟨1, 8, 1⟩, ⟨1, 7, 1⟩, ⟨1, 6, 1⟩, ⟨2, 25, -1⟩, ⟨2, 24, -1⟩,
  ⟨2, 23, -2⟩, ⟨2, 22, -1⟩, ⟨2, 21, -2⟩, ⟨2, 20, -1⟩, ⟨2, 19, -1⟩,
  ⟨2, 18, -1⟩, ⟨2, 17, -2⟩, ⟨2, 16, -1⟩, ⟨2, 15, -1⟩, ⟨2, 14, -2⟩,
  ⟨2, 13, -1⟩, ⟨2, 12, -1⟩, ⟨2, 11, -2⟩, ⟨2, 10, -1⟩, ⟨2, 9, -1⟩,
  ⟨2, 8, -1⟩, ⟨2, 7, -2⟩, ⟨2, 6, -1⟩, ⟨2, 5, -2⟩, ⟨2, 4, -1⟩,
  ⟨2, 3, -1⟩, ⟨3, 23, 1⟩, ⟨3, 22, 1⟩, ⟨3, 21, 1⟩, ⟨3, 20, 1⟩,
  ⟨3, 19, 1⟩, ⟨3, 17, 1⟩, ⟨3, 16, 1⟩, ⟨3, 15, 1⟩, ⟨3, 14, 1⟩,
  ⟨3, 13, 1⟩, ⟨3, 11, 1⟩, ⟨3, 10, 1⟩, ⟨3, 9, 1⟩, ⟨3, 8, 1⟩,
  ⟨3, 7, 1⟩, ⟨3, 5, 1⟩, ⟨3, 4, 1⟩, ⟨3, 3, 1⟩, ⟨3, 2, 1⟩,
  ⟨3, 1, 1⟩, ⟨4, 20, -1⟩, ⟨4, 15, -1⟩, ⟨4, 10, -1⟩, ⟨4, 5, -1⟩,
  ⟨4, 0, -1⟩]

/-- All table source moment indices are valid. -/
theorem remainderTable_sources_valid :
    (∀ a ∈ r0Terms, a.source < 5) ∧
    (∀ a ∈ r1Terms, a.source < 5) ∧
    (∀ a ∈ r2Terms, a.source < 5) ∧
    (∀ a ∈ r3Terms, a.source < 5) ∧
    (∀ a ∈ r4Terms, a.source < 5) := by
  native_decide

/-- The exact maximum polynomial shifts used by the five rows. -/
theorem remainderTable_shift_bounds :
    (∀ a ∈ r0Terms, a.shift ≤ 10) ∧
    (∀ a ∈ r1Terms, a.shift ≤ 14) ∧
    (∀ a ∈ r2Terms, a.shift ≤ 18) ∧
    (∀ a ∈ r3Terms, a.shift ≤ 22) ∧
    (∀ a ∈ r4Terms, a.shift ≤ 26) := by
  native_decide

set_option maxHeartbeats 1000000 in
theorem momentRemainder_eq_r0 :
    momentRemainder 1 = sparsePolynomial r0Terms := by
  simp [momentRemainder, geodeKernel, momentQuotient, powerSum,
    sparsePolynomial, r0Terms, y, t, Finset.prod_range_succ,
    Finset.sum_range_succ, Polynomial.derivative_sub,
    Polynomial.derivative_mul, Polynomial.derivative_C,
    Polynomial.derivative_X]
  ring

set_option maxHeartbeats 1000000 in
theorem momentRemainder_eq_r1 :
    momentRemainder 2 = sparsePolynomial r1Terms := by
  simp [momentRemainder, geodeKernel, momentQuotient, powerSum,
    sparsePolynomial, r1Terms, y, t, Finset.prod_range_succ,
    Finset.sum_range_succ, Polynomial.derivative_sub,
    Polynomial.derivative_mul, Polynomial.derivative_C,
    Polynomial.derivative_X]
  ring

set_option maxHeartbeats 1000000 in
theorem momentRemainder_eq_r2 :
    momentRemainder 3 = sparsePolynomial r2Terms := by
  simp [momentRemainder, geodeKernel, momentQuotient, powerSum,
    sparsePolynomial, r2Terms, y, t, Finset.prod_range_succ,
    Finset.sum_range_succ, Polynomial.derivative_sub,
    Polynomial.derivative_mul, Polynomial.derivative_C,
    Polynomial.derivative_X]
  ring

set_option maxHeartbeats 1000000 in
theorem momentRemainder_eq_r3 :
    momentRemainder 4 = sparsePolynomial r3Terms := by
  simp [momentRemainder, geodeKernel, momentQuotient, powerSum,
    sparsePolynomial, r3Terms, y, t, Finset.prod_range_succ,
    Finset.sum_range_succ, Polynomial.derivative_sub,
    Polynomial.derivative_mul, Polynomial.derivative_C,
    Polynomial.derivative_X]
  ring

set_option maxHeartbeats 1000000 in
theorem momentRemainder_eq_r4 :
    momentRemainder 5 = sparsePolynomial r4Terms := by
  simp [momentRemainder, geodeKernel, momentQuotient, powerSum,
    sparsePolynomial, r4Terms, y, t, Finset.prod_range_succ,
    Finset.sum_range_succ, Polynomial.derivative_sub,
    Polynomial.derivative_mul, Polynomial.derivative_C,
    Polynomial.derivative_X]
  ring

#print axioms momentRemainder_eq_r0
#print axioms momentRemainder_eq_r1
#print axioms momentRemainder_eq_r2
#print axioms momentRemainder_eq_r3
#print axioms momentRemainder_eq_r4

end

end Arxiv.«2508.10245».Geode5Proof
