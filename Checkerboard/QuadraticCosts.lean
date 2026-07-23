import Checkerboard.QuadraticWeights
import Checkerboard.FinPolynomialSums

/-!
# Exact objectives of the quadratic line covers
-/

namespace Checkerboard

open scoped BigOperators

private def oddCapExpr (m : ℕ) {k : ℕ} (j : Fin k) : ℚ :=
  2 * ((2 * m : ℚ) ^ 2 - ((j.1 : ℚ) - 2 * m) ^ 2)

private def evenCapExpr (m : ℕ) {k : ℕ} (j : Fin k) : ℚ :=
  2 * (((2 * m : ℚ) - 1) ^ 2 -
    ((j.1 : ℚ) - ((2 * m : ℚ) - 1)) ^ 2)

private theorem odd_axis_sum (m : ℕ) :
    (∑ i : Fin (2 * m + 1), (2 * (i.1 : ℚ) - 2 * m) ^ 2) =
      4 * (m : ℚ) * ((m : ℚ) + 1) * (2 * (m : ℚ) + 1) / 3 := by
  have h := axis_quadratic_sum (2 * m + 1)
  push_cast at h ⊢
  convert h using 1 <;> ring

private theorem even_axis_sum (m : ℕ) :
    (∑ i : Fin (2 * m),
      (2 * (i.1 : ℚ) - ((2 * m : ℚ) - 1)) ^ 2) =
      2 * (m : ℚ) * (4 * (m : ℚ) ^ 2 - 1) / 3 := by
  have h := axis_quadratic_sum (2 * m)
  push_cast at h ⊢
  convert h using 1 <;> ring

private theorem odd_even_diag_sum (m : ℕ) :
    (∑ j : Fin (2 * (2 * m + 1) - 1),
      if j.1 % 2 = 0 then oddCapExpr m j else 0) =
      8 * (m : ℚ) * (2 * (m : ℚ) - 1) *
        (2 * (m : ℚ) + 1) / 3 := by
  have hdim : 2 * (2 * m + 1) - 1 = 4 * m + 1 := by omega
  rw [hdim]
  simpa [oddCapExpr] using fin_even_quadratic_cap_sum m

private theorem odd_odd_diag_sum (m : ℕ) :
    (∑ j : Fin (2 * (2 * m + 1) - 1),
      if j.1 % 2 = 1 then oddCapExpr m j else 0) =
      4 * (m : ℚ) * (8 * (m : ℚ) ^ 2 + 1) / 3 := by
  have hdim : 2 * (2 * m + 1) - 1 = 4 * m + 1 := by omega
  rw [hdim]
  simpa [oddCapExpr] using fin_odd_quadratic_cap_sum m

private theorem parity_partition {k : ℕ} (f : Fin k → ℚ) :
    (∑ j : Fin k, if j.1 % 2 = 0 then f j else 0) +
        (∑ j : Fin k, if j.1 % 2 = 1 then f j else 0) =
      ∑ j : Fin k, f j := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rcases Nat.mod_two_eq_zero_or_one j.1 with h | h <;> simp [h]

private theorem even_all_diag_sum (m : ℕ) (hm : 1 ≤ m) :
    (∑ j : Fin (2 * (2 * m) - 1), evenCapExpr m j) =
      2 * ((2 * m : ℚ) - 1) * (4 * (m : ℚ) - 3) *
        (4 * (m : ℚ) - 1) / 3 := by
  have hdim : 2 * (2 * m) - 1 = 2 * (2 * m - 1) + 1 := by omega
  rw [hdim]
  have h := fin_quadratic_cap_sum (2 * m - 1)
  push_cast at h ⊢
  simpa [evenCapExpr] using h

/-- Exact objective for the fat color of an odd board. -/
theorem oddQuadratic_cost_zero (m : ℕ) :
    fourCost (oddQuadraticWeights m 0) =
      16 * (m : ℚ) * (10 * (m : ℚ) ^ 2 + 3 * (m : ℚ) - 1) / 3 := by
  change 2 * (
    (∑ i : Fin (2 * m + 1), (2 * (i.1 : ℚ) - 2 * m) ^ 2) +
    (∑ i : Fin (2 * m + 1), (2 * (i.1 : ℚ) - 2 * m) ^ 2) +
    (∑ j : Fin (2 * (2 * m + 1) - 1),
      if j.1 % 2 = 0 then oddCapExpr m j else 0) +
    (∑ j : Fin (2 * (2 * m + 1) - 1),
      if j.1 % 2 = 0 then oddCapExpr m j else 0)) = _
  rw [odd_axis_sum, odd_axis_sum, odd_even_diag_sum, odd_even_diag_sum]
  ring

/-- Exact objective for the thin color of an odd board. -/
theorem oddQuadratic_cost_one (m : ℕ) :
    fourCost (oddQuadraticWeights m 1) =
      16 * (m : ℚ) * (10 * (m : ℚ) ^ 2 + 3 * (m : ℚ) + 2) / 3 := by
  change 2 * (
    (∑ i : Fin (2 * m + 1), (2 * (i.1 : ℚ) - 2 * m) ^ 2) +
    (∑ i : Fin (2 * m + 1), (2 * (i.1 : ℚ) - 2 * m) ^ 2) +
    (∑ j : Fin (2 * (2 * m + 1) - 1),
      if j.1 % 2 = 1 then oddCapExpr m j else 0) +
    (∑ j : Fin (2 * (2 * m + 1) - 1),
      if j.1 % 2 = 1 then oddCapExpr m j else 0)) = _
  rw [odd_axis_sum, odd_axis_sum, odd_odd_diag_sum, odd_odd_diag_sum]
  ring

/-- Both checkerboard colors have the same objective on an even board. -/
theorem evenQuadratic_cost_zero (m : ℕ) (hm : 1 ≤ m) :
    fourCost (evenQuadraticWeights m 0) =
      4 * ((2 * m : ℚ) - 1) *
        (20 * (m : ℚ) ^ 2 - 14 * (m : ℚ) + 3) / 3 := by
  change 2 * (
    (∑ i : Fin (2 * m),
      (2 * (i.1 : ℚ) - ((2 * m : ℚ) - 1)) ^ 2) +
    (∑ i : Fin (2 * m),
      (2 * (i.1 : ℚ) - ((2 * m : ℚ) - 1)) ^ 2) +
    (∑ j : Fin (2 * (2 * m) - 1),
      if j.1 % 2 = 0 then evenCapExpr m j else 0) +
    (∑ j : Fin (2 * (2 * m) - 1),
      if j.1 % 2 = 1 then evenCapExpr m j else 0)) = _
  rw [even_axis_sum, even_axis_sum,
    parity_partition (fun j : Fin (2 * (2 * m) - 1) => evenCapExpr m j),
    even_all_diag_sum m hm]
  ring

/-- Same objective for the other color of an even board. -/
theorem evenQuadratic_cost_one (m : ℕ) (hm : 1 ≤ m) :
    fourCost (evenQuadraticWeights m 1) =
      4 * ((2 * m : ℚ) - 1) *
        (20 * (m : ℚ) ^ 2 - 14 * (m : ℚ) + 3) / 3 := by
  change 2 * (
    (∑ i : Fin (2 * m),
      (2 * (i.1 : ℚ) - ((2 * m : ℚ) - 1)) ^ 2) +
    (∑ i : Fin (2 * m),
      (2 * (i.1 : ℚ) - ((2 * m : ℚ) - 1)) ^ 2) +
    (∑ j : Fin (2 * (2 * m) - 1),
      if j.1 % 2 = 1 then evenCapExpr m j else 0) +
    (∑ j : Fin (2 * (2 * m) - 1),
      if j.1 % 2 = 0 then evenCapExpr m j else 0)) = _
  rw [even_axis_sum, even_axis_sum]
  have hpartition :=
    parity_partition (fun j : Fin (2 * (2 * m) - 1) => evenCapExpr m j)
  rw [add_comm] at hpartition
  rw [hpartition, even_all_diag_sum m hm]
  ring

end Checkerboard
