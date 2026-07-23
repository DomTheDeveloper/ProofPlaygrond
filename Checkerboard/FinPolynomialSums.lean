import Checkerboard.PolynomialSums

/-!
# Polynomial sums over `Fin`
-/

namespace Checkerboard

open scoped BigOperators

/-- Sum of an affine square over `Fin n`. -/
theorem sum_fin_affine_sq (n : ℕ) (a b : ℚ) :
    (∑ i : Fin n, (a * (i.1 : ℚ) + b) ^ 2) =
      a ^ 2 * ((n : ℚ) * ((n : ℚ) - 1) * (2 * (n : ℚ) - 1) / 6) +
      2 * a * b * ((n : ℚ) * ((n : ℚ) - 1) / 2) +
      (n : ℚ) * b ^ 2 := by
  rw [Finset.sum_fin_eq_sum_range]
  convert sum_range_affine_sq n a b using 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [dif_pos hi]

/-- Sum of the centered axis-square weights. -/
theorem axis_quadratic_sum (n : ℕ) :
    (∑ i : Fin n, (2 * (i.1 : ℚ) - ((n : ℚ) - 1)) ^ 2) =
      (n : ℚ) * ((n : ℚ) ^ 2 - 1) / 3 := by
  have h := sum_fin_affine_sq n (2 : ℚ) (1 - (n : ℚ))
  calc
    (∑ i : Fin n, (2 * (i.1 : ℚ) - ((n : ℚ) - 1)) ^ 2) =
        ∑ i : Fin n, (2 * (i.1 : ℚ) + (1 - (n : ℚ))) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = 2 ^ 2 * ((n : ℚ) * ((n : ℚ) - 1) * (2 * (n : ℚ) - 1) / 6) +
        2 * 2 * (1 - (n : ℚ)) * ((n : ℚ) * ((n : ℚ) - 1) / 2) +
        (n : ℚ) * (1 - (n : ℚ)) ^ 2 := h
    _ = (n : ℚ) * ((n : ℚ) ^ 2 - 1) / 3 := by ring

/-- Full sum of a quadratic diagonal cap over `Fin (2N+1)`. -/
theorem fin_quadratic_cap_sum (N : ℕ) :
    (∑ j : Fin (2 * N + 1),
      2 * ((N : ℚ) ^ 2 - ((j.1 : ℚ) - N) ^ 2)) =
      2 * (N : ℚ) * (2 * (N : ℚ) - 1) * (2 * (N : ℚ) + 1) / 3 := by
  rw [Finset.sum_fin_eq_sum_range]
  convert sum_range_quadratic_cap N using 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  rw [dif_pos hj]

/-- Even-indexed cap sum over `Fin (4m+1)`. -/
theorem fin_even_quadratic_cap_sum (m : ℕ) :
    (∑ j : Fin (4 * m + 1),
      if j.1 % 2 = 0 then
        2 * ((2 * m : ℚ) ^ 2 - ((j.1 : ℚ) - 2 * m) ^ 2)
      else 0) =
      8 * (m : ℚ) * (2 * (m : ℚ) - 1) *
        (2 * (m : ℚ) + 1) / 3 := by
  rw [Finset.sum_fin_eq_sum_range]
  convert even_quadratic_cap_sum m using 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  rw [dif_pos hj]

/-- Odd-indexed cap sum over `Fin (4m+1)`. -/
theorem fin_odd_quadratic_cap_sum (m : ℕ) :
    (∑ j : Fin (4 * m + 1),
      if j.1 % 2 = 1 then
        2 * ((2 * m : ℚ) ^ 2 - ((j.1 : ℚ) - 2 * m) ^ 2)
      else 0) =
      4 * (m : ℚ) * (8 * (m : ℚ) ^ 2 + 1) / 3 := by
  rw [Finset.sum_fin_eq_sum_range]
  convert odd_quadratic_cap_sum m using 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  rw [dif_pos hj]

end Checkerboard
