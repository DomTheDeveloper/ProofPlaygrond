import Mathlib

/-!
# Exact polynomial sums used by the all-n line cover
-/

namespace Checkerboard

open scoped BigOperators

/-- Sum of an affine square over `0, …, n-1`. -/
theorem sum_range_affine_sq (n : ℕ) (a b : ℚ) :
    (∑ i ∈ Finset.range n, (a * (i : ℚ) + b) ^ 2) =
      a ^ 2 * ((n : ℚ) * ((n : ℚ) - 1) * (2 * (n : ℚ) - 1) / 6) +
      2 * a * b * ((n : ℚ) * ((n : ℚ) - 1) / 2) +
      (n : ℚ) * b ^ 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- Sum of a quadratic cap centered at `N` on the full interval `0, …, 2N`. -/
theorem sum_range_quadratic_cap (N : ℕ) :
    (∑ j ∈ Finset.range (2 * N + 1),
      2 * ((N : ℚ) ^ 2 - ((j : ℚ) - N) ^ 2)) =
      2 * (N : ℚ) * (2 * (N : ℚ) - 1) * (2 * (N : ℚ) + 1) / 3 := by
  have h := sum_range_affine_sq (2 * N + 1) (1 : ℚ) (-(N : ℚ))
  push_cast at h
  have hsum :
      (∑ j ∈ Finset.range (2 * N + 1), ((j : ℚ) - N) ^ 2) =
        ∑ j ∈ Finset.range (2 * N + 1),
          ((1 : ℚ) * (j : ℚ) + (-(N : ℚ))) ^ 2 := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  calc
    (∑ j ∈ Finset.range (2 * N + 1),
      2 * ((N : ℚ) ^ 2 - ((j : ℚ) - N) ^ 2)) =
        2 * (∑ j ∈ Finset.range (2 * N + 1),
          ((N : ℚ) ^ 2 - ((j : ℚ) - N) ^ 2)) := by
          rw [Finset.mul_sum]
    _ = 2 * ((2 * (N : ℚ) + 1) * (N : ℚ) ^ 2 -
          ∑ j ∈ Finset.range (2 * N + 1), ((j : ℚ) - N) ^ 2) := by
          rw [Finset.sum_sub_distrib]
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
    _ = 2 * (N : ℚ) * (2 * (N : ℚ) - 1) *
          (2 * (N : ℚ) + 1) / 3 := by
          rw [hsum, h]
          ring

/-- Extract the even-indexed terms from a range of even length. -/
theorem sum_range_even_terms (k : ℕ) (f : ℕ → ℚ) :
    (∑ j ∈ Finset.range (2 * k), if j % 2 = 0 then f j else 0) =
      ∑ r ∈ Finset.range k, f (2 * r) := by
  induction k with
  | zero => simp
  | succ k ih =>
      simp only [Nat.mul_succ, Finset.sum_range_succ]
      rw [ih]
      norm_num [Nat.add_mod, Nat.mul_mod]

/-- Extract the odd-indexed terms from a range of even length. -/
theorem sum_range_odd_terms (k : ℕ) (f : ℕ → ℚ) :
    (∑ j ∈ Finset.range (2 * k), if j % 2 = 1 then f j else 0) =
      ∑ r ∈ Finset.range k, f (2 * r + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
      simp only [Nat.mul_succ, Finset.sum_range_succ]
      rw [ih]
      norm_num [Nat.add_mod, Nat.mul_mod]

/-- Even-indexed terms in a range ending at an even index. -/
theorem sum_range_even_terms_succ (k : ℕ) (f : ℕ → ℚ) :
    (∑ j ∈ Finset.range (2 * k + 1), if j % 2 = 0 then f j else 0) =
      ∑ r ∈ Finset.range (k + 1), f (2 * r) := by
  rw [Finset.sum_range_succ, sum_range_even_terms, Finset.sum_range_succ]
  norm_num [Nat.add_mod, Nat.mul_mod]

/-- Odd-indexed terms in a range ending at an even index. -/
theorem sum_range_odd_terms_succ (k : ℕ) (f : ℕ → ℚ) :
    (∑ j ∈ Finset.range (2 * k + 1), if j % 2 = 1 then f j else 0) =
      ∑ r ∈ Finset.range k, f (2 * r + 1) := by
  rw [Finset.sum_range_succ, sum_range_odd_terms]
  norm_num [Nat.add_mod, Nat.mul_mod]

/-- Even offsets in the quadratic cap on `-2m, …, 2m`. -/
theorem even_quadratic_cap_sum (m : ℕ) :
    (∑ j ∈ Finset.range (4 * m + 1),
      if j % 2 = 0 then
        2 * ((2 * m : ℚ) ^ 2 - ((j : ℚ) - 2 * m) ^ 2)
      else 0) =
      8 * (m : ℚ) * (2 * (m : ℚ) - 1) *
        (2 * (m : ℚ) + 1) / 3 := by
  have h := sum_range_quadratic_cap m
  rw [show 4 * m + 1 = 2 * (2 * m) + 1 by omega,
    sum_range_even_terms_succ]
  push_cast
  calc
    (∑ r ∈ Finset.range (2 * m + 1),
      2 * ((2 * (m : ℚ)) ^ 2 -
        (2 * (r : ℚ) - 2 * (m : ℚ)) ^ 2)) =
        4 * (∑ r ∈ Finset.range (2 * m + 1),
          2 * ((m : ℚ) ^ 2 - ((r : ℚ) - m) ^ 2)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r _
          ring
    _ = 8 * (m : ℚ) * (2 * (m : ℚ) - 1) *
          (2 * (m : ℚ) + 1) / 3 := by
          rw [h]
          ring

/-- Odd offsets in the quadratic cap on `-2m, …, 2m`. -/
theorem odd_quadratic_cap_sum (m : ℕ) :
    (∑ j ∈ Finset.range (4 * m + 1),
      if j % 2 = 1 then
        2 * ((2 * m : ℚ) ^ 2 - ((j : ℚ) - 2 * m) ^ 2)
      else 0) =
      4 * (m : ℚ) * (8 * (m : ℚ) ^ 2 + 1) / 3 := by
  rw [show 4 * m + 1 = 2 * (2 * m) + 1 by omega,
    sum_range_odd_terms_succ]
  have h := sum_range_affine_sq (2 * m) (2 : ℚ)
    (1 - 2 * (m : ℚ))
  push_cast at h
  simp_rw [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  calc
    (∑ r ∈ Finset.range (2 * m),
      2 * ((2 * (m : ℚ)) ^ 2 -
        (2 * (r : ℚ) + 1 - 2 * (m : ℚ)) ^ 2)) =
        2 * (∑ r ∈ Finset.range (2 * m),
          ((2 * (m : ℚ)) ^ 2 -
            (2 * (r : ℚ) + 1 - 2 * (m : ℚ)) ^ 2)) := by
          rw [Finset.mul_sum]
    _ = 2 * ((2 * (m : ℚ)) * (2 * (m : ℚ)) ^ 2 -
          ∑ r ∈ Finset.range (2 * m),
            (2 * (r : ℚ) + (1 - 2 * (m : ℚ))) ^ 2) := by
          rw [Finset.sum_sub_distrib]
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
    _ = 4 * (m : ℚ) * (8 * (m : ℚ) ^ 2 + 1) / 3 := by
      rw [h]
      ring

end Checkerboard
