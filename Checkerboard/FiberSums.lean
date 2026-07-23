import Mathlib

/-!
# Exact finite fiber sums

Elementary double-counting lemmas used to pass between sums over selected board
points and sums over rows, columns, or diagonal fibers.
-/

namespace Checkerboard

open scoped BigOperators

section

variable {α β R : Type*} [DecidableEq α] [DecidableEq β]

/-- Cardinality of one fiber of `f` inside `s`. -/
def fiberCard (s : Finset α) (f : α → β) (b : β) : ℕ :=
  (s.filter fun a => f a = b).card

@[simp] theorem fiberCard_empty (f : α → β) (b : β) :
    fiberCard ∅ f b = 0 := by
  simp [fiberCard]

private theorem fiberCard_mul_eq_sum [CommSemiring R]
    (s : Finset α) (f : α → β) (b : β) (g : β → R) :
    (fiberCard s f b : R) * g b =
      ∑ a ∈ s, if f a = b then g b else 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [fiberCard]
  | @insert a s ha ih =>
      by_cases h : f a = b
      · have hnot : a ∉ s.filter fun x => f x = b := by
          intro hmem
          exact ha (Finset.mem_of_mem_filter hmem)
        simp [fiberCard, ha, h, hnot, ih, add_mul]
      · simp [fiberCard, ha, h, ih]

/-- Weighted double counting over all fibers. -/
theorem sum_fiberCard_mul [Fintype β] [CommSemiring R]
    (s : Finset α) (f : α → β) (g : β → R) :
    ∑ b : β, (fiberCard s f b : R) * g b =
      ∑ a ∈ s, g (f a) := by
  classical
  calc
    ∑ b : β, (fiberCard s f b : R) * g b =
        ∑ b : β, ∑ a ∈ s, if f a = b then g b else 0 := by
          apply Finset.sum_congr rfl
          intro b _
          exact fiberCard_mul_eq_sum s f b g
    _ = ∑ a ∈ s, ∑ b : β, if f a = b then g b else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ a ∈ s, g (f a) := by
          apply Finset.sum_congr rfl
          intro a _
          simp

/-- Every element of a finite set belongs to exactly one fiber. -/
theorem sum_fiberCard [Fintype β] (s : Finset α) (f : α → β) :
    ∑ b : β, fiberCard s f b = s.card := by
  simpa using sum_fiberCard_mul (R := ℕ) s f (fun _ => 1)

/-- Unweighted point count as the sum of all fiber counts, cast to a semiring. -/
theorem sum_fiberCard_cast [Fintype β] [CommSemiring R]
    (s : Finset α) (f : α → β) :
    ∑ b : β, (fiberCard s f b : R) = (s.card : R) := by
  simpa using sum_fiberCard_mul (R := R) s f (fun _ => 1)

/-- A pointwise bound on fiber cardinalities sums to a global bound. -/
theorem card_le_sum_capacity [Fintype β]
    (s : Finset α) (f : α → β) (capacity : β → ℕ)
    (hcapacity : ∀ b, fiberCard s f b ≤ capacity b) :
    s.card ≤ ∑ b, capacity b := by
  rw [← sum_fiberCard s f]
  exact Finset.sum_le_sum fun b _ => hcapacity b

/-- Real first moment of natural deficits. -/
theorem sum_defect_mul [Fintype β]
    (s : Finset α) (f : α → β) (capacity : β → ℕ)
    (coordinate : β → ℝ)
    (hcapacity : ∀ b, fiberCard s f b ≤ capacity b) :
    (∑ b, ((capacity b - fiberCard s f b : ℕ) : ℝ) * coordinate b) =
      (∑ b, (capacity b : ℝ) * coordinate b) -
        ∑ a ∈ s, coordinate (f a) := by
  calc
    (∑ b, ((capacity b - fiberCard s f b : ℕ) : ℝ) * coordinate b) =
        ∑ b, ((capacity b : ℝ) - (fiberCard s f b : ℝ)) * coordinate b := by
          apply Finset.sum_congr rfl
          intro b _
          rw [Nat.cast_sub (hcapacity b)]
    _ = (∑ b, (capacity b : ℝ) * coordinate b) -
          ∑ b, (fiberCard s f b : ℝ) * coordinate b := by
          simp only [sub_mul, Finset.sum_sub_distrib]
    _ = (∑ b, (capacity b : ℝ) * coordinate b) -
          ∑ a ∈ s, coordinate (f a) := by
          rw [sum_fiberCard_mul]

/-- Real second moment of natural deficits. -/
theorem sum_defect_mul_sq [Fintype β]
    (s : Finset α) (f : α → β) (capacity : β → ℕ)
    (coordinate : β → ℝ)
    (hcapacity : ∀ b, fiberCard s f b ≤ capacity b) :
    (∑ b, ((capacity b - fiberCard s f b : ℕ) : ℝ) * coordinate b ^ 2) =
      (∑ b, (capacity b : ℝ) * coordinate b ^ 2) -
        ∑ a ∈ s, coordinate (f a) ^ 2 := by
  simpa using sum_defect_mul s f capacity (fun b => coordinate b ^ 2) hcapacity

end

end Checkerboard
