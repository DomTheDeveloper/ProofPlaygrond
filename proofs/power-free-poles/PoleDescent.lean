module

public import Init

@[expose] public section

namespace PowerFree

/-- Starting at a zero and ending at a nonzero value produces a first adjacent
zero/nonzero pair. The bound is on the number of scalings, and the starting
zero need not be simple. -/
theorem first_exit {P : Nat → Prop} (start : P 0) {N : Nat} (stop : ¬ P N) :
    ∃ j, j < N ∧ (∀ i, i ≤ j → P i) ∧ ¬ P (j + 1) := by
  classical
  have split : ∀ n : Nat, (∀ i, i ≤ n → P i) ∨
      ∃ j, j < n ∧ (∀ i, i ≤ j → P i) ∧ ¬ P (j + 1) := by
    intro n
    induction n with
    | zero =>
        exact Or.inl (fun i hi ↦ Nat.le_zero.mp hi ▸ start)
    | succ n ih =>
        rcases ih with all | ⟨j, hj, before, after⟩
        · by_cases next : P (n + 1)
          · left
            intro i hi
            rcases Nat.lt_or_eq_of_le hi with h | h
            · exact all i (Nat.le_of_lt_succ h)
            · exact h ▸ next
          · exact Or.inr ⟨n, Nat.lt_succ_self _, all, next⟩
        · exact Or.inr ⟨j, Nat.lt_trans hj (Nat.lt_succ_self _), before, after⟩
  exact (split N).resolve_left (fun all ↦ stop (all N (Nat.le_refl N)))

/-- An exact certificate of a negative quotient order along a sequence of
scalings. At the first nonzero numerator its order is zero, hence the quotient
has the negative of the preceding zero's full order. -/
theorem first_pole_order {P : Nat → Prop} (order : Nat → Int)
    (positive_at_zero : ∀ n, P n → 0 < order n)
    (zero_at_nonzero : ∀ n, ¬ P n → order n = 0)
    (start : P 0) {N : Nat} (stop : ¬ P N) :
    ∃ j, j < N ∧ (∀ i, i ≤ j → P i) ∧ ¬ P (j + 1) ∧
      0 < order j ∧ order (j + 1) - order j = -order j := by
  obtain ⟨j, bound, before, after⟩ := first_exit start stop
  exact ⟨j, bound, before, after, positive_at_zero j (before j (Nat.le_refl j)),
    by rw [zero_at_nonzero _ after, Int.zero_sub]⟩

end PowerFree
