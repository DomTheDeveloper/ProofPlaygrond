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

import FormalConjectures.OEIS.«147983»
import ChompKernelCertificate

/-!
# Chomp is progressively bounded

Every legal bite strictly decreases the total number of remaining squares.  This supplies the
natural-number rank used by the kernel certificate theorem.
-/

namespace OeisA147983

/-- Cutting a suffix never increases its total row length. -/
theorem cutSuffix_sum_le (t : ℕ) : ∀ p : List ℕ, (cutSuffix t p).sum ≤ p.sum
  | [] => by simp [cutSuffix]
  | x :: xs => by
      simpa [cutSuffix] using
        Nat.add_le_add (min_le_left x t) (cutSuffix_sum_le t xs)

/-- A legal bite strictly decreases the total number of remaining squares. -/
theorem bite_sum_lt {p : List ℕ} {i t : ℕ}
    (hi : i < p.length) (ht : t < p.getD i 0) :
    (bite i t p).sum < p.sum := by
  induction i generalizing p with
  | zero =>
      cases p with
      | nil => simp at hi
      | cons x xs =>
          have htx : t < x := by simpa using ht
          have htail := cutSuffix_sum_le t xs
          simp only [bite, cutSuffix, List.sum_cons]
          rw [min_eq_right (Nat.le_of_lt htx)]
          omega
  | succ i ih =>
      cases p with
      | nil => simp at hi
      | cons x xs =>
          have hi' : i < xs.length := by simpa using hi
          have ht' : t < xs.getD i 0 := by simpa using ht
          have hrec := ih (p := xs) hi' ht'
          simpa only [bite, List.sum_cons] using Nat.add_lt_add_left hrec x

/-- Every move in the catalog Chomp relation strictly decreases area. -/
theorem move_sum_lt {p q : List ℕ} (h : Move p q) : q.sum < p.sum := by
  rcases h with ⟨i, t, hi, ht, _, rfl⟩
  exact bite_sum_lt hi ht

/-- The catalog Chomp relation as a progressively bounded ranked game. -/
def rankedGame : ChompKernel.RankedGame (List ℕ) where
  Move := Move
  rank := List.sum
  decreases := move_sum_lt

#print axioms cutSuffix_sum_le
#print axioms bite_sum_lt
#print axioms move_sum_lt

end OeisA147983
