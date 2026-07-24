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

import ChompRank

/-!
# Legal Chomp moves preserve the position invariants
-/

namespace OeisA147983

/-- Cutting every row at a fixed threshold preserves the Ferrers inequalities. -/
theorem cutSuffix_isFerrers (t : ℕ) : ∀ {p : List ℕ}, IsFerrers p → IsFerrers (cutSuffix t p)
  | [], h => by simp [IsFerrers] at h
  | [x], _ => by simp [cutSuffix, IsFerrers]
  | x :: y :: xs, h => by
      rcases h with ⟨hyx, htail⟩
      simp only [cutSuffix, IsFerrers]
      exact ⟨min_le_min hyx le_rfl, cutSuffix_isFerrers t htail⟩

/-- Cutting a suffix preserves the number of rows. -/
theorem cutSuffix_length (t : ℕ) : ∀ p : List ℕ,
    (cutSuffix t p).length = p.length
  | [] => by simp [cutSuffix]
  | x :: xs => by simp [cutSuffix, cutSuffix_length t xs]

/-- A bite never increases the first row. -/
theorem bite_head_le (i t : ℕ) : ∀ p : List ℕ,
    (bite i t p).getD 0 0 ≤ p.getD 0 0
  | [] => by simp [bite]
  | x :: xs => by
      cases i <;> simp [bite, cutSuffix]

/-- A bite preserves the number of rows. -/
theorem bite_length (i t : ℕ) (p : List ℕ) :
    (bite i t p).length = p.length := by
  induction i generalizing p with
  | zero =>
      cases p <;> simp [bite, cutSuffix_length]
  | succ i ih =>
      cases p with
      | nil => simp [bite]
      | cons x xs => simp [bite, ih]

/-- A bite preserves the Ferrers inequalities. -/
theorem bite_isFerrers (t : ℕ) : ∀ i : ℕ, ∀ {p : List ℕ},
    IsFerrers p → IsFerrers (bite i t p)
  | 0, [], h => by
      simp [IsFerrers] at h
  | 0, x :: xs, h => by
      simpa [bite] using cutSuffix_isFerrers t h
  | i + 1, [], h => by
      simp [IsFerrers] at h
  | i + 1, [x], _ => by
      simp [bite, IsFerrers]
  | i + 1, x :: y :: xs, h => by
      rcases h with ⟨hyx, htail⟩
      have htailFerrers : IsFerrers (bite i t (y :: xs)) :=
        bite_isFerrers t i htail
      have hhead : (bite i t (y :: xs)).getD 0 0 ≤ x :=
        le_trans (bite_head_le i t (y :: xs)) hyx
      have hnonempty : bite i t (y :: xs) ≠ [] := by
        cases i <;> simp [bite, cutSuffix]
      cases hbite : bite i t (y :: xs) with
      | nil => exact (hnonempty hbite).elim
      | cons z zs =>
          have hz : z ≤ x := by simpa [hbite] using hhead
          simp only [bite, hbite, IsFerrers]
          exact ⟨hz, by simpa [hbite] using htailFerrers⟩

/-- If the poisoned square was present and a first-row move does not take it, the bitten
position still contains the poisoned square. -/
theorem bite_head_pos {p : List ℕ} {i t : ℕ}
    (hp : 0 < p.getD 0 0) (hpoison : i = 0 → 0 < t) :
    0 < (bite i t p).getD 0 0 := by
  cases p with
  | nil => simp at hp
  | cons x xs =>
      have hx : 0 < x := by simpa using hp
      cases i with
      | zero =>
          have ht : 0 < t := hpoison rfl
          simpa [bite, cutSuffix] using (lt_min hx ht)
      | succ i =>
          simpa [bite] using hx

/-- Every legal move from a legal Chomp position produces another legal Chomp position. -/
theorem move_preserves_position {p q : List ℕ}
    (hp : IsPosition p) (hmove : Move p q) : IsPosition q := by
  rcases hp with ⟨hferrers, hpoisoned⟩
  rcases hmove with ⟨i, t, _, _, hpoison, rfl⟩
  exact ⟨bite_isFerrers t i hferrers, bite_head_pos hpoisoned hpoison⟩

/-- The finite symbolic-certificate universe: legal ten-row positions whose first row has width
at most 42. -/
def CertificateDomain (p : List ℕ) : Prop :=
  IsPosition p ∧ p.length = 10 ∧ p.getD 0 0 ≤ 42

/-- The concrete 10 × 42 certificate domain is closed under legal Chomp moves. -/
theorem move_preserves_certificateDomain {p q : List ℕ}
    (hp : CertificateDomain p) (hmove : Move p q) : CertificateDomain q := by
  rcases hp with ⟨hpPosition, hpLength, hpHead⟩
  rcases hmove with ⟨i, t, hi, ht, hpoison, rfl⟩
  refine ⟨move_preserves_position hpPosition ⟨i, t, hi, ht, hpoison, rfl⟩, ?_, ?_⟩
  · calc
      (bite i t p).length = p.length := bite_length i t p
      _ = 10 := hpLength
  · exact (bite_head_le i t p).trans hpHead

#print axioms cutSuffix_isFerrers
#print axioms cutSuffix_length
#print axioms bite_length
#print axioms bite_isFerrers
#print axioms bite_head_pos
#print axioms move_preserves_position
#print axioms move_preserves_certificateDomain

end OeisA147983
