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

import ChompKernelCertificate

/-!
# Certified P-sets give genuine normal-play outcome proofs

For a progressively bounded game, a predicate is the losing-position predicate when

* no position satisfying it can move to another position satisfying it; and
* every position not satisfying it has a move to a position satisfying it.

The local form additionally restricts those obligations to a move-closed domain.  This is the
form needed by the concrete Chomp certificate: only the finite descendant domain of the three
10 × 42 children must be represented by the symbolic decision diagram.
-/

namespace ChompKernel
namespace RankedGame

variable {P : Type} {G : RankedGame P}

/-- A predicate satisfying the two global P-position conditions produces actual losing and
winning proof objects for every ranked game position. -/
theorem outcomes_of_pSet
    (S : P → Prop)
    (no_move : ∀ {p : P}, S p → ∀ q, G.Move p q → ¬S q)
    (has_reply : ∀ {p : P}, ¬S p → ∃ q, G.Move p q ∧ S q) :
    ∀ p : P, (S p → Outcome G.Move p false) ∧ (¬S p → Outcome G.Move p true) := by
  intro p
  have all : ∀ k : ℕ, ∀ p : P, G.rank p = k →
      (S p → Outcome G.Move p false) ∧ (¬S p → Outcome G.Move p true) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro p hrank
        constructor
        · intro hp
          exact Outcome.losing (fun q hmove ↦ by
            have hnq : ¬S q := no_move hp q hmove
            have hlt : G.rank q < k := by
              simpa [← hrank] using G.decreases hmove
            exact (ih _ hlt q rfl).2 hnq)
        · intro hnp
          obtain ⟨q, hmove, hq⟩ := has_reply hnp
          have hlt : G.rank q < k := by
            simpa [← hrank] using G.decreases hmove
          exact Outcome.winning hmove ((ih _ hlt q rfl).1 hq)
  exact all _ p rfl

/-- Membership in a certified global P-set gives a kernel-checked losing proof. -/
theorem losing_of_pSet
    (S : P → Prop)
    (no_move : ∀ {p : P}, S p → ∀ q, G.Move p q → ¬S q)
    (has_reply : ∀ {p : P}, ¬S p → ∃ q, G.Move p q ∧ S q)
    {p : P} (hp : S p) : IsLosing G.Move p := by
  exact ⟨(outcomes_of_pSet S no_move has_reply p).1 hp⟩

/-- Nonmembership in a certified global P-set gives a kernel-checked winning proof. -/
theorem winning_of_not_pSet
    (S : P → Prop)
    (no_move : ∀ {p : P}, S p → ∀ q, G.Move p q → ¬S q)
    (has_reply : ∀ {p : P}, ¬S p → ∃ q, G.Move p q ∧ S q)
    {p : P} (hp : ¬S p) : IsWinning G.Move p := by
  exact ⟨(outcomes_of_pSet S no_move has_reply p).2 hp⟩

/-- A P-set certificate restricted to a move-closed domain still reconstructs genuine outcomes
for every position in that domain. -/
theorem outcomes_of_local_pSet
    (D S : P → Prop)
    (closed : ∀ {p q : P}, D p → G.Move p q → D q)
    (no_move : ∀ {p : P}, D p → S p → ∀ q, G.Move p q → ¬S q)
    (has_reply : ∀ {p : P}, D p → ¬S p → ∃ q, G.Move p q ∧ S q) :
    ∀ p : P, D p →
      (S p → Outcome G.Move p false) ∧ (¬S p → Outcome G.Move p true) := by
  intro p hpD
  have all : ∀ k : ℕ, ∀ p : P, G.rank p = k → D p →
      (S p → Outcome G.Move p false) ∧ (¬S p → Outcome G.Move p true) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro p hrank hpD
        constructor
        · intro hp
          exact Outcome.losing (fun q hmove ↦ by
            have hqD : D q := closed hpD hmove
            have hnq : ¬S q := no_move hpD hp q hmove
            have hlt : G.rank q < k := by
              simpa [← hrank] using G.decreases hmove
            exact (ih _ hlt q rfl hqD).2 hnq)
        · intro hnp
          obtain ⟨q, hmove, hq⟩ := has_reply hpD hnp
          have hqD : D q := closed hpD hmove
          have hlt : G.rank q < k := by
            simpa [← hrank] using G.decreases hmove
          exact Outcome.winning hmove ((ih _ hlt q rfl hqD).1 hq)
  exact all _ p rfl hpD

/-- Membership in a locally certified P-set gives a kernel-checked losing proof. -/
theorem losing_of_local_pSet
    (D S : P → Prop)
    (closed : ∀ {p q : P}, D p → G.Move p q → D q)
    (no_move : ∀ {p : P}, D p → S p → ∀ q, G.Move p q → ¬S q)
    (has_reply : ∀ {p : P}, D p → ¬S p → ∃ q, G.Move p q ∧ S q)
    {p : P} (hpD : D p) (hp : S p) : IsLosing G.Move p := by
  exact ⟨(outcomes_of_local_pSet D S closed no_move has_reply p hpD).1 hp⟩

/-- Nonmembership in a locally certified P-set gives a kernel-checked winning proof. -/
theorem winning_of_not_local_pSet
    (D S : P → Prop)
    (closed : ∀ {p q : P}, D p → G.Move p q → D q)
    (no_move : ∀ {p : P}, D p → S p → ∀ q, G.Move p q → ¬S q)
    (has_reply : ∀ {p : P}, D p → ¬S p → ∃ q, G.Move p q ∧ S q)
    {p : P} (hpD : D p) (hp : ¬S p) : IsWinning G.Move p := by
  exact ⟨(outcomes_of_local_pSet D S closed no_move has_reply p hpD).2 hp⟩

#print axioms outcomes_of_pSet
#print axioms losing_of_pSet
#print axioms winning_of_not_pSet
#print axioms outcomes_of_local_pSet
#print axioms losing_of_local_pSet
#print axioms winning_of_not_local_pSet

end RankedGame
end ChompKernel
