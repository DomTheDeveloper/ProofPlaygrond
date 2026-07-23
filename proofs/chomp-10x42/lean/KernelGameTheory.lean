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
# Determinacy of progressively bounded normal-play games

No finite-branching assumption is needed: classical excluded middle selects whether a position
has a losing child, and the natural rank makes the recursive outcome proof well founded.
-/

namespace ChompKernel

namespace Outcome

variable {P : Type} {Move : P → P → Prop} {p : P}

/-- A losing proof supplies a winning proof for every child. -/
theorem children (h : Outcome Move p false) : ∀ q, Move p q → Outcome Move q true := by
  cases h with
  | losing children => exact children

/-- A winning proof supplies one legal losing reply. -/
theorem reply (h : Outcome Move p true) : ∃ q, Move p q ∧ Outcome Move q false := by
  cases h with
  | winning move child => exact ⟨_, move, child⟩

end Outcome

namespace RankedGame

variable {P : Type} (G : RankedGame P)

/-- Every position in a progressively bounded normal-play game is losing or winning. -/
theorem outcome_total (p : P) : Outcome G.Move p false ∨ Outcome G.Move p true := by
  have all : ∀ k : ℕ, ∀ p : P, G.rank p = k →
      Outcome G.Move p false ∨ Outcome G.Move p true := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro p hrank
        by_cases hasLosingChild : ∃ q, G.Move p q ∧ Outcome G.Move q false
        · obtain ⟨q, hmove, hq⟩ := hasLosingChild
          exact Or.inr (Outcome.winning hmove hq)
        · apply Or.inl
          exact Outcome.losing (fun q hmove ↦ by
            have hlt : G.rank q < k := by
              simpa [← hrank] using G.decreases hmove
            rcases ih _ hlt q rfl with hq | hq
            · exact (hasLosingChild ⟨q, hmove, hq⟩).elim
            · exact hq)
  exact all _ p rfl

/-- A position cannot be both losing and winning. -/
theorem outcome_exclusive (p : P) :
    ¬(Outcome G.Move p false ∧ Outcome G.Move p true) := by
  have all : ∀ k : ℕ, ∀ p : P, G.rank p = k →
      ¬(Outcome G.Move p false ∧ Outcome G.Move p true) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro p hrank hboth
        rcases hboth with ⟨hlosing, hwinning⟩
        obtain ⟨q, hmove, hqLosing⟩ := hwinning.reply
        have hqWinning := hlosing.children q hmove
        have hlt : G.rank q < k := by
          simpa [← hrank] using G.decreases hmove
        exact ih _ hlt q rfl ⟨hqLosing, hqWinning⟩
  exact all _ p rfl

/-- A losing proof rules out every winning proof of the same position. -/
theorem not_winning_of_losing {p : P} (h : Outcome G.Move p false) :
    ¬Outcome G.Move p true := by
  intro hw
  exact G.outcome_exclusive p ⟨h, hw⟩

/-- A winning proof rules out every losing proof of the same position. -/
theorem not_losing_of_winning {p : P} (h : Outcome G.Move p true) :
    ¬Outcome G.Move p false := by
  intro hl
  exact G.outcome_exclusive p ⟨hl, h⟩

#print axioms outcome_total
#print axioms outcome_exclusive
#print axioms not_winning_of_losing
#print axioms not_losing_of_winning

end RankedGame
end ChompKernel
