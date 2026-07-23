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

import ChompPosition
import ChompKernelGameTheory

/-!
# Bridge from kernel game outcomes to the catalog P-set definition

The catalog defines a P-position by membership in a global complete P-set.  For a progressively
bounded normal-play game, the set of valid positions having a losing outcome is exactly such a
set.  Thus a finite certificate proving one child losing implies the existing catalog predicate;
the theorem statement does not need to be weakened.
-/

namespace OeisA147983

/-- The global set of valid positions with kernel-checked losing outcomes. -/
def kernelPSet : Set (List ℕ) :=
  {p | IsPosition p ∧ ChompKernel.IsLosing rankedGame.Move p}

/-- The global losing-outcome set is a complete Chomp P-set. -/
theorem kernelPSet_isPSet : IsPSet kernelPSet := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    exact hp.1
  · intro p q hp hmove hq
    rcases hp with ⟨_, ⟨hpLosing⟩⟩
    rcases hq with ⟨_, ⟨hqLosing⟩⟩
    have hqWinning : ChompKernel.Outcome rankedGame.Move q true :=
      hpLosing.children q hmove
    exact rankedGame.outcome_exclusive q ⟨hqLosing, hqWinning⟩
  · intro p hpPosition hpNot
    rcases rankedGame.outcome_total p with hpLosing | hpWinning
    · exact (hpNot ⟨hpPosition, ⟨hpLosing⟩⟩).elim
    · obtain ⟨q, hmove, hqLosing⟩ := hpWinning.reply
      refine ⟨q, ?_, hmove⟩
      exact ⟨move_preserves_position hpPosition hmove, ⟨hqLosing⟩⟩

/-- Every valid position with a losing outcome satisfies the catalog's `IsPPosition`. -/
theorem isPPosition_of_losing {p : List ℕ}
    (hp : IsPosition p) (hlosing : ChompKernel.IsLosing rankedGame.Move p) :
    IsPPosition p := by
  exact ⟨kernelPSet, kernelPSet_isPSet, hp, hlosing⟩

@[category test, AMS 5]
theorem child₁_is_position : IsPosition child₁ := by
  norm_num [IsPosition, IsFerrers, child₁]

@[category test, AMS 5]
theorem child₂_is_position : IsPosition child₂ := by
  norm_num [IsPosition, IsFerrers, child₂]

@[category test, AMS 5]
theorem child₃_is_position : IsPosition child₃ := by
  norm_num [IsPosition, IsFerrers, child₃]

/-- Three kernel losing proofs discharge the catalog theorem without any external axiom. -/
theorem three_openings_of_losing
    (h₁ : ChompKernel.IsLosing rankedGame.Move child₁)
    (h₂ : ChompKernel.IsLosing rankedGame.Move child₂)
    (h₃ : ChompKernel.IsLosing rankedGame.Move child₃) :
    IsWinningOpening rectangle child₁ ∧
      IsWinningOpening rectangle child₂ ∧
      IsWinningOpening rectangle child₃ ∧
      child₁ ≠ child₂ ∧ child₁ ≠ child₃ ∧ child₂ ≠ child₃ := by
  apply three_openings_of_p_positions
  · exact isPPosition_of_losing child₁_is_position h₁
  · exact isPPosition_of_losing child₂_is_position h₂
  · exact isPPosition_of_losing child₃_is_position h₃

#print axioms kernelPSet_isPSet
#print axioms isPPosition_of_losing
#print axioms three_openings_of_losing

end OeisA147983
