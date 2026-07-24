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

import FormalConjecturesUtil

/-!
# Kernel-checked finite game certificates

The certificate producer is untrusted. A certificate contains finitely many nodes, interprets
each node as an actual game position, and proves every edge it uses is a real move. At a
losing-labelled node it must additionally prove that every real legal child is represented.
Lean reconstructs the normal-play outcome proof by strong induction on a decreasing rank.
-/

namespace ChompKernel

/-- A finite proof that a position is losing (`false`) or winning (`true`).

A losing proof contains a winning proof for every legal child. A winning proof contains one
legal move to a position with a losing proof. -/
inductive Outcome {P : Type} (Move : P → P → Prop) : P → Bool → Prop
  | losing {p : P} (children : ∀ q, Move p q → Outcome Move q true) : Outcome Move p false
  | winning {p q : P} (move : Move p q) (child : Outcome Move q false) : Outcome Move p true

/-- A position has a kernel-checked losing proof. -/
def IsLosing {P : Type} (Move : P → P → Prop) (p : P) : Prop :=
  Nonempty (Outcome Move p false)

/-- A position has a kernel-checked winning proof. -/
def IsWinning {P : Type} (Move : P → P → Prop) (p : P) : Prop :=
  Nonempty (Outcome Move p true)

/-- A progressively bounded game: every move strictly decreases a natural-number rank. -/
structure RankedGame (P : Type) where
  Move : P → P → Prop
  rank : P → ℕ
  decreases : ∀ {p q : P}, Move p q → rank q < rank p

namespace RankedGame

variable {P : Type} {G : RankedGame P} {n : ℕ}

/-- A finite, interpreted game certificate.

At losing nodes, `losing_complete` proves that all actual legal children occur in `children`.
At winning nodes only one legal losing reply is required, so irrelevant alternatives need not be
stored. -/
structure Certificate (G : RankedGame P) (n : ℕ) where
  pos : Fin n → P
  label : Fin n → Bool
  children : Fin n → Finset (Fin n)
  reply : Fin n → Option (Fin n)
  children_sound : ∀ {i j : Fin n}, j ∈ children i → G.Move (pos i) (pos j)
  losing_complete : ∀ (i : Fin n), label i = false → ∀ (q : P), G.Move (pos i) q →
    ∃ j, j ∈ children i ∧ pos j = q

namespace Certificate

/-- Local outcome-label validity.

* Every represented child of a losing-labelled node is labelled winning.
* Every winning-labelled node names a represented child labelled losing.
-/
def ValidAt (C : Certificate G n) (i : Fin n) : Prop :=
  match C.label i with
  | false => ∀ j, j ∈ C.children i → C.label j = true
  | true => ∃ j, C.reply i = some j ∧ j ∈ C.children i ∧ C.label j = false

/-- A valid finite interpreted certificate yields genuine outcome proofs for the actual game.

An arbitrary real move from a losing node is brought into the finite certificate through
`losing_complete`. A winning node needs only its one certified reply. -/
theorem outcome_of_valid (C : Certificate G n) (hvalid : ∀ i, C.ValidAt i) (i : Fin n) :
    Outcome G.Move (C.pos i) (C.label i) := by
  have all : ∀ k : ℕ, ∀ i : Fin n, G.rank (C.pos i) = k →
      Outcome G.Move (C.pos i) (C.label i) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro i hrank
        cases hi : C.label i with
        | false =>
            have hv : ∀ j, j ∈ C.children i → C.label j = true := by
              simpa [ValidAt, hi] using hvalid i
            exact Outcome.losing (fun q hq ↦ by
              obtain ⟨j, hj, hpos⟩ := C.losing_complete i hi q hq
              subst q
              have hlt : G.rank (C.pos j) < k := by
                simpa [← hrank] using G.decreases (C.children_sound hj)
              have hout := ih _ hlt j rfl
              simpa [hv j hj] using hout)
        | true =>
            have hv : ∃ j, C.reply i = some j ∧ j ∈ C.children i ∧ C.label j = false := by
              simpa [ValidAt, hi] using hvalid i
            obtain ⟨j, _, hj, hlabel⟩ := hv
            exact Outcome.winning (C.children_sound hj) (by
              have hlt : G.rank (C.pos j) < k := by
                simpa [← hrank] using G.decreases (C.children_sound hj)
              have hout := ih _ hlt j rfl
              simpa [hlabel] using hout)
  exact all _ i rfl

/-- A losing-labelled root of a valid certificate has a kernel-checked losing proof. -/
theorem losing_of_valid (C : Certificate G n) (hvalid : ∀ i, C.ValidAt i) {i : Fin n}
    (hi : C.label i = false) : IsLosing G.Move (C.pos i) := by
  refine ⟨?_⟩
  simpa [hi] using C.outcome_of_valid hvalid i

/-- A winning-labelled root of a valid certificate has a kernel-checked winning proof. -/
theorem winning_of_valid (C : Certificate G n) (hvalid : ∀ i, C.ValidAt i) {i : Fin n}
    (hi : C.label i = true) : IsWinning G.Move (C.pos i) := by
  refine ⟨?_⟩
  simpa [hi] using C.outcome_of_valid hvalid i

end Certificate
end RankedGame

#print axioms RankedGame.Certificate.outcome_of_valid
#print axioms RankedGame.Certificate.losing_of_valid
#print axioms RankedGame.Certificate.winning_of_valid

end ChompKernel
