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
# Kernel certificates for layered decision-diagram languages

The concrete Chomp P-set is represented externally by a reduced layered multi-valued decision
diagram. This file supplies the small trusted theorem layer: local simulation certificates imply
language inclusion, and local product-closure certificates imply language disjointness.

Concrete node tables and local certificates remain untrusted data until these hypotheses are
proved in Lean.
-/

namespace ChompKernel
namespace MDD

/-- A deterministic finite-state acceptor. Layering is not needed for semantic correctness;
the concrete MDD checker separately proves that its node table is layered and well formed. -/
structure Automaton (σ : Type) (n : ℕ) where
  step : Fin n → σ → Option (Fin n)
  accept : Fin n → Bool

namespace Automaton

variable {σ : Type} {n m : ℕ}

/-- Evaluate a word from a selected automaton state. -/
def acceptsFrom (A : Automaton σ n) (i : Fin n) : List σ → Bool
  | [] => A.accept i
  | a :: word =>
      match A.step i a with
      | none => false
      | some j => A.acceptsFrom j word

/-- A local forward simulation between deterministic acceptors. -/
structure InclusionCertificate (A : Automaton σ n) (B : Automaton σ m) where
  Rel : Fin n → Fin m → Prop
  accept_mono : ∀ {i j}, Rel i j → A.accept i = true → B.accept j = true
  step_sim : ∀ {i j i'} (a : σ), Rel i j → A.step i a = some i' →
    ∃ j', B.step j a = some j' ∧ Rel i' j'

namespace InclusionCertificate

variable {A : Automaton σ n} {B : Automaton σ m}

/-- Related states accept an included language. -/
theorem accepts_mono (C : InclusionCertificate A B) {i : Fin n} {j : Fin m}
    (hrel : C.Rel i j) (word : List σ) :
    A.acceptsFrom i word = true → B.acceptsFrom j word = true := by
  induction word generalizing i j with
  | nil =>
      simpa [acceptsFrom] using C.accept_mono hrel
  | cons a word ih =>
      intro haccept
      cases hi : A.step i a with
      | none =>
          simp [acceptsFrom, hi] at haccept
      | some i' =>
          obtain ⟨j', hj, hnext⟩ := C.step_sim a hrel hi
          have htail : A.acceptsFrom i' word = true := by
            simpa [acceptsFrom, hi] using haccept
          have := ih hnext htail
          simpa [acceptsFrom, hj] using this

end InclusionCertificate

/-- A local synchronized-product certificate proving that two languages are disjoint. -/
structure DisjointnessCertificate (A : Automaton σ n) (B : Automaton σ m) where
  Rel : Fin n → Fin m → Prop
  terminal_disjoint : ∀ {i j}, Rel i j → ¬(A.accept i = true ∧ B.accept j = true)
  step_closed : ∀ {i j i' j'} (a : σ), Rel i j →
    A.step i a = some i' → B.step j a = some j' → Rel i' j'

namespace DisjointnessCertificate

variable {A : Automaton σ n} {B : Automaton σ m}

/-- Related product states cannot both accept the same word. -/
theorem not_both_accept (C : DisjointnessCertificate A B) {i : Fin n} {j : Fin m}
    (hrel : C.Rel i j) (word : List σ) :
    ¬(A.acceptsFrom i word = true ∧ B.acceptsFrom j word = true) := by
  induction word generalizing i j with
  | nil =>
      simpa [acceptsFrom] using C.terminal_disjoint hrel
  | cons a word ih =>
      intro hboth
      rcases hboth with ⟨ha, hb⟩
      cases hi : A.step i a with
      | none =>
          simp [acceptsFrom, hi] at ha
      | some i' =>
          cases hj : B.step j a with
          | none =>
              simp [acceptsFrom, hj] at hb
          | some j' =>
              have hnext := C.step_closed a hrel hi hj
              have ha' : A.acceptsFrom i' word = true := by
                simpa [acceptsFrom, hi] using ha
              have hb' : B.acceptsFrom j' word = true := by
                simpa [acceptsFrom, hj] using hb
              exact ih hnext ⟨ha', hb'⟩

end DisjointnessCertificate

/-- Two opposite inclusion certificates prove language equality at related roots. -/
theorem language_eq_of_inclusions
    {A : Automaton σ n} {B : Automaton σ m}
    (AB : InclusionCertificate A B) (BA : InclusionCertificate B A)
    {i : Fin n} {j : Fin m} (hAB : AB.Rel i j) (hBA : BA.Rel j i) :
    ∀ word, A.acceptsFrom i word = B.acceptsFrom j word := by
  intro word
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact AB.accepts_mono hAB word
  · exact BA.accepts_mono hBA word

#print axioms InclusionCertificate.accepts_mono
#print axioms DisjointnessCertificate.not_both_accept
#print axioms language_eq_of_inclusions

end Automaton
end MDD
end ChompKernel
