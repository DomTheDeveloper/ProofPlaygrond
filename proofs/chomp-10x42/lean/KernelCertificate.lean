import FormalConjectures.Util.ProblemImports

/-!
# Kernel-checked finite game certificates

This module defines proof objects for finite normal-play games and a generic theorem turning a
valid ranked certificate into an actual inductive outcome proof.  The certificate producer is
untrusted: only the proof of `Certificate.ValidAt` is used.
-/

namespace ChompKernel

/-- A finite proof that a state is losing (`false`) or winning (`true`).

A losing proof contains a winning proof for every legal child.  A winning proof contains one
legal move to a state with a losing proof.  Because this is an inductive type, every accepted
proof object is finite. -/
inductive Outcome {S : Type} (Move : S → S → Prop) : S → Bool → Prop
  | losing {s : S} (children : ∀ t, Move s t → Outcome Move t true) : Outcome Move s false
  | winning {s t : S} (move : Move s t) (child : Outcome Move t false) : Outcome Move s true

/-- A state has a kernel-checked losing proof. -/
def IsLosing {S : Type} (Move : S → S → Prop) (s : S) : Prop :=
  Nonempty (Outcome Move s false)

/-- A state has a kernel-checked winning proof. -/
def IsWinning {S : Type} (Move : S → S → Prop) (s : S) : Prop :=
  Nonempty (Outcome Move s true)

/-- A finite game presented by its children and a strictly decreasing natural-number rank. -/
structure RankedGame (S : Type) [DecidableEq S] where
  moves : S → Finset S
  rank : S → ℕ
  decreases : ∀ {s t : S}, t ∈ moves s → rank t < rank s

namespace RankedGame

variable {S : Type} [DecidableEq S]

/-- The move relation represented by a ranked finite game. -/
def Move (G : RankedGame S) (s t : S) : Prop := t ∈ G.moves s

/-- An untrusted outcome labelling together with one proposed reply at winning states. -/
structure Certificate (G : RankedGame S) where
  label : S → Bool
  reply : S → Option S

namespace Certificate

variable {G : RankedGame S}

/-- Local certificate validity.

* A losing-labelled node must have every legal child labelled winning.
* A winning-labelled node must name one legal losing-labelled reply.
-/
def ValidAt (C : Certificate G) (s : S) : Prop :=
  match C.label s with
  | false => ∀ t, t ∈ G.moves s → C.label t = true
  | true => ∃ t, C.reply s = some t ∧ t ∈ G.moves s ∧ C.label t = false

/-- A total valid ranked certificate yields genuine inductive outcome proofs.

For the generated Chomp certificate, the total functions are implemented by a finite ranked
array plus an unreachable default.  Closure of every losing node and the recorded reply at every
winning node ensure that the default is never used below a certified root.
-/
theorem outcome_of_valid (C : Certificate G) (hvalid : ∀ s, C.ValidAt s) (s : S) :
    Outcome G.Move s (C.label s) := by
  refine (measure_wf G.rank).induction s ?_
  intro s ih
  cases hs : C.label s with
  | false =>
      have hv : ∀ t, t ∈ G.moves s → C.label t = true := by
        simpa [ValidAt, hs] using hvalid s
      rw [hs]
      exact Outcome.losing (fun t hm => by
        have ht := ih t (G.decreases hm)
        simpa [hv t hm] using ht)
  | true =>
      have hv : ∃ t, C.reply s = some t ∧ t ∈ G.moves s ∧ C.label t = false := by
        simpa [ValidAt, hs] using hvalid s
      obtain ⟨t, _, hm, htlabel⟩ := hv
      rw [hs]
      exact Outcome.winning hm (by
        have ht := ih t (G.decreases hm)
        simpa [htlabel] using ht)

/-- A losing-labelled root of a valid certificate has a kernel-checked losing proof. -/
theorem losing_of_valid (C : Certificate G) (hvalid : ∀ s, C.ValidAt s) {s : S}
    (hs : C.label s = false) : IsLosing G.Move s := by
  refine ⟨?_⟩
  simpa [hs] using C.outcome_of_valid hvalid s

/-- A winning-labelled root of a valid certificate has a kernel-checked winning proof. -/
theorem winning_of_valid (C : Certificate G) (hvalid : ∀ s, C.ValidAt s) {s : S}
    (hs : C.label s = true) : IsWinning G.Move s := by
  refine ⟨?_⟩
  simpa [hs] using C.outcome_of_valid hvalid s

end Certificate
end RankedGame

end ChompKernel
