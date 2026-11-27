import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic

/-! A natural-valued counting table cannot satisfy the finite identity in A346214
    on its printed domain. The argument is independent of how the table is computed. -/
namespace NilpotentCoindex

/-- The order of GL(n,2), obtained by successively choosing independent columns. -/
def glOrder (n : Nat) : Nat :=
  ((List.range n).map (fun i => 2 ^ n - 2 ^ i)).prod

/-- Clearing the powers-of-two denominator avoids natural-number division. -/
def PrintedFinite (T : Nat → Nat → Nat) : Prop :=
  ∀ n j : Nat, 0 < n → j < n → j < 2 * n →
    T n (n - j) * glOrder j * 2 ^ n =
      glOrder n * 2 ^ (((j : Int) - 1).natAbs ^ 2)

theorem printed_finite_impossible (T : Nat → Nat → Nat) : ¬ PrintedFinite T := by
  intro h
  have bad := h 2 1 (by decide) (by decide) (by decide)
  change T 2 1 * 1 * 4 = 6 * 1 at bad
  omega

/-- The actual OEIS table counts matrices of least positive zero power k. -/
noncomputable def indexCount (n k : Nat) : Nat := by
  classical
  exact ((Finset.univ : Finset (Matrix (Fin n) (Fin n) (ZMod 2))).filter
    (fun A => 0 < k ∧ A ^ k = 0 ∧ (k = 1 ∨ A ^ (k - 1) ≠ 0))).card

theorem index_one_count (n : Nat) : indexCount n 1 = 1 := by
  classical
  simp [indexCount, Finset.filter_eq']

theorem coindex_finite_false : ¬ PrintedFinite indexCount :=
  printed_finite_impossible indexCount

#print axioms printed_finite_impossible
#print axioms index_one_count
#print axioms coindex_finite_false
end NilpotentCoindex
