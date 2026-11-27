import Mathlib.Data.Matrix.Block

/-! The block identity used to lift square-zero matrices, over any ring. -/
namespace SquareZeroLift
open Matrix

variable {R i s : Type*} [Ring R] [Fintype i] [Fintype s] [DecidableEq i]

/-- Relative to the image, its chosen preimages, and the remaining basis. -/
def liftBlock (C D : Matrix i s R) (B : Matrix s s R) :
    Matrix (i ⊕ (i ⊕ s)) (i ⊕ (i ⊕ s)) R :=
  .of fun row col => match row, col with
    | .inl u, .inr (.inl v) => (1 : Matrix i i R) u v
    | .inl u, .inr (.inr w) => C u w
    | .inr (.inl v), .inr (.inr w) => D v w
    | .inr (.inr v), .inr (.inr w) => B v w
    | _, _ => 0

def lastColumn (P Q : Matrix i s R) (S : Matrix s s R) :
    Matrix (i ⊕ (i ⊕ s)) (i ⊕ (i ⊕ s)) R :=
  .of fun row col => match row, col with
    | .inl u, .inr (.inr w) => P u w
    | .inr (.inl v), .inr (.inr w) => Q v w
    | .inr (.inr v), .inr (.inr w) => S v w
    | _, _ => 0

theorem square_formula (C D : Matrix i s R) (B : Matrix s s R) :
    liftBlock C D B * liftBlock C D B =
      lastColumn (D + C * B) (D * B) (B * B) := by
  ext row col
  rcases row with u | v | w <;> rcases col with a | b | c <;>
    simp [liftBlock, lastColumn, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

omit [Fintype i] [Fintype s] [DecidableEq i] in
theorem lastColumn_eq_zero (P Q : Matrix i s R) (S : Matrix s s R) :
    lastColumn P Q S = 0 ↔ P = 0 ∧ Q = 0 ∧ S = 0 := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · ext u w
      exact congrFun (congrFun h (.inl u)) (.inr (.inr w))
    · ext v w
      exact congrFun (congrFun h (.inr (.inl v))) (.inr (.inr w))
    · ext v w
      exact congrFun (congrFun h (.inr (.inr v))) (.inr (.inr w))
  · rintro ⟨rfl, rfl, rfl⟩
    ext row col
    rcases row with u | v | w <;> rcases col with a | b | c <;> rfl

theorem square_zero_iff (C D : Matrix i s R) (B : Matrix s s R) :
    liftBlock C D B * liftBlock C D B = 0 ↔ D = -(C * B) ∧ B * B = 0 := by
  rw [square_formula, lastColumn_eq_zero]
  constructor
  · rintro ⟨h, _, hB⟩
    exact ⟨eq_neg_of_add_eq_zero_left h, hB⟩
  · rintro ⟨rfl, hB⟩
    simp [Matrix.neg_mul, Matrix.mul_assoc, hB]

#print axioms square_zero_iff
end SquareZeroLift
