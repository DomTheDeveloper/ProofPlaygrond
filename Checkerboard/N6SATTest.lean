import Mathlib

/-!
# Compact 6×6 checkerboard arithmetic certificates

Proof developed by Dominic Dabish. ProofOrchestrator, using OpenAI GPT-5.6 Thinking,
assisted with the mathematical argument, Lean formalization, and submission
preparation. All formal claims are checked by the repository-pinned Lean compiler.
-/

namespace Checkerboard

set_option maxHeartbeats 0

/-- Convert a Boolean selection bit to its natural indicator. -/
def bitNat (b : Bool) : ℕ := if b then 1 else 0

@[simp] theorem bitNat_false : bitNat false = 0 := rfl
@[simp] theorem bitNat_true : bitNat true = 1 := rfl

theorem bitNat_le_one (b : Bool) : bitNat b ≤ 1 := by
  cases b <;> simp

/-- Integer certificate for the even checkerboard color class on the 6-board. -/
theorem n6p0_sat
    (x0 : Bool) (x1 : Bool) (x2 : Bool) (x3 : Bool) (x4 : Bool) (x5 : Bool)
    (x6 : Bool) (x7 : Bool) (x8 : Bool) (x9 : Bool) (x10 : Bool) (x11 : Bool)
    (x12 : Bool) (x13 : Bool) (x14 : Bool) (x15 : Bool) (x16 : Bool) (x17 : Bool)
    (h0 : bitNat x0 + bitNat x1 + bitNat x2 ≤ 2)
    (h1 : bitNat x3 + bitNat x4 + bitNat x5 ≤ 2)
    (h2 : bitNat x6 + bitNat x7 + bitNat x8 ≤ 2)
    (h3 : bitNat x9 + bitNat x10 + bitNat x11 ≤ 2)
    (h4 : bitNat x12 + bitNat x13 + bitNat x14 ≤ 2)
    (h5 : bitNat x15 + bitNat x16 + bitNat x17 ≤ 2)
    (h6 : bitNat x0 + bitNat x6 + bitNat x12 ≤ 2)
    (h7 : bitNat x1 + bitNat x7 + bitNat x13 ≤ 2)
    (h8 : bitNat x2 + bitNat x8 + bitNat x14 ≤ 2)
    (h9 : bitNat x3 + bitNat x9 + bitNat x15 ≤ 2)
    (h10 : bitNat x4 + bitNat x10 + bitNat x16 ≤ 2)
    (h11 : bitNat x5 + bitNat x11 + bitNat x17 ≤ 2)
    (h12 : bitNat x1 + bitNat x3 + bitNat x6 ≤ 2)
    (h13 : bitNat x2 + bitNat x4 + bitNat x7 + bitNat x9 + bitNat x12 ≤ 2)
    (h14 : bitNat x5 + bitNat x8 + bitNat x10 + bitNat x13 + bitNat x15 ≤ 2)
    (h15 : bitNat x11 + bitNat x14 + bitNat x16 ≤ 2)
    (h16 : bitNat x0 + bitNat x3 + bitNat x7 + bitNat x10 + bitNat x14 + bitNat x17 ≤ 2)
    (h17 : bitNat x1 + bitNat x4 + bitNat x8 + bitNat x11 ≤ 2)
    (h18 : bitNat x6 + bitNat x9 + bitNat x13 + bitNat x16 ≤ 2) :
    bitNat x0 + bitNat x1 + bitNat x2 + bitNat x3 + bitNat x4 + bitNat x5 +
      bitNat x6 + bitNat x7 + bitNat x8 + bitNat x9 + bitNat x10 + bitNat x11 +
      bitNat x12 + bitNat x13 + bitNat x14 + bitNat x15 + bitNat x16 + bitNat x17 ≤ 8 := by
  have hx0 := bitNat_le_one x0
  have hx1 := bitNat_le_one x1
  have hx2 := bitNat_le_one x2
  have hx3 := bitNat_le_one x3
  have hx4 := bitNat_le_one x4
  have hx5 := bitNat_le_one x5
  have hx6 := bitNat_le_one x6
  have hx7 := bitNat_le_one x7
  have hx8 := bitNat_le_one x8
  have hx9 := bitNat_le_one x9
  have hx10 := bitNat_le_one x10
  have hx11 := bitNat_le_one x11
  have hx12 := bitNat_le_one x12
  have hx13 := bitNat_le_one x13
  have hx14 := bitNat_le_one x14
  have hx15 := bitNat_le_one x15
  have hx16 := bitNat_le_one x16
  have hx17 := bitNat_le_one x17
  cases x0 <;> cases x1
  · simp only [bitNat_false, bitNat_true, Nat.zero_add, Nat.add_zero] at *
    clear h0 h1 h2 h3 h4 h6 h7 h9 h10 h12
      hx0 hx1 hx2 hx4 hx5 hx7 hx8 hx9 hx10 hx13 hx14 hx15 hx16 hx17
    omega
  · simp only [bitNat_false, bitNat_true, Nat.zero_add, Nat.add_zero] at *
    clear h0 h1 h2 h3 h6 h7 h9 h10
      hx0 hx1 hx2 hx3 hx4 hx5 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17
    omega
  · simp only [bitNat_false, bitNat_true, Nat.zero_add, Nat.add_zero] at *
    clear h0 h2 h3 h4 h7 h8 h9 h10 h11 h12
      hx0 hx1 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx12 hx13 hx14 hx15 hx16 hx17
    omega
  · simp only [bitNat_false, bitNat_true, Nat.zero_add, Nat.add_zero] at *
    clear h1 h2 h3 h4 h7 h8 h10 h12
      hx0 hx1 hx2 hx3 hx4 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx17
    omega

/-- Integer certificate for the odd checkerboard color class on the 6-board. -/
theorem n6p1_sat
    (x0 : Bool) (x1 : Bool) (x2 : Bool) (x3 : Bool) (x4 : Bool) (x5 : Bool)
    (x6 : Bool) (x7 : Bool) (x8 : Bool) (x9 : Bool) (x10 : Bool) (x11 : Bool)
    (x12 : Bool) (x13 : Bool) (x14 : Bool) (x15 : Bool) (x16 : Bool) (x17 : Bool)
    (h0 : bitNat x0 + bitNat x1 + bitNat x2 ≤ 2)
    (h1 : bitNat x3 + bitNat x4 + bitNat x5 ≤ 2)
    (h2 : bitNat x6 + bitNat x7 + bitNat x8 ≤ 2)
    (h3 : bitNat x9 + bitNat x10 + bitNat x11 ≤ 2)
    (h4 : bitNat x12 + bitNat x13 + bitNat x14 ≤ 2)
    (h5 : bitNat x15 + bitNat x16 + bitNat x17 ≤ 2)
    (h6 : bitNat x0 + bitNat x6 + bitNat x12 ≤ 2)
    (h7 : bitNat x1 + bitNat x7 + bitNat x13 ≤ 2)
    (h8 : bitNat x2 + bitNat x8 + bitNat x14 ≤ 2)
    (h9 : bitNat x3 + bitNat x9 + bitNat x15 ≤ 2)
    (h10 : bitNat x4 + bitNat x10 + bitNat x16 ≤ 2)
    (h11 : bitNat x5 + bitNat x11 + bitNat x17 ≤ 2)
    (h12 : bitNat x1 + bitNat x4 + bitNat x6 + bitNat x9 ≤ 2)
    (h13 : bitNat x2 + bitNat x5 + bitNat x7 + bitNat x10 + bitNat x12 + bitNat x15 ≤ 2)
    (h14 : bitNat x8 + bitNat x11 + bitNat x13 + bitNat x16 ≤ 2)
    (h15 : bitNat x0 + bitNat x4 + bitNat x7 + bitNat x11 + bitNat x14 ≤ 2)
    (h16 : bitNat x1 + bitNat x5 + bitNat x8 ≤ 2)
    (h17 : bitNat x3 + bitNat x6 + bitNat x10 + bitNat x13 + bitNat x17 ≤ 2)
    (h18 : bitNat x9 + bitNat x12 + bitNat x16 ≤ 2) :
    bitNat x0 + bitNat x1 + bitNat x2 + bitNat x3 + bitNat x4 + bitNat x5 +
      bitNat x6 + bitNat x7 + bitNat x8 + bitNat x9 + bitNat x10 + bitNat x11 +
      bitNat x12 + bitNat x13 + bitNat x14 + bitNat x15 + bitNat x16 + bitNat x17 ≤ 8 := by
  have hx0 := bitNat_le_one x0
  have hx1 := bitNat_le_one x1
  have hx2 := bitNat_le_one x2
  have hx3 := bitNat_le_one x3
  have hx4 := bitNat_le_one x4
  have hx5 := bitNat_le_one x5
  have hx6 := bitNat_le_one x6
  have hx7 := bitNat_le_one x7
  have hx8 := bitNat_le_one x8
  have hx9 := bitNat_le_one x9
  have hx10 := bitNat_le_one x10
  have hx11 := bitNat_le_one x11
  have hx12 := bitNat_le_one x12
  have hx13 := bitNat_le_one x13
  have hx14 := bitNat_le_one x14
  have hx15 := bitNat_le_one x15
  have hx16 := bitNat_le_one x16
  have hx17 := bitNat_le_one x17
  cases x0 <;> cases x1
  · simp only [bitNat_false, bitNat_true, Nat.zero_add, Nat.add_zero] at *
    clear h0 h2 h3 h4 h6 h7 h10 h16
      hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx9 hx10 hx11 hx12 hx13 hx15 hx16 hx17
    omega
  · simp only [bitNat_false, bitNat_true, Nat.zero_add, Nat.add_zero] at *
    clear h0 h1 h2 h3 h4 h6 h7 h10
      hx0 hx1 hx2 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx15 hx16 hx17
    omega
  · simp only [bitNat_false, bitNat_true, Nat.zero_add, Nat.add_zero] at *
    clear h0 h2 h3 h4 h6 h7 h10 h11 h16
      hx0 hx1 hx2 hx3 hx4 hx6 hx7 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17
    omega
  · simp only [bitNat_false, bitNat_true, Nat.zero_add, Nat.add_zero] at *
    clear h1 h2 h3 h7 h8 h10 h11
      hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17
    omega

#print axioms n6p0_sat
#print axioms n6p1_sat

end Checkerboard
