import Mathlib

namespace Checkerboard

/-- Convert a Boolean selection bit to its natural indicator. -/
def bitNat (b : Bool) : ℕ := if b then 1 else 0

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
  have hx0 : bitNat x0 ≤ 1 := by cases x0 <;> simp [bitNat]
  have hx1 : bitNat x1 ≤ 1 := by cases x1 <;> simp [bitNat]
  have hx2 : bitNat x2 ≤ 1 := by cases x2 <;> simp [bitNat]
  have hx3 : bitNat x3 ≤ 1 := by cases x3 <;> simp [bitNat]
  have hx4 : bitNat x4 ≤ 1 := by cases x4 <;> simp [bitNat]
  have hx5 : bitNat x5 ≤ 1 := by cases x5 <;> simp [bitNat]
  have hx6 : bitNat x6 ≤ 1 := by cases x6 <;> simp [bitNat]
  have hx7 : bitNat x7 ≤ 1 := by cases x7 <;> simp [bitNat]
  have hx8 : bitNat x8 ≤ 1 := by cases x8 <;> simp [bitNat]
  have hx9 : bitNat x9 ≤ 1 := by cases x9 <;> simp [bitNat]
  have hx10 : bitNat x10 ≤ 1 := by cases x10 <;> simp [bitNat]
  have hx11 : bitNat x11 ≤ 1 := by cases x11 <;> simp [bitNat]
  have hx12 : bitNat x12 ≤ 1 := by cases x12 <;> simp [bitNat]
  have hx13 : bitNat x13 ≤ 1 := by cases x13 <;> simp [bitNat]
  have hx14 : bitNat x14 ≤ 1 := by cases x14 <;> simp [bitNat]
  have hx15 : bitNat x15 ≤ 1 := by cases x15 <;> simp [bitNat]
  have hx16 : bitNat x16 ≤ 1 := by cases x16 <;> simp [bitNat]
  have hx17 : bitNat x17 ≤ 1 := by cases x17 <;> simp [bitNat]
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
  have hx0 : bitNat x0 ≤ 1 := by cases x0 <;> simp [bitNat]
  have hx1 : bitNat x1 ≤ 1 := by cases x1 <;> simp [bitNat]
  have hx2 : bitNat x2 ≤ 1 := by cases x2 <;> simp [bitNat]
  have hx3 : bitNat x3 ≤ 1 := by cases x3 <;> simp [bitNat]
  have hx4 : bitNat x4 ≤ 1 := by cases x4 <;> simp [bitNat]
  have hx5 : bitNat x5 ≤ 1 := by cases x5 <;> simp [bitNat]
  have hx6 : bitNat x6 ≤ 1 := by cases x6 <;> simp [bitNat]
  have hx7 : bitNat x7 ≤ 1 := by cases x7 <;> simp [bitNat]
  have hx8 : bitNat x8 ≤ 1 := by cases x8 <;> simp [bitNat]
  have hx9 : bitNat x9 ≤ 1 := by cases x9 <;> simp [bitNat]
  have hx10 : bitNat x10 ≤ 1 := by cases x10 <;> simp [bitNat]
  have hx11 : bitNat x11 ≤ 1 := by cases x11 <;> simp [bitNat]
  have hx12 : bitNat x12 ≤ 1 := by cases x12 <;> simp [bitNat]
  have hx13 : bitNat x13 ≤ 1 := by cases x13 <;> simp [bitNat]
  have hx14 : bitNat x14 ≤ 1 := by cases x14 <;> simp [bitNat]
  have hx15 : bitNat x15 ≤ 1 := by cases x15 <;> simp [bitNat]
  have hx16 : bitNat x16 ≤ 1 := by cases x16 <;> simp [bitNat]
  have hx17 : bitNat x17 ≤ 1 := by cases x17 <;> simp [bitNat]
  omega

#print axioms n6p0_sat
#print axioms n6p1_sat

end Checkerboard
