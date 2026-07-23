import Mathlib

namespace Checkerboard

private def bitNat (b : Bool) : ℕ := if b then 1 else 0

private theorem p0_sat
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
  bv_decide

private theorem p1_sat
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
  bv_decide

#print axioms p0_sat
#print axioms p1_sat

end Checkerboard
