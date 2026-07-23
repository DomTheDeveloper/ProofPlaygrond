import Mathlib

namespace Checkerboard

private def pop18 (x : BitVec 18) : BitVec 18 :=
  go x 0 18
where
  go (x pop : BitVec 18) : Nat → BitVec 18
    | 0 => pop
    | n + 1 => go (x >>> 1) (pop + (x &&& 1)) n

private theorem p0_sat (x : BitVec 18)
    (h0 : pop18 (x &&& 0x7#18) ≤ 2#18)
    (h1 : pop18 (x &&& 0x38#18) ≤ 2#18)
    (h2 : pop18 (x &&& 0x1c0#18) ≤ 2#18)
    (h3 : pop18 (x &&& 0xe00#18) ≤ 2#18)
    (h4 : pop18 (x &&& 0x7000#18) ≤ 2#18)
    (h5 : pop18 (x &&& 0x38000#18) ≤ 2#18)
    (h6 : pop18 (x &&& 0x1041#18) ≤ 2#18)
    (h7 : pop18 (x &&& 0x2082#18) ≤ 2#18)
    (h8 : pop18 (x &&& 0x4104#18) ≤ 2#18)
    (h9 : pop18 (x &&& 0x8208#18) ≤ 2#18)
    (h10 : pop18 (x &&& 0x10410#18) ≤ 2#18)
    (h11 : pop18 (x &&& 0x20820#18) ≤ 2#18)
    (h12 : pop18 (x &&& 0x4a#18) ≤ 2#18)
    (h13 : pop18 (x &&& 0x1294#18) ≤ 2#18)
    (h14 : pop18 (x &&& 0xa520#18) ≤ 2#18)
    (h15 : pop18 (x &&& 0x14800#18) ≤ 2#18)
    (h16 : pop18 (x &&& 0x24489#18) ≤ 2#18)
    (h17 : pop18 (x &&& 0x912#18) ≤ 2#18)
    (h18 : pop18 (x &&& 0x12240#18) ≤ 2#18) :
    pop18 x ≤ 8#18 := by
  dsimp [pop18, pop18.go] at *
  bv_decide?

private theorem p1_sat (x : BitVec 18)
    (h0 : pop18 (x &&& 0x7#18) ≤ 2#18)
    (h1 : pop18 (x &&& 0x38#18) ≤ 2#18)
    (h2 : pop18 (x &&& 0x1c0#18) ≤ 2#18)
    (h3 : pop18 (x &&& 0xe00#18) ≤ 2#18)
    (h4 : pop18 (x &&& 0x7000#18) ≤ 2#18)
    (h5 : pop18 (x &&& 0x38000#18) ≤ 2#18)
    (h6 : pop18 (x &&& 0x1041#18) ≤ 2#18)
    (h7 : pop18 (x &&& 0x2082#18) ≤ 2#18)
    (h8 : pop18 (x &&& 0x4104#18) ≤ 2#18)
    (h9 : pop18 (x &&& 0x8208#18) ≤ 2#18)
    (h10 : pop18 (x &&& 0x10410#18) ≤ 2#18)
    (h11 : pop18 (x &&& 0x20820#18) ≤ 2#18)
    (h12 : pop18 (x &&& 0x252#18) ≤ 2#18)
    (h13 : pop18 (x &&& 0x94a4#18) ≤ 2#18)
    (h14 : pop18 (x &&& 0x12900#18) ≤ 2#18)
    (h15 : pop18 (x &&& 0x4891#18) ≤ 2#18)
    (h16 : pop18 (x &&& 0x122#18) ≤ 2#18)
    (h17 : pop18 (x &&& 0x22448#18) ≤ 2#18)
    (h18 : pop18 (x &&& 0x11200#18) ≤ 2#18) :
    pop18 x ≤ 8#18 := by
  dsimp [pop18, pop18.go] at *
  bv_decide?

end Checkerboard
