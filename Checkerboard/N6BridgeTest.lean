import Checkerboard.FourCertificate
import Checkerboard.N6SATTest

namespace Checkerboard

private def p0Point : Fin 18 → Point 6 := ![
  ((0 : Fin 6), (0 : Fin 6)), ((0 : Fin 6), (2 : Fin 6)),
  ((0 : Fin 6), (4 : Fin 6)), ((1 : Fin 6), (1 : Fin 6)),
  ((1 : Fin 6), (3 : Fin 6)), ((1 : Fin 6), (5 : Fin 6)),
  ((2 : Fin 6), (0 : Fin 6)), ((2 : Fin 6), (2 : Fin 6)),
  ((2 : Fin 6), (4 : Fin 6)), ((3 : Fin 6), (1 : Fin 6)),
  ((3 : Fin 6), (3 : Fin 6)), ((3 : Fin 6), (5 : Fin 6)),
  ((4 : Fin 6), (0 : Fin 6)), ((4 : Fin 6), (2 : Fin 6)),
  ((4 : Fin 6), (4 : Fin 6)), ((5 : Fin 6), (1 : Fin 6)),
  ((5 : Fin 6), (3 : Fin 6)), ((5 : Fin 6), (5 : Fin 6))]

private theorem p0_bridge
    (x : Fin 18 → Bool)
    (hline : ∀ line : PrincipalLine 6,
      (Finset.univ.filter fun i => x i = true ∧ OnLine line (p0Point i)).card ≤ 2) :
    (Finset.univ.filter fun i => x i = true).card ≤ 8 := by
  have h0 := hline (LineFamily.row, ⟨0, by decide⟩)
  have h1 := hline (LineFamily.row, ⟨1, by decide⟩)
  have h2 := hline (LineFamily.row, ⟨2, by decide⟩)
  have h3 := hline (LineFamily.row, ⟨3, by decide⟩)
  have h4 := hline (LineFamily.row, ⟨4, by decide⟩)
  have h5 := hline (LineFamily.row, ⟨5, by decide⟩)
  have h6 := hline (LineFamily.column, ⟨0, by decide⟩)
  have h7 := hline (LineFamily.column, ⟨2, by decide⟩)
  have h8 := hline (LineFamily.column, ⟨4, by decide⟩)
  have h9 := hline (LineFamily.column, ⟨1, by decide⟩)
  have h10 := hline (LineFamily.column, ⟨3, by decide⟩)
  have h11 := hline (LineFamily.column, ⟨5, by decide⟩)
  have h12 := hline (LineFamily.sum, ⟨2, by decide⟩)
  have h13 := hline (LineFamily.sum, ⟨4, by decide⟩)
  have h14 := hline (LineFamily.sum, ⟨6, by decide⟩)
  have h15 := hline (LineFamily.sum, ⟨8, by decide⟩)
  have h16 := hline (LineFamily.difference, ⟨5, by decide⟩)
  have h17 := hline (LineFamily.difference, ⟨3, by decide⟩)
  have h18 := hline (LineFamily.difference, ⟨7, by decide⟩)
  norm_num [p0Point, OnLine, lineValue, bitNat] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 ⊢
  exact n6p0_sat (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)
    (x 6) (x 7) (x 8) (x 9) (x 10) (x 11)
    (x 12) (x 13) (x 14) (x 15) (x 16) (x 17)
    h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18

#print axioms p0_bridge

end Checkerboard
