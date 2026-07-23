import Checkerboard.FourCertificate

/-!
# Quadratic line-cover weights

For a point `(x,y)` on an `n` board, put `N=n-1`, `u=x+y-N`,
and `v=x-y`.  The exact identity

`(2x-N)^2 + (2y-N)^2 + 2(N^2-u^2) + 2(N^2-v^2) = 4N^2`

gives constant point coverage after retaining the diagonals of the required
checkerboard parity.
-/

namespace Checkerboard

private def oddCap (m : ℕ) {k : ℕ} (j : Fin k) : ℚ :=
  2 * ((2 * m : ℚ) ^ 2 - ((j.1 : ℚ) - 2 * m) ^ 2)

private def evenCap (m : ℕ) {k : ℕ} (j : Fin k) : ℚ :=
  2 * (((2 * m : ℚ) - 1) ^ 2 -
    ((j.1 : ℚ) - ((2 * m : ℚ) - 1)) ^ 2)

/-- Quadratic cover for the odd board `n=2m+1`. -/
def oddQuadraticWeights (m parity : ℕ) : FourWeights (2 * m + 1) where
  row i := (2 * (i.1 : ℚ) - 2 * m) ^ 2
  column i := (2 * (i.1 : ℚ) - 2 * m) ^ 2
  sum j := if j.1 % 2 = parity % 2 then oddCap m j else 0
  difference j := if j.1 % 2 = parity % 2 then oddCap m j else 0

/-- Quadratic cover for the even board `n=2m`.  Difference-line indices are
shifted by the odd number `2m-1`, hence use the opposite index parity. -/
def evenQuadraticWeights (m parity : ℕ) : FourWeights (2 * m) where
  row i := (2 * (i.1 : ℚ) - ((2 * m : ℚ) - 1)) ^ 2
  column i := (2 * (i.1 : ℚ) - ((2 * m : ℚ) - 1)) ^ 2
  sum j := if j.1 % 2 = parity % 2 then evenCap m j else 0
  difference j :=
    if j.1 % 2 = (parity + 1) % 2 then evenCap m j else 0

private theorem oddCap_nonneg (m : ℕ)
    (j : Fin (2 * (2 * m + 1) - 1)) : 0 ≤ oddCap m j := by
  have hj0 : (0 : ℚ) ≤ j.1 := by positivity
  have hjmax : (j.1 : ℚ) ≤ 4 * (m : ℚ) := by
    exact_mod_cast (show j.1 ≤ 4 * m by omega)
  have hprod : 0 ≤ (j.1 : ℚ) * (4 * (m : ℚ) - j.1) :=
    mul_nonneg hj0 (sub_nonneg.mpr hjmax)
  unfold oddCap
  nlinarith

private theorem evenCap_nonneg (m : ℕ) (hm : 1 ≤ m)
    (j : Fin (2 * (2 * m) - 1)) : 0 ≤ evenCap m j := by
  have hj0 : (0 : ℚ) ≤ j.1 := by positivity
  have hjmax : (j.1 : ℚ) ≤ 2 * ((2 * m : ℚ) - 1) := by
    have hjmaxNat : j.1 ≤ 2 * (2 * m - 1) := by omega
    have htwo : 1 ≤ 2 * m := by omega
    calc
      (j.1 : ℚ) ≤ ((2 * (2 * m - 1) : ℕ) : ℚ) := by
        exact_mod_cast hjmaxNat
      _ = 2 * ((2 * m : ℚ) - 1) := by
        norm_num [Nat.cast_sub htwo]
  have hprod : 0 ≤ (j.1 : ℚ) *
      (2 * ((2 * m : ℚ) - 1) - j.1) :=
    mul_nonneg hj0 (sub_nonneg.mpr hjmax)
  unfold evenCap
  nlinarith

/-- All four odd-board line weights are nonnegative. -/
theorem oddQuadratic_nonnegative (m parity : ℕ) :
    (∀ i, 0 ≤ (oddQuadraticWeights m parity).row i) ∧
    (∀ i, 0 ≤ (oddQuadraticWeights m parity).column i) ∧
    (∀ i, 0 ≤ (oddQuadraticWeights m parity).sum i) ∧
    ∀ i, 0 ≤ (oddQuadraticWeights m parity).difference i := by
  constructor
  · intro i
    simp [oddQuadraticWeights]
    positivity
  constructor
  · intro i
    simp [oddQuadraticWeights]
    positivity
  constructor
  · intro i
    simp only [oddQuadraticWeights]
    split <;> simp_all [oddCap_nonneg]
  · intro i
    simp only [oddQuadraticWeights]
    split <;> simp_all [oddCap_nonneg]

/-- All four even-board line weights are nonnegative. -/
theorem evenQuadratic_nonnegative (m parity : ℕ) (hm : 1 ≤ m) :
    (∀ i, 0 ≤ (evenQuadraticWeights m parity).row i) ∧
    (∀ i, 0 ≤ (evenQuadraticWeights m parity).column i) ∧
    (∀ i, 0 ≤ (evenQuadraticWeights m parity).sum i) ∧
    ∀ i, 0 ≤ (evenQuadraticWeights m parity).difference i := by
  constructor
  · intro i
    simp [evenQuadraticWeights]
    positivity
  constructor
  · intro i
    simp [evenQuadraticWeights]
    positivity
  constructor
  · intro i
    simp only [evenQuadraticWeights]
    split <;> simp_all [evenCap_nonneg m hm]
  · intro i
    simp only [evenQuadraticWeights]
    split <;> simp_all [evenCap_nonneg m hm]

/-- Constant coverage on an odd board. -/
theorem oddQuadratic_coverage (m parity : ℕ) (hp : parity = 0 ∨ parity = 1)
    (p : Point (2 * m + 1)) (hcolor : InColor parity p) :
    fourCoverage (oddQuadraticWeights m parity) p = 16 * (m : ℚ) ^ 2 := by
  have hsum : (sumIndex p).1 % 2 = parity % 2 := by
    simpa [sumIndex, InColor] using hcolor
  have hdiff : (differenceIndex p).1 % 2 = parity % 2 := by
    rcases hp with rfl | rfl <;>
      simp [differenceIndex, InColor] at hcolor ⊢ <;> omega
  have hy : p.2.1 ≤ 2 * m := by omega
  unfold fourCoverage oddQuadraticWeights
  dsimp
  rw [if_pos hsum, if_pos hdiff]
  simp only [oddCap, sumIndex, differenceIndex]
  push_cast [Nat.cast_sub hy]
  ring

/-- Constant coverage on an even board. -/
theorem evenQuadratic_coverage (m parity : ℕ) (hp : parity = 0 ∨ parity = 1)
    (hm : 1 ≤ m) (p : Point (2 * m)) (hcolor : InColor parity p) :
    fourCoverage (evenQuadraticWeights m parity) p =
      4 * ((2 * m : ℚ) - 1) ^ 2 := by
  have hsum : (sumIndex p).1 % 2 = parity % 2 := by
    simpa [sumIndex, InColor] using hcolor
  have hdiff : (differenceIndex p).1 % 2 = (parity + 1) % 2 := by
    rcases hp with rfl | rfl <;>
      simp [differenceIndex, InColor] at hcolor ⊢ <;> omega
  have hy : p.2.1 ≤ 2 * m - 1 := by omega
  have hmtwo : 1 ≤ m * 2 := by omega
  have hcast : (((m * 2 - 1 : ℕ) : ℚ)) = 2 * (m : ℚ) - 1 := by
    rw [Nat.cast_sub hmtwo]
    norm_num
    ring
  unfold fourCoverage evenQuadraticWeights
  dsimp
  rw [if_pos hsum, if_pos hdiff]
  simp only [evenCap, sumIndex, differenceIndex]
  push_cast [Nat.cast_sub hy]
  rw [hcast]
  ring

end Checkerboard
