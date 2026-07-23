import Checkerboard.Model
import Checkerboard.FiberSums

/-!
# Four-direction rational line-cover certificates

A no-three-in-line set has capacity at most two on every row, column, sum
diagonal, and difference diagonal. This file packages that observation as a
generic exact rational certificate theorem.
-/

namespace Checkerboard

open scoped BigOperators

/-- Index of the sum diagonal through a board point. -/
def sumIndex {n : ℕ} (p : Point n) : Fin (2 * n - 1) :=
  ⟨p.1.1 + p.2.1, by omega⟩

/-- Index of the difference diagonal, shifted to the interval `0, …, 2n-2`. -/
def differenceIndex {n : ℕ} (p : Point n) : Fin (2 * n - 1) :=
  ⟨p.1.1 + (n - 1 - p.2.1), by omega⟩

/-- Rational weights on the four principal line families. -/
structure FourWeights (n : ℕ) where
  row : Fin n → ℚ
  column : Fin n → ℚ
  sum : Fin (2 * n - 1) → ℚ
  difference : Fin (2 * n - 1) → ℚ

/-- Coverage of one point by its four incident principal lines. -/
def fourCoverage {n : ℕ} (w : FourWeights n) (p : Point n) : ℚ :=
  w.row p.1 + w.column p.2 + w.sum (sumIndex p) +
    w.difference (differenceIndex p)

/-- Capacity-two objective of a four-direction line cover. -/
def fourCost {n : ℕ} (w : FourWeights n) : ℚ :=
  2 * ((∑ i, w.row i) + (∑ i, w.column i) +
    (∑ i, w.sum i) + ∑ i, w.difference i)

private theorem fiberCard_le_two_of_collinear
    {n : ℕ} {β : Type*} [DecidableEq β]
    {s : Finset (Point n)} (hntil : NoThreeInLine s)
    (f : Point n → β)
    (hcollinear : ∀ {a b c : Point n},
      f a = f b → f a = f c → determinant a b c = 0)
    (value : β) : fiberCard s f value ≤ 2 := by
  change (s.filter fun p => f p = value).card ≤ 2
  by_contra h
  have hthree : 2 < (s.filter fun p => f p = value).card :=
    Nat.lt_of_not_ge h
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ :=
    Finset.two_lt_card.mp hthree
  have haS : a ∈ s := (Finset.mem_filter.mp ha).1
  have hbS : b ∈ s := (Finset.mem_filter.mp hb).1
  have hcS : c ∈ s := (Finset.mem_filter.mp hc).1
  have haf : f a = value := (Finset.mem_filter.mp ha).2
  have hbf : f b = value := (Finset.mem_filter.mp hb).2
  have hcf : f c = value := (Finset.mem_filter.mp hc).2
  have hab' : (⟨a, haS⟩ : ↥s) ≠ ⟨b, hbS⟩ := by
    intro e
    exact hab (congrArg Subtype.val e)
  have hac' : (⟨a, haS⟩ : ↥s) ≠ ⟨c, hcS⟩ := by
    intro e
    exact hac (congrArg Subtype.val e)
  have hbc' : (⟨b, hbS⟩ : ↥s) ≠ ⟨c, hcS⟩ := by
    intro e
    exact hbc (congrArg Subtype.val e)
  exact hntil ⟨a, haS⟩ ⟨b, hbS⟩ ⟨c, hcS⟩ hab' hac' hbc'
    (hcollinear (haf.trans hbf.symm) (haf.trans hcf.symm))

/-- A no-three-in-line set occupies each row at most twice. -/
theorem rowFiber_le_two {n : ℕ} {s : Finset (Point n)}
    (hntil : NoThreeInLine s) (i : Fin n) :
    fiberCard s (fun p : Point n => p.1) i ≤ 2 := by
  apply fiberCard_le_two_of_collinear hntil (fun p : Point n => p.1)
  intro a b c hab hac
  have habv : a.1.1 = b.1.1 := congrArg Fin.val hab
  have hacv : a.1.1 = c.1.1 := congrArg Fin.val hac
  simp [determinant, habv, hacv]

/-- A no-three-in-line set occupies each column at most twice. -/
theorem columnFiber_le_two {n : ℕ} {s : Finset (Point n)}
    (hntil : NoThreeInLine s) (i : Fin n) :
    fiberCard s (fun p : Point n => p.2) i ≤ 2 := by
  apply fiberCard_le_two_of_collinear hntil (fun p : Point n => p.2)
  intro a b c hab hac
  have habv : a.2.1 = b.2.1 := congrArg Fin.val hab
  have hacv : a.2.1 = c.2.1 := congrArg Fin.val hac
  simp [determinant, habv, hacv]

/-- A no-three-in-line set occupies each sum diagonal at most twice. -/
theorem sumFiber_le_two {n : ℕ} {s : Finset (Point n)}
    (hntil : NoThreeInLine s) (i : Fin (2 * n - 1)) :
    fiberCard s sumIndex i ≤ 2 := by
  apply fiberCard_le_two_of_collinear hntil sumIndex
  intro a b c hab hac
  have habv : a.1.1 + a.2.1 = b.1.1 + b.2.1 :=
    congrArg Fin.val hab
  have hacv : a.1.1 + a.2.1 = c.1.1 + c.2.1 :=
    congrArg Fin.val hac
  have habz : (a.1.1 : ℤ) + a.2.1 = (b.1.1 : ℤ) + b.2.1 := by
    exact_mod_cast habv
  have hacz : (a.1.1 : ℤ) + a.2.1 = (c.1.1 : ℤ) + c.2.1 := by
    exact_mod_cast hacv
  have hb : (b.2.1 : ℤ) - a.2.1 = -((b.1.1 : ℤ) - a.1.1) := by
    linarith
  have hc : (c.2.1 : ℤ) - a.2.1 = -((c.1.1 : ℤ) - a.1.1) := by
    linarith
  rw [determinant, hb, hc]
  ring

/-- A no-three-in-line set occupies each difference diagonal at most twice. -/
theorem differenceFiber_le_two {n : ℕ} {s : Finset (Point n)}
    (hntil : NoThreeInLine s) (i : Fin (2 * n - 1)) :
    fiberCard s differenceIndex i ≤ 2 := by
  apply fiberCard_le_two_of_collinear hntil differenceIndex
  intro a b c hab hac
  have habv :
      a.1.1 + (n - 1 - a.2.1) = b.1.1 + (n - 1 - b.2.1) :=
    congrArg Fin.val hab
  have hacv :
      a.1.1 + (n - 1 - a.2.1) = c.1.1 + (n - 1 - c.2.1) :=
    congrArg Fin.val hac
  have habn : a.1.1 + b.2.1 = b.1.1 + a.2.1 := by omega
  have hacn : a.1.1 + c.2.1 = c.1.1 + a.2.1 := by omega
  have habz : (a.1.1 : ℤ) + b.2.1 = (b.1.1 : ℤ) + a.2.1 := by
    exact_mod_cast habn
  have hacz : (a.1.1 : ℤ) + c.2.1 = (c.1.1 : ℤ) + a.2.1 := by
    exact_mod_cast hacn
  have hb : (b.2.1 : ℤ) - a.2.1 = (b.1.1 : ℤ) - a.1.1 := by
    linarith
  have hc : (c.2.1 : ℤ) - a.2.1 = (c.1.1 : ℤ) - a.1.1 := by
    linarith
  rw [determinant, hb, hc]
  ring

private theorem weightedFibers_le_two
    {α β : Type*} [DecidableEq α] [DecidableEq β] [Fintype β]
    (s : Finset α) (f : α → β) (weight : β → ℚ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hcard : ∀ i, fiberCard s f i ≤ 2) :
    (∑ i, (fiberCard s f i : ℚ) * weight i) ≤
      2 * ∑ i, weight i := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hi : (fiberCard s f i : ℚ) ≤ 2 := by
    exact_mod_cast hcard i
  nlinarith [hweight i]

/-- Exact capacity-two upper bound supplied by any nonnegative rational cover. -/
theorem fourCertificate_bound {n : ℕ} {s : Finset (Point n)}
    (w : FourWeights n)
    (hrow : ∀ i, 0 ≤ w.row i)
    (hcolumn : ∀ i, 0 ≤ w.column i)
    (hsum : ∀ i, 0 ≤ w.sum i)
    (hdifference : ∀ i, 0 ≤ w.difference i)
    (hntil : NoThreeInLine s) :
    (∑ p ∈ s, fourCoverage w p) ≤ fourCost w := by
  have hr : (∑ p ∈ s, w.row p.1) ≤ 2 * ∑ i, w.row i := by
    rw [← sum_fiberCard_mul (R := ℚ) s (fun p : Point n => p.1) w.row]
    exact weightedFibers_le_two s (fun p : Point n => p.1) w.row hrow
      (rowFiber_le_two hntil)
  have hc : (∑ p ∈ s, w.column p.2) ≤ 2 * ∑ i, w.column i := by
    rw [← sum_fiberCard_mul (R := ℚ) s (fun p : Point n => p.2) w.column]
    exact weightedFibers_le_two s (fun p : Point n => p.2) w.column hcolumn
      (columnFiber_le_two hntil)
  have hs : (∑ p ∈ s, w.sum (sumIndex p)) ≤ 2 * ∑ i, w.sum i := by
    rw [← sum_fiberCard_mul (R := ℚ) s sumIndex w.sum]
    exact weightedFibers_le_two s sumIndex w.sum hsum
      (sumFiber_le_two hntil)
  have hd : (∑ p ∈ s, w.difference (differenceIndex p)) ≤
      2 * ∑ i, w.difference i := by
    rw [← sum_fiberCard_mul (R := ℚ) s differenceIndex w.difference]
    exact weightedFibers_le_two s differenceIndex w.difference hdifference
      (differenceFiber_le_two hntil)
  calc
    (∑ p ∈ s, fourCoverage w p) =
        (∑ p ∈ s, w.row p.1) + (∑ p ∈ s, w.column p.2) +
          (∑ p ∈ s, w.sum (sumIndex p)) +
            ∑ p ∈ s, w.difference (differenceIndex p) := by
              simp [fourCoverage, Finset.sum_add_distrib, add_assoc]
    _ ≤ 2 * (∑ i, w.row i) + 2 * (∑ i, w.column i) +
          2 * (∑ i, w.sum i) + 2 * ∑ i, w.difference i := by
            linarith
    _ = fourCost w := by
      simp [fourCost]
      ring

/-- A positive cover whose objective is below `q(k+1)` proves `|s| ≤ k`. -/
theorem card_le_of_fourCertificate {n k : ℕ} {q : ℚ}
    {s : Finset (Point n)} (w : FourWeights n)
    (hq : 0 < q)
    (hcost : fourCost w < q * (k + 1))
    (hrow : ∀ i, 0 ≤ w.row i)
    (hcolumn : ∀ i, 0 ≤ w.column i)
    (hsum : ∀ i, 0 ≤ w.sum i)
    (hdifference : ∀ i, 0 ≤ w.difference i)
    (hcover : ∀ p : ↥s, q ≤ fourCoverage w p.1)
    (hntil : NoThreeInLine s) : s.card ≤ k := by
  have hlower : q * (s.card : ℚ) ≤ ∑ p ∈ s, fourCoverage w p := by
    calc
      q * (s.card : ℚ) = ∑ _p ∈ s, q := by simp [mul_comm]
      _ ≤ ∑ p ∈ s, fourCoverage w p := by
        apply Finset.sum_le_sum
        intro p hp
        exact hcover ⟨p, hp⟩
  have hupper := fourCertificate_bound w hrow hcolumn hsum hdifference hntil
  have hltQ : (s.card : ℚ) < k + 1 := by
    nlinarith
  have hltN : s.card < k + 1 := by
    exact_mod_cast hltQ
  omega

end Checkerboard
