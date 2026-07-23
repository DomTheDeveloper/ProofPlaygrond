import Mathlib

/-!
# Finite checkerboard no-three-in-line model

This file gives a self-contained finite model of monochromatic checkerboard
point sets, Euclidean collinearity, the four principal line families, and a
kernel-checked weighted line-cover bound.
-/

namespace Checkerboard

abbrev Point (n : ℕ) := Fin n × Fin n

/-- Twice the signed Euclidean area of the triangle `a b c`. -/
def determinant {n : ℕ} (a b c : Point n) : ℤ :=
  ((b.1.1 : ℤ) - (a.1.1 : ℤ)) * ((c.2.1 : ℤ) - (a.2.1 : ℤ)) -
    ((b.2.1 : ℤ) - (a.2.1 : ℤ)) * ((c.1.1 : ℤ) - (a.1.1 : ℤ))

/-- The checkerboard color class indexed by `parity mod 2`. -/
def InColor {n : ℕ} (parity : ℕ) (p : Point n) : Prop :=
  (p.1.1 + p.2.1) % 2 = parity % 2

/-- Every point of `s` lies in one checkerboard color class. -/
def Monochromatic {n : ℕ} (parity : ℕ) (s : Finset (Point n)) : Prop :=
  ∀ p : ↥s, InColor parity p.1

/-- No three distinct selected points are collinear. Quantifying over the
subtype `↥s` makes direct checking of explicit constructions finite and small. -/
def NoThreeInLine {n : ℕ} (s : Finset (Point n)) : Prop :=
  ∀ a b c : ↥s, a ≠ b → a ≠ c → b ≠ c →
    determinant a.1 b.1 c.1 ≠ 0

/-- A convenient exact-maximum statement, avoiding any dependence on a chosen
implementation of `argmax` over all subsets. -/
def IsExactMaximum (n parity k : ℕ) : Prop :=
  (∃ s : Finset (Point n),
      Monochromatic parity s ∧ NoThreeInLine s ∧ s.card = k) ∧
    ∀ s : Finset (Point n),
      Monochromatic parity s → NoThreeInLine s → s.card ≤ k

inductive LineFamily
  | row
  | column
  | sum
  | difference
  deriving DecidableEq, Fintype, Repr

/-- Principal rows, columns, and slope `±1` diagonals. The second component is
an index in `0, …, 2n-2`; unused row/column indices simply describe empty lines. -/
abbrev PrincipalLine (n : ℕ) := LineFamily × Fin (2 * n - 1)

/-- Integer line coordinate. Difference diagonals are shifted by `n-1`, so all
four families use nonnegative indices. -/
def lineValue {n : ℕ} (family : LineFamily) (p : Point n) : ℤ :=
  match family with
  | .row => p.1.1
  | .column => p.2.1
  | .sum => p.1.1 + p.2.1
  | .difference => (p.1.1 : ℤ) - (p.2.1 : ℤ) + (n - 1 : ℕ)

/-- Incidence with a principal line. -/
def OnLine {n : ℕ} (line : PrincipalLine n) (p : Point n) : Prop :=
  lineValue line.1 p = line.2.1

instance {n : ℕ} (line : PrincipalLine n) : DecidablePred (OnLine line) :=
  fun _ => inferInstance

/-- Three points on one principal line are Euclidean-collinear. -/
theorem principal_collinear {n : ℕ} {line : PrincipalLine n}
    {a b c : Point n} (ha : OnLine line a) (hb : OnLine line b)
    (hc : OnLine line c) : determinant a b c = 0 := by
  rcases line with ⟨family, index⟩
  cases family with
  | row =>
      simp only [OnLine, lineValue] at ha hb hc
      simp [determinant, ha, hb, hc]
  | column =>
      simp only [OnLine, lineValue] at ha hb hc
      simp [determinant, ha, hb, hc]
  | sum =>
      simp only [OnLine, lineValue] at ha hb hc
      have hba : ((b.2.1 : ℤ) - (a.2.1 : ℤ)) =
          -((b.1.1 : ℤ) - (a.1.1 : ℤ)) := by
        linarith
      have hca : ((c.2.1 : ℤ) - (a.2.1 : ℤ)) =
          -((c.1.1 : ℤ) - (a.1.1 : ℤ)) := by
        linarith
      rw [determinant, hba, hca]
      ring
  | difference =>
      simp only [OnLine, lineValue] at ha hb hc
      have hba : ((b.2.1 : ℤ) - (a.2.1 : ℤ)) =
          ((b.1.1 : ℤ) - (a.1.1 : ℤ)) := by
        linarith
      have hca : ((c.2.1 : ℤ) - (a.2.1 : ℤ)) =
          ((c.1.1 : ℤ) - (a.1.1 : ℤ)) := by
        linarith
      rw [determinant, hba, hca]
      ring

/-- A no-three-in-line set occupies every principal line at most twice. -/
theorem principalLine_card_le_two {n : ℕ} {s : Finset (Point n)}
    (hntil : NoThreeInLine s) (line : PrincipalLine n) :
    (s.filter (OnLine line)).card ≤ 2 := by
  by_contra h
  have hthree : 2 < (s.filter (OnLine line)).card := Nat.lt_of_not_ge h
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ :=
    Finset.two_lt_card.mp hthree
  have haS : a ∈ s := (Finset.mem_filter.mp ha).1
  have hbS : b ∈ s := (Finset.mem_filter.mp hb).1
  have hcS : c ∈ s := (Finset.mem_filter.mp hc).1
  have haL : OnLine line a := (Finset.mem_filter.mp ha).2
  have hbL : OnLine line b := (Finset.mem_filter.mp hb).2
  have hcL : OnLine line c := (Finset.mem_filter.mp hc).2
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
    (principal_collinear haL hbL hcL)

/-- Weighted coverage of a point by all principal lines. -/
def coverage {n : ℕ} (weight : PrincipalLine n → ℕ) (p : Point n) : ℕ :=
  ∑ line : PrincipalLine n, if OnLine line p then weight line else 0

/-- Twice the total line weight, the capacity-two dual objective. -/
def certificateCost {n : ℕ} (weight : PrincipalLine n → ℕ) : ℕ :=
  ∑ line : PrincipalLine n, 2 * weight line

private theorem sum_indicator_eq_card_filter {α : Type*} [DecidableEq α]
    (s : Finset α) (P : α → Prop) [DecidablePred P] (w : ℕ) :
    (∑ a ∈ s, if P a then w else 0) = (s.filter P).card * w := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      by_cases hP : P a <;>
        simp [ha, hP, ih, Nat.add_mul]

private theorem double_count {n : ℕ} (s : Finset (Point n))
    (weight : PrincipalLine n → ℕ) :
    (∑ p ∈ s, coverage weight p) =
      ∑ line : PrincipalLine n, (s.filter (OnLine line)).card * weight line := by
  calc
    (∑ p ∈ s, coverage weight p) =
        ∑ p ∈ s, ∑ line : PrincipalLine n,
          if OnLine line p then weight line else 0 := by rfl
    _ = ∑ line : PrincipalLine n, ∑ p ∈ s,
          if OnLine line p then weight line else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ line : PrincipalLine n,
          (s.filter (OnLine line)).card * weight line := by
          apply Finset.sum_congr rfl
          intro line _
          exact sum_indicator_eq_card_filter s (OnLine line) (weight line)

/-- Exact weighted line-cover inequality. -/
theorem certificate_bound {n q : ℕ} {s : Finset (Point n)}
    (weight : PrincipalLine n → ℕ)
    (hcover : ∀ p : ↥s, q ≤ coverage weight p.1)
    (hntil : NoThreeInLine s) :
    q * s.card ≤ certificateCost weight := by
  have hpoint : (∑ p ∈ s, q) ≤ ∑ p ∈ s, coverage weight p := by
    apply Finset.sum_le_sum
    intro p hp
    exact hcover ⟨p, hp⟩
  have hline :
      (∑ line : PrincipalLine n,
          (s.filter (OnLine line)).card * weight line) ≤
        certificateCost weight := by
    apply Finset.sum_le_sum
    intro line _
    exact Nat.mul_le_mul_right (weight line)
      (principalLine_card_le_two hntil line)
  calc
    q * s.card = ∑ _p ∈ s, q := by simp [Nat.mul_comm]
    _ ≤ ∑ p ∈ s, coverage weight p := hpoint
    _ = ∑ line : PrincipalLine n,
          (s.filter (OnLine line)).card * weight line := double_count s weight
    _ ≤ certificateCost weight := hline

/-- A strict integral dual objective gives a cardinality upper bound. -/
theorem card_le_of_certificate {n parity q k : ℕ} {s : Finset (Point n)}
    (weight : PrincipalLine n → ℕ) (hq : 0 < q)
    (hcost : certificateCost weight < q * (k + 1))
    (hglobal : ∀ p : Point n, InColor parity p → q ≤ coverage weight p)
    (hcolor : Monochromatic parity s) (hntil : NoThreeInLine s) :
    s.card ≤ k := by
  have hb := certificate_bound weight (fun p => hglobal p.1 (hcolor p)) hntil
  have hmul : q * s.card < q * (k + 1) := lt_of_le_of_lt hb hcost
  have hlt : s.card < k + 1 := (Nat.mul_lt_mul_left hq).mp hmul
  omega

end Checkerboard
