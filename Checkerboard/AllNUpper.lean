import Checkerboard.QuadraticCosts

/-!
# The general checkerboard upper bound above the final 6×6 base case

The quadratic line cover proves `|S| ≤ 2n-4` for both checkerboard colors on
every board `n≥7`.  The thin color of the 7-board uses a separate exact small
cover; all larger cases use the uniform quadratic family.
-/

namespace Checkerboard

/-- Fat color on every odd board `2m+1`, `m≥3`. -/
theorem odd_zero_upper {m : ℕ} (hm : 3 ≤ m)
    (s : Finset (Point (2 * m + 1)))
    (hcolor : Monochromatic 0 s) (hntil : NoThreeInLine s) :
    s.card ≤ 4 * m - 2 := by
  obtain ⟨hr, hc, hs, hd⟩ := oddQuadratic_nonnegative m 0
  apply card_le_of_fourCertificate (oddQuadraticWeights m 0)
      (q := 16 * (m : ℚ) ^ 2) (k := 4 * m - 2)
  · positivity
  · rw [oddQuadratic_cost_zero]
    have hmQ : (3 : ℚ) ≤ m := by exact_mod_cast hm
    have hmpos : (0 : ℚ) < m := by nlinarith
    have hpoly : 0 < 2 * (m : ℚ) ^ 2 - 6 * m + 1 := by nlinarith
    have hprod := mul_pos hmpos hpoly
    have hk : 2 ≤ 4 * m := by omega
    have hcast : (((4 * m - 2 : ℕ) : ℚ)) = 4 * (m : ℚ) - 2 := by
      rw [Nat.cast_sub hk]
      norm_num
    rw [hcast]
    nlinarith
  · exact hr
  · exact hc
  · exact hs
  · exact hd
  · intro p
    rw [oddQuadratic_coverage m 0 (Or.inl rfl) p.1 (hcolor p)]
  · exact hntil

/-- Thin color on every odd board `2m+1`, `m≥4`. -/
theorem odd_one_upper {m : ℕ} (hm : 4 ≤ m)
    (s : Finset (Point (2 * m + 1)))
    (hcolor : Monochromatic 1 s) (hntil : NoThreeInLine s) :
    s.card ≤ 4 * m - 2 := by
  obtain ⟨hr, hc, hs, hd⟩ := oddQuadratic_nonnegative m 1
  apply card_le_of_fourCertificate (oddQuadraticWeights m 1)
      (q := 16 * (m : ℚ) ^ 2) (k := 4 * m - 2)
  · positivity
  · rw [oddQuadratic_cost_one]
    have hmQ : (4 : ℚ) ≤ m := by exact_mod_cast hm
    have hmpos : (0 : ℚ) < m := by nlinarith
    have hpoly : 0 < 2 * (m : ℚ) ^ 2 - 6 * m - 2 := by nlinarith
    have hprod := mul_pos hmpos hpoly
    have hk : 2 ≤ 4 * m := by omega
    have hcast : (((4 * m - 2 : ℕ) : ℚ)) = 4 * (m : ℚ) - 2 := by
      rw [Nat.cast_sub hk]
      norm_num
    rw [hcast]
    nlinarith
  · exact hr
  · exact hc
  · exact hs
  · exact hd
  · intro p
    rw [oddQuadratic_coverage m 1 (Or.inr rfl) p.1 (hcolor p)]
  · exact hntil

/-- Both colors on every even board `2m`, `m≥4`. -/
theorem even_upper {m parity : ℕ} (hm : 4 ≤ m)
    (hp : parity = 0 ∨ parity = 1)
    (s : Finset (Point (2 * m)))
    (hcolor : Monochromatic parity s) (hntil : NoThreeInLine s) :
    s.card ≤ 4 * m - 4 := by
  have hm1 : 1 ≤ m := by omega
  have hmQ : (4 : ℚ) ≤ m := by exact_mod_cast hm
  have hcenter : (0 : ℚ) < 2 * m - 1 := by nlinarith
  have hpoly : 0 < 2 * (m : ℚ) ^ 2 - 8 * m + 3 := by nlinarith
  have hprod := mul_pos hcenter hpoly
  have hk : 4 ≤ 4 * m := by omega
  have hcast : (((4 * m - 4 : ℕ) : ℚ)) = 4 * (m : ℚ) - 4 := by
    rw [Nat.cast_sub hk]
    norm_num
  have hpCost := hp
  obtain ⟨hr, hc, hs, hd⟩ := evenQuadratic_nonnegative m parity hm1
  apply card_le_of_fourCertificate (evenQuadraticWeights m parity)
      (q := 4 * ((2 * m : ℚ) - 1) ^ 2) (k := 4 * m - 4)
  · positivity
  · rcases hpCost with rfl | rfl
    · rw [evenQuadratic_cost_zero m hm1, hcast]
      nlinarith
    · rw [evenQuadratic_cost_one m hm1, hcast]
      nlinarith
  · exact hr
  · exact hc
  · exact hs
  · exact hd
  · intro p
    rw [evenQuadratic_coverage m parity hp hm1 p.1 (hcolor p)]
  · exact hntil

/-- Small exact cover for the exceptional thin color of the 7-board. -/
def n7ThinWeights : FourWeights 7 where
  row i := if i.1 = 0 ∨ i.1 = 6 then 1 else 0
  column i := if i.1 = 0 ∨ i.1 = 6 then 1 else 0
  sum j :=
    if j.1 % 2 = 1 then
      if Nat.dist j.1 6 = 1 then 2 else if Nat.dist j.1 6 = 3 then 1 else 0
    else 0
  difference j :=
    if j.1 % 2 = 1 then
      if Nat.dist j.1 6 = 1 then 2 else if Nat.dist j.1 6 = 3 then 1 else 0
    else 0

private theorem n7Thin_cost : fourCost n7ThinWeights = 32 := by
  norm_num [fourCost, n7ThinWeights, Fin.sum_univ_succ, Nat.dist]
  decide

private theorem n7Thin_nonnegative :
    (∀ i, 0 ≤ n7ThinWeights.row i) ∧
    (∀ i, 0 ≤ n7ThinWeights.column i) ∧
    (∀ i, 0 ≤ n7ThinWeights.sum i) ∧
    ∀ i, 0 ≤ n7ThinWeights.difference i := by
  constructor
  · intro i
    fin_cases i <;> norm_num [n7ThinWeights]
  constructor
  · intro i
    fin_cases i <;> norm_num [n7ThinWeights]
  constructor
  · intro i
    fin_cases i <;> norm_num [n7ThinWeights, Nat.dist]
  · intro i
    fin_cases i <;> norm_num [n7ThinWeights, Nat.dist]

private theorem n7Thin_cover :
    ∀ p : Point 7, InColor 1 p → 3 ≤ fourCoverage n7ThinWeights p := by
  rintro ⟨i, j⟩ hp
  fin_cases i <;> fin_cases j
  all_goals
    norm_num [InColor] at hp
  all_goals
    norm_num [fourCoverage, n7ThinWeights, sumIndex,
      differenceIndex, Nat.dist]

/-- Exceptional thin-color bound on the 7-board. -/
theorem n7_one_upper (s : Finset (Point 7))
    (hcolor : Monochromatic 1 s) (hntil : NoThreeInLine s) : s.card ≤ 10 := by
  obtain ⟨hr, hc, hs, hd⟩ := n7Thin_nonnegative
  apply card_le_of_fourCertificate n7ThinWeights (q := 3) (k := 10)
  · norm_num
  · rw [n7Thin_cost]
    norm_num
  · exact hr
  · exact hc
  · exact hs
  · exact hd
  · intro p
    exact n7Thin_cover p.1 (hcolor p)
  · exact hntil

/-- Fat-color bound on the 7-board. -/
theorem n7_zero_upper (s : Finset (Point 7))
    (hcolor : Monochromatic 0 s) (hntil : NoThreeInLine s) : s.card ≤ 10 := by
  simpa using odd_zero_upper (m := 3) (by decide) s hcolor hntil

/-- The general bound for all boards `n≥7` and either color. -/
theorem checkerboard_upper_from_seven {n parity : ℕ}
    (hn : 7 ≤ n) (hp : parity = 0 ∨ parity = 1)
    (s : Finset (Point n))
    (hcolor : Monochromatic parity s) (hntil : NoThreeInLine s) :
    s.card ≤ 2 * n - 4 := by
  obtain ⟨m, hEven | hOdd⟩ := n.even_or_odd'
  · subst n
    have hm : 4 ≤ m := by omega
    have h := even_upper hm hp s hcolor hntil
    omega
  · subst n
    have hm : 3 ≤ m := by omega
    by_cases hsmall : m = 3
    · subst m
      rcases hp with rfl | rfl
      · exact n7_zero_upper s hcolor hntil
      · exact n7_one_upper s hcolor hntil
    · have hm4 : 4 ≤ m := by omega
      rcases hp with rfl | rfl
      · have h := odd_zero_upper hm s hcolor hntil
        omega
      · have h := odd_one_upper hm4 s hcolor hntil
        omega

end Checkerboard
