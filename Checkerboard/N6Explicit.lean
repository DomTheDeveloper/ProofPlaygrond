import Checkerboard.FourCertificate
import Checkerboard.N6SATTest

/-!
# Explicit 6×6 checkerboard base cases

The quadratic relaxation is not integral on the 6-board.  This module transports
an arbitrary monochromatic no-three-in-line set to eighteen Boolean indicators,
uses closed certificates for the relevant row, column, and diagonal fibers, and
then applies the compact Presburger certificates in `N6SATTest`.

Proof developed by Dominic Dabish. ProofOrchestrator, using OpenAI GPT-5.6 Thinking,
assisted with the mathematical argument, Lean formalization, and submission
preparation. All formal claims are checked by the repository-pinned Lean compiler.
-/

namespace Checkerboard

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

private def n6p0Point : Fin 18 → Point 6 := ![
  ((0 : Fin 6), (0 : Fin 6)), ((0 : Fin 6), (2 : Fin 6)),
  ((0 : Fin 6), (4 : Fin 6)), ((1 : Fin 6), (1 : Fin 6)),
  ((1 : Fin 6), (3 : Fin 6)), ((1 : Fin 6), (5 : Fin 6)),
  ((2 : Fin 6), (0 : Fin 6)), ((2 : Fin 6), (2 : Fin 6)),
  ((2 : Fin 6), (4 : Fin 6)), ((3 : Fin 6), (1 : Fin 6)),
  ((3 : Fin 6), (3 : Fin 6)), ((3 : Fin 6), (5 : Fin 6)),
  ((4 : Fin 6), (0 : Fin 6)), ((4 : Fin 6), (2 : Fin 6)),
  ((4 : Fin 6), (4 : Fin 6)), ((5 : Fin 6), (1 : Fin 6)),
  ((5 : Fin 6), (3 : Fin 6)), ((5 : Fin 6), (5 : Fin 6))]

private def n6p1Point : Fin 18 → Point 6 := ![
  ((0 : Fin 6), (1 : Fin 6)), ((0 : Fin 6), (3 : Fin 6)),
  ((0 : Fin 6), (5 : Fin 6)), ((1 : Fin 6), (0 : Fin 6)),
  ((1 : Fin 6), (2 : Fin 6)), ((1 : Fin 6), (4 : Fin 6)),
  ((2 : Fin 6), (1 : Fin 6)), ((2 : Fin 6), (3 : Fin 6)),
  ((2 : Fin 6), (5 : Fin 6)), ((3 : Fin 6), (0 : Fin 6)),
  ((3 : Fin 6), (2 : Fin 6)), ((3 : Fin 6), (4 : Fin 6)),
  ((4 : Fin 6), (1 : Fin 6)), ((4 : Fin 6), (3 : Fin 6)),
  ((4 : Fin 6), (5 : Fin 6)), ((5 : Fin 6), (0 : Fin 6)),
  ((5 : Fin 6), (2 : Fin 6)), ((5 : Fin 6), (4 : Fin 6))]

private theorem n6p0_injective : Function.Injective n6p0Point := by decide
private theorem n6p1_injective : Function.Injective n6p1Point := by decide

private theorem n6p0_surjective :
    ∀ p : Point 6, InColor 0 p → ∃ i, n6p0Point i = p := by
  letI : DecidablePred (fun p : Point 6 =>
      InColor 0 p → ∃ i, n6p0Point i = p) := by
    intro p
    unfold InColor
    infer_instance
  exact of_decide_eq_true rfl

private theorem n6p1_surjective :
    ∀ p : Point 6, InColor 1 p → ∃ i, n6p1Point i = p := by
  letI : DecidablePred (fun p : Point 6 =>
      InColor 1 p → ∃ i, n6p1Point i = p) := by
    intro p
    unfold InColor
    infer_instance
  exact of_decide_eq_true rfl

private def chosenIndices (point : Fin 18 → Point 6)
    (s : Finset (Point 6)) : Finset (Fin 18) :=
  Finset.univ.filter fun i => point i ∈ s

private def chosenOnLine (point : Fin 18 → Point 6)
    (s : Finset (Point 6)) (line : PrincipalLine 6) : Finset (Fin 18) :=
  Finset.univ.filter fun i => point i ∈ s ∧ OnLine line (point i)

private theorem card_filter_bool {α : Type*} (s : Finset α) (x : α → Bool) :
    (s.filter fun i => x i = true).card =
      Finset.sum s (fun i => bitNat (x i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      cases hxa : x a <;> simp [ha, ih, hxa, bitNat]

private theorem card_filter_bool_and {α : Type*} (s : Finset α)
    (x : α → Bool) (p : α → Prop) [DecidablePred p] :
    (s.filter fun i => x i = true ∧ p i).card =
      Finset.sum (s.filter p) (fun i => bitNat (x i)) := by
  classical
  have hfilter :
      s.filter (fun i => x i = true ∧ p i) =
        (s.filter p).filter (fun i => x i = true) := by
    ext i
    simp [and_comm, and_left_comm, and_assoc]
  rw [hfilter]
  exact card_filter_bool (s.filter p) x

private theorem chosenIndices_image
    {parity : ℕ} (point : Fin 18 → Point 6)
    (hsurj : ∀ p : Point 6, InColor parity p → ∃ i, point i = p)
    (s : Finset (Point 6)) (hcolor : Monochromatic parity s) :
    (chosenIndices point s).image point = s := by
  ext p
  constructor
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨i, hi, rfl⟩
    exact (Finset.mem_filter.mp hi).2
  · intro hp
    obtain ⟨i, hi⟩ := hsurj p (hcolor ⟨p, hp⟩)
    subst p
    apply Finset.mem_image.mpr
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩, rfl⟩

private theorem chosenOnLine_image
    {parity : ℕ} (point : Fin 18 → Point 6)
    (hsurj : ∀ p : Point 6, InColor parity p → ∃ i, point i = p)
    (s : Finset (Point 6)) (hcolor : Monochromatic parity s)
    (line : PrincipalLine 6) :
    (chosenOnLine point s line).image point = s.filter (OnLine line) := by
  ext p
  constructor
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨i, hi, rfl⟩
    exact Finset.mem_filter.mpr (Finset.mem_filter.mp hi).2
  · intro hp
    have hpS := (Finset.mem_filter.mp hp).1
    have hpL := (Finset.mem_filter.mp hp).2
    obtain ⟨i, hi⟩ := hsurj p (hcolor ⟨p, hpS⟩)
    subst p
    apply Finset.mem_image.mpr
    exact ⟨i, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ⟨hpS, hpL⟩⟩, rfl⟩

private theorem upper_of_boolean_certificate
    {parity : ℕ} (point : Fin 18 → Point 6)
    (hinj : Function.Injective point)
    (hsurj : ∀ p : Point 6, InColor parity p → ∃ i, point i = p)
    (hfinite : ∀ x : Fin 18 → Bool,
      (∀ line : PrincipalLine 6,
        (Finset.univ.filter fun i => x i = true ∧ OnLine line (point i)).card ≤ 2) →
      (Finset.univ.filter fun i => x i = true).card ≤ 8)
    (s : Finset (Point 6))
    (hcolor : Monochromatic parity s) (hntil : NoThreeInLine s) :
    s.card ≤ 8 := by
  let x : Fin 18 → Bool := fun i => decide (point i ∈ s)
  have hline : ∀ line : PrincipalLine 6,
      (Finset.univ.filter fun i => x i = true ∧ OnLine line (point i)).card ≤ 2 := by
    intro line
    have himage := chosenOnLine_image point hsurj s hcolor line
    have hcardImage := Finset.card_image_of_injective
      (chosenOnLine point s line) hinj
    have hchosen :
        (chosenOnLine point s line).card = (s.filter (OnLine line)).card := by
      calc
        (chosenOnLine point s line).card =
            ((chosenOnLine point s line).image point).card := hcardImage.symm
        _ = (s.filter (OnLine line)).card := congrArg Finset.card himage
    have heq :
        (Finset.univ.filter fun i => x i = true ∧ OnLine line (point i)).card =
          (s.filter (OnLine line)).card := by
      simpa [x, chosenOnLine] using hchosen
    rw [heq]
    exact principalLine_card_le_two hntil line
  have hbool := hfinite x hline
  have himage := chosenIndices_image point hsurj s hcolor
  have hcardImage := Finset.card_image_of_injective (chosenIndices point s) hinj
  have hchosen : (chosenIndices point s).card = s.card := by
    calc
      (chosenIndices point s).card = ((chosenIndices point s).image point).card :=
        hcardImage.symm
      _ = s.card := congrArg Finset.card himage
  have heq : (Finset.univ.filter fun i => x i = true).card = s.card := by
    simpa [x, chosenIndices] using hchosen
  rwa [heq] at hbool

private def p0Line : Fin 19 → PrincipalLine 6 := ![
  (.row, ⟨0, by decide⟩), (.row, ⟨1, by decide⟩),
  (.row, ⟨2, by decide⟩), (.row, ⟨3, by decide⟩),
  (.row, ⟨4, by decide⟩), (.row, ⟨5, by decide⟩),
  (.column, ⟨0, by decide⟩), (.column, ⟨2, by decide⟩),
  (.column, ⟨4, by decide⟩), (.column, ⟨1, by decide⟩),
  (.column, ⟨3, by decide⟩), (.column, ⟨5, by decide⟩),
  (.sum, ⟨2, by decide⟩), (.sum, ⟨4, by decide⟩),
  (.sum, ⟨6, by decide⟩), (.sum, ⟨8, by decide⟩),
  (.difference, ⟨5, by decide⟩), (.difference, ⟨3, by decide⟩),
  (.difference, ⟨7, by decide⟩)]

private def p0Index : Fin 19 → Finset (Fin 18) := ![
  {0, 1, 2}, {3, 4, 5}, {6, 7, 8}, {9, 10, 11},
  {12, 13, 14}, {15, 16, 17}, {0, 6, 12}, {1, 7, 13},
  {2, 8, 14}, {3, 9, 15}, {4, 10, 16}, {5, 11, 17},
  {1, 3, 6}, {2, 4, 7, 9, 12}, {5, 8, 10, 13, 15},
  {11, 14, 16}, {0, 3, 7, 10, 14, 17}, {1, 4, 8, 11},
  {6, 9, 13, 16}]

private def p1Line : Fin 19 → PrincipalLine 6 := ![
  (.row, ⟨0, by decide⟩), (.row, ⟨1, by decide⟩),
  (.row, ⟨2, by decide⟩), (.row, ⟨3, by decide⟩),
  (.row, ⟨4, by decide⟩), (.row, ⟨5, by decide⟩),
  (.column, ⟨1, by decide⟩), (.column, ⟨3, by decide⟩),
  (.column, ⟨5, by decide⟩), (.column, ⟨0, by decide⟩),
  (.column, ⟨2, by decide⟩), (.column, ⟨4, by decide⟩),
  (.sum, ⟨3, by decide⟩), (.sum, ⟨5, by decide⟩),
  (.sum, ⟨7, by decide⟩), (.difference, ⟨4, by decide⟩),
  (.difference, ⟨2, by decide⟩), (.difference, ⟨6, by decide⟩),
  (.difference, ⟨8, by decide⟩)]

private def p1Index : Fin 19 → Finset (Fin 18) := ![
  {0, 1, 2}, {3, 4, 5}, {6, 7, 8}, {9, 10, 11},
  {12, 13, 14}, {15, 16, 17}, {0, 6, 12}, {1, 7, 13},
  {2, 8, 14}, {3, 9, 15}, {4, 10, 16}, {5, 11, 17},
  {1, 4, 6, 9}, {2, 5, 7, 10, 12, 15}, {8, 11, 13, 16},
  {0, 4, 7, 11, 14}, {1, 5, 8}, {3, 6, 10, 13, 17},
  {9, 12, 16}]

private theorem p0_line_indices (j : Fin 19) :
    Finset.univ.filter (fun i => OnLine (p0Line j) (n6p0Point i)) = p0Index j := by
  fin_cases j <;> decide

private theorem p1_line_indices (j : Fin 19) :
    Finset.univ.filter (fun i => OnLine (p1Line j) (n6p1Point i)) = p1Index j := by
  fin_cases j <;> decide

private theorem line_sum_le_two
    (point : Fin 18 → Point 6) (x : Fin 18 → Bool)
    (line : PrincipalLine 6) (idx : Finset (Fin 18))
    (hidx : Finset.univ.filter (fun i => OnLine line (point i)) = idx)
    (hline : (Finset.univ.filter fun i =>
      x i = true ∧ OnLine line (point i)).card ≤ 2) :
    Finset.sum idx (fun i => bitNat (x i)) ≤ 2 := by
  rw [card_filter_bool_and, hidx] at hline
  exact hline

private def all18 : Finset (Fin 18) :=
  {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17}

private theorem all18_eq_univ : all18 = Finset.univ := by decide

private theorem n6p0_boolean_bound :
    ∀ x : Fin 18 → Bool,
      (∀ line : PrincipalLine 6,
        (Finset.univ.filter fun i =>
          x i = true ∧ OnLine line (n6p0Point i)).card ≤ 2) →
      (Finset.univ.filter fun i => x i = true).card ≤ 8 := by
  intro x hline
  have hb (j : Fin 19) : Finset.sum (p0Index j) (fun i => bitNat (x i)) ≤ 2 :=
    line_sum_le_two n6p0Point x (p0Line j) (p0Index j)
      (p0_line_indices j) (hline (p0Line j))
  have h0 : bitNat (x 0) + bitNat (x 1) + bitNat (x 2) ≤ 2 := by simpa [p0Index, Nat.add_assoc] using hb 0
  have h1 : bitNat (x 3) + bitNat (x 4) + bitNat (x 5) ≤ 2 := by simpa [p0Index, Nat.add_assoc] using hb 1
  have h2 : bitNat (x 6) + bitNat (x 7) + bitNat (x 8) ≤ 2 := by simpa [p0Index, Nat.add_assoc] using hb 2
  have h3 : bitNat (x 9) + bitNat (x 10) + bitNat (x 11) ≤ 2 := by simpa [p0Index, Nat.add_assoc] using hb 3
  have h4 : bitNat (x 12) + bitNat (x 13) + bitNat (x 14) ≤ 2 := by simpa [p0Index, Nat.add_assoc] using hb 4
  have h5 : bitNat (x 15) + bitNat (x 16) + bitNat (x 17) ≤ 2 := by simpa [p0Index, Nat.add_assoc] using hb 5
  have h6 : bitNat (x 0) + bitNat (x 6) + bitNat (x 12) ≤ 2 := by simpa [p0Index, Nat.add_assoc] using hb 6
  have h7 : bitNat (x 1) + bitNat (x 7) + bitNat (x 13) ≤ 2 := by simpa [p0Index, Nat.add_assoc] using hb 7
  have h8 : bitNat (x 2) + bitNat (x 8) + bitNat (x 14) ≤ 2 := by simpa [p0Index, Nat.add_assoc] using hb 8
  have h9 : bitNat (x 3) + bitNat (x 9) + bitNat (x 15) ≤ 2 := by simpa [p0Index, Nat.add_assoc] using hb 9
  have h10 : bitNat (x 4) + bitNat (x 10) + bitNat (x 16) ≤ 2 := by simpa [p0Index, Nat.add_assoc] using hb 10
  have h11 : bitNat (x 5) + bitNat (x 11) + bitNat (x 17) ≤ 2 := by simpa [p0Index, Nat.add_assoc] using hb 11
  have h12 : bitNat (x 1) + bitNat (x 3) + bitNat (x 6) ≤ 2 := by simpa [p0Index, Nat.add_assoc] using hb 12
  have h13 : bitNat (x 2) + bitNat (x 4) + bitNat (x 7) + bitNat (x 9) + bitNat (x 12) ≤ 2 := by simpa [p0Index, Nat.add_assoc] using hb 13
  have h14 : bitNat (x 5) + bitNat (x 8) + bitNat (x 10) + bitNat (x 13) + bitNat (x 15) ≤ 2 := by simpa [p0Index, Nat.add_assoc] using hb 14
  have h15 : bitNat (x 11) + bitNat (x 14) + bitNat (x 16) ≤ 2 := by simpa [p0Index, Nat.add_assoc] using hb 15
  have h16 : bitNat (x 0) + bitNat (x 3) + bitNat (x 7) + bitNat (x 10) + bitNat (x 14) + bitNat (x 17) ≤ 2 := by simpa [p0Index, Nat.add_assoc] using hb 16
  have h17 : bitNat (x 1) + bitNat (x 4) + bitNat (x 8) + bitNat (x 11) ≤ 2 := by simpa [p0Index, Nat.add_assoc] using hb 17
  have h18 : bitNat (x 6) + bitNat (x 9) + bitNat (x 13) + bitNat (x 16) ≤ 2 := by simpa [p0Index, Nat.add_assoc] using hb 18
  rw [card_filter_bool]
  rw [← all18_eq_univ]
  simpa [all18, Nat.add_assoc] using
    n6p0_sat (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)
      (x 6) (x 7) (x 8) (x 9) (x 10) (x 11)
      (x 12) (x 13) (x 14) (x 15) (x 16) (x 17)
      h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18

private theorem n6p1_boolean_bound :
    ∀ x : Fin 18 → Bool,
      (∀ line : PrincipalLine 6,
        (Finset.univ.filter fun i =>
          x i = true ∧ OnLine line (n6p1Point i)).card ≤ 2) →
      (Finset.univ.filter fun i => x i = true).card ≤ 8 := by
  intro x hline
  have hb (j : Fin 19) : Finset.sum (p1Index j) (fun i => bitNat (x i)) ≤ 2 :=
    line_sum_le_two n6p1Point x (p1Line j) (p1Index j)
      (p1_line_indices j) (hline (p1Line j))
  have h0 : bitNat (x 0) + bitNat (x 1) + bitNat (x 2) ≤ 2 := by simpa [p1Index, Nat.add_assoc] using hb 0
  have h1 : bitNat (x 3) + bitNat (x 4) + bitNat (x 5) ≤ 2 := by simpa [p1Index, Nat.add_assoc] using hb 1
  have h2 : bitNat (x 6) + bitNat (x 7) + bitNat (x 8) ≤ 2 := by simpa [p1Index, Nat.add_assoc] using hb 2
  have h3 : bitNat (x 9) + bitNat (x 10) + bitNat (x 11) ≤ 2 := by simpa [p1Index, Nat.add_assoc] using hb 3
  have h4 : bitNat (x 12) + bitNat (x 13) + bitNat (x 14) ≤ 2 := by simpa [p1Index, Nat.add_assoc] using hb 4
  have h5 : bitNat (x 15) + bitNat (x 16) + bitNat (x 17) ≤ 2 := by simpa [p1Index, Nat.add_assoc] using hb 5
  have h6 : bitNat (x 0) + bitNat (x 6) + bitNat (x 12) ≤ 2 := by simpa [p1Index, Nat.add_assoc] using hb 6
  have h7 : bitNat (x 1) + bitNat (x 7) + bitNat (x 13) ≤ 2 := by simpa [p1Index, Nat.add_assoc] using hb 7
  have h8 : bitNat (x 2) + bitNat (x 8) + bitNat (x 14) ≤ 2 := by simpa [p1Index, Nat.add_assoc] using hb 8
  have h9 : bitNat (x 3) + bitNat (x 9) + bitNat (x 15) ≤ 2 := by simpa [p1Index, Nat.add_assoc] using hb 9
  have h10 : bitNat (x 4) + bitNat (x 10) + bitNat (x 16) ≤ 2 := by simpa [p1Index, Nat.add_assoc] using hb 10
  have h11 : bitNat (x 5) + bitNat (x 11) + bitNat (x 17) ≤ 2 := by simpa [p1Index, Nat.add_assoc] using hb 11
  have h12 : bitNat (x 1) + bitNat (x 4) + bitNat (x 6) + bitNat (x 9) ≤ 2 := by simpa [p1Index, Nat.add_assoc] using hb 12
  have h13 : bitNat (x 2) + bitNat (x 5) + bitNat (x 7) + bitNat (x 10) + bitNat (x 12) + bitNat (x 15) ≤ 2 := by simpa [p1Index, Nat.add_assoc] using hb 13
  have h14 : bitNat (x 8) + bitNat (x 11) + bitNat (x 13) + bitNat (x 16) ≤ 2 := by simpa [p1Index, Nat.add_assoc] using hb 14
  have h15 : bitNat (x 0) + bitNat (x 4) + bitNat (x 7) + bitNat (x 11) + bitNat (x 14) ≤ 2 := by simpa [p1Index, Nat.add_assoc] using hb 15
  have h16 : bitNat (x 1) + bitNat (x 5) + bitNat (x 8) ≤ 2 := by simpa [p1Index, Nat.add_assoc] using hb 16
  have h17 : bitNat (x 3) + bitNat (x 6) + bitNat (x 10) + bitNat (x 13) + bitNat (x 17) ≤ 2 := by simpa [p1Index, Nat.add_assoc] using hb 17
  have h18 : bitNat (x 9) + bitNat (x 12) + bitNat (x 16) ≤ 2 := by simpa [p1Index, Nat.add_assoc] using hb 18
  rw [card_filter_bool]
  rw [← all18_eq_univ]
  simpa [all18, Nat.add_assoc] using
    n6p1_sat (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)
      (x 6) (x 7) (x 8) (x 9) (x 10) (x 11)
      (x 12) (x 13) (x 14) (x 15) (x 16) (x 17)
      h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18

/-- `D_mono(6,0) ≤ 8`. -/
theorem n6_zero_upper (s : Finset (Point 6))
    (hcolor : Monochromatic 0 s) (hntil : NoThreeInLine s) : s.card ≤ 8 := by
  exact upper_of_boolean_certificate n6p0Point n6p0_injective n6p0_surjective
    n6p0_boolean_bound s hcolor hntil

/-- `D_mono(6,1) ≤ 8`. -/
theorem n6_one_upper (s : Finset (Point 6))
    (hcolor : Monochromatic 1 s) (hntil : NoThreeInLine s) : s.card ≤ 8 := by
  exact upper_of_boolean_certificate n6p1Point n6p1_injective n6p1_surjective
    n6p1_boolean_bound s hcolor hntil

end Checkerboard
