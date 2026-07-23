import Checkerboard.FourCertificate

/-!
# The final 6×6 base cases

The uniform quadratic cover is sharp at value nine on the 6-board, so an
integrality argument is required. Each color class has eighteen points. We
transport an arbitrary monochromatic set to eighteen Boolean variables, and
`bv_decide` checks the finite statement that row, column, and slope `±1`
capacities already force at most eight selected points.
-/

namespace Checkerboard

/-- Enumeration of the fat color class of the 6-board. -/
def n6p0Point : Fin 18 → Point 6 := ![
  ((0 : Fin 6), (0 : Fin 6)), ((0 : Fin 6), (2 : Fin 6)),
  ((0 : Fin 6), (4 : Fin 6)), ((1 : Fin 6), (1 : Fin 6)),
  ((1 : Fin 6), (3 : Fin 6)), ((1 : Fin 6), (5 : Fin 6)),
  ((2 : Fin 6), (0 : Fin 6)), ((2 : Fin 6), (2 : Fin 6)),
  ((2 : Fin 6), (4 : Fin 6)), ((3 : Fin 6), (1 : Fin 6)),
  ((3 : Fin 6), (3 : Fin 6)), ((3 : Fin 6), (5 : Fin 6)),
  ((4 : Fin 6), (0 : Fin 6)), ((4 : Fin 6), (2 : Fin 6)),
  ((4 : Fin 6), (4 : Fin 6)), ((5 : Fin 6), (1 : Fin 6)),
  ((5 : Fin 6), (3 : Fin 6)), ((5 : Fin 6), (5 : Fin 6))]

/-- Enumeration of the thin color class of the 6-board. -/
def n6p1Point : Fin 18 → Point 6 := ![
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
    ∀ p : Point 6, InColor 0 p → ∃ i, n6p0Point i = p := by decide

private theorem n6p1_surjective :
    ∀ p : Point 6, InColor 1 p → ∃ i, n6p1Point i = p := by decide

private def chosenIndices (point : Fin 18 → Point 6)
    (s : Finset (Point 6)) : Finset (Fin 18) :=
  Finset.univ.filter fun i => point i ∈ s

private def chosenOnLine (point : Fin 18 → Point 6)
    (s : Finset (Point 6)) (line : PrincipalLine 6) : Finset (Fin 18) :=
  Finset.univ.filter fun i => point i ∈ s ∧ OnLine line (point i)

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

private theorem n6p0_boolean_bound :
    ∀ x : Fin 18 → Bool,
      (∀ line : PrincipalLine 6,
        (Finset.univ.filter fun i =>
          x i = true ∧ OnLine line (n6p0Point i)).card ≤ 2) →
      (Finset.univ.filter fun i => x i = true).card ≤ 8 := by
  bv_decide

private theorem n6p1_boolean_bound :
    ∀ x : Fin 18 → Bool,
      (∀ line : PrincipalLine 6,
        (Finset.univ.filter fun i =>
          x i = true ∧ OnLine line (n6p1Point i)).card ≤ 2) →
      (Finset.univ.filter fun i => x i = true).card ≤ 8 := by
  bv_decide

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
