import Checkerboard.FourCertificate
import Checkerboard.N6SATTest

/-!
# The final 6×6 base cases

The uniform quadratic cover does not exclude nine points on the 6-board, so an
integrality argument is required. Each color class has eighteen points. We
transport an arbitrary monochromatic set to eighteen Boolean variables, derive
explicit row, column, and slope `±1` capacity inequalities, and discharge the
resulting Presburger certificates with `omega`.

Proof developed by Dominic Dabish. ProofOrchestrator, using OpenAI GPT-5.6 Thinking,
assisted with the mathematical argument, Lean formalization, and submission
preparation. All formal claims are checked by the repository-pinned Lean compiler.
-/

namespace Checkerboard

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

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
  intro x hline
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
  norm_num [n6p0Point, OnLine, lineValue, bitNat] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 ⊢
  exact n6p0_sat (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)
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
  have h0 := hline (LineFamily.row, ⟨0, by decide⟩)
  have h1 := hline (LineFamily.row, ⟨1, by decide⟩)
  have h2 := hline (LineFamily.row, ⟨2, by decide⟩)
  have h3 := hline (LineFamily.row, ⟨3, by decide⟩)
  have h4 := hline (LineFamily.row, ⟨4, by decide⟩)
  have h5 := hline (LineFamily.row, ⟨5, by decide⟩)
  have h6 := hline (LineFamily.column, ⟨1, by decide⟩)
  have h7 := hline (LineFamily.column, ⟨3, by decide⟩)
  have h8 := hline (LineFamily.column, ⟨5, by decide⟩)
  have h9 := hline (LineFamily.column, ⟨0, by decide⟩)
  have h10 := hline (LineFamily.column, ⟨2, by decide⟩)
  have h11 := hline (LineFamily.column, ⟨4, by decide⟩)
  have h12 := hline (LineFamily.sum, ⟨3, by decide⟩)
  have h13 := hline (LineFamily.sum, ⟨5, by decide⟩)
  have h14 := hline (LineFamily.sum, ⟨7, by decide⟩)
  have h15 := hline (LineFamily.difference, ⟨4, by decide⟩)
  have h16 := hline (LineFamily.difference, ⟨2, by decide⟩)
  have h17 := hline (LineFamily.difference, ⟨6, by decide⟩)
  have h18 := hline (LineFamily.difference, ⟨8, by decide⟩)
  norm_num [n6p1Point, OnLine, lineValue, bitNat] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 ⊢
  exact n6p1_sat (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)
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
