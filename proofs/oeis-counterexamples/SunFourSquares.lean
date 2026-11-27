import Init

/-!
# Counterexamples to Sun's four-square conjecture

The triple (18,38,18) appears in Sun's published Conjecture 4.13(iv) and in
part (ii) of OEIS A261876. The numerical checks use Lean 4.33.1's native
evaluator. The completeness argument below ranges over unbounded naturals.
-/

namespace SunFourSquares

def Represents (n : Nat) : Prop :=
  ∃ x y z w : Nat, n = x^2+y^2+z^2+w^2 ∧
    ∃ r : Nat, x*y*(18*x^2+38*y^2+18*z^2) = r*r

private abbrev Table := Array (List Nat)

/-- Cell s records possible z-coordinates of pairs z²+w²=s. -/
private def table (n lim : Nat) : Table := (List.range lim).foldl (fun a z =>
  (List.range lim).foldl (fun b w =>
    let s := z*z+w*w
    if s ≤ n then b.modify s (z :: ·) else b) a)
  (Array.replicate (n+1) [])

/-- Verify independently that every bounded pair is recorded in its cell. -/
private def covers (n lim : Nat) (t : Table) := (List.range lim).all fun z =>
  (List.range lim).all fun w =>
    let s := z*z+w*w
    if s ≤ n then (t.getD s []).contains z else true

private def nonsquare (q : Nat) := q.sqrt * q.sqrt != q

private def rejects (n lim : Nat) (t : Table) := (List.range lim).all fun x =>
  (List.range lim).all fun y =>
    let s := x*x+y*y
    if s ≤ n then (t.getD (n-s) []).all fun z =>
      nonsquare (x*y*(18*x^2+38*y^2+18*z^2))
    else true

private def checked (n lim : Nat) :=
  let t := table n lim
  covers n lim t && rejects n lim t

private theorem sqrt_square (r : Nat) : (r*r).sqrt = r := by
  apply Nat.le_antisymm
  · apply Nat.le_of_not_gt
    intro h
    have hl := Nat.mul_self_lt_mul_self h
    have hu := Nat.sqrt_le (r*r)
    omega
  · apply Nat.le_of_not_gt
    intro h
    have hl := Nat.mul_le_mul (Nat.succ_le_of_lt h) (Nat.succ_le_of_lt h)
    have hu := Nat.lt_succ_sqrt (r*r)
    omega

private theorem of_check {n lim : Nat} (bound : n < lim*lim)
    (cert : checked n lim = true) : ¬ Represents n := by
  rintro ⟨x,y,z,w,hn,r,hr⟩
  obtain ⟨complete, rejected⟩ := Bool.and_eq_true_iff.mp cert
  have member (u : Nat) (hu : u*u ≤ n) : u ∈ List.range lim := by
    apply List.mem_range.mpr
    apply Nat.lt_of_not_ge
    intro h
    have hb := Nat.mul_le_mul h h
    omega
  simp only [Nat.pow_two] at hn
  have xm := member x (by omega)
  have ym := member y (by omega)
  have zm := member z (by omega)
  have wm := member w (by omega)
  have hz := List.all_eq_true.mp (List.all_eq_true.mp complete z zm) w wm
  have hc := List.all_eq_true.mp (List.all_eq_true.mp rejected x xm) y ym
  have hzw : z*z+w*w ≤ n := by omega
  have hxy : x*x+y*y ≤ n := by omega
  have heq : n-(x*x+y*y) = z*z+w*w := by omega
  have hmem : z ∈ (table n lim).getD (n-(x*x+y*y)) [] := by
    simpa only [heq, if_pos hzw, List.contains_iff_mem] using hz
  simp only [if_pos hxy] at hc
  have hfail := List.all_eq_true.mp hc z hmem
  simp [nonsquare, hr, sqrt_square] at hfail

theorem no_representation_822335 : ¬ Represents 822335 :=
  of_check (lim := 907) (by decide) (by native_decide)

theorem no_representation_3249407 : ¬ Represents 3249407 :=
  of_check (lim := 1803) (by decide) (by native_decide)

/-- Coefficient triples in the OEIS and DeepMind formulations. -/
def triples : List (Nat × Nat × Nat) :=
  [(1,8,20), (3,5,15), (6,14,4), (7,29,5), (18,38,18), (39,81,51), (42,98,14)]

/-- Negation of the universal claim, spelling out the root of the square. -/
theorem conjecture_3_false :
    ¬ (∀ t ∈ triples, ∀ n : Nat, ∃ x y z w : Nat,
      n = x^2+y^2+z^2+w^2 ∧
        ∃ r : Nat, x*y*(t.1*x^2+t.2.1*y^2+t.2.2*z^2) = r*r) := by
  intro h
  exact no_representation_822335 (h (18,38,18) (by decide) 822335)

/-- Negates the six-triple open variant proposed in DeepMind PR 8070. -/
theorem remaining_triples_false :
    ¬ (∀ t ∈ triples, t ≠ (42,98,14) → ∀ n : Nat, ∃ x y z w : Nat,
      n = x^2+y^2+z^2+w^2 ∧
        ∃ r : Nat, x*y*(t.1*x^2+t.2.1*y^2+t.2.2*z^2) = r*r) := by
  intro h
  exact no_representation_822335 (h (18,38,18) (by decide) (by decide) 822335)

#print axioms remaining_triples_false
#print axioms conjecture_3_false
#print axioms no_representation_3249407
end SunFourSquares
