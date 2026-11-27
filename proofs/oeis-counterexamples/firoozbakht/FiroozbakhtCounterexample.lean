/-
The definition of a below is from google-deepmind/formal-conjectures,
FormalConjectures/OEIS/86766.lean, licensed under Apache-2.0.
Copyright 2026 The Formal Conjectures Authors.
Source: https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/OEIS/86766.lean
Original conjecture: https://oeis.org/A086766
Proposed refinement: https://archive.ph/zao2Y
-/
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# A counterexample to the decimal-concatenation conjecture

For every positive number of copies of the decimal block 109890, appending a 1
gives a composite number. The digit 9 also rules out every repetition of a
block consisting of a 1 followed by zeros. This file checks both assertions.

The sequence definition is copied verbatim into its own namespace so the
certificate runs with Mathlib alone. In a project importing the upstream file,
the two definitions are definitionally equal.
-/
namespace A086766Certificate

noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let ℓ : ℕ := (Nat.digits 10 n).length
    let M : ℕ := 10 ^ ℓ
    let repCatVal (r : ℕ) : ℕ := n * ∑ i ∈ Finset.range r, M ^ i
    let primeCandidate (r : ℕ) : ℕ := repCatVal r * 10 + 1
    sInf {r : ℕ | 0 < r ∧ (primeCandidate r).Prime}


/-- Both factors in a product equal to d * n exceed d, so n cannot be prime. -/
private theorem composite_of_scaled_product {n d u v : ℕ}
    (h : d * n = u * v) (hu : d < u) (hv : d < v) : ¬ n.Prime := by
  intro hp
  have hdiv : n ∣ u * v := ⟨d, by simpa [Nat.mul_comm] using h.symm⟩
  rcases hp.dvd_mul.mp hdiv with hnu | hnv
  · have hle := Nat.le_of_dvd (by omega : 0 < u) hnu
    have h₁ := Nat.mul_le_mul_left d hle
    have h₂ := Nat.mul_lt_mul_of_pos_right hv (by omega : 0 < u)
    nlinarith
  · have hle := Nat.le_of_dvd (by omega : 0 < v) hnv
    have h₁ := Nat.mul_le_mul_left d hle
    have h₂ := Nat.mul_lt_mul_of_pos_right hu (by omega : 0 < v)
    nlinarith

/-- Geometric sum for concatenating six-digit blocks. -/
private theorem geometric (r : ℕ) :
    999999 * (∑ i ∈ Finset.range r, (1000000 : ℕ) ^ i) + 1 = 1000000 ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, pow_succ]
    omega

/-- Every candidate from 109890 is composite, for arbitrarily many copies. -/
theorem every_repetition_composite (r : ℕ) (hr : 0 < r) :
    ¬ Nat.Prime ((109890 * ∑ i ∈ Finset.range r, (1000000 : ℕ) ^ i) * 10 + 1) := by
  let x := 10 * (1000 : ℕ) ^ r
  have hpow : (1000 : ℕ) ^ 1 ≤ 1000 ^ r := Nat.pow_le_pow_right (by decide) hr
  have hx : 10000 ≤ x := by dsimp [x]; norm_num at hpow; omega
  have hs : (1000000 : ℕ) ^ r = (1000 ^ r) ^ 2 := by
    calc
      (1000000 : ℕ) ^ r = (1000 ^ 2) ^ r := by norm_num
      _ = (1000 ^ r) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 r]
  have hscaled : 91 * ((109890 * ∑ i ∈ Finset.range r, (1000000 : ℕ) ^ i) * 10 + 1) + 9 =
      x ^ 2 := by
    dsimp [x]
    nlinarith [geometric r, hs]
  apply composite_of_scaled_product (d := 91) (u := x - 3) (v := x + 3) _ (by omega) (by omega)
  have hx' : x - 3 + 3 = x := by omega
  have hprod : (x - 3) * (x + 3) + 9 = x ^ 2 := by
    conv_rhs => rw [← hx']
    nth_rw 2 [← hx']
    ring
  omega

/-- The exact OEIS sequence value is zero. -/
theorem a_109890 : a 109890 = 0 := by
  have hdigit : (Nat.digits 10 109890).length = 6 := by decide
  simp only [a, show (109890 : ℕ) ≠ 0 by decide, if_false, hdigit]
  have hempty : {r : ℕ | 0 < r ∧
      Nat.Prime ((109890 * ∑ i ∈ Finset.range r, (1000000 : ℕ) ^ i) * 10 + 1)} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro r hr
    exact every_repetition_composite r hr.1 hr.2
  change sInf {r : ℕ | 0 < r ∧
    Nat.Prime ((109890 * ∑ i ∈ Finset.range r, (1000000 : ℕ) ^ i) * 10 + 1)} = 0
  rw [hempty, Nat.sInf_empty]

/-- 109890 is strictly between successive powers of ten. -/
theorem not_power_of_ten (m : ℕ) : 109890 ≠ 10 ^ m := by
  by_cases h : m ≤ 5
  · have := Nat.pow_le_pow_right (by decide : 0 < 10) h
    norm_num at this
    omega
  · have := Nat.pow_le_pow_right (by decide : 0 < 10) (by omega : 6 ≤ m)
    norm_num at this
    omega

/-- Direct negation of OeisA86766.conjecture2 with the same sequence definition. -/
theorem refutes_conjecture2 :
    ¬ (∀ n : ℕ, 0 < n → (∀ m : ℕ, n ≠ 10 ^ m) → a n ≠ 0) := by
  intro h
  exact h 109890 (by decide) not_power_of_ten a_109890

/-- Digits are least significant first. Every repeated power-of-ten block uses
only zeros and ones, whereas 109890 contains a nine. -/
theorem outside_repeated_blocks (zeros copies : ℕ) :
    Nat.digits 10 109890 ≠ (List.replicate copies (List.replicate zeros 0 ++ [1])).flatten := by
  intro h
  have hnine : 9 ∈ Nat.digits 10 109890 := by decide
  rw [h] at hnine
  simp at hnine

/-- The same witness refutes the revised decimal conjecture as well. -/
theorem refutes_revised_conjecture :
    ¬ (∀ n : ℕ, 0 < n →
      (∀ zeros copies : ℕ, 0 < zeros → 0 < copies →
        Nat.digits 10 n ≠ (List.replicate copies (List.replicate zeros 0 ++ [1])).flatten) →
      a n ≠ 0) := by
  intro h
  exact h 109890 (by decide) (fun z k _ _ => outside_repeated_blocks z k) a_109890

#print axioms refutes_conjecture2
#print axioms refutes_revised_conjecture

end A086766Certificate
