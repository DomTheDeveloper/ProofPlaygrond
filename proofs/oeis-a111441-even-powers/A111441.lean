import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic.NormNum

/-!
Candidate proof for https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/2808.
These are exactly the definitions of that proposed statement.  The strengthened
result proves every positive sequence term is coprime to six, including the
conjectured exclusion of residues three and nine modulo twelve. The obstruction is motivated by the
prime-square obstruction used in recent PR #2807; this proof is independent.
The original and even-power conjectural comments are attributed to
Daniel Bamberger in https://oeis.org/A111441.
-/

namespace OMA.S_oeis_a111441

noncomputable def sumSquaresFirstPrimes (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k, Nat.nth Nat.Prime i ^ 2

def IsTerm (k : ℕ) : Prop :=
  0 < k ∧ k ∣ sumSquaresFirstPrimes k

lemma nth_prime_sq_mod_two {i : ℕ} (hi : 1 ≤ i) :
    (Nat.nth Nat.Prime i) ^ 2 % 2 = 1 := by
  have hp := Nat.prime_nth_prime i
  have hlarge := Nat.add_two_le_nth_prime i
  have hnz : Nat.nth Nat.Prime i % 2 ≠ 0 := by
    intro hzero
    have hdvd := Nat.dvd_of_mod_eq_zero hzero
    have heq := (Nat.dvd_prime hp).mp hdvd
    rcases heq with h | h <;> omega
  have hmod : Nat.nth Nat.Prime i % 2 = 1 := by omega
  simp [Nat.pow_mod, hmod]

lemma sumSquaresFirstPrimes_mod_two (k : ℕ) (hk : 1 ≤ k) :
    sumSquaresFirstPrimes k % 2 = (k - 1) % 2 := by
  induction k, hk using Nat.le_induction with
  | base =>
      norm_num [sumSquaresFirstPrimes, Finset.sum_range_succ,
        Nat.nth_prime_zero_eq_two]
  | succ k hk ih =>
      have hstep : sumSquaresFirstPrimes (k + 1) =
          sumSquaresFirstPrimes k + Nat.nth Nat.Prime k ^ 2 :=
        Finset.sum_range_succ _ _
      rw [hstep, Nat.add_mod, ih, nth_prime_sq_mod_two hk]
      omega

theorem term_not_divisible_by_two {k : ℕ} (hk : IsTerm k) : ¬ 2 ∣ k := by
  intro hdvd
  have hsum0 : sumSquaresFirstPrimes k % 2 = 0 := Nat.mod_eq_zero_of_dvd (hdvd.trans hk.2)
  have hk0 : k % 2 = 0 := Nat.mod_eq_zero_of_dvd hdvd
  have h := sumSquaresFirstPrimes_mod_two k hk.1
  have hkpos := hk.1
  omega

lemma nth_prime_sq_mod_three {i : ℕ} (hi : 2 ≤ i) :
    (Nat.nth Nat.Prime i) ^ 2 % 3 = 1 := by
  have hp := Nat.prime_nth_prime i
  have hlarge := Nat.add_two_le_nth_prime i
  have hnz : Nat.nth Nat.Prime i % 3 ≠ 0 := by
    intro hzero
    have hdvd := Nat.dvd_of_mod_eq_zero hzero
    have heq := (Nat.dvd_prime hp).mp hdvd
    rcases heq with h | h <;> omega
  have hcases : Nat.nth Nat.Prime i % 3 = 1 ∨ Nat.nth Nat.Prime i % 3 = 2 := by
    omega
  rcases hcases with h | h <;> simp [Nat.pow_mod, h]

lemma sumSquaresFirstPrimes_mod_three (k : ℕ) (hk : 2 ≤ k) :
    sumSquaresFirstPrimes k % 3 = (k - 1) % 3 := by
  induction k, hk using Nat.le_induction with
  | base =>
      norm_num [sumSquaresFirstPrimes, Finset.sum_range_succ,
        Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three]
  | succ k hk ih =>
      have hstep : sumSquaresFirstPrimes (k + 1) =
          sumSquaresFirstPrimes k + Nat.nth Nat.Prime k ^ 2 :=
        Finset.sum_range_succ _ _
      rw [hstep, Nat.add_mod, ih, nth_prime_sq_mod_three hk]
      omega

theorem term_not_divisible_by_three {k : ℕ} (hk : IsTerm k) : ¬ 3 ∣ k := by
  intro hdvd
  have hk3 : 3 ≤ k := Nat.le_of_dvd hk.1 hdvd
  have hsum0 : sumSquaresFirstPrimes k % 3 = 0 := Nat.mod_eq_zero_of_dvd (hdvd.trans hk.2)
  have hk0 : k % 3 = 0 := Nat.mod_eq_zero_of_dvd hdvd
  have h := sumSquaresFirstPrimes_mod_three k (by omega)
  omega

theorem term_coprime_six {k : ℕ} (hk : IsTerm k) : k.Coprime 6 := by
  have htwo : Nat.Coprime 2 k :=
    Nat.prime_two.coprime_iff_not_dvd.mpr (term_not_divisible_by_two hk)
  have hthree : Nat.Coprime 3 k :=
    Nat.prime_three.coprime_iff_not_dvd.mpr (term_not_divisible_by_three hk)
  exact htwo.symm.mul_right hthree.symm

theorem term_gcd_six {k : ℕ} (hk : IsTerm k) : Nat.gcd k 6 = 1 :=
  term_coprime_six hk

theorem main : ∀ k : ℕ, IsTerm k → k % 12 ≠ 3 ∧ k % 12 ≠ 9 := by
  intro k hk
  have h := term_not_divisible_by_three hk
  have hmod : k % 3 ≠ 0 := fun hz => h (Nat.dvd_of_mod_eq_zero hz)
  omega

/-- The sum of the first `k` prime powers of even exponent `2 * r`. -/
noncomputable def sumEvenPowers (r k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k, Nat.nth Nat.Prime i ^ (2 * r)

lemma sumEvenPowers_mod_two (r k : ℕ) (hr : 0 < r) (hk : 1 ≤ k) :
    sumEvenPowers r k % 2 = (k - 1) % 2 := by
  induction k, hk using Nat.le_induction with
  | base =>
      simp [sumEvenPowers, Finset.sum_range_succ, Nat.nth_prime_zero_eq_two,
        pow_mul, Nat.pow_mod, hr.ne']
  | succ k hk ih =>
      have hstep : sumEvenPowers r (k + 1) =
          sumEvenPowers r k + Nat.nth Nat.Prime k ^ (2 * r) :=
        Finset.sum_range_succ _ _
      have hp : Nat.nth Nat.Prime k ^ (2 * r) % 2 = 1 := by
        rw [pow_mul, Nat.pow_mod, nth_prime_sq_mod_two hk]
        simp
      rw [hstep, Nat.add_mod, ih, hp]
      omega

lemma sumEvenPowers_mod_three (r k : ℕ) (hr : 0 < r) (hk : 2 ≤ k) :
    sumEvenPowers r k % 3 = (k - 1) % 3 := by
  induction k, hk using Nat.le_induction with
  | base =>
      simp [sumEvenPowers, Finset.sum_range_succ, Nat.nth_prime_zero_eq_two,
        Nat.nth_prime_one_eq_three, pow_mul, Nat.add_mod, Nat.pow_mod, hr.ne']
  | succ k hk ih =>
      have hstep : sumEvenPowers r (k + 1) =
          sumEvenPowers r k + Nat.nth Nat.Prime k ^ (2 * r) :=
        Finset.sum_range_succ _ _
      have hp : Nat.nth Nat.Prime k ^ (2 * r) % 3 = 1 := by
        rw [pow_mul, Nat.pow_mod, nth_prime_sq_mod_three hk]
        simp
      rw [hstep, Nat.add_mod, ih, hp]
      omega

/-- The same obstruction holds for every positive even exponent, as suggested
in the source OEIS comment: all positive divisibility indices are coprime to six. -/
theorem even_power_term_gcd_six (r k : ℕ) (hr : 0 < r) (hk : 0 < k)
    (hdiv : k ∣ sumEvenPowers r k) : Nat.gcd k 6 = 1 := by
  have htwo : ¬ 2 ∣ k := by
    intro hdvd
    have hsum0 : sumEvenPowers r k % 2 = 0 := Nat.mod_eq_zero_of_dvd (hdvd.trans hdiv)
    have hk0 : k % 2 = 0 := Nat.mod_eq_zero_of_dvd hdvd
    have h := sumEvenPowers_mod_two r k hr hk
    omega
  have hthree : ¬ 3 ∣ k := by
    intro hdvd
    have hk3 : 3 ≤ k := Nat.le_of_dvd hk hdvd
    have hsum0 : sumEvenPowers r k % 3 = 0 := Nat.mod_eq_zero_of_dvd (hdvd.trans hdiv)
    have hk0 : k % 3 = 0 := Nat.mod_eq_zero_of_dvd hdvd
    have h := sumEvenPowers_mod_three r k hr (by omega)
    omega
  have hcoprime_two := (Nat.prime_two.coprime_iff_not_dvd.mpr htwo).symm
  have hcoprime_three := (Nat.prime_three.coprime_iff_not_dvd.mpr hthree).symm
  exact hcoprime_two.mul_right hcoprime_three

end OMA.S_oeis_a111441

#print axioms OMA.S_oeis_a111441.main
#print axioms OMA.S_oeis_a111441.term_not_divisible_by_three
#print axioms OMA.S_oeis_a111441.term_gcd_six
#print axioms OMA.S_oeis_a111441.even_power_term_gcd_six
