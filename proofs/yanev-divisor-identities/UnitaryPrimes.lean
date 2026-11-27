module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

public section

namespace UnitaryPrimes

open Finset

/-- Sum the weights of primes that divide n exactly once. -/
def sumExactOne {M : Type*} [AddCommMonoid M] (w : ℕ → M) (n : ℕ) : M :=
  ∑ p ∈ n.primeFactors, if n.factorization p = 1 then w p else 0

private theorem extendSum {M : Type*} [AddCommMonoid M] (w : ℕ → M) {n : ℕ}
    {s : Finset ℕ} (hs : n.primeFactors ⊆ s) :
    sumExactOne w n = ∑ p ∈ s, if n.factorization p = 1 then w p else 0 := by
  apply sum_subset hs
  intro p _ h
  have hz : n.factorization p = 0 := by
    apply Finsupp.notMem_support_iff.mp
    simpa only [Nat.support_factorization] using h
  simp [hz]

private theorem localOne {M : Type*} [AddCommMonoid M] (t : M) (e f : ℕ) :
    (if e+f = 1 then t else 0) + (if min (2*e) f = 1 then t else 0) +
      (if min e (2*f) = 1 then t else 0) =
      (if e = 1 then t else 0) + (if f = 1 then t else 0) := by
  by_cases he : e = 0
  · simp [he]
  by_cases hf : f = 0
  · simp [hf]
  have hsum : e+f ≠ 1 := by omega
  have hleft : min (2*e) f = 1 ↔ f = 1 := by omega
  have hright : min e (2*f) = 1 ↔ e = 1 := by omega
  simp only [if_neg hsum, zero_add, hleft, hright, add_comm]

/-- Yanev's A063956 identity, for arbitrary additive weights. -/
theorem weighted_gcd_identity {M : Type*} [AddCommMonoid M] (w : ℕ → M) {m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0) :
    sumExactOne w (m*n) + sumExactOne w ((m^2).gcd n) + sumExactOne w (m.gcd (n^2)) =
      sumExactOne w m + sumExactOne w n := by
  let S := (m*n).primeFactors
  have extTo (t : ℕ) (ht : t ∣ m*n) :
      sumExactOne w t = ∑ p ∈ S, if t.factorization p = 1 then w p else 0 :=
    extendSum w (Nat.primeFactors_mono ht (Nat.mul_ne_zero hm hn))
  have hmd : m ∣ m*n := dvd_mul_right _ _
  have hnd : n ∣ m*n := dvd_mul_left _ _
  rw [extTo _ (dvd_refl _), extTo _ ((Nat.gcd_dvd_right _ _).trans hnd),
    extTo _ ((Nat.gcd_dvd_left _ _).trans hmd), extTo _ hmd, extTo _ hnd]
  simp only [← sum_add_distrib]
  apply sum_congr rfl
  intro p _
  simpa only [Nat.factorization_mul hm hn, Finsupp.add_apply,
    Nat.factorization_gcd (pow_ne_zero 2 hm) hn, Nat.factorization_gcd hm (pow_ne_zero 2 hn),
    Nat.factorization_pow, Finsupp.inf_apply, Finsupp.smul_apply, smul_eq_mul]
    using localOne (w p) (m.factorization p) (n.factorization p)

/-- The original subtractive formula for the sum of the unitary prime divisors. -/
theorem yanev {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    sumExactOne id (m*n) = sumExactOne id m + sumExactOne id n -
      sumExactOne id ((m^2).gcd n) - sumExactOne id (m.gcd (n^2)) := by
  have h := weighted_gcd_identity (M := ℕ) id hm.ne' hn.ne'
  omega

#print axioms weighted_gcd_identity
#print axioms yanev

end UnitaryPrimes
