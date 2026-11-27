module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! The totient characterization proposed by Benoit Cloitre for OEIS A058383. -/
public section

namespace Pierpont

private theorem totient_mul_prime_le (p n : ℕ) (hp : p.Prime) :
    (p * n).totient ≤ p * n.totient := by
  by_cases h : p ∣ n
  · exact (Nat.totient_mul_of_prime_of_dvd hp h).le
  · rw [Nat.totient_mul_of_prime_of_not_dvd hp h]
    exact Nat.mul_le_mul_right _ (Nat.sub_le p 1)

private theorem totient_mul_le (a b : ℕ) : (a * b).totient ≤ a.totient * b := by
  induction b using induction_on_primes with
  | zero => simp
  | one => simp
  | prime_mul p b hp ih =>
    calc
      (a * (p * b)).totient = (p * (a * b)).totient := by rw [mul_left_comm]
      _ ≤ p * (a * b).totient := totient_mul_prime_le p _ hp
      _ ≤ p * (a.totient * b) := Nat.mul_le_mul_left _ ih
      _ = a.totient * (p * b) := by ring

private theorem smooth_totient (a b : ℕ) :
    (2 ^ (a + 1) * 3 ^ (b + 1)).totient = 2 * (2 ^ a * 3 ^ b) := by
  rw [Nat.totient_mul (((show Nat.Coprime 2 3 by decide).pow_left _).pow_right _),
    Nat.totient_prime_pow_succ Nat.prime_two, Nat.totient_prime_pow_succ Nat.prime_three]
  ring

/-- Equality in the totient bound for multiples of six forces all prime factors to be 2 or 3. -/
private theorem six_equality {k : ℕ} (hk : 0 < k) (h : (6 * k).totient = 2 * k) :
    ∃ a b : ℕ, k = 2 ^ a * 3 ^ b := by
  obtain ⟨a, d, hd2, hkd⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk.ne' 2 (by decide)
  have hd : d ≠ 0 := by intro hd; simp [hd] at hkd; omega
  obtain ⟨b, c, hc3, hdc⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd 3 (by decide)
  have hc2 : ¬2 ∣ c := by
    intro hc
    exact hd2 (hdc ▸ dvd_mul_of_dvd_right hc _)
  have hfac : 6 * k = (2 ^ (a + 1) * 3 ^ (b + 1)) * c := by rw [hkd, hdc]; ring
  have hc : c = 1 := by
    by_contra hc
    have hcpos : 0 < c := by
      apply Nat.pos_of_ne_zero
      intro hc0
      apply hd
      simpa [hc0] using hdc
    have hlt := Nat.totient_lt c (by omega)
    have hcop : (2 ^ (a+1) * 3 ^ (b+1)).Coprime c :=
      ((Nat.prime_two.coprime_iff_not_dvd.mpr hc2).pow_left _).mul_left
        ((Nat.prime_three.coprime_iff_not_dvd.mpr hc3).pow_left _)
    rw [hfac, Nat.totient_mul hcop, smooth_totient] at h
    have hh : 2 * (2 ^ a * 3 ^ b) * c.totient < 2 * (2 ^ a * 3 ^ b) * c :=
      Nat.mul_lt_mul_of_pos_left hlt (by positivity)
    rw [h, hkd, hdc] at hh
    nlinarith
  exact ⟨a, b, by simp [hkd, hdc, hc]⟩

/-- For x ≥ 7, the solutions are exactly the primes 1 + 2^a 3^b with a,b positive. -/
theorem characterization (x : ℕ) (hx : 7 ≤ x) :
    x.totient + (x - 1).totient = (4*x - 3)/3 ↔
    x.Prime ∧ ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ x = 1 + 2^a * 3^b := by
  constructor
  · intro heq
    obtain ⟨u, hu⟩ := Nat.totient_even (n := x) (by omega)
    obtain ⟨v, hv⟩ := Nat.totient_even (n := x-1) (by omega)
    have hmod : x % 3 = 1 := by omega
    have hodd : ¬ 2 ∣ x := by
      rintro ⟨k, hk⟩
      have hdiv : 3 ∣ x-1 := by omega
      obtain ⟨l, hl⟩ := hdiv
      have hkφ := totient_mul_le 2 k
      have hlφ := totient_mul_le 3 l
      rw [← hk] at hkφ
      rw [← hl] at hlφ
      norm_num [Nat.totient_prime Nat.prime_two, Nat.totient_prime Nat.prime_three] at hkφ hlφ
      omega
    have hdiv : 6 ∣ x-1 := by omega
    obtain ⟨k, hk⟩ := hdiv
    have hxk : x = 6*k + 1 := by omega
    have hphi := totient_mul_le 6 k
    have h6 : Nat.totient 6 = 2 := by decide
    rw [h6, ← hk] at hphi
    have hxphi := Nat.totient_lt x (by omega)
    have heqx : x.totient = x-1 := by omega
    have heqk : (6*k).totient = 2*k := by rw [← hk]; omega
    obtain ⟨a,b,hab⟩ := six_equality (by omega) heqk
    refine ⟨(Nat.totient_eq_iff_prime (by omega)).mp heqx, a+1, b+1, by omega, by omega, ?_⟩
    rw [hxk, hab]; ring
  · rintro ⟨hp, a, b, ha, hb, hxform⟩
    obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
    obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb.ne'
    change x = 1 + 2 ^ (a + 1) * 3 ^ (b + 1) at hxform
    have hpred : x - 1 = 2 ^ (a + 1) * 3 ^ (b + 1) := by
      rw [hxform, Nat.add_sub_cancel_left]
    have hpow : 2 ^ (a + 1) * 3 ^ (b + 1) = 6 * (2 ^ a * 3 ^ b) := by ring
    rw [Nat.totient_prime hp, hpred, smooth_totient, hxform, hpow]
    omega

end Pierpont

#print axioms Pierpont.characterization
