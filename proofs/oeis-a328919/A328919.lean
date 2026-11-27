import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-! Divisor-power sums, OEIS A328919. The two questions are due to Jianing Song. -/

namespace OMA.S_oeis_a328919
open Finset
open ArithmeticFunction

def periodicFrom (n m : ℕ) : Prop :=
  ∃ T : ℕ, 0 < T ∧ ∀ k : ℕ, m ≤ k →
    ArithmeticFunction.sigma k n % n = ArithmeticFunction.sigma (k + T) n % n

noncomputable def preperiod (n : ℕ) : ℕ := sInf {m : ℕ | periodicFrom n m}

private theorem unit_pow_period {d q T : ℕ} (hd : d.Coprime q) (hT : q.totient ∣ T) :
    d ^ T ≡ 1 [MOD q] := by
  obtain ⟨u, rfl⟩ := hT
  simpa [pow_mul] using (Nat.ModEq.pow_totient hd).pow u

private theorem residue_stable {n p e d k : ℕ} (hn : 0 < n) (hp : p.Prime)
    (hpn : p ^ e ∣ n) (hk : e ≤ k) :
    d ^ k ≡ d ^ (k + n.factorial) [MOD p ^ e] := by
  by_cases hpd : p ∣ d
  · have zero_at (j : ℕ) (hj : e ≤ j) : d ^ j ≡ 0 [MOD p ^ e] :=
      Nat.modEq_zero_iff_dvd.mpr ((pow_dvd_pow p hj).trans (pow_dvd_pow_of_dvd hpd j))
    exact (zero_at _ hk).trans (zero_at _ (by omega)).symm
  · have hu : d.Coprime (p ^ e) := (hp.coprime_iff_not_dvd.mpr hpd).symm.pow_right _
    have hT : (p ^ e).totient ∣ n.factorial :=
      Nat.dvd_factorial (Nat.totient_pos.mpr (pow_pos hp.pos _))
        ((Nat.totient_le _).trans (Nat.le_of_dvd hn hpn))
    simpa [pow_add] using (unit_pow_period hu hT).symm.mul_left (d ^ k)

private theorem periodic_of_bound {n m : ℕ} (hn : 0 < n)
    (hm : ∀ p e : ℕ, p.Prime → p ^ e ∣ n → e ≤ m) : periodicFrom n m := by
  refine ⟨n.factorial, Nat.factorial_pos _, ?_⟩
  intro k hk
  change sigma k n ≡ sigma (k + n.factorial) n [MOD n]
  apply (Nat.modEq_iff_dvd' (sigma_mono _ _ _ (by omega))).2
  apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).2
  intro p e hp hd
  apply Nat.ModEq.dvd'
  simp only [sigma_apply]
  exact Nat.ModEq.sum fun d _ => residue_stable hn hp hd (le_trans (hm p e hp hd) hk)

private theorem bound_below_pow {n e p j : ℕ} (hn : 0 < n) (h : n < 2 ^ e)
    (hp : p.Prime) (hd : p ^ j ∣ n) : j < e := by
  have hj := Nat.le_of_dvd hn hd
  have hj' := Nat.pow_le_pow_left hp.two_le j
  by_contra! hc
  have hh := Nat.pow_le_pow_right (by decide : 0 < 2) hc
  omega

private theorem exists_periodic {n : ℕ} (hn : 0 < n) : ∃ m, periodicFrom n m :=
  ⟨n, periodic_of_bound hn fun p e hp hd => by
    have hb := bound_below_pow hn (show n < 2 ^ (n + 1) by
      have := n.lt_two_pow_self
      rw [pow_succ]; omega) hp hd
    omega⟩

private theorem preperiod_spec {n : ℕ} (hn : 0 < n) : periodicFrom n (preperiod n) :=
  Nat.sInf_mem (exists_periodic hn)

private theorem preperiod_le {n m : ℕ} (h : periodicFrom n m) : preperiod n ≤ m :=
  Nat.sInf_le h

private theorem prime_power_tail {p e k : ℕ} (hp : p.Prime) (hk : e ≤ k) :
    sigma k (p ^ e) ≡ 1 [MOD p ^ e] := by
  rw [sigma_apply_prime_pow hp, Finset.sum_range_succ']
  simp only [zero_mul, pow_zero]
  suffices h : (∑ j ∈ range e, p ^ ((j + 1) * k)) ≡ 0 [MOD p ^ e] by
    simpa using h.add_right 1
  exact Nat.ModEq.sum_zero fun j _ => Nat.modEq_zero_iff_dvd.mpr
    (pow_dvd_pow p (by rw [Nat.add_mul, one_mul]; omega))

private theorem two_prime_power_last {e : ℕ} (he : 0 < e) :
    ¬ sigma (e - 1) (2 ^ e) ≡ 1 [MOD 2 ^ e] := by
  by_cases h1 : e = 1
  · subst e
    decide
  obtain ⟨t, rfl⟩ : ∃ t, e = t + 2 := ⟨e - 2, by omega⟩
  rw [sigma_apply_prime_pow Nat.prime_two, Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [zero_mul, pow_zero, zero_add, one_mul]
  intro h
  have htail : (∑ j ∈ range t.succ, 2 ^ ((j + 1 + 1) * (t + 1))) ≡ 0 [MOD 2 ^ (t + 2)] :=
    Nat.ModEq.sum_zero fun j _ => Nat.modEq_zero_iff_dvd.mpr
      (pow_dvd_pow 2 (by nlinarith))
  have hbad : 2 ^ (t + 1) + 1 ≡ 1 [MOD 2 ^ (t + 2)] := by
    apply Nat.ModEq.trans _ h
    simpa [Nat.add_assoc] using ((htail.symm.add_right (2 ^ (t + 1))).add_right 1)
  have hd := hbad.symm.dvd'
  simp only [Nat.add_sub_cancel] at hd
  have hle := Nat.le_of_dvd (by positivity) hd
  rw [show t + 2 = (t+1)+1 by omega, pow_succ] at hle
  have : 0 < 2^(t+1) := pow_pos (by decide) _
  omega

theorem preperiod_two_pow (e : ℕ) : preperiod (2 ^ e) = e := by
  have hn : 0 < 2 ^ e := pow_pos (by decide) _
  apply Nat.le_antisymm
  · apply preperiod_le
    refine ⟨1, by decide, fun k hk =>
      (prime_power_tail Nat.prime_two hk).trans (prime_power_tail Nat.prime_two (by omega : e ≤ k+1)).symm⟩
  · by_contra! hh
    obtain ⟨T, hT, hh'⟩ := preperiod_spec hn
    have hl := hh' (e-1) (by omega)
    exact two_prime_power_last (by omega : 0 < e)
      (Nat.ModEq.trans hl (prime_power_tail Nat.prime_two (by omega : e ≤ e-1+T)))

theorem first_occurrence (e : ℕ) :
    IsLeast {n : ℕ | 0 < n ∧ preperiod n = e} (2 ^ e) := by
  refine ⟨⟨pow_pos (by decide) _, preperiod_two_pow e⟩, ?_⟩
  rintro n ⟨hn, he⟩
  by_contra! h
  have he' : 0 < e := by by_contra! h0; simp [show e = 0 by omega] at h; omega
  have periodic := periodic_of_bound (m := e-1) hn fun p j hp hd => by
    have := bound_below_pow hn h hp hd
    omega
  have := preperiod_le periodic
  omega

/-- Song's necessary local condition, obtained by comparing index zero with a common multiple of
the period and the totient of the prime power. -/
private theorem local_condition {n p : ℕ} (hn : 0 < n) (hp : p.Prime)
    (h0 : periodicFrom n 0) :
    p ^ n.factorization p ∣ n.factorization p * (n / p ^ n.factorization p).divisors.card := by
  let e := n.factorization p
  let q := p ^ e
  let m := n / q
  have hprod : q * m = n := Nat.ordProj_mul_ordCompl_eq_self n p
  have hcop : p.Coprime m := Nat.coprime_ordCompl hp hn.ne'
  have hq : q ∣ n := Nat.ordProj_dvd n p
  obtain ⟨T, hT, hperiod⟩ := h0
  have periodic_multiple (u : ℕ) : sigma 0 n ≡ sigma (T * u) n [MOD n] := by
    induction u with
    | zero => rfl
    | succ u ih => simpa only [Nat.mul_succ] using ih.trans (hperiod (T * u) (Nat.zero_le _))
  let u := (e + 1) * q.totient
  let L := T * u
  have hphi : 0 < q.totient := Nat.totient_pos.mpr (pow_pos hp.pos _)
  have heL : e ≤ L := by
    have hu : e+1 ≤ u := Nat.le_mul_of_pos_right _ hphi
    have hL : u ≤ L := Nat.le_mul_of_pos_left _ hT
    omega
  have hdiv : q.totient ∣ L := dvd_mul_of_dvd_right (dvd_mul_left _ _) _
  have heq (k : ℕ) : sigma k n = sigma k q * sigma k m := by
    conv_lhs => rw [← hprod]
    exact isMultiplicative_sigma.map_mul_of_coprime (hcop.pow_left _)
  have hm : sigma L m ≡ sigma 0 m [MOD q] := by
    simp only [sigma_apply]
    apply Nat.ModEq.sum
    intro d hd
    have hdm : d ∣ m := Nat.dvd_of_mem_divisors hd
    simpa using unit_pow_period ((hcop.symm.of_dvd_left hdm).pow_right e) hdiv
  have hl : sigma L n ≡ sigma 0 m [MOD q] := by
    rw [heq L]
    simpa using (prime_power_tail hp heL).mul hm
  have hstart := ((periodic_multiple u).of_dvd hq).trans hl
  rw [heq 0, sigma_zero_apply_prime_pow hp] at hstart
  have hd := hstart.symm.dvd'
  rw [Nat.succ_mul, Nat.add_sub_cancel] at hd
  simpa only [sigma_zero_apply] using hd

private def weight (e : ℕ) : ℕ := if e = 0 then 1 else e * (e + 1)

private theorem exp_pos {n p : ℕ} (hp : p ∈ n.primeFactors) : 0 < n.factorization p :=
  ((Nat.prime_of_mem_primeFactors hp).dvd_iff_one_le_factorization
    (Nat.mem_primeFactors.mp hp).2.2).mp (Nat.dvd_of_mem_primeFactors hp)

private theorem global_bound {n : ℕ} (hn : 0 < n) (h : periodicFrom n 0) :
    n ≤ ∏ p ∈ n.primeFactors, weight (n.factorization p) := by
  let E := ∏ p ∈ n.primeFactors, n.factorization p
  let D := n.divisors.card
  have hD : 0 < D := Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hn.ne'⟩
  have hE : 0 < E := Finset.prod_pos fun _ hp => exp_pos hp
  have hd : n ∣ E * D := by
    apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).2
    intro p k hp hpk
    by_cases hk : k = 0
    · simp [hk]
    have hpn : p ∣ n := (dvd_pow_self p hk).trans hpk
    have hmem := hp.mem_primeFactors hpn hn.ne'
    have hm := Nat.coprime_ordCompl hp hn.ne'
    have hprod := Nat.ordProj_mul_ordCompl_eq_self n p
    have hcount : (n / p ^ n.factorization p).divisors.card ∣ D := by
      change _ ∣ n.divisors.card
      conv_rhs => rw [← hprod, ← sigma_zero_apply, isMultiplicative_sigma.map_mul_of_coprime
        (hm.pow_left (n.factorization p)), sigma_zero_apply (n / p ^ n.factorization p)]
      exact dvd_mul_left _ _
    exact (pow_dvd_pow p ((hp.pow_dvd_iff_le_factorization hn.ne').mp hpk)).trans
      ((local_condition hn hp h).trans
        (Nat.mul_dvd_mul (Finset.dvd_prod_of_mem (fun r => n.factorization r) hmem) hcount))
  have hprod : E * D = ∏ p ∈ n.primeFactors, weight (n.factorization p) := by
    dsimp [E,D]
    rw [Nat.card_divisors hn.ne', ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun _ hp => by simp [weight, (exp_pos hp).ne']
  exact hprod ▸ Nat.le_of_dvd (Nat.mul_pos hE hD) hd

-- These four elementary estimates bound the product for all prime factorizations.
private theorem weight_two_large {e : ℕ} (h : 5 ≤ e) : weight e < 2^e := by
  obtain ⟨u, rfl⟩ : ∃ u, e = 5 + u := ⟨e-5, by omega⟩
  induction u with
  | zero => decide
  | succ u ih =>
    simp [weight, Nat.add_assoc] at ih ⊢
    rw [show 5 + (u+1) = (5+u)+1 by omega, pow_succ]
    nlinarith

private theorem weight_two (e : ℕ) : weight e ≤ 2 * 2^e := by
  by_cases h : 5 ≤ e
  · have := weight_two_large h; omega
  · interval_cases e <;> decide

private theorem weight_three_large {e : ℕ} (h : 3 ≤ e) : 2 * weight e < 3^e := by
  obtain ⟨u, rfl⟩ : ∃ u, e = 3 + u := ⟨e-3, by omega⟩
  induction u with
  | zero => decide
  | succ u ih =>
    simp [weight, Nat.add_assoc] at ih ⊢
    rw [show 3 + (u+1) = (3+u)+1 by omega, pow_succ]
    nlinarith

private theorem weight_three (e : ℕ) : weight e ≤ 3^e := by
  by_cases h : 3 ≤ e
  · have := weight_three_large h; omega
  · interval_cases e <;> decide

private theorem weight_five {p e : ℕ} (hp : 5 ≤ p) (he : 0 < e) : 2 * weight e < p^e := by
  by_cases h : 3 ≤ e
  · exact (weight_three_large h).trans_le (Nat.pow_le_pow_left (by omega) e)
  · have hb := Nat.pow_le_pow_left hp e
    interval_cases e <;> norm_num [weight] at * <;> omega

private theorem factor_out (s : Finset ℕ) (f : ℕ → ℕ) (p : ℕ)
    (h : p ∉ s → f p = 1) :
    s.prod f = f p * (s.erase p).prod f := by
  by_cases hp : p ∈ s
  · exact (Finset.mul_prod_erase s f hp).symm
  · simp [Finset.erase_eq_of_notMem hp, h hp]

private theorem small_candidates {n : ℕ} (hn : 0 < n) (hper : periodicFrom n 0) :
    n = 1 ∨ n = 12 := by
  let a := n.factorization 2
  let b := n.factorization 3
  let S := (n.primeFactors.erase 2).erase 3
  have expand (f : ℕ → ℕ → ℕ) (hf : ∀ p, f p 0 = 1) :
      (∏ p ∈ n.primeFactors, f p (n.factorization p)) =
      f 2 a * f 3 b * ∏ p ∈ S, f p (n.factorization p) := by
    let g := fun p => f p (n.factorization p)
    have missing (p : ℕ) (hp : p ∉ n.primeFactors) : g p = 1 := by
      simpa [g, (Finsupp.notMem_support_iff.mp hp : n.factorization p = 0)] using hf p
    have h2 := factor_out n.primeFactors g 2 (missing 2)
    have h3 := factor_out (n.primeFactors.erase 2) g 3 (by
      intro hm
      exact missing 3 (fun h => hm (mem_erase.mpr ⟨by decide, h⟩)))
    change n.primeFactors.prod g = g 2 * g 3 * S.prod g
    rw [h2,h3,mul_assoc]
  let value := fun p => p ^ n.factorization p
  let cost := fun p => weight (n.factorization p)
  have nval : n = 2^a * 3^b * S.prod value :=
    (Nat.prod_primeFactors_pow_factorization hn.ne').trans
      (expand (fun p i => p^i) (fun _ => pow_zero _))
  have ncost : n ≤ weight a * weight b * S.prod cost :=
    (global_bound hn hper).trans_eq (expand (fun _ => weight) (fun _ => rfl))
  have costly (p : ℕ) (hp : p ∈ S) : 2 * cost p < value p := by
    obtain ⟨hn3, hm⟩ := Finset.mem_erase.mp hp
    obtain ⟨hn2, hm'⟩ := Finset.mem_erase.mp hm
    have pp := Nat.prime_of_mem_primeFactors hm'
    have hp5 : 5 ≤ p := by
      by_contra! hl
      have small : ∀ j : Fin 5, (j : ℕ).Prime → (j : ℕ) = 2 ∨ (j : ℕ) = 3 := by decide
      exact (small ⟨p,hl⟩ pp).elim hn2 hn3
    exact weight_five hp5 (exp_pos hm')
  have S_empty : S = ∅ := by
    by_contra! h
    obtain ⟨q,hq⟩ := h
    have hcpos : 0 < (S.erase q).prod cost := Finset.prod_pos fun p hp => by
      dsimp [cost, weight]; split <;> (first | decide | positivity)
    have hrest : (S.erase q).prod cost ≤ (S.erase q).prod value := by
      apply Finset.prod_le_prod'
      intro p hp
      change cost p ≤ value p
      have := costly p (Finset.mem_of_mem_erase hp)
      omega
    have hratio : 2 * S.prod cost < S.prod value := by
      rw [← Finset.mul_prod_erase S cost hq, ← Finset.mul_prod_erase S value hq, ← mul_assoc]
      exact (Nat.mul_lt_mul_of_pos_right (costly q hq) hcpos).trans_le
        (Nat.mul_le_mul_left _ hrest)
    have hcost : weight a * weight b ≤ 2 * (2^a * 3^b) := by
      rw [← mul_assoc]
      exact Nat.mul_le_mul (weight_two a) (weight_three b)
    have hle : n ≤ (2^a * 3^b) * (2 * S.prod cost) := by
      calc n ≤ weight a * weight b * S.prod cost := ncost
           _ ≤ (2 * (2^a * 3^b)) * S.prod cost := Nat.mul_le_mul_right _ hcost
           _ = _ := by ac_rfl
    have hlt := Nat.mul_lt_mul_of_pos_left hratio (show 0 < 2^a * 3^b by positivity)
    omega
  rw [S_empty, prod_empty, mul_one] at nval ncost
  have ha : a < 5 := by
    by_contra! h
    have hlt := Nat.mul_lt_mul_of_pos_right (weight_two_large h) (show 0 < 3^b by positivity)
    have hle := Nat.mul_le_mul_left (weight a) (weight_three b)
    omega
  have hb : b < 3 := by
    by_contra! h
    have hlt := Nat.mul_lt_mul_of_pos_left (weight_three_large h) (show 0 < 2^a by positivity)
    have hle := Nat.mul_le_mul_right (weight b) (weight_two a)
    rw [mul_assoc, mul_left_comm 2] at hle
    omega
  have h2 := local_condition hn Nat.prime_two hper
  have h3 := local_condition hn Nat.prime_three hper
  have finite_check : ∀ i : Fin 5, ∀ j : Fin 3, let v := 2 ^ (i : ℕ) * 3 ^ (j : ℕ);
      (2 ^ v.factorization 2 ∣ v.factorization 2 * (v / 2 ^ v.factorization 2).divisors.card) →
      (3 ^ v.factorization 3 ∣ v.factorization 3 * (v / 3 ^ v.factorization 3).divisors.card) →
      v = 1 ∨ v = 12 := by decide +kernel
  have hv := finite_check ⟨a,ha⟩ ⟨b,hb⟩
  dsimp only at hv
  rw [← nval] at hv
  exact hv h2 h3

private theorem twelve_periodic : periodicFrom 12 0 := by
  refine ⟨2, by decide, ?_⟩
  rintro (_ | _ | k) _
  · decide
  · decide
  · change sigma (k + 2) 12 ≡ sigma ((k+2)+2) 12 [MOD 12]
    simp only [sigma_apply]
    apply Nat.ModEq.sum
    intro d hd
    have base : ∀ d ∈ (12 : ℕ).divisors, d^2 ≡ d^4 [MOD 12] := by decide
    have hh := (base d hd).mul_left (d^k)
    simpa only [← pow_add, Nat.add_assoc] using hh

theorem pure_iff {n : ℕ} (hn : 0 < n) : preperiod n = 0 ↔ n = 1 ∨ n = 12 := by
  constructor
  · intro h
    exact small_candidates hn (h ▸ preperiod_spec hn)
  · rintro (rfl | rfl)
    · exact Nat.eq_zero_of_le_zero (preperiod_le (show periodicFrom 1 0 from
        ⟨1,by decide,fun _ _ => Nat.modEq_one⟩))
    · exact Nat.eq_zero_of_le_zero (preperiod_le twelve_periodic)

theorem both_conjectures :
    (∀ n : ℕ, 0 < n → (preperiod n = 0 ↔ n = 1 ∨ n = 12)) ∧
    (∀ e : ℕ, IsLeast {n : ℕ | 0 < n ∧ preperiod n = e} (2 ^ e)) :=
  ⟨fun _ hn => pure_iff hn, first_occurrence⟩

end OMA.S_oeis_a328919
