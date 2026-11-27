import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A sharp bound for four prime factors in OEIS A245212

Dominic Aziz Dabish (DomTheDeveloper). The local prime-power estimates and
multiplicativity proofs come from Left to Solve PR 1048. The theorem below
applies when 3 divides the input exactly once.
-/

namespace DivisorSums.A245212

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- Krizek's A245212. -/
def a (n : ℕ) : ℤ :=
  (n : ℤ) * n.divisors.card - ∑ d ∈ n.properDivisors, (d : ℤ) * d.divisors.card

private lemma geom_bound (p c e : ℕ) (hp : c + 1 ≤ p) :
    c * (∑ j ∈ range (e + 1), p ^ j) ≤ (c + 1) * p ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [sum_range_succ]
    simp only [pow_succ p e]
    nlinarith only [ih, Nat.mul_le_mul_right (p^e) hp]

/-- The loss of one in the leading coefficient is important for small exponents. -/
private lemma weighted_bound (p c e : ℕ) (hp : c + 1 ≤ p) :
    c * (∑ j ∈ range (e + 1), p ^ j * (j + 1)) ≤ ((c + 1) * e + c) * p ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
    have hcoef : (c + 1) * e + c ≤ (e + 1) * p := by
      calc
        _ ≤ (e + 1) * (c + 1) := by nlinarith
        _ ≤ (e + 1) * p := Nat.mul_le_mul_left _ hp
    rw [sum_range_succ]
    simp only [pow_succ p e]
    nlinarith only [ih, Nat.mul_le_mul_right (p^e) hcoef]

private lemma moment_mul (u v : ℕ) (hc : u.Coprime v) :
    (∑ d ∈ (u*v).divisors, d * d.divisors.card) =
    (∑ d ∈ u.divisors, d * d.divisors.card) * (∑ d ∈ v.divisors, d * d.divisors.card) := by
  let F : ArithmeticFunction ℕ := (ArithmeticFunction.id.pmul (σ 0)) * ArithmeticFunction.zeta
  have hf : F.IsMultiplicative :=
    (isMultiplicative_id.pmul isMultiplicative_sigma).mul isMultiplicative_zeta
  have he (n : ℕ) : F n = ∑ d ∈ n.divisors, d * d.divisors.card := by
    change ((ArithmeticFunction.id.pmul (σ 0)) * ArithmeticFunction.zeta) n = _
    rw [ArithmeticFunction.mul_zeta_apply]
    simp only [pmul_apply, id_apply, sigma_zero_apply]
  simpa only [he] using hf.map_mul_of_coprime hc

private lemma moment_at_power (p e : ℕ) (hp : p.Prime) :
    (∑ d ∈ (p^e).divisors, d * d.divisors.card) =
    ∑ j ∈ range (e+1), p^j*(j+1) := by
  rw [Nat.sum_divisors_prime_pow hp]
  simp only [Nat.divisors_prime_pow hp, card_map, card_range]

private def W (p e : ℕ) := ∑ j ∈ range (e+1), p^j*(j+1)
private def S (p e : ℕ) := ∑ j ∈ range (e+1), p^j

private lemma bounds (p q r e f g : ℕ) (hp : 5 ≤ p) (hq : 7 ≤ q) (hr : 11 ≤ r)
    (hf : 0 < f) (hg : 0 < g) :
    240 * (7*W p e*W q f*W r g + 4*S p e*S q f*S r g) ≤
      2695 * (p^e*q^f*r^g) * ((e+1)*(f+1)*(g+1)) := by
  have hq' : 6*W q f ≤ (7*(f+1))*q^f :=
    (weighted_bound q 6 f hq).trans (Nat.mul_le_mul_right _ (by omega))
  have hr' : 10*W r g ≤ (11*(g+1))*r^g :=
    (weighted_bound r 10 g hr).trans (Nat.mul_le_mul_right _ (by omega))
  have hp' : 4*W p e ≤ (5*e+4)*p^e := weighted_bound p 4 e hp
  have hW := Nat.mul_le_mul (Nat.mul_le_mul hp' hq') hr'
  have hs₁ : 4*S p e ≤ 5*p^e := geom_bound p 4 e hp
  have hs₂ : 6*S q f ≤ 7*q^f := geom_bound q 6 f hq
  have hs₃ : 10*S r g ≤ 11*r^g := geom_bound r 10 g hr
  have hS := Nat.mul_le_mul (Nat.mul_le_mul hs₁ hs₂) hs₃
  have hcoef : 7*((5*e+4)*(7*(f+1))*(11*(g+1)))+1540 ≤
      2695*((e+1)*(f+1)*(g+1)) := by
    nlinarith only [Nat.mul_le_mul (show 2 ≤ f+1 by omega) (show 2 ≤ g+1 by omega)]
  nlinarith only [Nat.mul_le_mul_left 7 hW, Nat.mul_le_mul_left 4 hS,
    Nat.mul_le_mul_left (p^e*q^f*r^g) hcoef]

private lemma signed_identity (n : ℕ) (hn : n ≠ 0) :
    a n + ((∑ d ∈ n.divisors, d*d.divisors.card : ℕ) : ℤ) =
      2*(n:ℤ)*n.divisors.card := by
  have H : (∑ d ∈ n.divisors, d*d.divisors.card) =
      n*n.divisors.card + ∑ d ∈ n.properDivisors, d*d.divisors.card := by
    calc
      _ = ∑ d ∈ insert n n.properDivisors, d*d.divisors.card := by rw [Nat.insert_self_properDivisors hn]
      _ = _ := sum_insert Nat.self_notMem_properDivisors
  rw [H]
  push_cast
  unfold a
  ring

/-- The four-prime quantitative exclusion for all positive exponents on the three larger primes. -/
theorem four_prime_gap (p q r e f g : ℕ) (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hp5 : 5 ≤ p) (hpq : p < q) (hqr : q < r) (he : 0 < e) (hf : 0 < f) (hg : 0 < g) :
    let n := 3*p^e*q^f*r^g
    37*(n:ℤ)*n.divisors.card ≤ 288*(a n - (σ 1 n : ℤ)) := by
  have hq7 : 7 ≤ q := by
    by_contra h
    have heq : q = 6 := by omega
    subst q
    exact absurd hq (by decide)
  have hr11 : 11 ≤ r := by
    by_contra h
    have cases : r = 8 ∨ r = 9 ∨ r = 10 := by omega
    rcases cases with rfl | rfl | rfl <;> exact absurd hr (by decide)
  have cp (s t i j : ℕ) (hs : s.Prime) (ht : t.Prime) (hst : s < t) :
      (s^i).Coprime (t^j) := (((Nat.coprime_primes hs ht).mpr hst.ne).pow_left i).pow_right j
  have three (t j : ℕ) (ht : t.Prime) (hlt : 3 < t) : Nat.Coprime 3 (t^j) :=
    ((Nat.coprime_primes (by decide : Nat.Prime 3) ht).mpr hlt.ne).pow_right j
  have c1 := three p e hp (by omega)
  have c2 : Nat.Coprime (3*p^e) (q^f) := Nat.coprime_mul_iff_left.mpr
    ⟨three q f hq (by omega), cp _ _ _ _ hp hq hpq⟩
  have c3 : Nat.Coprime (3*p^e*q^f) (r^g) := Nat.coprime_mul_iff_left.mpr
    ⟨Nat.coprime_mul_iff_left.mpr ⟨three r g hr (by omega),cp _ _ _ _ hp hr (by omega)⟩,
      cp _ _ _ _ hq hr hqr⟩
  let n := 3*p^e*q^f*r^g
  have ht : n.divisors.card = 2*(e+1)*(f+1)*(g+1) := by
    dsimp [n]
    rw [c3.card_divisors_mul, c2.card_divisors_mul, c1.card_divisors_mul]
    simp only [Nat.divisors_prime_pow hp,Nat.divisors_prime_pow hq,Nat.divisors_prime_pow hr,
      card_map,card_range,show (3:ℕ).divisors.card=2 by decide]
  have hw : (∑ d ∈ n.divisors, d*d.divisors.card) = 7*W p e*W q f*W r g := by
    dsimp [n]
    rw [moment_mul _ _ c3,moment_mul _ _ c2,moment_mul _ _ c1,
      moment_at_power p e hp,moment_at_power q f hq,moment_at_power r g hr]
    rw [show (∑ d ∈ (3:ℕ).divisors, d*d.divisors.card) = 7 by decide]
    rfl
  have hs : σ 1 n = 4*S p e*S q f*S r g := by
    dsimp [n]
    rw [isMultiplicative_sigma.map_mul_of_coprime c3,isMultiplicative_sigma.map_mul_of_coprime c2,
      isMultiplicative_sigma.map_mul_of_coprime c1,sigma_apply_prime_pow hp,
      sigma_apply_prime_pow hq,sigma_apply_prime_pow hr]
    simp only [mul_one,show σ 1 3 = 4 by decide,S]
  have hn : n ≠ 0 := by dsimp [n]; exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by decide)
    (pow_ne_zero _ hp.ne_zero)) (pow_ne_zero _ hq.ne_zero)) (pow_ne_zero _ hr.ne_zero)
  have hbound := bounds p q r e f g hp5 hq7 hr11 hf hg
  rw [←hw,←hs] at hbound
  have hcount : n*n.divisors.card = 6*(p^e*q^f*r^g)*((e+1)*(f+1)*(g+1)) := by rw [ht]; dsimp [n]; ring
  have id := signed_identity n hn
  zify at hbound hcount
  push_cast at id
  change 37*(n:ℤ)*n.divisors.card ≤ 288*(a n - (σ 1 n : ℤ))
  linarith only [hbound,hcount,id]

end DivisorSums.A245212
