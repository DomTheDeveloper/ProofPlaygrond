module

public import Mathlib.Data.Nat.Factorization.Root
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

public section

namespace SquareDivisors

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- The roots d of square divisors d² of n are the divisors of floorRoot 2 n. -/
theorem square_indices {n d : ℕ} (hn : n ≠ 0) :
    d ∈ (Nat.floorRoot 2 n).divisors ↔ d^2 ∣ n := by
  rw [Nat.mem_divisors, Nat.pow_dvd_iff_dvd_floorRoot]
  exact and_iff_left (Nat.floorRoot_ne_zero.mpr ⟨by decide, hn⟩)

private def sqPhi : ArithmeticFunction ℕ := ⟨fun d => (d^2).totient, by simp⟩

private theorem sqPhi_mult : sqPhi.IsMultiplicative := by
  constructor
  · change (1^2 : ℕ).totient = 1
    simp
  · intro m n h
    change ((m*n)^2).totient = (m^2).totient * (n^2).totient
    rw [mul_pow, Nat.totient_mul ((h.pow_left 2).pow_right 2)]

private def divisorSum := sqPhi * (ArithmeticFunction.zeta : ArithmeticFunction ℕ)

private theorem divisorSum_apply (s : ℕ) :
    divisorSum s = ∑ d ∈ s.divisors, (d^2).totient := by
  unfold divisorSum
  rw [ArithmeticFunction.mul_zeta_apply]
  rfl

private theorem localTotient (p e : ℕ) (hp : p.Prime) :
    (∑ j ∈ range (e+1), ((p^j)^2).totient) * (p+1) = p*(p^e)^2+1 := by
  induction e with
  | zero => simp
  | succ e ih =>
    have ht : ((p^(e+1))^2).totient = p*(p^e)^2*(p-1) := by
      rw [← pow_mul, show (e+1)*2 = (e*2+1)+1 by omega,
        Nat.totient_prime_pow_succ hp, pow_succ, pow_mul]
      ring
    have hbase : (p-1)*(p+1)+1 = p*p := by
      obtain ⟨q, hq⟩ : ∃ q : ℕ, p=q+1 := ⟨p-1, (Nat.sub_add_cancel hp.one_le).symm⟩
      rw [hq, Nat.add_sub_cancel]
      ring
    rw [sum_range_succ, add_mul, ih, ht, pow_succ p e]
    calc
      _ = p*(p^e)^2*((p-1)*(p+1)+1)+1 := by ring
      _ = _ := by rw [hbase]; ring

private theorem pairGeom (p l : ℕ) :
    (∑ j ∈ range l, p^(j*2))*(p+1) = ∑ j ∈ range (2*l), p^j := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [show 2*(l+1) = 2*l+1+1 by omega, sum_range_succ, sum_range_succ,
        sum_range_succ, add_mul, ih, pow_succ, show l*2 = 2*l by omega]
    ring

private theorem geomRatio (p l : ℕ) :
    (∑ j ∈ range l, p^(j*2))*(p+1) = (p^l+1)*(∑ j ∈ range l, p^j) := by
  rw [pairGeom, two_mul, sum_range_add]
  simp_rw [pow_add]
  rw [← mul_sum]
  ring

private theorem primePower (p e : ℕ) (hp : p.Prime) :
    divisorSum (p^e) * σ 1 ((p^e)^2) = σ 2 ((p^e)^2) := by
  rw [divisorSum_apply, Nat.sum_divisors_prime_pow hp, ← pow_mul,
      sigma_one_apply_prime_pow hp, sigma_apply_prime_pow hp]
  apply Nat.eq_of_mul_eq_mul_right (Nat.succ_pos p)
  calc
    _ = ((∑ i ∈ range (e+1), ((p^i)^2).totient)*(p+1)) *
        (∑ j ∈ range (e*2+1), p^j) := by
      simp only [Nat.succ_eq_add_one]
      ring
    _ = (p^(e*2+1)+1)*(∑ j ∈ range (e*2+1), p^j) := by
      rw [localTotient p e hp, pow_succ p (e*2), pow_mul p e 2]
      ring
    _ = _ := (geomRatio p (e*2+1)).symm

private theorem squareIdentity (s : ℕ) :
    divisorSum s * σ 1 (s^2) = σ 2 (s^2) := by
  induction s using Nat.recOnPosPrimePosCoprime with
  | prime_pow p e hp _ => exact primePower p e hp
  | zero => simp
  | one => simp [divisorSum_apply]
  | coprime a b _ _ hc ha hb =>
    have hF : divisorSum.IsMultiplicative := sqPhi_mult.mul isMultiplicative_zeta
    have hc2 := (hc.pow_left 2).pow_right 2
    rw [hF.map_mul_of_coprime hc, mul_pow, isMultiplicative_sigma.map_mul_of_coprime hc2,
        isMultiplicative_sigma.map_mul_of_coprime hc2]
    calc
      _ = (divisorSum a * σ 1 (a^2))*(divisorSum b * σ 1 (b^2)) := by ring
      _ = _ := by rw [ha, hb]

/-- Cross-multiplied A055210. The square of the flooring root is n's largest square divisor. -/
theorem yanev (n : ℕ) :
    (∑ d ∈ (Nat.floorRoot 2 n).divisors, (d^2).totient) *
      σ 1 ((Nat.floorRoot 2 n)^2) = σ 2 ((Nat.floorRoot 2 n)^2) := by
  rw [← divisorSum_apply, squareIdentity]

/-- The quotient as it appears in Yanev's conjecture, with ordinary rational division. -/
theorem yanev_ratio (n : ℕ) (hn : 0 < n) :
    ((∑ d ∈ (Nat.floorRoot 2 n).divisors, (d^2).totient : ℕ) : ℚ) =
      (σ 2 ((Nat.floorRoot 2 n)^2) : ℚ) / (σ 1 ((Nat.floorRoot 2 n)^2) : ℚ) := by
  have hroot : Nat.floorRoot 2 n ≠ 0 := Nat.floorRoot_ne_zero.mpr ⟨by decide, hn.ne'⟩
  have hden : 0 < σ 1 ((Nat.floorRoot 2 n)^2) :=
    ArithmeticFunction.sigma_pos_iff.mpr (pow_pos (Nat.pos_of_ne_zero hroot) 2)
  apply (eq_div_iff (Nat.cast_ne_zero.mpr hden.ne' : (σ 1 ((Nat.floorRoot 2 n)^2) : ℚ) ≠ 0)).2
  exact_mod_cast yanev n

#print axioms yanev_ratio
#print axioms square_indices
#print axioms yanev

end SquareDivisors
