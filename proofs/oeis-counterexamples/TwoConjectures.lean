import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# Two conjectures about modular arithmetic

* `SunTrinomial.eleven_terms_conjecture_false` refutes the eleven-term conjecture
  of Zhi-Wei Sun (OEIS A279821, 2016) with the witness 1,316,632,279.
* `OrdowskiWilson.ordowski` proves the inverse-power characterization proposed
  by Thomas Ordowski (OEIS A079853, 2020).

Replay with Lean 4.33.1 in mathlib revision
`0df444a360eaa60ab8c11dca51a86af692955474` by running
`lake env lean /path/to/TwoConjectures.lean`.

The sources of the questions are https://oeis.org/A279821 and https://oeis.org/A079853.
The digit congruence is Theorem 4.7 of Deutsch and Sagan (2006),
https://doi.org/10.1016/j.jnt.2005.06.005. The second result also follows
from Lerch's 1905 congruence for the Fermat and Wilson quotients.
-/
namespace SunTrinomial
open Polynomial
open scoped BigOperators

noncomputable def trin (R : Type*) [CommSemiring R] : R[X] := X ^ 2 + (X + 1)

/-- The central coefficient, taken over the natural numbers. -/
noncomputable def T (n : ℕ) : ℕ := ((trin ℕ) ^ n).coeff n

private lemma cast_T (p n : ℕ) :
    (T n : ZMod p) = ((trin (ZMod p)) ^ n).coeff n := by
  change (Nat.castRingHom (ZMod p)) (((trin ℕ) ^ n).coeff n) = _
  rw [← Polynomial.coeff_map]
  simp [trin]

private lemma digit_unique {p a d i k : ℕ} (hd : d < p) (hi : i ≤ 2 * d)
    (h : i + p * k = p * a + d) : i = d ∧ k = a := by
  rcases lt_trichotomy k a with hka | rfl | hak
  · have hh := Nat.mul_le_mul_left p hka
    rw [Nat.mul_succ] at hh
    omega
  · exact ⟨by omega, rfl⟩
  · have hh := Nat.mul_le_mul_left p hak
    rw [Nat.mul_succ] at hh
    omega

/-- A base-p digit can be removed before evaluating the coefficient. -/
theorem digit (p : ℕ) [hp : Fact p.Prime] (a d : ℕ) (hd : d < p) :
    (T (p * a + d) : ZMod p) = (T d : ZMod p) * (T a : ZMod p) := by
  classical
  simp only [cast_T]
  let f := trin (ZMod p)
  change (f ^ (p * a + d)).coeff (p * a + d) =
      (f ^ d).coeff d * (f ^ a).coeff a
  have he : f ^ p = expand (ZMod p) p f := by
    simp only [f, trin, add_pow_expChar, one_pow, map_add, map_pow, expand_X, map_one]
    rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 p]
  have hb : (f ^ d).natDegree ≤ 2 * d := by
    rw [Nat.mul_comm]
    apply natDegree_pow_le_of_le
    apply natDegree_add_le_of_degree_le
    · exact natDegree_X_pow_le 2
    · apply natDegree_add_le_of_degree_le <;> simp
  rw [pow_add, pow_mul, he, ← map_pow, mul_comm, coeff_mul,
      Finset.sum_eq_single (d, p * a)]
  · rw [coeff_expand_mul' hp.out.pos]
  · rintro ⟨i, j⟩ hmem hne
    have hs : i + j = p * a + d := Finset.mem_antidiagonal.mp hmem
    by_cases hi : i ≤ 2 * d
    · by_cases hj : p ∣ j
      · obtain ⟨k, rfl⟩ := hj
        obtain ⟨rfl, rfl⟩ := digit_unique hd hi hs
        exact (hne rfl).elim
      · rw [coeff_expand hp.out.pos, if_neg hj, mul_zero]
    · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hb (by omega)), zero_mul]
  · exact fun h => (h (Finset.mem_antidiagonal.mpr (Nat.add_comm _ _))).elim

/-- The binomial expansion used to compute only the small digit coefficients. -/
private theorem T_formula (n : ℕ) :
    T n = ∑ k ∈ Finset.range (n + 1),
      (if 2 * k ≤ n then (n - k).choose (n - 2 * k) else 0) * n.choose k := by
  unfold T trin
  rw [add_pow, finsetSum_coeff]
  simp only [coeff_mul_natCast, ← pow_mul, coeff_X_pow_mul', coeff_X_add_one_pow, Nat.cast_id]

/-- Evaluate a digit coefficient by factorial quotients (ordinary kernel reduction). -/
private def small (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n+1),
    (if 2 * k ≤ n then Nat.fast_choose (n - k) (n - 2 * k) else 0) * Nat.fast_choose n k

private theorem T_small (n : ℕ) : T n = small n := by
  simpa only [small, ← Nat.choose_eq_fast_choose] using T_formula n

private def fromDigits (p : ℕ) : List ℕ → ℕ
  | [] => 0
  | d :: ds => p * fromDigits p ds + d

private def digitProduct : List ℕ → ℕ
  | [] => 1
  | d :: ds => small d * digitProduct ds

private lemma cast_digits (p : ℕ) [Fact p.Prime] (ds : List ℕ)
    (hd : ∀ d ∈ ds, d < p) :
    (T (fromDigits p ds) : ZMod p) = (digitProduct ds : ZMod p) := by
  induction ds with
  | nil => simp [fromDigits, digitProduct, T]
  | cons d ds ih =>
    rw [fromDigits, digit _ _ _ (hd d (by simp)), digitProduct, Nat.cast_mul,
        ih (fun j hj => hd j (List.mem_cons_of_mem d hj)), T_small]

private theorem certify (p n : ℕ) [Fact p.Prime] (ds : List ℕ)
    (hd : ∀ d ∈ ds, d < p) (hn : fromDigits p ds = n)
    (hv : digitProduct ds % p = 1 % p) : T n ≡ 1 [MOD p] := by
  rw [← hn, ← ZMod.natCast_eq_natCast_iff, cast_digits p ds hd]
  exact (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hv

/-- The witness is 31 times 42,472,009. Its base-31 digits from least to most
significant are 0, 25, 19, 20, 30, 14, 1. Their coefficient residues multiply
to 900. In base 42,472,009 the digits are 0 and 31, and
T(31) = 1 + 1,268,520 times 42,472,009. -/
theorem residue : T 1316632279 ≡ 1 [MOD 1316632279] := by
  let : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  let : Fact (Nat.Prime 42472009) := ⟨by norm_num⟩
  apply (Nat.modEq_and_modEq_iff_modEq_mul (m := 31) (n := 42472009) (by decide)).mp
  constructor
  · exact certify 31 _ [0, 25, 19, 20, 30, 14, 1] (by simp (config := {decide := true}))
      (by decide) (by decide +kernel)
  · exact certify 42472009 _ [0, 31] (by simp (config := {decide := true}))
      (by decide) (by decide +kernel)

/-- Membership uses the original coefficient and rules out every prime square. -/
def qualifies (m : ℕ) : Prop :=
  1 < m ∧ ¬ m.Prime ∧ (∀ q : ℕ, q.Prime → m ≠ q ^ 2) ∧ T m ≡ 1 [MOD m]

def listed : List ℕ :=
  [12, 30, 902, 1360, 2450, 3730, 21475, 74945, 82208, 88282, 254677]

theorem counterexample : qualifies 1316632279 ∧ 1316632279 ∉ listed := by
  refine ⟨⟨by decide, by norm_num, ?_, residue⟩, by decide⟩
  intro q _ h
  have hs := congrArg Nat.sqrt h
  rw [Nat.sqrt_eq'] at hs
  have hr : Nat.sqrt 1316632279 = 36285 := by decide +kernel
  rw [hr] at hs
  subst q
  exact (by decide : (1316632279 : ℕ) ≠ 36285 ^ 2) h

theorem eleven_terms_conjecture_false :
    ¬ (∀ m : ℕ, qualifies m → m ∈ listed) := by
  intro h
  exact counterexample.2 (h _ counterexample.1)

#print axioms eleven_terms_conjecture_false
end SunTrinomial

/-! Thomas Ordowski's July 2, 2020 conjecture in OEIS A079853.
The proof linearizes products modulo the square of the prime. -/
namespace OrdowskiWilson
open scoped BigOperators

private lemma linear_prod {R ι : Type*} [CommRing R] {z : R} (hz : z * z = 0)
    (s : Finset ι) (f : ι → R) :
    ∏ i ∈ s, (1 + z * f i) = 1 + z * ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih]
    linear_combination f a * (∑ i ∈ s, f i) * hz

private lemma linear_pow {R : Type*} [CommRing R] {z : R} (hz : z * z = 0)
    (a : R) (n : ℕ) : (1 + z * a) ^ n = 1 + (n : R) * z * a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, Nat.cast_succ]
    linear_combination (n : R) * a ^ 2 * hz

/-- The inverse of the (p−1)-st power represents k^(1−p) at an odd prime. -/
noncomputable def inverseSum (p : ℕ) : ZMod (p ^ 2) :=
  ∑ k ∈ Finset.Ico 1 p, (((k : ZMod (p ^ 2)) ^ (p - 1))⁻¹)

/-- The full residue of the sum for every odd prime. Each Fermat power has the
form 1 + p*b modulo p² and its inverse is 1 - p*b. Multiplying the powers
and applying Wilson's theorem determines the sum of the corrections p*b. -/
theorem inverseSum_eq (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
    inverseSum p = (p : ZMod (p ^ 2)) - 2 - (p - 1).factorial := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let R := ZMod (p ^ 2)
  let z : R := p
  let s := Finset.Ico 1 p
  have hp1 : 1 ≤ p := hp.one_le
  have hs : z * z = 0 := by
    change (p : ZMod (p ^ 2)) * p = 0
    rw [← Nat.cast_mul, ← pow_two, ZMod.natCast_self]
  have hex (k : ℕ) (hk : k ∈ s) : ∃ b : ℤ, (k : ℤ)^(p - 1) - 1 = (p : ℤ) * b := by
    obtain ⟨h1,h2⟩ := Finset.mem_Ico.mp hk
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    push_cast
    apply sub_eq_zero.mpr
    apply ZMod.pow_card_sub_one_eq_one
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun hd => (not_lt_of_ge (Nat.le_of_dvd h1 hd)) h2
  let b (k : ℕ) : R := if hk : k ∈ s then ((hex k hk).choose : ℤ) else 0
  have hb (k : ℕ) (hk : k ∈ s) : (k : R) ^ (p - 1) = 1 + z * b k := by
    have h := congrArg (Int.castRingHom R) (hex k hk).choose_spec
    simp only [map_sub, map_one, map_pow, map_mul, map_natCast] at h
    simp only [b, dif_pos hk, z]
    linear_combination h
  have hinv (k : ℕ) (hk : k ∈ s) : ((k : R) ^ (p - 1))⁻¹ = 1 - z * b k := by
    apply ZMod.inv_eq_of_mul_eq_one
    rw [hb k hk]
    linear_combination -(b k) ^ 2 * hs
  have hws : (p : ℤ) ∣ ((p - 1).factorial : ℤ) + 1 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    push_cast
    rw [ZMod.wilsons_lemma, neg_add_cancel]
  obtain ⟨w, hw⟩ := hws
  have hfac : ((p - 1).factorial : R) = -(1 + z * (-(w : R))) := by
    have h := congrArg (Int.castRingHom R) hw
    simp only [map_add, map_one, map_mul, map_natCast] at h
    dsimp [z]
    linear_combination h
  have heven : Even (p - 1) := hp.even_sub_one hodd
  have hz1 : ((p - 1 : ℕ) : R) = z - 1 := by rw [Nat.cast_sub hp1, Nat.cast_one]
  have hpow : ((p - 1).factorial : R) ^ (p - 1) = 1 + z * (w : R) := by
    rw [hfac, heven.neg_pow, linear_pow hs, hz1]
    linear_combination -(w : R) * hs
  have hprod : (∏ k ∈ s, (k : R)) = (p - 1).factorial := by
    rw [← Finset.prod_natCast _ (fun k : ℕ => k)]
    change ((∏ k ∈ Finset.Ico 1 p, k : ℕ) : R) = _
    apply congrArg (fun n : ℕ => (n : R))
    simpa only [Nat.sub_add_cancel hp1] using Finset.prod_Ico_id_eq_factorial (p - 1)
  have hsum : z * ∑ k ∈ s, b k = z * (w : R) := by
    have h := calc
      (1 + z * ∑ k ∈ s, b k) = ∏ k ∈ s, (1 + z * b k) := (linear_prod hs s b).symm
      _ = ∏ k ∈ s, (k : R) ^ (p - 1) := Finset.prod_congr rfl fun k hk => (hb k hk).symm
      _ = ((p - 1).factorial : R) ^ (p - 1) := by rw [Finset.prod_pow, hprod]
      _ = 1 + z * (w : R) := hpow
    exact add_left_cancel h
  change (∑ k ∈ s, ((k : R) ^ (p - 1))⁻¹) = z - 2 - ((p - 1).factorial : R)
  rw [Finset.sum_congr rfl hinv, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum,
    Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcard : s.card = p - 1 := by simp [s]
  rw [hcard, hz1, hfac]
  ring

/-- The inverse-power sum picks out precisely the odd near-Wilson primes of order two. -/
theorem ordowski (p : ℕ) (hp : p.Prime) :
    inverseSum p = -1 ↔ p ≠ 2 ∧ ((p - 2).factorial : ZMod (p ^ 2)) = 1 := by
  by_cases h2 : p = 2
  · subst p
    decide +kernel
  have hp2 : 2 ≤ p := hp.two_le
  have hfac : ((p - 1).factorial : ZMod (p ^ 2)) =
      ((p : ZMod (p ^ 2)) - 1) * (p - 2).factorial := by
    have he : p - 1 = (p - 2)+1 := by omega
    rw [he, Nat.factorial_succ, Nat.cast_mul, ← he, Nat.cast_sub hp.one_le, Nat.cast_one]
  have hnil : (p : ZMod (p ^ 2)) * p = 0 := by
    rw [← Nat.cast_mul, ← pow_two, ZMod.natCast_self]
  rw [inverseSum_eq p hp h2, hfac, and_iff_right h2]
  constructor
  · intro h
    linear_combination ((p : ZMod (p ^ 2))+1) * h + (((p - 2).factorial : ZMod (p ^ 2))-1) * hnil
  · intro h
    rw [h]
    ring

#print axioms ordowski
end OrdowskiWilson
