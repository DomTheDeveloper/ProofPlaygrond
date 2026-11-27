module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Algebra.Order.Round
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Nat.Size
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Int.ModEq
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.NumberTheory.LucasPrimality
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Tactic.NormNum.Prime

@[expose] public section

section

/-!
# Recovering the divisor sum from one prescribed bit per query

For a positive integer n let I(n) = sigma(n)/n. The main theorem
`sigmaFromBits_correct` recovers sigma(n) with a fixed list of queries
requesting one prescribed bit of I at each input. The theorem
`splitOddSemiprime_correct` gives the direct semiprime reduction.
The executable `decideAway` gives certified abundance decisions from
small prime divisors. The final note gives the bit costs and explains
how the stated results on full factorization use a separate preprint.
-/

namespace AbundancePrecision

open ArithmeticFunction

def index (n : ℕ) : ℚ := (sigma 1 n : ℚ) / n

def localIndex (p e : ℕ) : ℚ :=
  (∑ i ∈ Finset.range (e+1), (p : ℚ)^i) / (p : ℚ)^e

/-- Count powers of a tested prime by divisibility. No factorization of n is used. -/
def exponentAt (n p : ℕ) : ℕ :=
  ((Finset.range (n.log2+1)).filter fun e => p^e ∣ n).card - 1

/-- Product of the local indices for the prime divisors up to cutoff. -/
def truncated (n cutoff : ℕ) : ℚ :=
  ∏ p ∈ (Finset.range (cutoff+1)).filter (fun p => p.Prime ∧ p ∣ n),
    localIndex p (exponentAt n p)

theorem exponentAt_correct {n p : ℕ} (hn : 0 < n) (hp : p.Prime) :
    exponentAt n p = n.factorization p := by
  have hpow : p^(n.factorization p) ∣ n := (hp.pow_dvd_iff_le_factorization hn.ne').mpr le_rfl
  have hmax : n.factorization p ≤ n.log2 := (Nat.le_log2 hn.ne').mpr
    ((Nat.pow_le_pow_left hp.two_le _).trans (Nat.le_of_dvd hn hpow))
  have he : ((Finset.range (n.log2+1)).filter fun e => p^e ∣ n) =
      Finset.range (n.factorization p+1) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_range, hp.pow_dvd_iff_le_factorization hn.ne']
    omega
  simp [exponentAt, he]

private theorem local_lower {p : ℕ} (hp : 0 < p) (e : ℕ) : 1 ≤ localIndex p e := by
  apply (le_div_iff₀ (by positivity : 0 < (p : ℚ)^e)).mpr
  rw [one_mul]
  exact Finset.single_le_sum (fun i _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_self e))

private theorem local_upper {p U : ℕ} (hp : p.Prime) (hU : 0 < U) (hsmall : U < p)
    (e : ℕ) : localIndex p e ≤ 1 + 1/(U : ℚ) := by
  have hp1 : 1 < (p : ℚ) := by exact_mod_cast hp.one_lt
  have huq : 0 < (U : ℚ) := by exact_mod_cast hU
  have hup : (U : ℚ) ≤ (p : ℚ)-1 := by
    have hc : (U : ℚ)+1 ≤ (p : ℚ) := by exact_mod_cast hsmall
    linarith
  calc
    localIndex p e ≤ (p : ℚ)/(p-1 : ℚ) := by
      apply (div_le_div_iff₀ (by positivity) (by linarith)).mpr
      rw [geom_sum_mul, pow_succ, mul_comm (p : ℚ)]
      linarith
    _ = 1+1/(p-1 : ℚ) := by
      have he : (p : ℚ)-1 ≠ 0 := by linarith
      field_simp [he]
      ring
    _ ≤ _ := by linarith only [one_div_le_one_div_of_le huq hup]

private theorem index_product {n : ℕ} (hn : 0 < n) :
    index n = ∏ p ∈ n.primeFactors, localIndex p (n.factorization p) := by
  have hnum : (sigma 1 n : ℚ) =
      ∏ p ∈ n.primeFactors, ∑ i ∈ Finset.range (n.factorization p+1), (p : ℚ)^i := by
    rw [sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn.ne']
    push_cast
    simp
  have hden : (n : ℚ) = ∏ p ∈ n.primeFactors, (p : ℚ)^(n.factorization p) := by
    exact_mod_cast Nat.prod_primeFactors_pow_factorization hn.ne'
  rw [index, hnum, hden, ← Finset.prod_div_distrib]
  rfl

private theorem truncated_eq {n : ℕ} (hn : 0 < n) (U : ℕ) :
    truncated n U = ∏ p ∈ n.primeFactors.filter (fun p => p ≤ U),
      localIndex p (n.factorization p) := by
  have hs : (Finset.range (U+1)).filter (fun p => p.Prime ∧ p ∣ n) =
      n.primeFactors.filter (fun p => p ≤ U) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_primeFactors, Nat.lt_succ_iff]
    exact ⟨fun ⟨hb, hp, hd⟩ => ⟨⟨hp, hd, hn.ne'⟩, hb⟩,
      fun ⟨⟨hp, hd, _⟩, hb⟩ => ⟨hb, hp, hd⟩⟩
  rw [truncated, hs]
  apply Finset.prod_congr rfl
  intro p h
  rw [exponentAt_correct hn (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp h).1)]

private theorem card_primes_le {n : ℕ} (hn : 0 < n) : n.primeFactors.card ≤ n.log2 := by
  apply (Nat.le_log2 hn.ne').mpr
  calc
    2^n.primeFactors.card = ∏ _p ∈ n.primeFactors, 2 := by simp
    _ ≤ ∏ p ∈ n.primeFactors, p :=
      Finset.prod_le_prod' fun _ h => (Nat.prime_of_mem_primeFactors h).two_le
    _ ≤ n := Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd _)

private theorem growth_bound (U : ℚ) (k : ℕ) (hk : (k : ℚ) < U) :
    (1+1/U)^k ≤ U/(U-k) := by
  induction k with
  | zero =>
    have hU : U ≠ 0 := by simpa using (ne_of_gt hk)
    simp [hU]
  | succ k ih =>
    have hs : (k : ℚ)+1 < U := by exact_mod_cast hk
    have hU : 0 < U := by linarith [Nat.cast_nonneg (α := ℚ) k]
    have hk' : (k : ℚ) < U := by linarith
    rw [pow_succ, Nat.cast_succ]
    calc
      _ ≤ U/(U-k)*(1+1/U) :=
        mul_le_mul_of_nonneg_right (ih hk') (by positivity)
      _ = (U+1)/(U-k) := by field_simp
      _ ≤ _ := by
        apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
        nlinarith [Nat.cast_nonneg (α := ℚ) k]

/-- All omitted factors are accounted for using the size of the input. -/
theorem bracket {n U b : ℕ} (hn : 0 < n) (hb : n.log2 ≤ b) (hU : b < U) :
    truncated n U ≤ index n ∧
    index n ≤ truncated n U * ((U : ℚ)/(U-b)) := by
  let f (p : ℕ) := localIndex p (n.factorization p)
  let T := n.primeFactors.filter (fun p => ¬ p ≤ U)
  have hT : ∀ p ∈ T, p.Prime := fun _ h => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp h).1
  have ht1 : 1 ≤ ∏ p ∈ T, f p :=
    Finset.one_le_prod fun p hp => local_lower (hT p hp).pos _
  have hj1 : 1 ≤ truncated n U := by
    rw [truncated_eq hn]
    exact Finset.one_le_prod fun p hp =>
      local_lower (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos _
  have hs : truncated n U * (∏ p ∈ T, f p) = index n := by
    rw [truncated_eq hn, index_product hn]
    exact Finset.prod_filter_mul_prod_filter_not n.primeFactors _ _
  have hu : 0 < U := by omega
  have hc : T.card ≤ b :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans ((card_primes_le hn).trans hb)
  have ht : ∏ p ∈ T, f p ≤ (U : ℚ)/(U-b) := calc
    _ ≤ ∏ _p ∈ T, (1+1/(U : ℚ)) := by
      apply Finset.prod_le_prod
      · exact fun p hp => (zero_le_one.trans (local_lower (hT p hp).pos _))
      · exact fun p hp => local_upper (hT p hp) hu (lt_of_not_ge (Finset.mem_filter.mp hp).2) _
    _ = (1+1/(U : ℚ))^T.card := by simp
    _ ≤ (1+1/(U : ℚ))^b := pow_le_pow_right₀ (by linarith [show 0 ≤ 1/(U : ℚ) by positivity]) hc
    _ ≤ _ := growth_bound _ _ (by exact_mod_cast hU)
  rw [← hs]
  exact ⟨le_mul_of_one_le_right (zero_le_one.trans hj1) ht1,
    mul_le_mul_of_nonneg_left ht (zero_le_one.trans hj1)⟩

def lowerEstimate (n h : ℕ) : ℚ :=
  truncated n ((4*h+1)*(n.log2+1))

theorem estimate_error {n h : ℕ} (hn : 0 < n) (hh : 0 < h) :
    lowerEstimate n h ≤ index n ∧
    index n ≤ lowerEstimate n h * (1+1/(4*(h : ℚ))) := by
  let b := n.log2+1
  have hb : 0 < b := Nat.succ_pos _
  have hU : b < (4*h+1)*b := by nlinarith
  obtain ⟨hl, hu⟩ := bracket hn (b := b) (Nat.le_succ _) hU
  refine ⟨hl, ?_⟩
  have he : ((↑((4*h+1)*b) : ℚ)/(↑((4*h+1)*b)-(b : ℚ))) = 1+1/(4*(h : ℚ)) := by
    push_cast
    have hbq : (0 : ℚ) < b := by exact_mod_cast hb
    have hhq : (0 : ℚ) < h := by exact_mod_cast hh
    field_simp
    nlinarith [mul_pos hbq hhq]
  rwa [he] at hu

/-- Exact answers are returned only when the interval settles the comparison. -/
def decideAway (n h : ℕ) : Option Bool :=
  let lo := lowerEstimate n h
  if 2 < lo then some true
  else if lo*(1+1/(4*(h : ℚ))) ≤ 2 then some false
  else none

theorem decideAway_spec {n h : ℕ} (hn : 0 < n) (hh : 0 < h) :
    match decideAway n h with
    | some true => 2 < index n
    | some false => index n ≤ 2
    | none => |index n-2| ≤ 1/(2*(h : ℚ)) := by
  obtain ⟨hl, hu⟩ := estimate_error hn hh
  have hhq : (0 : ℚ) < h := by exact_mod_cast hh
  by_cases hlo : 2 < lowerEstimate n h
  · simp only [decideAway, if_pos hlo]
    exact hlo.trans_le hl
  · by_cases hhi : lowerEstimate n h * (1+1/(4*(h : ℚ))) ≤ 2
    · simp only [decideAway, if_neg hlo, if_pos hhi]
      exact hu.trans hhi
    · simp only [decideAway, if_neg hlo, if_neg hhi]
      have h1 : lowerEstimate n h ≤ 2 := le_of_not_gt hlo
      have hd : lowerEstimate n h*(1/(4*(h : ℚ))) ≤ 2*(1/(4*(h : ℚ))) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      have he : 2*(1/(4*(h : ℚ))) = 1/(2*(h : ℚ)) := by ring
      rw [he] at hd
      have h2 := lt_of_not_ge hhi
      exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The generic interval actually contains two rational values with opposite
bits at position k when the reliable precision falls short. This is a
limitation of using that interval as the only information about I(n). -/
theorem successive_floors_in_interval {lo : ℚ} {h k : ℕ} (hl : 1 ≤ lo)
    (hh : 0 < h) (hk : 4*h ≤ 2^k) :
    ∃ y : ℚ, lo ≤ y ∧ y ≤ lo*(1+1/(4*(h : ℚ))) ∧
      ⌊(2 : ℚ)^k*y⌋ = ⌊(2 : ℚ)^k*lo⌋+1 := by
  have hq : (0 : ℚ) < h := by exact_mod_cast hh
  have hp : 0 < (2 : ℚ)^k := by positivity
  have hkq : 4*(h : ℚ) ≤ (2 : ℚ)^k := by exact_mod_cast hk
  have hi := one_div_le_one_div_of_le (by positivity : 0 < 4*(h : ℚ)) hkq
  have he : 1/(4*(h : ℚ)) ≤ lo*(1/(4*(h : ℚ))) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hl
      (by positivity : 0 ≤ 1/(4*(h : ℚ)))
  refine ⟨lo+1/(2 : ℚ)^k, by linarith [show 0 ≤ 1/(2 : ℚ)^k by positivity], ?_, ?_⟩
  · linarith
  · rw [mul_add, mul_one_div_cancel hp.ne', Int.floor_add_one]

/-- Multiplication by 2^e is a known rescaling of the abundancy of an odd input. -/
def binaryWeight (e : ℕ) : ℚ := 2 - 1/(2 : ℚ)^e

theorem index_mul {m n : ℕ} (h : m.Coprime n) : index (m*n) = index m * index n := by
  simp only [index, isMultiplicative_sigma.map_mul_of_coprime h, Nat.cast_mul]
  ring

theorem two_power_sum (e : ℕ) : sigma 1 (2^e) = 2^(e+1)-1 := by
  rw [sigma_one_apply_prime_pow Nat.prime_two]
  simpa using geom_sum_mul_of_one_le (by decide : 1 ≤ (2 : ℕ)) (e+1)

theorem index_two_power (e : ℕ) : index (2^e) = binaryWeight e := by
  rw [index, two_power_sum, Nat.cast_sub (one_le_pow₀ (by decide : 1 ≤ (2 : ℕ)))]
  push_cast
  dsimp [binaryWeight]
  rw [pow_succ]
  field_simp

theorem one_le_binaryWeight (e : ℕ) : 1 ≤ binaryWeight e := by
  have h : (1 : ℚ) ≤ 2^e := one_le_pow₀ (by norm_num)
  have hb : (1 : ℚ)/2^e ≤ 1 := (div_le_iff₀ (by positivity)).mpr (by simpa)
  dsimp [binaryWeight]
  linarith

/-- Decode a supplied approximation y to I(2^e*w), with w odd. -/
def decodeOdd (w e : ℕ) (y : ℚ) : ℤ := round (y*((w : ℚ)/binaryWeight e))

theorem decodeOdd_correct {w e : ℕ} {y : ℚ} (hw : 0 < w) (hodd : Odd w)
    (hy : |y-index (2^e*w)| < 1/(2*(w : ℚ))) :
    decodeOdd w e y = (sigma 1 w : ℤ) := by
  have hwq : 0 < (w : ℚ) := by exact_mod_cast hw
  have hweight := one_le_binaryWeight e
  have hpos : 0 < binaryWeight e := zero_lt_one.trans_le hweight
  have hcop : (2^e).Coprime w := (Nat.coprime_two_left.mpr hodd).pow_left e
  have hid : y*((w : ℚ)/binaryWeight e)-(sigma 1 w : ℚ) =
      (y-index (2^e*w))*((w : ℚ)/binaryWeight e) := by
    rw [index_mul hcop, index_two_power, index]
    field_simp [hpos.ne', hwq.ne']
  have hscale : (w : ℚ)/binaryWeight e ≤ w :=
    (div_le_iff₀ hpos).mpr (le_mul_of_one_le_right hwq.le hweight)
  have he : |y*((w : ℚ)/binaryWeight e)-(sigma 1 w : ℚ)| < 1/2 := calc
    _ = |y-index (2^e*w)| * ((w : ℚ)/binaryWeight e) := by
      rw [hid, abs_mul, abs_of_pos (div_pos hwq hpos)]
    _ < (1/(2*(w : ℚ)))*((w : ℚ)/binaryWeight e) :=
      mul_lt_mul_of_pos_right hy (div_pos hwq hpos)
    _ ≤ (1/(2*(w : ℚ)))*w := mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = _ := by field_simp
  apply round_eq_iff.mpr
  obtain ⟨hl, hu⟩ := abs_lt.mp he
  change (↑(sigma 1 w : ℤ) : ℚ)-1/2 ≤ _ ∧ _ < (↑(sigma 1 w : ℤ) : ℚ)+1/2
  push_cast
  constructor <;> linarith

/-- Restore any power of two stripped from the original input. -/
theorem decode_general {w e a : ℕ} {y : ℚ} (hw : 0 < w) (hodd : Odd w)
    (hy : |y-index (2^e*w)| < 1/(2*(w : ℚ))) :
    ((2^(a+1)-1 : ℕ) : ℤ)*decodeOdd w e y = (sigma 1 (2^a*w) : ℤ) := by
  have hc : (2^a).Coprime w := (Nat.coprime_two_left.mpr hodd).pow_left a
  rw [decodeOdd_correct hw hodd hy, isMultiplicative_sigma.map_mul_of_coprime hc,
    two_power_sum, Nat.cast_mul]

/-- Finite precision criterion. b+1 accurate places suffice for w<2^b. -/
theorem decode_from_places {w e k b : ℕ} {y : ℚ} (hw : 0 < w) (hodd : Odd w)
    (hb : w < 2^b) (hk : b+1 ≤ k) (hy : |y-index (2^e*w)| ≤ 1/(2 : ℚ)^k) :
    decodeOdd w e y = (sigma 1 w : ℤ) := by
  apply decodeOdd_correct hw hodd
  apply hy.trans_lt
  apply one_div_lt_one_div_of_lt (by positivity)
  have h1 : 2*w < 2^(b+1) := by rw [pow_succ]; omega
  exact_mod_cast h1.trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) hk)

/-- A comparison can be applied to a padded integer with its threshold scaled
by a known divisor sum. The unfactored odd part stays the same. -/
theorem shifted_comparison {w : ℕ} (hodd : Odd w) (e h : ℕ) :
    (2^(e+1)-1)*h ≤ sigma 1 (2^e*w) ↔ h ≤ sigma 1 w := by
  have hc : (2^e).Coprime w := (Nat.coprime_two_left.mpr hodd).pow_left e
  have hpos := ArithmeticFunction.sigma_pos 1 (2^e) (by positivity)
  rw [isMultiplicative_sigma.map_mul_of_coprime hc, ← two_power_sum]
  exact Nat.mul_le_mul_left_iff hpos

/-- Quantitative form of the half-integer comparison in Shunia's Lemma 2.1.
If T approximates the target multiplier, its product with s/r retains a
margin of 1/(4r) on the correct side of 2. In the reduction, s is sigma(r). -/
theorem threshold_margin {r s g : ℕ} {T : ℚ} (hr : 0 < r) (hg : 0 < g)
    (hgr : g ≤ 2*r) (hsr : s ≤ 2*r)
    (ht : |T-4*(r : ℚ)/(2*(g : ℚ)-1)| ≤ 1/(100*(r : ℚ))) :
    (g ≤ s → 2+1/(4*(r : ℚ)) < T*((s : ℚ)/r)) ∧
    (s < g → T*((s : ℚ)/r) < 2-1/(4*(r : ℚ))) := by
  let D : ℚ := 2*(g : ℚ)-1
  have hrq : 0 < (r : ℚ) := by exact_mod_cast hr
  have hgq : 1 ≤ (g : ℚ) := by exact_mod_cast hg
  have hgrq : (g : ℚ) ≤ 2*r := by exact_mod_cast hgr
  have hsrq : (s : ℚ) ≤ 2*r := by exact_mod_cast hsr
  have hD : 0 < D := by dsimp [D]; linarith
  have hx : 0 ≤ (s : ℚ)/r := by positivity
  have hx' : (s : ℚ)/r ≤ 2 := (div_le_iff₀ hrq).mpr hsrq
  have hdif : T*((s : ℚ)/r)-4*s/D = (T-4*r/D)*((s : ℚ)/r) := by
    field_simp [hD.ne', hrq.ne']
  have he : |T*((s : ℚ)/r)-4*s/D| ≤ 1/(50*(r : ℚ)) := calc
    _ = |T-4*(r : ℚ)/D| * ((s : ℚ)/r) := by rw [hdif, abs_mul, abs_of_nonneg hx]
    _ ≤ (1/(100*(r : ℚ)))*2 := mul_le_mul ht hx' hx (by positivity)
    _ = _ := by ring
  obtain ⟨hl, hu⟩ := abs_le.mp he
  have hc : 1/(2*(r : ℚ)) ≤ 2/D := by
    apply (div_le_div_iff₀ (by positivity) hD).mpr
    dsimp [D]
    linarith
  have hslack : 1/(4*(r : ℚ))+1/(50*(r : ℚ)) < 1/(2*(r : ℚ)) := by
    field_simp
    linarith
  constructor
  · intro h
    have hq : (g : ℚ) ≤ s := by exact_mod_cast h
    have hbase : 2+2/D ≤ 4*(s : ℚ)/D := by
      apply (le_div_iff₀ hD).mpr
      rw [add_mul, div_mul_cancel₀ _ hD.ne']
      dsimp [D]
      linarith
    linarith
  · intro h
    have hq : (s : ℚ)+1 ≤ g := by exact_mod_cast h
    have hbase : 4*(s : ℚ)/D ≤ 2-2/D := by
      apply (div_le_iff₀ hD).mpr
      rw [sub_mul, div_mul_cancel₀ _ hD.ne']
      dsimp [D]
      linarith
    linarith

-- Opposite answers at inputs with the same product of small Euler factors.

private theorem small_example_formula {p : ℕ} (hp : p.Prime) (hcop : (32 : ℕ).Coprime p) :
    sigma 1 (32*p) = 63*(1+p) := by
  have he : sigma 1 p = 1+p := by
    simpa [Finset.sum_range_succ] using (sigma_one_apply_prime_pow (i := 1) hp)
  rw [isMultiplicative_sigma.map_mul_of_coprime hcop, he, show 32 = 2^5 by decide, two_power_sum]
  rfl

theorem example_above : sigma 1 (32*61) = 2*(32*61)+2 := by
  rw [small_example_formula (by decide) (by decide)]

theorem example_below : sigma 1 (32*67) + 4 = 2*(32*67) := by
  rw [small_example_formula (by decide) (by decide)]


/-! ## A nonadaptive reduction to one prescribed fractional bit -/

/-- The specified bit of I(z). This is the oracle specification. -/
def middleBit (z : ℕ) : Fin 2 :=
  ⟨(2^(z.size/2) * sigma 1 z / z)%2, Nat.mod_lt _ (by decide)⟩

/-- All query arguments depend solely on u and the digit index i. -/
def query (u i : ℕ) : ℕ := u <<< (5*u.size+2*i)

def readBits (bit : ℕ → Fin 2) (u : ℕ) : ℕ → ℕ
  | 0 => 0
  | i+1 => 2*readBits bit u i + (bit (query u i)).val

def leftFloor (S w j : ℕ) := (2^j*S-1)/w

/-- Integer floors just below a rational boundary, including exact multiples. -/
private theorem just_below {A D s w : ℕ} (hA : 0 < A) (hD : 0 < D)
    (hs : 0 < s) (hsD : s ≤ D) : (D*A-s)/(D*w) = (A-1)/w := by
  have hA' : A-1+1 = A := by omega
  have he : D*A = D*(A-1)+D := by
    calc
      _ = D*(A-1+1) := by rw [hA']
      _ = _ := by ring
  have hpos : 0 < D*A := Nat.mul_pos hD hA
  have hi : (D*A-s)/D = A-1 := by
    apply Nat.div_eq_of_lt_le
    · rw [Nat.mul_comm (A-1) D]
      omega
    · rw [hA', mul_comm A D]
      omega
  rw [← Nat.div_div_eq_div_mul, hi]

private theorem padded_floor {u : ℕ} (hu : 0 < u) (ho : Odd u) (k h : ℕ)
    (hS : sigma 1 u ≤ 2^h) :
    2^k * sigma 1 (2^(k+h)*u)/(2^(k+h)*u) = leftFloor (sigma 1 u) u (k+1) := by
  have hc : (2^(k+h)).Coprime u := (Nat.coprime_two_left.mpr ho).pow_left _
  have hs := ArithmeticFunction.sigma_pos 1 u hu.ne'
  have hden : 2^(k+h)*u = 2^k*(2^h*u) := by rw [pow_add, mul_assoc]
  have hn : (2^(k+h+1)-1)*sigma 1 u = 2^h*(2^(k+1)*sigma 1 u)-sigma 1 u := by
    rw [Nat.sub_mul, one_mul]
    simp only [pow_add, pow_one]
    ring_nf
  rw [isMultiplicative_sigma.map_mul_of_coprime hc, two_power_sum, hden,
    Nat.mul_div_mul_left _ _ (Nat.two_pow_pos _), hn]
  exact just_below (Nat.mul_pos (Nat.two_pow_pos _) hs) (Nat.two_pow_pos _) hs hS

theorem query_bit {u : ℕ} (hu : 0 < u) (ho : Odd u) (i : ℕ) :
    (middleBit (query u i)).val = leftFloor (sigma 1 u) u (3*u.size+i+1)%2 := by
  have hlen : (query u i).size / 2 = 3*u.size+i := by
    rw [query, Nat.size_shiftLeft hu.ne']
    omega
  have hz : query u i = 2^((3*u.size+i)+(2*u.size+i))*u := by
    rw [query, Nat.shiftLeft_eq, Nat.mul_comm]
    congr 2
    omega
  have hS : sigma 1 u ≤ 2^(2*u.size+i) := calc
    _ ≤ u^2 := sigma_le_pow_succ 1 u
    _ ≤ (2^u.size)^2 := Nat.pow_le_pow_left (Nat.lt_size_self _).le _
    _ = 2^(2*u.size) := by rw [← pow_mul, Nat.mul_comm u.size 2]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  change (2^((query u i).size/2)*sigma 1 (query u i)/(query u i))%2 = _
  rw [hlen, hz, padded_floor hu ho _ _ hS]

private theorem leftFloor_half {S w : ℕ} (hS : 0 < S) (j : ℕ) :
    leftFloor S w (j+1)/2 = leftFloor S w j := by
  dsimp [leftFloor]
  rw [Nat.div_div_eq_div_mul, Nat.mul_comm w 2]
  have he : 2^(j+1)*S = 2*(2^j*S) := by rw [pow_succ]; ring
  rw [he]
  exact just_below (Nat.mul_pos (Nat.two_pow_pos _) hS) (by decide) (by decide) (by decide)

private theorem assembled {u : ℕ} (hu : 0 < u) (ho : Odd u)
    (bit : ℕ → Fin 2) (i : ℕ) (correct : ∀ j < i, bit (query u j) = middleBit (query u j)) :
    leftFloor (sigma 1 u) u (3*u.size+i) =
      2^i*leftFloor (sigma 1 u) u (3*u.size)+readBits bit u i := by
  induction i with
  | zero => simp [readBits]
  | succ i ih =>
    let v := leftFloor (sigma 1 u) u (3*u.size+i+1)
    have hhalf : v/2 = leftFloor (sigma 1 u) u (3*u.size+i) :=
      leftFloor_half (ArithmeticFunction.sigma_pos 1 u hu.ne') _
    have hb : (bit (query u i)).val = v%2 := by
      rw [correct i (Nat.lt_succ_self _), query_bit hu ho]
    have hv : v = 2*leftFloor (sigma 1 u) u (3*u.size+i)+(bit (query u i)).val := by
      rw [← hhalf, hb, Nat.div_add_mod]
    change v = _
    rw [hv, ih (fun j hj => correct j (by omega)), readBits, pow_succ]
    ring

private theorem floor_block {P A w D : ℕ} (hA : 0 < A) (hw : 0 < w) (hP : w ≤ P)
    (h : (P*A-1)/w = P*((A-1)/w)+D) : D*w/P = (A-1)%w := by
  let r := (A-1)%w
  let t := (P*A-1)%w
  let f := (A-1)/w
  have hpos : 0 < P*A := Nat.mul_pos (by omega) hA
  have ha : A = w*f+(r+1) := by
    have hx := Nat.div_add_mod (A-1) w
    dsimp [f,r]
    omega
  have hy : P*A = w*(P*f+D)+(t+1) := by
    have hx := Nat.div_add_mod (P*A-1) w
    rw [h] at hx
    dsimp [f,t]
    omega
  have he : P*(r+1) = D*w+(t+1) := by
    nlinarith only [congrArg (fun x : ℕ => P*x) ha, hy]
  have ht : t < P := (Nat.mod_lt _ hw).trans_le hP
  change D*w/P = r
  apply Nat.div_eq_of_lt_le
  · rw [mul_comm r P]
    rw [Nat.mul_add, mul_one] at he
    omega
  · rw [mul_comm (r+1) P]
    omega

def residue (bit : ℕ → Fin 2) (u : ℕ) : ℕ := readBits bit u u.size*u/2^u.size+1

theorem residue_correct {u : ℕ} (hu : 0 < u) (ho : Odd u) (bit : ℕ → Fin 2)
    (correct : ∀ i < u.size, bit (query u i) = middleBit (query u i)) :
    residue bit u ≡ 2^(3*u.size)*sigma 1 u [MOD u] := by
  let A := 2^(3*u.size)*sigma 1 u
  have hA : 0 < A := Nat.mul_pos (Nat.two_pow_pos _) (ArithmeticFunction.sigma_pos _ _ hu.ne')
  have he := assembled hu ho bit u.size correct
  have hpow : 2^(3*u.size+u.size)*sigma 1 u = 2^u.size*A := by
    dsimp [A]
    rw [pow_add]
    ring
  dsimp only [leftFloor] at he
  rw [hpow] at he
  have r := floor_block hA hu (Nat.lt_size_self _).le he
  change readBits bit u u.size*u/2^u.size+1 ≡ A [MOD u]
  rw [r]
  have hm := (Nat.mod_modEq (A-1) u).add_right 1
  rwa [Nat.sub_add_cancel hA] at hm

private theorem three_power_sum (a : ℕ) : 2*sigma 1 (3^a)+1 = 3^(a+1) := by
  rw [sigma_one_apply_prime_pow Nat.prime_three, mul_comm]
  exact geom_sum_mul_add (2 : ℕ) (a+1)

/-- An odd power-of-three multiple turns the recovered residue into the whole
divisor sum. Inversion modulo 3^a uses the extended Euclidean algorithm. -/
def decodeCore (bit : ℕ → Fin 2) (w a : ℕ) : ℕ :=
  let M := 3^a
  let u := M*w
  ((-2*(residue bit u : ZMod M)) * ((2 : ZMod M)^(3*u.size))⁻¹).val

theorem decodeCore_correct {w a : ℕ} (hw : 0 < w) (ho : Odd w) (hc : (3 : ℕ).Coprime w)
    (hsize : sigma 1 w < 3^a) (bit : ℕ → Fin 2)
    (correct : ∀ i < (3^a*w).size, bit (query (3^a*w) i) = middleBit (query (3^a*w) i)) :
    decodeCore bit w a = sigma 1 w := by
  let M : ℕ := 3^a
  let u := M*w
  let K := 3*u.size
  have hM : 0 < M := by dsimp [M]; positivity
  have hu : 0 < u := Nat.mul_pos hM hw
  have hou : Odd u := ((show Odd (3 : ℕ) by decide).pow).mul ho
  have hm : M ∣ u := dvd_mul_right M w
  have hr := (residue_correct hu hou bit correct).of_dvd hm
  have hcast : (residue bit u : ZMod M) = (2 : ZMod M)^K*(sigma 1 u : ZMod M) := by
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr hr
  have hs : 2*(sigma 1 (3^a) : ZMod M) + 1 = 0 := by
    have he := congrArg (fun x : ℕ => (x : ZMod M)) (three_power_sum a)
    rw [pow_succ] at he
    have hz : ((3^a : ℕ) : ZMod M) = 0 := ZMod.natCast_self M
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, hz, zero_mul] using he
  have hsig : 2*(sigma 1 u : ZMod M) = -(sigma 1 w : ZMod M) := by
    have he : 2*(sigma 1 (3^a) : ZMod M) = -1 := eq_neg_of_add_eq_zero_left hs
    dsimp [u,M]
    rw [isMultiplicative_sigma.map_mul_of_coprime (hc.pow_left a), Nat.cast_mul, ← mul_assoc, he]
    ring
  have unit : IsUnit ((2 : ZMod M)^K) := by
    apply IsUnit.pow
    exact (ZMod.isUnit_iff_coprime 2 M).mpr ((by decide : Nat.Coprime 2 3).pow_right a)
  have hz : (-2*(residue bit u : ZMod M))*((2 : ZMod M)^K)⁻¹ = (sigma 1 w : ZMod M) := calc
    _ = -(2*(sigma 1 u : ZMod M)) * ((2 : ZMod M)^K*((2 : ZMod M)^K)⁻¹) := by
      rw [hcast]
      ring
    _ = _ := by rw [ZMod.mul_inv_of_unit _ unit, hsig, neg_neg, mul_one]
  change ((-2*(residue bit u : ZMod M))*((2 : ZMod M)^K)⁻¹).val = _
  rw [hz, ZMod.val_natCast, Nat.mod_eq_of_lt hsize]

private theorem strip_prime {n p : ℕ} (hn : 0 < n) (hp : p.Prime) :
    let e := exponentAt n p
    let w := n/p^e
    p^e*w = n ∧ 0 < w ∧ p.Coprime w := by
  dsimp only
  rw [exponentAt_correct hn hp]
  exact ⟨Nat.ordProj_mul_ordCompl_eq_self n p, Nat.ordCompl_pos p hn.ne',
    Nat.coprime_ordCompl hp hn.ne'⟩

/-- Recover sigma(n) with one bit per query. Only powers of 2 and 3 are
removed in preprocessing. The supplied routine is used at explicit arguments. -/
def sigmaFromBits (bit : ℕ → Fin 2) (n : ℕ) : ℕ :=
  let a := exponentAt n 2
  let v := n/2^a
  let c := exponentAt v 3
  let w := v/3^c
  (2^(a+1)-1) * ((3^(c+1)-1)/2) * decodeCore bit w (2*w.size)

theorem sigmaFromBits_correct {n : ℕ} (hn : 0 < n) :
    sigmaFromBits middleBit n = sigma 1 n := by
  let a := exponentAt n 2
  let v := n/2^a
  let c := exponentAt v 3
  let w := v/3^c
  obtain ⟨h2, hv, hv2⟩ := strip_prime hn Nat.prime_two
  change 2^a*v = n at h2
  change 0 < v at hv
  change Nat.Coprime 2 v at hv2
  obtain ⟨h3, hw, hw3⟩ := strip_prime hv Nat.prime_three
  change 3^c*w = v at h3
  change 0 < w at hw
  change Nat.Coprime 3 w at hw3
  have hwo : Odd w := Nat.coprime_two_left.mp (Nat.Coprime.coprime_dvd_right
    (show w ∣ v from ⟨3^c, by rw [← h3, mul_comm]⟩) hv2)
  have hsize : sigma 1 w < 3^(2*w.size) := calc
    _ ≤ w^2 := sigma_le_pow_succ 1 w
    _ < (2^w.size)^2 := Nat.pow_lt_pow_left (Nat.lt_size_self _) (by decide)
    _ = 2^(2*w.size) := by rw [← pow_mul, mul_comm w.size 2]
    _ ≤ _ := Nat.pow_le_pow_left (by decide) _
  have he := decodeCore_correct hw hwo hw3 hsize middleBit (fun _ _ => rfl)
  have hs2 : sigma 1 n = (2^(a+1)-1)*sigma 1 v := by
    conv_lhs => rw [← h2, isMultiplicative_sigma.map_mul_of_coprime (hv2.pow_left a), two_power_sum]
  have hs3 : sigma 1 v = sigma 1 (3^c)*sigma 1 w := by
    conv_lhs => rw [← h3, isMultiplicative_sigma.map_mul_of_coprime (hw3.pow_left c)]
  have hs := three_power_sum c
  change (2^(a+1)-1)*((3^(c+1)-1)/2)*decodeCore middleBit w (2*w.size) = _
  rw [he, hs2, hs3, show (3^(c+1)-1)/2 = sigma 1 (3^c) by omega, mul_assoc]

theorem query_length {u i : ℕ} (hu : 0 < u) (hi : i < u.size) :
    (query u i).size = 6*u.size+2*i ∧ (query u i).size < 8*u.size := by
  rw [query, Nat.size_shiftLeft hu.ne']
  omega

theorem tagged_length (w : ℕ) : (3^(2*w.size)*w).size ≤ 5*w.size := by
  apply Nat.size_le.mpr
  calc
    _ < 3^(2*w.size)*2^w.size :=
      Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self _) (by positivity)
    _ ≤ (2^2)^(2*w.size)*2^w.size :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by decide : 3 ≤ 2^2) _)
    _ = 2^(5*w.size) := by rw [← pow_mul, ← pow_add]; congr 1; omega

/-- For an odd semiprime it suffices to know the divisor sum modulo n. -/
def sigmaResidue (bit : ℕ → Fin 2) (n : ℕ) : ℕ :=
  ((residue bit n : ZMod n)*((2 : ZMod n)^(3*n.size))⁻¹).val

theorem sigmaResidue_correct {n : ℕ} (hn : 0 < n) (ho : Odd n) (bit : ℕ → Fin 2)
    (correct : ∀ i < n.size, bit (query n i) = middleBit (query n i)) :
    sigmaResidue bit n = sigma 1 n % n := by
  let K := 3*n.size
  have hc : (residue bit n : ZMod n) = (sigma 1 n : ZMod n)*(2 : ZMod n)^K := by
    have h := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (residue_correct hn ho bit correct)
    rw [mul_comm (sigma 1 n : ZMod n) ((2 : ZMod n)^K)]
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using h
  have h2 : IsUnit ((2 : ZMod n)^K) :=
    ((ZMod.isUnit_iff_coprime 2 n).mpr (Nat.coprime_two_left.mpr ho)).pow _
  change ((residue bit n : ZMod n)*((2 : ZMod n)^K)⁻¹).val = _
  rw [hc, mul_assoc, ZMod.mul_inv_of_unit _ h2, mul_one, ZMod.val_natCast]

def splitOddSemiprime (bit : ℕ → Fin 2) (n : ℕ) : ℕ × ℕ :=
  let s := sigmaResidue bit n-1
  let d := (s^2-4*n).sqrt
  ((s-d)/2, (s+d)/2)

theorem splitOddSemiprime_correct {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hop : Odd p) (hoq : Odd q) (hlt : p < q) (bit : ℕ → Fin 2)
    (correct : ∀ i < (p*q).size, bit (query (p*q) i) = middleBit (query (p*q) i)) :
    splitOddSemiprime bit (p*q) = (p,q) := by
  have primeSum {r : ℕ} (h : r.Prime) : sigma 1 r = 1+r := by
    simpa [Finset.sum_range_succ] using (sigma_one_apply_prime_pow (i := 1) h)
  have hcop : p.Coprime q := (Nat.coprime_primes hp hq).mpr hlt.ne
  have hp3 : 3 ≤ p := by
    have hn : p ≠ 2 := by rintro rfl; exact (by decide : ¬ Odd 2) hop
    have := hp.two_le
    omega
  have hbound : 1+p+q < p*q := by
    have h := Nat.mul_le_mul_right q hp3
    omega
  have hs : sigmaResidue bit (p*q)-1 = p+q := by
    rw [sigmaResidue_correct (Nat.mul_pos hp.pos hq.pos) (hop.mul hoq) bit correct,
      isMultiplicative_sigma.map_mul_of_coprime hcop, primeSum hp, primeSum hq,
      show (1+p)*(1+q) = (1+p+q)+p*q by ring, Nat.add_mod_right,
      Nat.mod_eq_of_lt hbound]
    omega
  let d := q-p
  have hd : p+d=q := by dsimp [d]; omega
  have hsq : (p+q)^2 = 4*(p*q)+d^2 := by rw [← hd]; ring
  dsimp only [splitOddSemiprime]
  rw [hs, hsq, Nat.add_sub_cancel_left, Nat.sqrt_eq']
  exact Prod.ext (by omega) (by omega)

-- These seven bits factor 77. Rewriting with query_bit evaluates only the
-- known divisor sum of 77, avoiding direct divisor enumeration on padded inputs.
example : (List.range 7).map (fun i => (middleBit (query 77 i)).val) = [0,0,0,1,0,0,0] := by
  simp only [query_bit (by decide : 0 < 77) (by decide : Odd 77)]
  decide


end AbundancePrecision

/-!
## Bit costs and consequences

Write L for the binary length of the integer tested. All approximations in
this note use absolute error in the normalized index I, unless an interval
is explicitly relative.

### One prescribed bit at each query

For a positive L-bit z define B(z) = floor(2^floor(L/2) I(z)) mod 2.
This fixes the position as a function of the input length, and fixes the
convention at an exact binary boundary. There is no request for a
particular position in a query. The implementation of 'middleBit' is
the mathematical specification of this bit. A deterministic polynomial
time implementation of this specification remains unknown.

Take an odd u, S = sigma(u), b = bit length(u), K = 3b. For i from 0
through b-1, ask B at z_i = 2^(5b+2i) u. Each argument is fixed in
advance and has length 6b+2i. Writing F(j) = floor((2^j S-1)/u),
the response is F(K+i+1) modulo 2. Indeed I(z_i) = (2-2^(-5b-2i))S/u.
After multiplying by 2^(3b+i), the numerator above u is
2^(3b+i+1) S minus S/2^(2b+i). This last quantity lies in (0,1)
since S ≤ u² < 2^(2b). The integer floor is unchanged if it is replaced
by a subtraction of 1. This also covers the case u divides 2^j S.

Read the b returned bits as an unsigned integer D, most significant
bit first. The recurrence floor(F(j+1)/2) = F(j) gives
D = F(K+b)-2^b F(K). Euclidean division shows that
A = floor(Du/2^b)+1 is the unique element of [1,u] congruent to 2^K S
modulo u. Since u is odd, multiplication by the inverse of 2^K recovers
S modulo u. For a product of two distinct odd primes p < q, this residue
equals 1+p+q. The quadratic X²-(p+q)X+u then gives both primes.
The semiprime case takes b yes/no queries, each shorter than 8b bits.

For a general input n, remove powers of 2 and 3, leaving w coprime to 6.
Take M = 3^(2 bitlength(w)) > w² and u = Mw. Recover the residue A as
above. Modulo M we have 2 sigma(u) = (3M-1) sigma(w) = -sigma(w).
Consequently -2 A (2^K)^(-1) modulo M is sigma(w) itself, since
sigma(w) ≤ w² < M. Restore the two removed prime-power divisor sums.
The length of u is at most 5 bitlength(n). Thus one exact divisor sum
takes at most 5 bitlength(n) one-bit queries of fewer than 40 bitlength(n)
bits each. All shifts, integer arithmetic and modular inversions take
polynomial bit time. The thresholds and arguments depend on n alone.

Shunia's Theorem 3.1 requests O(b) divisor sums at powers of a b-bit
integer, each of O(b³) bits, with exponents fixed before any answers.
Applying the verified decoder to those inputs gives full deterministic
factorization using O(b⁴) nonadaptive queries to B on O(b³)-bit inputs.
Conversely, a prime factorization evaluates B directly from geometric
sums. The all-input complexity equivalence uses that external theorem.
The reduction for distinct odd semiprimes is self-contained.

### The unconditional computation

For h ≥ 1, use the cutoff U = (4h+1)L. There are at most U small candidates
for primality and divisibility tests. Trial division through each candidate
is polynomial in U. The powers tested against the input have prime base
at most U and exponent at most L. Their bit length is O(L log(U+1)).
The product of the true prime-power denominators divides n. The accumulated
numerator before reducing those fractions is the divisor sum of a divisor
of n, at most n². Thus the exact rational arithmetic in the algorithm costs
polynomial time in L and h. For fixed c, taking h = ceil(L^c) gives
polynomial bit time in L. The mathematical definition of sigma is used in
proofs. Evaluating 'decideAway' calls only the small-prime computations.
Also I(n) is the sum of the reciprocals of its divisors. It is at most L
because the reciprocals in every interval [2^j,2^(j+1)) sum to at most 1.
Thus the same algorithm gives any fixed inverse-polynomial absolute
error by increasing h by a factor of L.

The direct attempt to read the middle bit from this interval fails.
The lower endpoint lo is at least 1. Once 2^floor(L/2) ≥ 4h, both
lo and lo+2^(-floor(L/2)) lie inside the certified interval. Their
scaled floors are consecutive integers, so the interval admits both
bit values. This obstruction is checked in 'successive_floors_in_interval'.

### Recovering exact divisor sums from partial precision

Fix alpha > 0. Suppose a polynomial-time algorithm, on every L-bit z,
returns a rational within 2^(-L^alpha) of I(z). To compute sigma(x),
strip the power of 2, writing x = 2^a w with w odd. Let b be the bit
length of x. Choose a fixed positive integer d with 1/d ≤ alpha, and put
E = (b+2)^d and z = 2^E w. The binary length L of z is at least E and
polynomial in b. Hence L^alpha ≥ b+2. Rounding
the approximation times w/I(2^E) recovers sigma(w) exactly, and the
known factor 2^(a+1)-1 restores sigma(x). The integer-version rounding
argument is 'decode_from_places'. Shunia's Theorem 3.1 recovers the
complete factorization from polynomially many bits of exact divisor
sums of polynomial-size powers. Conversely the prime factorization gives
the exact index by geometric sums. This establishes the equivalence
with full deterministic polynomial-time factorization, conditional on
the stated approximation algorithm in the forward direction.

### Restricting abundance queries to a band

Fix constants c > 0 and alpha > 0. Consider a promise algorithm that
answers I(z)>2 on L-bit inputs satisfying the inequality

    2^(-L^alpha) ≤ |I(z)-2| ≤ L^(-c).

Here is a deterministic polynomial-time reduction of full factorization
to such queries. Use Shunia's factor-recovery theorem and binary search
for each needed divisor sum. It suffices to implement a comparison
sigma(x) ≥ H. The following calculation also applies to arbitrary x, H.

1. Write x = 2^a w with w odd, and set h = ceil(H/(2^(a+1)-1)).
   Choose a fixed positive integer d with 1/d ≤ alpha, b = bit length(x),
   E = (b+2)^d, and y = 2^E w. By multiplicativity the original answer
   equals that of sigma(y) ≥ (2^(E+1)-1) h.
2. Apply the comparison construction in Section 2 of Shunia's preprint
   to this padded integer y. If preprocessing gives an answer, return it.
   Otherwise all powers of 2 were removed before the threshold was placed.
   Its remaining cofactor r divides w, so r ≤ x. The construction provides
   0 < g ≤ 2r, sigma(r) < 2r, and a known coprime multiplier m with I(m)
   within 1/(100r) of 4r/(2g-1). Therefore z = mr has the correct sign
   and |I(z)-2| > 1/(4r) ≥ 1/(4x), by 'threshold_margin'.
3. The final paragraph of Section 5 in the preprint proves that the
   multiplier of every nontrivial comparison has bit length of order
   (log y)^2, with both upper and lower bounds. Thus for all sufficiently
   large x, the binary length L of z satisfies L ≥ (b+2)^d. This condition
   can be checked directly, and trial division of x handles the bounded
   exceptions. It follows that 2^(-L^alpha) ≤ 2^(-b-2) < 1/(4x).
   The longer query still has polynomially many bits in b.
4. Run 'decideAway' on z with h' = L^ceil(c). If it returns a Boolean,
   return that answer. Otherwise its checked error bound gives
   |I(z)-2| ≤ 1/(2h') ≤ L^(-c). Step 2 supplied the lower margin, so
   every remaining oracle call satisfies both sides of the promise.

Conversely, complete factorization decides every promised abundance query
by evaluating sigma exactly. The reduction applies to every integer x,
irrespective of whether x itself lies near the abundance threshold. A
polynomial-time algorithm for the sign inside this band remains missing.

The upper-band condition defines a set of natural density zero. For every
fixed delta > 0, all sufficiently large members have |I(z)-2| ≤ delta.
The distribution function of z/sigma(z) is continuous at 1/2 by
Davenport's theorem. Taking delta down to zero bounds the upper density by
zero. In particular 'decideAway', with h growing as a power of the input
length, gives certified abundance decisions on a set of density one.

The finite arithmetic statements, examples, and 'decideAway_spec' are
verified in Lean. The bit-cost analysis, use of the external factor-recovery
and multiplier-size theorems, and the density deduction are mathematical
arguments in this note.

* J. M. Shunia, Deterministic integer factorization from abundance decisions,
  Theorems 1.1, 1.2 and 3.1, Lemma 2.1, and the end of Section 5.
  https://arxiv.org/abs/2611.34242
* E. Jennings, P. Pollack, and L. Thompson, Variations on a theorem of
  Davenport concerning abundant numbers. https://arxiv.org/abs/1306.0537
* E. Bach, G. Miller, and J. Shallit, Sums of Divisors, Perfect Numbers
  and Factoring (1986), gives an earlier randomized reduction from a
  single exact divisor sum. https://doi.org/10.1137/0215083
-/

end

section

/-!
# A short separating block in a doubling orbit

A bad multiplier has a nonzero relation a*x = y modulo n with 1 <= x <= W
and 0 < |y| <= H. For the factoring application the multiplier is a power
of two modulo an odd n, so a zero residue is impossible when W < n.
-/

namespace DoublingWindow

structure Relation (n a W H x y : ℤ) : Prop where
  xpos : 0 < x
  width : x ≤ W
  ypos : 0 < |y|
  height : |y| ≤ H
  congruence : n ∣ a*x-y

private theorem product_bound {W H x y : ℤ} (hx : 0 ≤ x) (hxW : x ≤ W)
    (hy : |y| ≤ H) : |y*x| ≤ W*H := by
  rw [abs_mul, abs_of_nonneg hx, mul_comm W H]
  exact mul_le_mul hy hxW hx (by linarith [abs_nonneg y])

/-- Two nearby relations at consecutive exponents have zero integer determinant. -/
theorem consecutive {n a W H x y z v : ℤ} (hn : 0 < n) (small : 3*W*H < n)
    (first : Relation n a W H x y) (second : Relation n (2*a) W H z v) :
    v*x=2*y*z := by
  obtain ⟨k,hk⟩ := first.congruence
  obtain ⟨l,hl⟩ := second.congruence
  have hy : y=a*x-n*k := by linarith
  have hv : v=2*a*z-n*l := by linarith
  have eq : v*x-2*y*z = n*(2*k*z-l*x) := by rw [hy,hv]; ring
  have hxv := abs_le.mp (product_bound first.xpos.le first.width second.height)
  have hzy := abs_le.mp (product_bound second.xpos.le second.width first.height)
  have hsmall : |v*x-2*y*z| < n := by
    apply abs_lt.mpr
    constructor <;> nlinarith
  by_contra bad
  have hne : 2*k*z-l*x ≠ 0 := by
    intro hz
    rw [hz,mul_zero] at eq
    exact bad (sub_eq_zero.mp eq)
  have hpos := abs_pos.mpr hne
  have hlower : (1:ℤ) ≤ |2*k*z-l*x| := by omega
  rw [eq,abs_mul,abs_of_pos hn] at hsmall
  nlinarith [mul_le_mul_of_nonneg_left hlower hn.le]

/-- By this many doublings there is a multiplier with no short nonzero relation. -/
theorem exists_separating_shift (n a W H : ℕ) (hn : 0 < n) (small : 3*W*H < n) :
    ∃ i ≤ (W*H).size, ¬ ∃ x y : ℤ, Relation (n:ℤ) ((a:ℤ)*2^i) W H x y := by
  classical
  let T := (W*H).size
  by_contra! every
  obtain ⟨x₀,y₀,h₀⟩ := every 0 (Nat.zero_le _)
  have chain : ∀ i ≤ T, ∃ x y : ℤ, Relation (n:ℤ) ((a:ℤ)*2^i) W H x y ∧
      y*x₀ = 2^i*y₀*x := by
    intro i
    induction i with
    | zero =>
      intro _
      exact ⟨x₀,y₀,h₀,by ring⟩
    | succ i ih =>
      intro hi
      obtain ⟨x,y,h,eq⟩ := ih (by omega)
      obtain ⟨z,v,h'⟩ := every (i+1) hi
      have mult : (a:ℤ)*2^(i+1) = 2*((a:ℤ)*2^i) := by rw [pow_succ]; ring
      have h'2 := h'
      rw [mult] at h'2
      have det := consecutive (by exact_mod_cast hn) (by exact_mod_cast small) h h'2
      refine ⟨z,v,h',?_⟩
      apply mul_right_cancel₀ h.xpos.ne'
      calc
        v*x₀*x = (v*x)*x₀ := by ring
        _ = (2*y*z)*x₀ := by rw [det]
        _ = 2*z*(y*x₀) := by ring
        _ = 2*z*(2^i*y₀*x) := by rw [eq]
        _ = 2^(i+1)*y₀*z*x := by rw [pow_succ]; ring
  obtain ⟨x,y,h,eq⟩ := chain T le_rfl
  have upper := product_bound h₀.xpos.le h₀.width h.height
  have h₁ : (1:ℤ) ≤ |y₀| := h₀.ypos
  have h₂ : (1:ℤ) ≤ x := h.xpos
  have lower : (2:ℤ)^T ≤ |2^T*y₀*x| := by
    rw [abs_mul, abs_mul, abs_of_nonneg (show 0 ≤ (2:ℤ)^T by positivity), abs_of_pos h.xpos]
    have e := mul_le_mul_of_nonneg_left h₁ (show 0 ≤ (2:ℤ)^T by positivity)
    have f := mul_le_mul_of_nonneg_left h₂ (show 0 ≤ (2:ℤ)^T*|y₀| by positivity)
    simpa using (by nlinarith : (2:ℤ)^T ≤ (2:ℤ)^T * |y₀| * x)
  have strict : (W:ℤ)*H < 2^T := by exact_mod_cast Nat.lt_size_self (W*H)
  rw [← eq] at lower
  omega

/-- Equal quantization bins imply a short ordinary difference between residues. -/
theorem equal_bin_narrow {n P r s : ℕ} (hn : 0 < n) (hP : 0 < P)
    (hr : 0 < r) (hrs : r ≤ s) (same : (P*r-1)/n=(P*s-1)/n) :
    s-r ≤ (n-1)/P := by
  have hp₁ : 0 < P*r := Nat.mul_pos hP hr
  have hp₂ : 0 < P*s := Nat.mul_pos hP (lt_of_lt_of_le hr hrs)
  have eb := Nat.mod_add_div (P*r-1) n
  have ec := Nat.mod_add_div (P*s-1) n
  rw [same] at eb
  have hb := Nat.mod_lt (P*s-1) hn
  apply (Nat.le_div_iff_mul_le hP).mpr
  rw [Nat.mul_comm, Nat.mul_sub]
  omega

def leftFloor (n r j : ℕ) := (2^j*r-1)/n

/-- Read consecutive replies in order, most significant bit first. -/
def word (n r start : ℕ) : ℕ → ℕ
  | 0 => 0
  | h+1 => 2*word n r start h + leftFloor n r (start+h+1)%2

private theorem floor_double {n r : ℕ} (hr : 0 < r) (j : ℕ) :
    leftFloor n r (j+1)/2=leftFloor n r j := by
  let v := 2^j*r
  have hv : 0 < v := Nat.mul_pos (Nat.two_pow_pos _) hr
  unfold leftFloor
  rw [Nat.div_div_eq_div_mul, mul_comm n 2, ← Nat.div_div_eq_div_mul]
  have e : 2^(j+1)*r = 2*v := by dsimp [v]; rw [pow_succ]; ring
  rw [e]
  have : (2*v-1)/2 = v-1 := by omega
  rw [this]

theorem word_eq_mod {n r : ℕ} (hr : 0 < r) (start h : ℕ) :
    word n r start h = leftFloor n r (start+h)%2^h := by
  induction h with
  | zero => simp [word, Nat.mod_one]
  | succ h ih =>
    rw [word, ih, pow_succ', Nat.mod_mul]
    simp only [Nat.add_succ]
    rw [floor_double hr]
    simp only [Nat.add_zero]
    omega

private def rep (n A m : ℕ) := (A*(1+2*m)-1)%n+1

private theorem rep_split {n A : ℕ} (hA : 0 < A) (m : ℕ) :
    A*(1+2*m) = rep n A m + n*((A*(1+2*m)-1)/n) := by
  have pos : 0 < A*(1+2*m) := by positivity
  have := Nat.mod_add_div (A*(1+2*m)-1) n
  dsimp [rep]
  omega

private theorem word_eq_cell {n : ℕ} (hn : 0 < n) (m j h : ℕ) :
    word n (1+2*m) j h = (2^h*rep n (2^j) m-1)/n := by
  rw [word_eq_mod (by omega), leftFloor]
  let A := 2^j
  let P := 2^h
  let r := rep n A m
  let q := (A*(1+2*m)-1)/n
  have hp : 0<P := Nat.two_pow_pos _
  have hr : 0<r := Nat.succ_pos _
  have hrn : r ≤ n := Nat.mod_lt _ hn
  have e : A*(1+2*m)=r+n*q := rep_split (Nat.two_pow_pos _) _
  have e' : 2^(j+h)*(1+2*m) = P*r+n*(P*q) := calc
    _ = P*(A*(1+2*m)) := by dsimp [P,A]; rw [pow_add]; ring
    _ = _ := by rw [e]; ring
  have hpr : 0<P*r := Nat.mul_pos hp hr
  have lt : (P*r-1)/n < P := (Nat.div_lt_iff_lt_mul hn).mpr
    (by have := Nat.mul_le_mul_left P hrn; omega)
  rw [e', show P*r+n*(P*q)-1=(P*r-1)+n*(P*q) by omega, Nat.add_mul_div_left _ _ hn]
  change ((P*r-1)/n+P*q)%P = (P*r-1)/n
  simpa using Nat.mod_eq_of_lt lt

private theorem different_words {n W m d j h : ℕ} (hn : 0 < n) (hd : 0<d)
    (hdW : d ≤ W) (hW : W < n) (oddN : Odd n)
    (sep : ¬ ∃ x y : ℤ,
      Relation n (2*(2:ℤ)^j) W (((n-1)/2^h : ℕ) : ℤ) x y) :
    word n (1+2*m) j h ≠ word n (1+2*(m+d)) j h := by
  intro eq
  rw [word_eq_cell hn, word_eq_cell hn] at eq
  let A := 2^j
  let r := rep n A m
  let s := rep n A (m+d)
  let q := (A*(1+2*m)-1)/n
  let t := (A*(1+2*(m+d))-1)/n
  have e₁ : A*(1+2*m)=r+n*q := rep_split (Nat.two_pow_pos _) _
  have e₂ : A*(1+2*(m+d))=s+n*t := rep_split (Nat.two_pow_pos _) _
  have z₁ : (A:ℤ)*(1+2*m)=r+(n:ℤ)*q := by exact_mod_cast e₁
  have z₂ : (A:ℤ)*(1+2*((m:ℤ)+d))=s+(n:ℤ)*t := by exact_mod_cast e₂
  have dv : (n:ℤ) ∣ 2*(A:ℤ)*(d:ℤ)-((s:ℤ)-r) := by
    refine ⟨(t:ℤ)-q,?_⟩
    nlinarith only [z₁,z₂]
  have ne : (s:ℤ)-r ≠ 0 := by
    intro hz
    rw [hz,sub_zero] at dv
    have dvd : n ∣ 2*A*d := by exact_mod_cast dv
    have hc := Nat.coprime_two_left.mpr oddN
    have hnd := (hc.mul_left (hc.pow_left j)).symm.dvd_of_dvd_mul_left dvd
    have := Nat.le_of_dvd hd hnd
    omega
  have hr : 0<r := Nat.succ_pos _
  have hs : 0<s := Nat.succ_pos _
  have bound : |(s:ℤ)-r| ≤ (((n-1)/2^h : ℕ) : ℤ) := by
    rw [abs_le]
    rcases le_total r s with h₁ | h₁
    · have := equal_bin_narrow hn (Nat.two_pow_pos _) hr h₁ eq
      omega
    · have := equal_bin_narrow hn (Nat.two_pow_pos _) hs h₁ eq.symm
      omega
  exact sep ⟨d,(s:ℤ)-r,⟨by exact_mod_cast hd,by exact_mod_cast hdW,abs_pos.mpr ne,bound,
    by exact_mod_cast dv⟩⟩

/-- At some computably bounded starting index the observed word is injective on
every interval of midpoints of width W, provided the number of cells exceeds 3W. -/
theorem short_word_separates {n W h : ℕ} (hn : 0<n) (oddN : Odd n)
    (hW : W<n) (cells : 3*W < 2^h) (base : ℕ) :
    ∃ i ≤ (W*((n-1)/2^h)).size, ∀ m d, 0<d → d≤W →
      word n (1+2*m) (base+i) h ≠ word n (1+2*(m+d)) (base+i) h := by
  let H := (n-1)/2^h
  have small : 3*W*H<n := calc
    _ ≤ 2^h*H := Nat.mul_le_mul_right H cells.le
    _ ≤ n-1 := Nat.mul_div_le _ _
    _ < n := by omega
  obtain ⟨i,hi,good⟩ := exists_separating_shift n (2*2^base) W H hn small
  refine ⟨i, hi, ?_⟩
  intro m d hd hdW
  apply different_words hn hd hdW hW oddN
  simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,pow_add,mul_assoc,H] using good

end DoublingWindow

end

section

/-!
# How much of the divisor-sum reply is determined by powers of two?

A midpoint m is locally possible at two if m²-N has a square root modulo
every power of two. We construct at least floor(sqrt(N)/2048) different
such integer midpoints in the real range for factors of ratio at most two.
We also verify the injective binary encoding used to measure ambiguous
answers and the floor-sum identity used to certify individual bits.
-/

namespace LocalBitCertificates

def LocallyPossible (n m : ℕ) : Prop :=
  ∀ k : ℕ, ∃ d : ZMod (2^k), (m : ZMod (2^k))^2 = (n : ZMod (2^k)) + d^2

def BalancedRange (n m : ℕ) : Prop := n ≤ m^2 ∧ 8*m^2 ≤ 9*n

private theorem odd_unit (k : ℕ) (x : ZMod (2^k)) : IsUnit (1+2*x) := by
  let s := 1+2*x.val
  have ho : Odd s := ⟨x.val, by dsimp [s]; omega⟩
  have hc : s.Coprime (2^k) := (Nat.coprime_two_right.mpr ho).pow_right _
  simpa [s] using (ZMod.isUnit_iff_coprime s _).mpr hc

private theorem quadratic_surj (k : ℕ) :
    Function.Surjective (fun x : ZMod (2^k) => x+2*x^2) := by
  apply Finite.injective_iff_surjective.mp
  intro x y h
  apply sub_eq_zero.mp
  apply (odd_unit k (x+y)).mul_left_eq_zero.mp
  calc
    (x-y)*(1+2*(x+y)) = (x+2*x^2)-(y+2*y^2) := by ring
    _ = 0 := sub_eq_zero.mpr h

/-- An explicit family of integer gaps which are squares at every dyadic precision. -/
theorem local_of_shape {n m j w : ℕ} (shape : m^2 = n+4^j*(8*w+1)) :
    LocallyPossible n m := by
  intro k
  obtain ⟨t, ht⟩ := quadratic_surj k (w : ZMod (2^k))
  refine ⟨2^j*(1+4*t), ?_⟩
  have he : (m : ZMod (2^k))^2 = n+4^j*(8*(w : ZMod (2^k))+1) := by
    exact_mod_cast congrArg (fun a : ℕ => (a : ZMod (2^k))) shape
  rw [he, ← ht, mul_pow, ← pow_mul, Nat.mul_comm j 2, pow_mul]
  norm_num
  ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem residue_table : ∀ n : Fin 128, n.val%2=1 →
    ∃ r : Fin 64, ∃ j : Fin 3,
      r.val^2%(8*4^j.val) = (n.val+4^j.val)%(8*4^j.val) := by decide

private theorem square_reduces (m : ℕ) : m^2 ≡ (m%64)^2 [MOD 128] := by
  let r := m%64
  let t := m/64
  have e : m = r+64*t := (Nat.mod_add_div _ _).symm
  have eq : m^2 = r^2 + 128*(r*t+32*t^2) := by
    conv_lhs => rw [e]
    ring
  change m^2 % 128 = r^2 % 128
  rw [eq]
  simp

/-- One entire class modulo 64 survives every power of two, for each odd N. -/
theorem surviving_class {n : ℕ} (ho : n%2=1) :
    ∃ r < 64, ∀ m, m%64=r → n ≤ m^2 → LocallyPossible n m := by
  let a : Fin 128 := ⟨n%128, Nat.mod_lt _ (by decide)⟩
  have hodd : a.val%2=1 := by dsimp [a]; omega
  obtain ⟨r,j,ht⟩ := residue_table a hodd
  refine ⟨r.val,r.isLt,?_⟩
  intro m hr hm
  let f := 4^j.val
  let Q := 8*f
  have divides : Q ∣ 128 := by
    have : ∀ i : Fin 3, 8*4^i.val ∣ 128 := by decide
    exact this j
  have h₁ : m^2 ≡ r.val^2 [MOD Q] := by
    have h := (square_reduces m).of_dvd divides
    rwa [hr] at h
  have h₂ : a.val+f ≡ n+f [MOD Q] :=
    ((Nat.mod_modEq n 128).of_dvd divides).add_right f
  have eq : m^2 ≡ n+f [MOD Q] := (h₁.trans ht).trans h₂
  let d := m^2-n
  have hd : n+d=m^2 := by dsimp [d]; omega
  have hrem : d ≡ f [MOD Q] := Nat.ModEq.add_left_cancel' n (hd ▸ eq)
  have hf : 0 < f := by dsimp [f]; positivity
  have hfQ : f < Q := by dsimp [Q]; omega
  change d%Q=f%Q at hrem
  rw [Nat.mod_eq_of_lt hfQ] at hrem
  have hdiv := Nat.mod_add_div d Q
  rw [hrem] at hdiv
  apply local_of_shape (j:=j.val) (w:=d/Q)
  calc
    m^2 = n+d := hd.symm
    _ = n+(f+Q*(d/Q)) := congrArg (n+·) hdiv.symm
    _ = _ := by dsimp [Q, f]; ring

/-- Every index gives a different surviving midpoint in the balanced real interval. -/
theorem surviving_grid {n : ℕ} (ho : n%2=1) :
    ∃ g : Fin (n.sqrt/2048) → ℕ, Function.Injective g ∧
      ∀ i, BalancedRange n (g i) ∧ LocallyPossible n (g i) := by
  obtain ⟨r,hr,hs⟩ := surviving_class ho
  let t := n.sqrt
  let offset := (r+64-(t+1)%64)%64
  let g (i : Fin (n.sqrt/2048)) := t+1+offset+64*i.val
  refine ⟨g, ?_, ?_⟩
  · intro i j h
    apply Fin.ext
    dsimp [g] at h
    omega
  intro i
  have hi : i.val < t/2048 := i.isLt
  have hmod : (g i)%64 = r := by dsimp [g, offset]; omega
  have hlow : t+1 ≤ g i := by dsimp [g]; omega
  have htop : 32*g i ≤ 33*t := by dsimp [g, offset]; omega
  have hnlo : n ≤ (g i)^2 :=
    (Nat.lt_succ_sqrt' n).le.trans (Nat.pow_le_pow_left hlow _)
  have hb := Nat.pow_le_pow_left htop 2
  have ht : t^2 ≤ n := Nat.sqrt_le' n
  exact ⟨⟨hnlo, by nlinarith⟩, hs _ hmod hnlo⟩

/-- The parity of a nonnegative floor is a difference of floors. -/
theorem floor_parity (x n : ℕ) : (x/n)%2 + 2*(x/(2*n)) = x/n := by
  rw [Nat.mul_comm 2 n, ← Nat.div_div_eq_div_mul]
  exact Nat.mod_add_div _ _

/-- The exact number of ones over a progression, written without subtraction. -/
theorem progression_ones (count n a d : ℕ) :
    (∑ i ∈ Finset.range count, ((a*i+d)/n)%2) +
    2*(∑ i ∈ Finset.range count, (a*i+d)/(2*n)) =
    ∑ i ∈ Finset.range count, (a*i+d)/n := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => floor_parity _ _)

end LocalBitCertificates

end

section

namespace SemiprimeBridge
open AbundancePrecision ArithmeticFunction DoublingWindow

/-- The selected consecutive oracle answers as an unsigned binary word. -/
def observed (n start : ℕ) : ℕ → ℕ
  | 0 => 0
  | h+1 => 2*observed n start h + (middleBit (query n (start+h))).val

private theorem shift_by_n {n r : ℕ} (hn : 0<n) (hr : 0<r) (j : ℕ) :
    DoublingWindow.leftFloor n (n+r) (j+1)%2=DoublingWindow.leftFloor n r (j+1)%2 := by
  have pos : 0 < 2^(j+1)*r := Nat.mul_pos (Nat.two_pow_pos _) hr
  have e : 2^(j+1)*(n+r)-1=(2^(j+1)*r-1)+n*2^(j+1) := by
    rw [Nat.mul_add, Nat.mul_comm _ n]
    omega
  unfold DoublingWindow.leftFloor
  rw [e,Nat.add_mul_div_left _ _ hn, pow_succ]
  omega

theorem observed_eq_word {n m : ℕ} (hn : 0<n) (ho : Odd n)
    (hs : sigma 1 n=n+(1+2*m)) (start h : ℕ) :
    observed n start h = word n (1+2*m) (3*n.size+start) h := by
  induction h with
  | zero => rfl
  | succ h ih =>
    have qr := query_bit hn ho (start+h)
    change (middleBit (query n (start+h))).val =
      DoublingWindow.leftFloor n (sigma 1 n) (3*n.size+(start+h)+1)%2 at qr
    rw [hs,shift_by_n hn (by omega)] at qr
    rw [observed,word,ih,qr]
    rw [Nat.add_assoc (3*n.size) start h]

theorem semiprime_sigma {p q m : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hlt : p<q) (mid : 2*m=p+q) : sigma 1 (p*q)=p*q+(1+2*m) := by
  have prime_value {s : ℕ} (hs : s.Prime) : sigma 1 s=1+s := by
    simpa [Finset.sum_range_succ] using (sigma_one_apply_prime_pow (i:=1) hs)
  rw [isMultiplicative_sigma.map_mul_of_coprime ((Nat.coprime_primes hp hq).mpr hlt.ne),
    prime_value hp,prime_value hq,mid]
  ring

theorem midpoint_range {p q m : ℕ} (hle : p≤q) (hbal : q≤2*p)
    (mid : 2*m=p+q) : LocalBitCertificates.BalancedRange (p*q) m := by
  have h₁ : (p:ℤ)≤q := by exact_mod_cast hle
  have h₂ : (q:ℤ)≤2*p := by exact_mod_cast hbal
  have he : 2*(m:ℤ)=p+q := by exact_mod_cast mid
  have sq := congrArg (fun z:ℤ => z^2) he
  have ordered : 0 ≤ 2*(q:ℤ)-p := by linarith
  constructor
  · exact_mod_cast (show (p:ℤ)*q ≤ (m:ℤ)^2 by nlinarith [sq_nonneg ((q:ℤ)-p)])
  · exact_mod_cast (show 8*(m:ℤ)^2 ≤ 9*((p:ℤ)*q) by
      nlinarith [mul_nonneg ordered (sub_nonneg.mpr h₂)])

/-- The number of requested bits fits in half the binary input length, rounded up. -/
theorem half_bit_count {n lo W : ℕ} (hn : 0<n) (lower : n≤lo^2)
    (upper : 8*(lo+W)^2≤9*n) : (3*W).size ≤ (n.size+1)/2 := by
  apply Nat.size_le.mpr
  let t := (n.size+1)/2
  have hpow : n < (2^t)^2 := calc
    _ < 2^n.size := Nat.lt_size_self _
    _ ≤ 2^(t*2) := Nat.pow_le_pow_right (by decide) (by dsimp [t]; omega)
    _ = _ := pow_mul _ _ _
  have sm : 9*W^2 ≤ n := by
    by_cases h : lo≤4*W
    · have e := Nat.mul_le_mul_right lo h
      nlinarith
    · have e := Nat.pow_le_pow_left (show 5*W≤lo+W by omega) 2
      nlinarith
  change 3*W < 2^t
  by_contra! bad
  have e := Nat.pow_le_pow_left bad 2
  nlinarith

def splitAt (n m : ℕ) : ℕ × ℕ :=
  let d := (m^2-n).sqrt
  (m-d,m+d)

/-- Once the midpoint is located, an integer square root recovers both factors. -/
theorem splitAt_true {p q m : ℕ} (hle : p≤q) (mid : 2*m=p+q) :
    splitAt (p*q) m=(p,q) := by
  let d := m-p
  have e : p+d=m := by dsimp [d]; omega
  have f : m+d=q := by omega
  have sq : m^2=p*q+d^2 := by rw [← f,← e]; ring
  dsimp [splitAt]
  rw [sq,Nat.add_sub_cancel_left,Nat.sqrt_eq']
  exact Prod.ext (by omega) f

/-- One block of actual middle bits of the divisor-sum ratio uniquely selects
the true midpoint from an integer interval of width W. -/
theorem actual_block_unique {p q m lo W h : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hop : Odd p) (hoq : Odd q) (hlt : p<q)
    (mid : 2*m=p+q) (within : lo≤m ∧ m≤lo+W) (width : W<p*q) (cells : 3*W<2^h) :
    ∃ i ≤ (W*((p*q-1)/2^h)).size, ∀ z, lo≤z → z≤lo+W →
      (word (p*q) (1+2*z) (3*(p*q).size+i) h = observed (p*q) i h ↔ z=m) := by
  let n := p*q
  have hn : 0<n := Nat.mul_pos hp.pos hq.pos
  have ho : Odd n := hop.mul hoq
  have hs : sigma 1 n=n+(1+2*m) := semiprime_sigma hp hq hlt mid
  obtain ⟨i,hi,sep⟩ := short_word_separates hn ho width cells (3*n.size)
  refine ⟨i,hi,?_⟩
  intro z lz uz
  rw [observed_eq_word hn ho hs]
  constructor
  · intro eq
    rcases lt_trichotomy z m with hlt' | he | hgt
    · have e := sep z (m-z) (by omega) (by omega)
      rw [show z+(m-z)=m by omega] at e
      exact (e eq).elim
    · exact he
    · have e := sep m (z-m) (by omega) (by omega)
      rw [show m+(z-m)=z by omega] at e
      exact (e eq.symm).elim
  · rintro rfl
    rfl

/-- Counting lower bound for schemes that cover every locally possible midpoint.
The transcript determines a list of at most T possible candidates. -/
theorem list_capacity {n h T : ℕ}
    (code : Fin (n.sqrt/2048) → Fin (2^h))
    (capacity : ∀ z, (Finset.univ.filter (fun x => code x=z)).card ≤ T) :
    n.sqrt/2048 ≤ 2^h*T := by
  classical
  have hc := Finset.card_le_mul_card_image_of_maps_to
    (s:=Finset.univ) (t:=Finset.univ) (f:=code)
    (fun _ _ => Finset.mem_univ _) T (fun z _ => capacity z)
  simpa [Nat.mul_comm] using hc

end SemiprimeBridge

end

section

/-! Primality, the splitting gcd, and the 48-bit and 88-bit divisor-sum words. -/
namespace OrderWitness

set_option exponentiation.threshold 2048
set_option maxRecDepth 8192

private theorem mem_of_prime_dvd {r : ℕ} (hr : r.Prime) {fs : List ℕ}
    (ps : ∀ s ∈ fs, Nat.Prime s) (hd : r ∣ fs.prod) : r ∈ fs := by
  induction fs with
  | nil => exact False.elim (hr.not_dvd_one hd)
  | cons a fs ih =>
    rcases hr.dvd_mul.mp (show r ∣ a * fs.prod from hd) with hl | ht
    · exact List.mem_cons.mpr (Or.inl ((Nat.prime_dvd_prime_iff_eq hr (ps a (by simp))).mp hl))
    · exact List.mem_cons_of_mem a (ih (fun s hs => ps s (List.mem_cons_of_mem a hs)) ht)

private theorem pratt (n a : ℕ) (fs : List ℕ) (fac : fs.prod = n - 1)
    (ps : ∀ s ∈ fs, Nat.Prime s) (full : (a : ZMod n) ^ (n-1) = 1)
    (proper : ∀ s ∈ fs, (a : ZMod n) ^ ((n-1)/s) ≠ 1) : n.Prime := by
  apply lucas_primality n (a : ZMod n) full
  intro r hr hd
  rw [← fac] at hd
  exact proper r (mem_of_prime_dvd hr ps hd)

theorem p88272167 : Nat.Prime 88272167 := by
  apply pratt 88272167 5 [2, 1307, 33769]
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · norm_num1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> norm_num1 <;> reduce_mod_char <;> decide

theorem p17477889067 : Nat.Prime 17477889067 := by
  apply pratt 17477889067 2 [2, 3, 3, 11, 88272167]
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact p88272167
  · norm_num1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> norm_num1 <;> reduce_mod_char <;> decide

theorem p13326496357100595419 : Nat.Prime 13326496357100595419 := by
  apply pratt 13326496357100595419 2 [2, 29, 109, 120607, 17477889067]
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact p17477889067
  · norm_num1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> norm_num1 <;> reduce_mod_char <;> decide

theorem p2554897 : Nat.Prime 2554897 := by
  apply pratt 2554897 5 [2, 2, 2, 2, 3, 17, 31, 101]
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · norm_num1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num1 <;> reduce_mod_char <;> decide

theorem p1340300341 : Nat.Prime 1340300341 := by
  apply pratt 1340300341 2 [2, 2, 3, 3, 5, 1709, 4357]
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · norm_num1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num1 <;> reduce_mod_char <;> decide

theorem p14978016447079141999 : Nat.Prime 14978016447079141999 := by
  apply pratt 14978016447079141999 3 [2, 3, 3, 3, 3, 3, 3, 3, 2554897, 1340300341]
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact p2554897
    · exact p1340300341
  · norm_num1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num1 <;> reduce_mod_char <;> decide

theorem p1249691 : Nat.Prime 1249691 := by
  apply pratt 1249691 2 [2, 5, 13, 9613]
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · norm_num1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> norm_num1 <;> reduce_mod_char <;> decide

theorem p8324893 : Nat.Prime 8324893 := by
  apply pratt 8324893 5 [2, 2, 3, 3, 71, 3257]
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · norm_num1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num1 <;> reduce_mod_char <;> decide

theorem p130917267319 : Nat.Prime 130917267319 := by
  apply pratt 130917267319 11 [2, 3, 2621, 8324893]
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact p8324893
  · norm_num1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> norm_num1 <;> reduce_mod_char <;> decide

theorem p629973890339029 : Nat.Prime 629973890339029 := by
  apply pratt 629973890339029 2 [2, 2, 3, 401, 130917267319]
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact p130917267319
  · norm_num1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> norm_num1 <;> reduce_mod_char <;> decide

theorem p302312717180801852174977 : Nat.Prime 302312717180801852174977 := by
  apply pratt 302312717180801852174977 5 [2, 2, 2, 2, 2, 2, 2, 3, 1249691, 629973890339029]
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact p1249691
    · exact p629973890339029
  · norm_num1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num1 <;> reduce_mod_char <;> decide

theorem p56790746890224677187052303600871 : Nat.Prime 56790746890224677187052303600871 := by
  apply pratt 56790746890224677187052303600871 7 [2, 5, 7, 1129, 2377, 302312717180801852174977]
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact p302312717180801852174977
  · norm_num1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num1 <;> reduce_mod_char <;> decide

theorem p7555843 : Nat.Prime 7555843 := by
  apply pratt 7555843 2 [2, 3, 3, 3, 3, 3, 7, 2221]
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · norm_num1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num1 <;> reduce_mod_char <;> decide

theorem p276392736941 : Nat.Prime 276392736941 := by
  apply pratt 276392736941 2 [2, 2, 5, 31, 59, 7555843]
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact p7555843
  · norm_num1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num1 <;> reduce_mod_char <;> decide

theorem p233921 : Nat.Prime 233921 := by
  apply pratt 233921 3 [2, 2, 2, 2, 2, 2, 5, 17, 43]
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · norm_num1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num1 <;> reduce_mod_char <;> decide

theorem p61443561229 : Nat.Prime 61443561229 := by
  apply pratt 61443561229 13 [2, 2, 3, 7, 53, 59, 233921]
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact p233921
  · norm_num1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num1 <;> reduce_mod_char <;> decide

theorem p20890810817861 : Nat.Prime 20890810817861 := by
  apply pratt 20890810817861 3 [2, 2, 5, 17, 61443561229]
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact p61443561229
  · norm_num1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> norm_num1 <;> reduce_mod_char <;> decide

theorem p429509850430270667801235909587 : Nat.Prime 429509850430270667801235909587 := by
  apply pratt 429509850430270667801235909587 2 [2, 13, 2861, 276392736941, 20890810817861]
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact p276392736941
    · exact p20890810817861
  · norm_num1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> norm_num1 <;> reduce_mod_char <;> decide

theorem p73016674573146013526210104629791 : Nat.Prime 73016674573146013526210104629791 := by
  apply pratt 73016674573146013526210104629791 13 [2, 5, 17, 429509850430270667801235909587]
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact p429509850430270667801235909587
  · norm_num1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> norm_num1 <;> reduce_mod_char <;> decide

theorem p89634023 : Nat.Prime 89634023 := by
  apply pratt 89634023 5 [2, 463, 96797]
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · norm_num1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> norm_num1 <;> reduce_mod_char <;> decide

theorem p3897161 : Nat.Prime 3897161 := by
  apply pratt 3897161 3 [2, 2, 2, 5, 97429]
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · norm_num1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> norm_num1 <;> reduce_mod_char <;> decide

theorem p7794323 : Nat.Prime 7794323 := by
  apply pratt 7794323 2 [2, 3897161]
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · norm_num
    · exact p3897161
  · norm_num1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> norm_num1 <;> reduce_mod_char <;> decide

theorem p155886461 : Nat.Prime 155886461 := by
  apply pratt 155886461 3 [2, 2, 5, 7794323]
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact p7794323
  · norm_num1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> norm_num1 <;> reduce_mod_char <;> decide

theorem p12035993653811 : Nat.Prime 12035993653811 := by
  apply pratt 12035993653811 2 [2, 5, 7, 1103, 155886461]
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact p155886461
  · norm_num1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> norm_num1 <;> reduce_mod_char <;> decide

theorem p20942628957631141 : Nat.Prime 20942628957631141 := by
  apply pratt 20942628957631141 7 [2, 2, 3, 5, 29, 12035993653811]
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact p12035993653811
  · norm_num1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num1 <;> reduce_mod_char <;> decide

theorem p42678434690689936321894022265043 : Nat.Prime 42678434690689936321894022265043 := by
  apply pratt 42678434690689936321894022265043 3 [2, 3, 3, 17, 191, 389, 89634023, 20942628957631141]
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact p89634023
    · exact p20942628957631141
  · norm_num1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num1 <;> reduce_mod_char <;> decide

theorem p810547 : Nat.Prime 810547 := by
  apply pratt 810547 5 [2, 3, 11, 12281]
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · norm_num1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> norm_num1 <;> reduce_mod_char <;> decide

theorem p91637201633 : Nat.Prime 91637201633 := by
  apply pratt 91637201633 3 [2, 2, 2, 2, 2, 3533, 810547]
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact p810547
  · norm_num1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num1 <;> reduce_mod_char <;> decide

theorem p395038336556321 : Nat.Prime 395038336556321 := by
  apply pratt 395038336556321 3 [2, 2, 2, 2, 2, 5, 47, 839, 4273, 14653]
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · norm_num1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num1 <;> reduce_mod_char <;> decide

theorem p4740460038675853 : Nat.Prime 4740460038675853 := by
  apply pratt 4740460038675853 2 [2, 2, 3, 395038336556321]
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact p395038336556321
  · norm_num1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> norm_num1 <;> reduce_mod_char <;> decide

theorem p54523594430756986474678777350787 : Nat.Prime 54523594430756986474678777350787 := by
  apply pratt 54523594430756986474678777350787 3 [2, 3, 3, 19, 367, 91637201633, 4740460038675853]
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact p91637201633
    · exact p4740460038675853
  · norm_num1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num1 <;> reduce_mod_char <;> decide

abbrev N : ℕ := 199604481618592988980642015258549902581
abbrev P : ℕ := 13326496357100595419
abbrev Q : ℕ := 14978016447079141999
abbrev M : ℕ := 14152256402089868709

theorem gcd_witness : Nat.gcd 175950992768636282823936990212460475462 N = P := by decide

theorem factorization : N = P*Q ∧ P.Prime ∧ Q.Prime :=
  ⟨by decide, p13326496357100595419, p14978016447079141999⟩

private theorem size_from_bounds {n k : ℕ} (lo : 2^k ≤ n) (hi : n < 2^(k+1)) :
    n.size = k+1 :=
  le_antisymm (Nat.size_le.mpr hi) (Nat.lt_size.mpr lo)

private theorem transcript_from {n p q m start width v bits : ℕ}
    (prodEq : n = p*q) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p < q) (mid : 2*m = p+q) (positive : 0<n) (odd : Odd n)
    (sizeEq : n.size = bits)
    (value : DoublingWindow.leftFloor n (1+2*m) (3*bits+start+width) % 2^width = v) :
    SemiprimeBridge.observed n start width = v := by
  subst bits
  subst n
  have hs := SemiprimeBridge.semiprime_sigma (p:=p) (q:=q) (m:=m) hp hq hpq mid
  have hr : 0 < 1+2*m := Nat.add_pos_left (by decide : 0 < 1) _
  exact (SemiprimeBridge.observed_eq_word (n:=p*q) (m:=m) positive odd hs start width).trans
    ((DoublingWindow.word_eq_mod (n:=p*q) (r:=1+2*m) hr (3*(p*q).size+start) width).trans value)

theorem actual_transcript : SemiprimeBridge.observed N 0 48 = 58857791485019 :=
  transcript_from (n:=N) (p:=P) (q:=Q) (m:=M) (start:=0) (width:=48)
    (v:=58857791485019) (bits:=128) factorization.1 factorization.2.1 factorization.2.2
    (by decide) (by decide) (by decide) ⟨N/2, by decide⟩
    (size_from_bounds (n:=N) (k:=127) (by decide) (by decide)) (by decide)

theorem second_factorization :
    4146671484449439226230522340054012195065466778887760737680147961 =
        56790746890224677187052303600871 * 73016674573146013526210104629791 ∧
    Nat.Prime 56790746890224677187052303600871 ∧ Nat.Prime 73016674573146013526210104629791 :=
  ⟨by decide, p56790746890224677187052303600871, p73016674573146013526210104629791⟩

theorem second_transcript : SemiprimeBridge.observed 4146671484449439226230522340054012195065466778887760737680147961 2 88 = 180561757351988294691417104 :=
  transcript_from (n:=4146671484449439226230522340054012195065466778887760737680147961)
    (p:=56790746890224677187052303600871) (q:=73016674573146013526210104629791) (m:=64903710731685345356631204115331)
    (start:=2) (width:=88) (v:=180561757351988294691417104) (bits:=212)
    second_factorization.1 second_factorization.2.1 second_factorization.2.2
    (by decide) (by decide) (by decide) ⟨4146671484449439226230522340054012195065466778887760737680147961/2, by decide⟩
    (size_from_bounds (n:=4146671484449439226230522340054012195065466778887760737680147961) (k:=211)
      (by decide) (by decide)) (by decide)

theorem multiplier_identity :
    1022233444024044189366941464816376 ^ 2 =
      4 * 63 * 4146671484449439226230522340054012195065466778887760737680147961 + 698 ^ 2 := by decide

theorem third_factorization : 2326981664014727582718789409779272096176399345327619480698638841 = 42678434690689936321894022265043 * 54523594430756986474678777350787 ∧
    Nat.Prime 42678434690689936321894022265043 ∧ Nat.Prime 54523594430756986474678777350787 :=
  ⟨by decide, p42678434690689936321894022265043, p54523594430756986474678777350787⟩

#print axioms second_transcript
#print axioms third_factorization
#print axioms actual_transcript
#print axioms gcd_witness
#print axioms second_factorization
end OrderWitness

end
