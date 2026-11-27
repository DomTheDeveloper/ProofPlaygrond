import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.PSeries
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Transcendental.Liouville.Basic
import Mathlib.Topology.Instances.CantorSet
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Binary-normal Liouville numbers in the middle-third Cantor set

Lean 4.33.1, mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
In a mathlib project at this revision, run `lake env lean CantorNormalLiouville.lean`.

`uncountable_binaryNormal_cantor_liouville` uses mathlib's `cantorSet` and `Liouville`.
`BinaryNormal` measures the limiting frequency of every half-open dyadic interval
along the doubling orbit, so overlapping occurrences are counted.

The free ternary digit at position `2 * slot n` records bit n. The next digit is 2.
The slot jumps when n reaches a marker B to give arbitrarily good rational approximations.
The proof averages the Fourier energy over the first j independent bits by finite
translations of Haar measure on the space of bit sequences. All remaining bits can
be fixed in the finite estimate. The sample times r · 3^k give the limit at every N.
-/

namespace CantorNormal
noncomputable section

/-! ## Ternary truncation and rational approximation -/

section

open Finset Real

/-- The integer numerator of the first k ternary digits. Digit 0 is the first digit after the point. -/
def numerator (d : ℕ → Fin 3) : ℕ → ℕ
  | 0 => 0
  | k + 1 => 3 * numerator d k + (d k).val

theorem prefix_sum (d : ℕ → Fin 3) (k : ℕ) :
    ∑ i ∈ range k, ofDigitsTerm d i = (numerator d k : ℝ) / 3 ^ k := by
  induction k with
  | zero => simp [numerator]
  | succ k ih =>
    rw [sum_range_succ, ih]
    simp only [numerator, ofDigitsTerm, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, pow_succ]
    field_simp

private def trunc (d : ℕ → Fin 3) (k i : ℕ) : Fin 3 :=
  if i < k then d i else 0

private theorem trunc_value (d : ℕ → Fin 3) (k : ℕ) :
    ofDigits (trunc d k) = (numerator d k : ℝ) / 3 ^ k := by
  rw [ofDigits_eq_sum_add_ofDigits _ k, ← prefix_sum]
  have hh : (fun i ↦ trunc d k (i+k)) = fun _ ↦ (0 : Fin 3) := by
    funext i
    simp [trunc]
  rw [hh]
  simp only [ofDigits, ofDigitsTerm, Fin.val_zero, Nat.cast_zero, zero_mul, tsum_zero,
    mul_zero, add_zero]
  exact sum_congr rfl fun i hi ↦ by simp [trunc, mem_range.mp hi]

/-- A zero gap [a,b) gives a certified error bound for the rational ternary truncation. -/
theorem gap_error (d : ℕ → Fin 3) (a b : ℕ)
    (hz : ∀ i, a ≤ i → i < b → d i = 0) :
    |ofDigits d - (numerator d a : ℝ) / 3 ^ a| ≤ ((3 : ℝ)^b)⁻¹ := by
  rw [← trunc_value]
  apply abs_ofDigits_sub_ofDigits_le
  intro i hi
  by_cases ha : i < a
  · simp [trunc, ha]
  · simp [trunc, ha, hz i (by omega) hi]

/-- Applies to any gap schedule, including the blocks of the note. -/
theorem cantor_liouville_of_gaps (d : ℕ → Fin 3)
    (h02 : ∀ i, d i ≠ 1) (hnz : ∀ a, ∃ i ≥ a, d i ≠ 0)
    (hg : ∀ L : ℕ, ∃ a b : ℕ, 0 < a ∧ a * L < b ∧
      ∀ i, a ≤ i → i < b → d i = 0) :
    ofDigits d ∈ cantorSet ∧ Liouville (ofDigits d) := by
  refine ⟨ofDigits_zero_two_sequence_mem_cantorSet h02, ?_⟩
  intro L
  obtain ⟨a,b,ha,hab,hz⟩ := hg L
  refine ⟨(numerator d a : ℤ), (3 : ℤ)^a, one_lt_pow₀ (by decide) ha.ne', ?_, ?_⟩
  · push_cast
    rw [← trunc_value]
    intro heq
    have ht (i : ℕ) : trunc d a i ≠ 1 := by
      by_cases hi : i < a <;> simp [trunc, hi, h02]
    have h := ofDigits_zero_two_sequence_unique h02 ht heq
    obtain ⟨i,hi,hdi⟩ := hnz a
    apply hdi
    simpa [trunc, Nat.not_lt.mpr hi] using congrFun h i
  · push_cast
    apply (gap_error d a b hz).trans_lt
    rw [one_div, ← pow_mul]
    exact inv_lt_inv₀ (by positivity) (by positivity) |>.2
      (pow_lt_pow_right₀ (by norm_num) hab)

end

/-! ## Frequency collisions modulo powers of three -/

section

open Finset
private theorem two_order_mod_three : orderOf (2 : ZMod 3) = 2 := by
  apply orderOf_eq_prime
  · decide
  · decide

/-- A collision of two frequencies forces their indices into a single residue class. -/
theorem collision_modEq (h t n m : ℕ) (hh : h ≠ 0)
    (hc : h * 2 ^ n ≡ h * 2 ^ m [MOD 3 ^ (padicValNat 3 h + t + 1)]) :
    n ≡ m [MOD 2 * 3 ^ t] := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  wlog hn : n ≤ m generalizing n m
  · exact (this m n hc.symm (by omega)).symm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  rcases eq_or_ne d 0 with rfl | hd
  · rfl
  have hp : 1 < (2 : ℕ) ^ d := one_lt_pow₀ (by decide) hd
  have hs : 2 ^ d - 1 ≠ 0 := by omega
  have hu : 3 ^ (padicValNat 3 h + t + 1) ∣ h * 2 ^ n * (2 ^ d - 1) := by
    simpa [pow_add, Nat.mul_sub, ← Nat.mul_assoc] using hc.dvd'
  have hv := (Nat.pow_dvd_iff_le_padicValNat (by decide : 3 ≠ 1)
    (mul_ne_zero (mul_ne_zero hh (pow_ne_zero n (by decide))) hs)).mp hu
  have h2 : padicValNat 3 (2 ^ n) = 0 := by
    rw [padicValNat.pow]
    simp [padicValNat.eq_zero_of_not_dvd (by decide : ¬3 ∣ 2)]
  rw [padicValNat.mul (mul_ne_zero hh (pow_ne_zero n (by decide))) hs,
    padicValNat.mul hh (pow_ne_zero n (by decide)), h2, add_zero] at hv
  have h3 : 3 ∣ 2 ^ d - 1 := by
    have := (Nat.pow_dvd_iff_le_padicValNat (by decide : 3 ≠ 1) hs (k := 1)).mpr (by omega)
    simpa using this
  have hpow : (2 : ZMod 3) ^ d = 1 := by
    have hn' := (Nat.modEq_iff_dvd' hp.le).2 h3
    have he := (ZMod.natCast_eq_natCast_iff 1 (2^d) 3).2 hn'
    simpa using he.symm
  have heven := orderOf_dvd_of_pow_eq_one hpow
  rw [two_order_mod_three] at heven
  obtain ⟨u, rfl⟩ := heven
  have hu0 : u ≠ 0 := by omega
  have hval := padicValNat.pow_sub_pow (p := 3) (x := 4) (y := 1)
    (by decide) (by decide) (by decide) (by decide) hu0
  norm_num [padicValNat_self] at hval
  rw [pow_mul, show (2 : ℕ)^2 = 4 by decide, hval] at hv
  have hdvd := (Nat.pow_dvd_iff_le_padicValNat (by decide : 3 ≠ 1) hu0 (k := t)).mpr (by omega)
  apply (Nat.modEq_iff_dvd' (Nat.le_add_right _ _)).2
  simpa using Nat.mul_dvd_mul_left 2 hdvd

/-- The finite multiplicity bound used with character orthogonality. -/
theorem collision_card (h t N n : ℕ) (hh : h ≠ 0) :
    ((range N).filter (fun m ↦
      ((h : ZMod (3 ^ (padicValNat 3 h + t + 1))) * 2 ^ n) = h * 2 ^ m)).card ≤
        N / (2 * 3 ^ t) + 1 := by
  classical
  let P := 2 * 3 ^ t
  calc
    _ ≤ ((range N).filter (fun m ↦ m ≡ n [MOD P])).card := by
      apply card_le_card
      intro m hm
      obtain ⟨hmN, hm⟩ := mem_filter.mp hm
      apply mem_filter.mpr ⟨hmN, ?_⟩
      apply (collision_modEq h t m n hh)
      apply (ZMod.natCast_eq_natCast_iff _ _ _).1
      push_cast
      exact hm.symm
    _ ≤ _ := by
      rw [← Nat.count_eq_card_filter_range, Nat.count_modEq_card _ (by positivity : 0 < P)]
      dsimp [P]
      split_ifs <;> omega

end

/-! ## Finite Fourier orthogonality -/

section

open Finset Complex
open scoped ComplexConjugate BigOperators

private lemma char_sum {M : ℕ} [NeZero M] (t : ZMod M) :
    ∑ a : ZMod M, ZMod.stdAddChar (t * a) = if t = 0 then (M : ℂ) else 0 := by
  split_ifs with h
  · simp [h, ZMod.card]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar M h)

private lemma char_conj {M : ℕ} [NeZero M] (t : ZMod M) :
    conj (ZMod.stdAddChar t) = ZMod.stdAddChar (-t) := by
  change conj (ZMod.toCircle t : ℂ) = (ZMod.toCircle (-t) : ℂ)
  rw [AddChar.map_neg_eq_inv]
  exact (Circle.coe_inv_eq_conj _).symm

/-- Orthogonality with arbitrary phases. Equal frequencies are precisely the surviving pairs. -/
theorem energy_identity {M N : ℕ} [NeZero M] (f : ℕ → ZMod M) (w : ℕ → ℂ) :
    ((∑ a : ZMod M, ‖∑ n ∈ range N, w n * ZMod.stdAddChar (f n * a)‖ ^ 2 : ℝ) : ℂ) =
    ∑ n ∈ range N, ∑ m ∈ range N, if f n = f m then (M : ℂ) * w n * conj (w m) else 0 := by
  push_cast
  simp_rw [← Complex.mul_conj', map_sum, map_mul, char_conj, sum_mul, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun n _ ↦ ?_
  rw [sum_comm]
  refine sum_congr rfl fun m _ ↦ ?_
  have h (a : ZMod M) :
      w n * ZMod.stdAddChar (f n * a) * (conj (w m) * ZMod.stdAddChar (-(f m * a))) =
      (w n * conj (w m)) * ZMod.stdAddChar ((f n - f m) * a) := by
    rw [sub_mul, sub_eq_add_neg, AddChar.map_add_eq_mul]
    ring
  simp_rw [h]
  rw [← mul_sum, char_sum]
  by_cases he : f n = f m <;> simp [he, sub_eq_zero, mul_comm, mul_left_comm, mul_assoc]

/-- The sum over any prefix set is bounded by the maximal frequency multiplicity. -/
theorem energy_le {M N L : ℕ} [NeZero M] (B : Finset (ZMod M))
    (f : ℕ → ZMod M) (w : ℕ → ℂ) (hw : ∀ n, ‖w n‖ ≤ 1)
    (hf : ∀ n < N, ((range N).filter (fun m ↦ f n = f m)).card ≤ L) :
    ∑ a ∈ B, ‖∑ n ∈ range N, w n * ZMod.stdAddChar (f n * a)‖ ^ 2 ≤
      (M : ℝ) * N * L := by
  classical
  have h0 : 0 ≤ ∑ a : ZMod M, ‖∑ n ∈ range N, w n * ZMod.stdAddChar (f n * a)‖ ^ 2 := by positivity
  calc
    _ ≤ ∑ a : ZMod M, ‖∑ n ∈ range N, w n * ZMod.stdAddChar (f n * a)‖ ^ 2 :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ ↦ sq_nonneg _)
    _ = ‖∑ n ∈ range N, ∑ m ∈ range N, if f n = f m then (M : ℂ) * w n * conj (w m) else 0‖ := by
      rw [← energy_identity f w, Complex.norm_real, Real.norm_of_nonneg h0]
    _ ≤ ∑ n ∈ range N, ∑ m ∈ range N, if f n = f m then (M : ℝ) else 0 := by
      apply (norm_sum_le _ _).trans
      gcongr with n
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro m _
      split_ifs
      · simp only [norm_mul, Complex.norm_natCast, Complex.norm_conj]
        calc (M : ℝ) * ‖w n‖ * ‖w m‖ ≤ (M : ℝ) * 1 * 1 := by gcongr <;> apply hw
             _ = _ := by ring
      · simp
    _ ≤ ∑ _n ∈ range N, (L : ℝ) * M := by
      apply sum_le_sum
      intro n hn
      rw [← sum_filter]
      simp only [sum_const, nsmul_eq_mul]
      gcongr
      exact_mod_cast hf n (mem_range.mp hn)
    _ = _ := by simp [mul_comm, mul_left_comm, mul_assoc]

end

/-! ## Interpolation between sample sizes -/

section

open Filter Finset
open scoped Topology

/-- Normalized complex partial sums, including the conventional value zero at N = 0. -/
def mean (u : ℕ → ℂ) (N : ℕ) : ℂ := (∑ n ∈ range N, u n) / N

theorem between_means (u : ℕ → ℂ) (hu : ∀ i, ‖u i‖ ≤ 1)
    {A N : ℕ} (ha : 0 < A) (han : A ≤ N) :
    ‖mean u N‖ ≤ ‖mean u A‖ + (N - A : ℕ) / (N : ℝ) := by
  have hn : 0 < N := ha.trans_le han
  have hsum : ‖∑ n ∈ range (N-A), u (A+n)‖ ≤ (N-A : ℕ) := by
    calc
      _ ≤ ∑ n ∈ range (N-A), ‖u (A+n)‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ range (N-A), (1 : ℝ) := sum_le_sum fun _ _ ↦ hu _
      _ = _ := by simp
  have htotal : ‖∑ n ∈ range N, u n‖ ≤ ‖∑ n ∈ range A, u n‖ + (N-A : ℕ) := by
    conv_lhs => rw [← Nat.add_sub_of_le han, sum_range_add]
    exact (norm_add_le _ _).trans (by gcongr)
  simp only [mean, norm_div, Complex.norm_natCast]
  calc
    _ ≤ (‖∑ n ∈ range A, u n‖ + (N-A : ℕ)) / (N : ℝ) := by gcongr
    _ ≤ _ := by rw [add_div]; gcongr

/-- Multiples of successive powers of 3, with all fixed positive integer multipliers,
    form a sufficiently fine collection of sample times for bounded averages. -/
theorem tendsto_of_ternary_samples (u : ℕ → ℂ) (hu : ∀ i, ‖u i‖ ≤ 1)
    (hs : ∀ r : ℕ, 0 < r → Tendsto (fun k : ℕ ↦ mean u (r * 3^k)) atTop (𝓝 0)) :
    Tendsto (mean u) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨C, hC⟩ := exists_nat_gt (2 / ε)
  have hC0 : 0 < C := by
    have : 0 < (C : ℝ) := (by positivity : (0 : ℝ) < 2 / ε).trans hC
    exact_mod_cast this
  have hsmall : (1 : ℝ) / C < ε / 2 := by
    have hc' : (0 : ℝ) < C := by exact_mod_cast hC0
    apply (div_lt_iff₀ hc').2
    have := (div_lt_iff₀ hε).1 hC
    nlinarith
  have he (r : ℕ) (hr : r ∈ Icc C (3*C)) :
      ∀ᶠ k : ℕ in atTop, ‖mean u (r*3^k)‖ < ε/2 := by
    simpa [dist_zero_right] using
      (Metric.tendsto_nhds.mp (hs r (hC0.trans_le (mem_Icc.mp hr).1)) (ε/2) (by positivity))
  obtain ⟨K,hK⟩ := eventually_atTop.1 ((Finset.eventually_all (Icc C (3*C))).2 he)
  refine ⟨C * 3^K, fun N hN ↦ ?_⟩
  have hb : 3^K ≤ N/C := (Nat.le_div_iff_mul_le hC0).2 (by simpa [mul_comm] using hN)
  have hNC : N / C ≠ 0 := (by positivity : 0 < 3^K).trans_le hb |>.ne'
  let k := Nat.log 3 (N/C)
  let b := 3^k
  have hb0 : 0 < b := by dsimp [b]; positivity
  have hk : K ≤ k := (Nat.le_log_iff_pow_le (by decide) hNC).2 hb
  have hlo : b ≤ N / C := Nat.pow_log_le_self _ hNC
  have hhi : N / C < 3 * b := by simpa [b,k,pow_succ,mul_comm] using
    (Nat.lt_pow_succ_log_self (by decide : 1 < 3) (N/C))
  have hCB : C*b ≤ N := by simpa [mul_comm] using (Nat.le_div_iff_mul_le hC0).1 hlo
  have hBN : N < (3*b)*C := (Nat.div_lt_iff_lt_mul hC0).1 hhi
  let r := N/b
  have hr : C ≤ r := (Nat.le_div_iff_mul_le hb0).2 hCB
  have hr' : r ≤ 3*C := le_of_lt <| (Nat.div_lt_iff_lt_mul hb0).2 (by simpa [mul_assoc,mul_comm,mul_left_comm] using hBN)
  have hA : r*b ≤ N := Nat.div_mul_le_self _ _
  have hpos : 0 < r*b := Nat.mul_pos (hC0.trans_le hr) hb0
  have hrem : N-r*b < b := by
    have hd := Nat.mod_add_div N b
    have hm := Nat.mod_lt N hb0
    dsimp [r]
    rw [mul_comm b (N/b)] at hd
    omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hpos.trans_le hA
  have herr : ((N-r*b : ℕ) : ℝ) / N ≤ 1 / C := by
    rw [div_le_div_iff₀ hNr (by exact_mod_cast hC0 : 0 < (C : ℝ)), one_mul]
    exact_mod_cast ((Nat.mul_le_mul_right C hrem.le).trans (by simpa [mul_comm] using hCB))
  rw [dist_zero_right]
  have hmid := hK k hk r (mem_Icc.mpr ⟨hr,hr'⟩)
  have hh := between_means u hu hpos hA
  change ‖mean u (r*b)‖ < ε/2 at hmid
  linarith

end

/-! ## An injective sparse ternary construction -/

section

open Real
open Classical in
private noncomputable def lastMarker (n : ℕ) := Nat.findGreatest (fun a ↦ ∃ j : ℕ, a = 4^(2^j)) n

private def marker (j : ℕ) : ℕ := 4^(2^j)

private theorem marker_succ (j : ℕ) : marker (j+1) = marker j ^ 2 := by
  simp [marker, pow_succ (2 : ℕ) j, pow_mul]

private theorem marker_strict : StrictMono marker := by
  intro i j hij
  exact Nat.pow_lt_pow_right (by decide) (Nat.pow_lt_pow_right (by decide) hij)

private theorem marker_large (j : ℕ) : j ≤ marker j := marker_strict.id_le j

/-- When a marker B is reached, the next free position jumps by order B². -/
private def slot (n : ℕ) := n + (lastMarker n)^2

private theorem slot_strict : StrictMono slot := by
  classical
  intro i j hij
  unfold slot
  have hm : lastMarker i ≤ lastMarker j := Nat.findGreatest_mono_right _ hij.le
  exact Nat.add_lt_add_of_lt_of_le hij (Nat.pow_le_pow_left hm 2)

private theorem slot_bound (i : ℕ) : slot i ≤ i+i^2 := by
  classical
  unfold slot
  gcongr
  exact Nat.findGreatest_le _

private theorem slot_at (j : ℕ) : slot (marker j) = marker j + (marker j)^2 := by
  classical
  have h : ∃ i : ℕ, marker j = 4^(2^i) := ⟨j,rfl⟩
  have hh : lastMarker (marker j) = marker j := Nat.findGreatest_eq (P := fun a ↦ ∃ i : ℕ, a = 4^(2^i)) h
  rw [slot,hh]

private theorem slot_before (j i : ℕ) (hi : i < marker (j+1)) :
    slot i < 2 * marker (j+1) := by
  classical
  have h : lastMarker i ≤ marker j := by
    by_cases hz : lastMarker i = 0
    · omega
    obtain ⟨t,ht⟩ := Nat.findGreatest_of_ne_zero (P := fun a ↦ ∃ j : ℕ, a = 4^(2^j))
      (rfl : Nat.findGreatest _ i = lastMarker i) hz
    change lastMarker i = marker t at ht
    have hm : marker t ≤ i := ht ▸ (Nat.findGreatest_le i : lastMarker i ≤ i)
    have hj := marker_strict.lt_iff_lt.mp (hm.trans_lt hi)
    rw [ht]
    exact marker_strict.monotone (by omega)
  have hh := Nat.pow_le_pow_left h 2
  rw [← marker_succ] at hh
  unfold slot
  omega

abbrev Bits := ℕ → ZMod 2

open Classical in
private def digit (x : Bits) (i : ℕ) : Fin 3 :=
  if h : ∃ n, 2 * slot n = i then
    if x h.choose = 0 then 0 else 2
  else if ∃ n, 2*slot n+1 = i then 2 else 0

private theorem digit_free (x : Bits) (n : ℕ) :
    digit x (2*slot n) = if x n = 0 then 0 else 2 := by
  classical
  have h : ∃ l, 2*slot l = 2*slot n := ⟨n,rfl⟩
  have hc : h.choose = n := slot_strict.injective (by have := h.choose_spec; omega)
  rw [digit, dif_pos h, hc]

private theorem digit_mark (x : Bits) (n : ℕ) : digit x (2*slot n+1) = 2 := by
  classical
  have ha : ¬ ∃ l, 2 * slot l = 2*slot n+1 := by omega
  have hb : ∃ l, 2*slot l+1 = 2*slot n+1 := ⟨n,rfl⟩
  rw [digit, dif_neg ha, if_pos hb]

private theorem digit_ne_one (x : Bits) (i : ℕ) : digit x i ≠ 1 := by
  classical
  unfold digit
  split_ifs <;> decide

private theorem digit_zero_gap (x : Bits) (j i : ℕ) (hlo : 4*marker (j+1) ≤ i)
    (hhi : i < 2*marker (j+1)^2) : digit x i = 0 := by
  have hh (n : ℕ) : 2*slot n+1 < 4*marker (j+1) ∨ 2*marker (j+1)^2 ≤ 2*slot n := by
    by_cases hn : n < marker (j+1)
    · left; have := slot_before j n hn; omega
    · right
      have hl := slot_strict.monotone (Nat.le_of_not_gt hn)
      rw [slot_at] at hl
      omega
  classical
  have ha : ¬ ∃ n, 2*slot n = i := by rintro ⟨n,h⟩; specialize hh n; omega
  have hb : ¬ ∃ n, 2*slot n+1 = i := by rintro ⟨n,h⟩; specialize hh n; omega
  rw [digit, dif_neg ha, if_neg hb]

def value (x : Bits) : ℝ := ofDigits (digit x)

theorem value_cantor_liouville (x : Bits) : value x ∈ cantorSet ∧ Liouville (value x) := by
  apply cantor_liouville_of_gaps _ (digit_ne_one x)
  · intro a
    refine ⟨2*slot a+1, ?_, by rw [digit_mark]; decide⟩
    have : a ≤ slot a := Nat.le_add_right _ _
    omega
  · intro L
    let j := 2*L
    let B := marker (j+1)
    have hB : 2*L < B := by have := marker_large (j+1); dsimp [j,B] at *; omega
    refine ⟨4*B,2*B^2,by omega,?_,fun i hi hi' ↦ digit_zero_gap x j i hi hi'⟩
    nlinarith [Nat.mul_lt_mul_of_pos_left hB (by omega : 0 < B)]

private theorem bit_inj : ∀ u v : ZMod 2,
    (if u = 0 then (0 : Fin 3) else 2) = (if v = 0 then 0 else 2) → u = v := by decide

theorem value_injective : Function.Injective value := by
  intro x y heq
  have hd := ofDigits_zero_two_sequence_unique (digit_ne_one x) (digit_ne_one y) heq
  funext n
  have hh := congrFun hd (2*slot n)
  simp only [digit_free] at hh
  exact bit_inj _ _ hh

end

/-! ## A second-moment estimate uniform in the tail -/

section

open Finset Complex

/-- The h-th Fourier character along the binary shift. -/
def phase (h n : ℕ) (x : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (h : ℂ) * 2^n * x)

theorem phase_norm (h n : ℕ) (x : ℝ) : ‖phase h n x‖ = 1 := by
  rw [phase, Complex.norm_exp]
  have e : ((2:ℂ) * Real.pi * I * (h:ℂ) * 2^n * x) =
      (((2 * Real.pi * h * (2:ℝ)^n * x : ℝ) : ℂ) * I) := by push_cast; ring
  rw [e, Complex.mul_I_re, Complex.ofReal_im, neg_zero, Real.exp_zero]

def weyl (h N : ℕ) (x : ℝ) : ℂ := mean (fun n ↦ phase h n x) N

private theorem phase_prefix (h n M p : ℕ) [NeZero M] (T : ℝ) :
    phase h n ((p:ℝ)/M + T) = phase h n T *
      ZMod.stdAddChar ((h : ZMod M) * 2^n * (p : ZMod M)) := by
  have hx : ((h : ZMod M) * 2^n * (p : ZMod M)) = ((↑h * 2^n * ↑p : ℤ) : ZMod M) := by push_cast; rfl
  rw [hx, ZMod.stdAddChar_coe]
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The finite version of (2), uniform in T. The exponent k is v_3(h)+t+1. -/
theorem prefix_mean_square {h t N : ℕ} (hh : h ≠ 0) (hN : N ≠ 0)
    (T : ℝ) (B : Finset (ZMod (3 ^ (padicValNat 3 h + t + 1)))) :
    ∑ a ∈ B, ‖weyl h N ((a.val : ℝ)/(3:ℝ)^(padicValNat 3 h + t + 1) + T)‖^2 ≤
      ((3 : ℝ)^(padicValNat 3 h + t + 1) / N) * (N / (2 * 3^t) + 1 : ℕ) := by
  let k := padicValNat 3 h + t + 1
  let M := 3^k
  have : NeZero M := ⟨by dsimp [M]; positivity⟩
  have hp (a : ZMod M) (n : ℕ) :
      phase h n ((a.val:ℝ)/(3:ℝ)^k + T) =
      phase h n T * ZMod.stdAddChar ((h : ZMod M) * 2^n * a) := by
    have := phase_prefix h n M a.val T
    simpa [M, ZMod.natCast_zmod_val] using this
  change (∑ a ∈ B, ‖weyl h N ((a.val : ℝ)/(3:ℝ)^k + T)‖^2) ≤ _
  simp only [weyl, mean, hp, norm_div, Complex.norm_natCast, div_pow, ← sum_div]
  have hE := energy_le B (fun n ↦ (h : ZMod M) * 2^n) (fun n ↦ phase h n T)
    (fun n ↦ (phase_norm h n T).le) (fun n _ ↦ collision_card h t N n hh)
  have hpos : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
  apply (div_le_iff₀ (sq_pos_of_pos hpos)).2
  convert hE using 1
  all_goals simp only [M,k, Nat.cast_pow,Nat.cast_ofNat] at *
  all_goals try rfl
  all_goals field_simp

end

/-! ## The topology on a single bit -/

section

scoped instance bitTopology : TopologicalSpace (ZMod 2) := ⊥
scoped instance bitDiscrete : DiscreteTopology (ZMod 2) := ⟨rfl⟩

end

/-! ## Averaging over the free digits -/

section

open Finset Filter MeasureTheory Real
open scoped Topology

private def law : Measure Bits := MeasureTheory.Measure.addHaarMeasure ⊤
  deriving Measure.IsAddHaarMeasure

private instance : IsProbabilityMeasure law :=
  ⟨Measure.addHaarMeasure_self⟩

@[fun_prop] private theorem value_cont : Continuous value := by
  apply continuous_ofDigits.comp
  apply continuous_pi
  intro i
  classical
  by_cases h : ∃ n, 2*slot n = i
  · simp only [digit,dif_pos h]
    exact (continuous_of_discreteTopology (f := fun z : ZMod 2 ↦
        if z = 0 then (0 : Fin 3) else 2)).comp (continuous_apply h.choose)
  · simp only [digit,dif_neg h]
    exact continuous_const

private def shift {j : ℕ} (y : Fin j → ZMod 2) (n : ℕ) : ZMod 2 :=
  if h : n < j then y ⟨n,h⟩ else 0

private theorem tail_fixed {j k : ℕ} (x : Bits) (y : Fin j → ZMod 2)
    (hk : ∀ n < j, 2*slot n < k) (i : ℕ) (hi : k ≤ i) :
    digit (x+shift y) i = digit x i := by
  classical
  by_cases h : ∃ n, 2*slot n = i
  · have he := h.choose_spec
    have hn : ¬ h.choose < j := by intro hlt; have := hk _ hlt; omega
    simp only [digit,dif_pos h,Pi.add_apply,shift,dif_neg hn,add_zero]
  · simp only [digit,dif_neg h]

private theorem numerator_lt (d : ℕ → Fin 3) (k : ℕ) : numerator d k < 3^k := by
  induction k with
  | zero => simp [numerator]
  | succ k ih =>
    rw [numerator, pow_succ]
    have := (d k).isLt
    omega

private theorem prefix_inj {j k : ℕ} (x : Bits) (hk : ∀ n < j, 2*slot n < k) :
    Function.Injective (fun y : Fin j → ZMod 2 ↦
      (numerator (digit (x+shift y)) k : ZMod (3^k))) := by
  intro y z he
  have hnum := congrArg ZMod.val he
  simp only [ZMod.val_natCast_of_lt (numerator_lt _ _)] at hnum
  have ht (w : Bits) (i : ℕ) : trunc (digit w) k i ≠ 1 := by
    by_cases h : i < k <;> simp [trunc,h,digit_ne_one]
  have heq : ofDigits (trunc (digit (x+shift y)) k) = ofDigits (trunc (digit (x+shift z)) k) := by
    rw [trunc_value, trunc_value, hnum]
  have hf := ofDigits_zero_two_sequence_unique (ht _) (ht _) heq
  funext n
  have hh := congrFun hf (2*slot n.val)
  simp only [trunc,hk _ n.isLt,if_pos,digit_free,Pi.add_apply,shift,dif_pos n.isLt,Fin.eta] at hh
  exact add_left_cancel (bit_inj _ _ hh)

private theorem split_value {j k : ℕ} (x : Bits) (y : Fin j → ZMod 2)
    (hk : ∀ n < j, 2*slot n < k) :
    value (x+shift y) =
      (numerator (digit (x+shift y)) k : ℝ) / (3:ℝ)^k +
      ((3:ℝ)^k)⁻¹ * ofDigits (fun i ↦ digit x (i+k)) := by
  rw [value,ofDigits_eq_sum_add_ofDigits _ k,prefix_sum]
  congr 2
  apply congrArg ofDigits
  funext i
  exact tail_fixed x y hk _ (by omega)

private def moment (h N : ℕ) (x : Bits) : ℝ := ‖weyl h N (value x)‖^2

private lemma moment_cont (h N : ℕ) : Continuous (moment h N) := by
  unfold moment weyl mean phase
  fun_prop (disch := first | exact value_cont | positivity)

private theorem integral_moment (h r t j : ℕ) (hh : h ≠ 0) (hr : 0 < r)
    (hk : ∀ n < j, 2*slot n < padicValNat 3 h + t + 1) :
    (2:ℝ)^j * (∫ x, moment h (r * 3^(padicValNat 3 h+t+1)) x ∂law) ≤
      (3:ℝ)^(padicValNat 3 h+1) + 1 := by
  classical
  let k := padicValNat 3 h + t + 1
  let M := 3^k
  let N := r*M
  let P := 2*3^t
  let Y := Fin j → ZMod 2
  have hM : 0 < M := by dsimp [M]; positivity
  have hN : 0 < N := Nat.mul_pos hr hM
  have hY : (Fintype.card Y : ℝ) = 2^j := by simp [Y, ZMod.card]
  have hin (y : Y) : Integrable (fun x : Bits ↦ moment h N (x+shift y)) law :=
    ((moment_cont h N).comp (continuous_id.add continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have bound (x : Bits) : ∑ y : Y, moment h N (x+shift y) ≤ (3:ℝ)^(padicValNat 3 h+1) + 1 := by
    let A (y : Y) : ZMod M := numerator (digit (x+shift y)) k
    let T := ((3:ℝ)^k)⁻¹ * ofDigits (fun i ↦ digit x (i+k))
    have heq (y : Y) : moment h N (x+shift y) =
        ‖weyl h N (((A y).val : ℝ) / (3:ℝ)^k + T)‖ ^ 2 := by
      rw [moment,split_value x y hk]
      simp [A, M, T, k, ZMod.val_natCast_of_lt (numerator_lt _ _)]
    simp_rw [heq]
    rw [← sum_image (f := fun a : ZMod M ↦ ‖weyl h N ((a.val : ℝ)/(3:ℝ)^k + T)‖^2)
      (prefix_inj x hk).injOn]
    apply (prefix_mean_square hh hN.ne' T _).trans
    have hdiv : N / P ≤ r*3^(padicValNat 3 h+1) := by
      apply Nat.le_of_lt_succ
      apply (Nat.div_lt_iff_lt_mul (by dsimp [P]; positivity)).2
      have hn' : N = r * 3^(padicValNat 3 h+1) * 3^t := by
        dsimp [N,M,k]
        rw [show padicValNat 3 h+t+1 = (padicValNat 3 h+1)+t by omega, pow_add, mul_assoc]
      dsimp [P]
      rw [hn']
      nlinarith [show 0 < (3:ℕ)^t by positivity]
    have hratio : (3:ℝ)^k / (N:ℝ) = 1 / (r:ℝ) := by
      dsimp [N,M]; push_cast; field_simp
    change (3:ℝ)^k / N * ((N/P+1 : ℕ) : ℝ) ≤ _
    rw [hratio]
    rw [one_div, ← div_eq_inv_mul, div_le_iff₀ (by exact_mod_cast hr : 0 < (r:ℝ))]
    have hd : (↑(N/P) : ℝ) ≤ (r:ℝ)*3^(padicValNat 3 h+1) := by exact_mod_cast hdiv
    have hr1 : (1:ℝ) ≤ r := by exact_mod_cast hr
    push_cast
    nlinarith
  change (2:ℝ)^j * (∫ x, moment h N x ∂law) ≤ _
  calc
    _ = ∑ y : Y, ∫ x : Bits, moment h N (x+shift y) ∂law := by
      simp only [integral_add_right_eq_self, sum_const, card_univ, nsmul_eq_mul,hY]
    _ = ∫ x : Bits, ∑ y : Y, moment h N (x+shift y) ∂law := by
      rw [integral_finsetSum _ (fun y _ ↦ hin y)]
    _ ≤ ∫ _x : Bits, ((3:ℝ)^(padicValNat 3 h+1)+1) ∂law :=
      integral_mono (integrable_finsetSum _ (fun y _ ↦ hin y)) (integrable_const _) bound
    _ = _ := by simp

end

/-! ## Almost-sure Fourier cancellation and uncountability -/

section

open Filter MeasureTheory Finset
open scoped Topology ENNReal

private theorem exp_majorant (a : ℕ) (ha : 16 ≤ a) :
    2 * (2*a + (2*a)^2) < 2^a := by
  induction a, ha using Nat.le_induction with
  | base => decide
  | succ a ha ih =>
    rw [pow_succ (2:ℕ) a]
    nlinarith [Nat.mul_le_mul_left a ha]

private theorem summable_moments (h r : ℕ) (hh : h ≠ 0) (hr : 0 < r) :
    Summable (fun k : ℕ ↦ ∫ x, moment h (r*3^k) x ∂law) := by
  let C : ℝ := 3^(padicValNat 3 h+1)+1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hs : Summable (fun k : ℕ ↦ (4*C)*((k:ℝ)^2)⁻¹) :=
    (Real.summable_nat_pow_inv.mpr (by decide : 1 < 2)).mul_left _
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop (max (2^16) (padicValNat 3 h+1))] with k hk
  have h0 : 0 < k := lt_of_lt_of_le (by decide : 0 < 2^16) ((le_max_left _ _).trans hk)
  let a := Nat.log 2 k
  have ha : 16 ≤ a := (Nat.le_log_iff_pow_le (by decide) h0.ne').2 ((le_max_left _ _).trans hk)
  have hlow : 2^a ≤ k := Nat.pow_log_le_self 2 h0.ne'
  have hhi : k < 2*2^a := by simpa [a,pow_succ,mul_comm] using Nat.lt_pow_succ_log_self (by decide : 1<2) k
  let t := k-(padicValNat 3 h+1)
  have ht : padicValNat 3 h+t+1 = k := by
    have := (le_max_right (2^16) _).trans hk
    dsimp [t]; omega
  have hbound (n : ℕ) (hn : n < 2*a) : 2*slot n < padicValNat 3 h+t+1 := by
    rw [ht]
    apply lt_of_lt_of_le _ hlow
    apply lt_of_le_of_lt _ (exp_majorant a ha)
    have := slot_bound n
    exact Nat.mul_le_mul_left _ (this.trans (by gcongr))
  have he := integral_moment h r t (2*a) hh hr hbound
  rw [ht] at he
  have hquad : (k:ℝ)^2 ≤ 4*(2:ℝ)^(2*a) := by
    have hq := Nat.pow_le_pow_left hhi.le 2
    rw [mul_pow, ← pow_mul, mul_comm a 2] at hq
    exact_mod_cast hq
  have hi : 0 ≤ ∫ x, moment h (r*3^k) x ∂law := integral_nonneg (fun x ↦ sq_nonneg _)
  rw [Real.norm_of_nonneg hi, ← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity : 0 < (k:ℝ)^2)).2
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_left hquad hi
    _ ≤ 4*C := by dsimp [C]; nlinarith only [he]

private theorem ae_samples (h r : ℕ) (hh : h ≠ 0) (hr : 0 < r) :
    ∀ᵐ x ∂law, Tendsto (fun k : ℕ ↦ weyl h (r*3^k) (value x)) atTop (𝓝 0) := by
  let F (k : ℕ) (x : Bits) := moment h (r*3^k) x
  have hF (k : ℕ) : Continuous (F k) := moment_cont _ _
  have hpos (k : ℕ) (x : Bits) : 0 ≤ F k x := sq_nonneg _
  have hir (k : ℕ) : Integrable (F k) law := (hF k).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hl (k : ℕ) : ∫⁻ x, ENNReal.ofReal (F k x) ∂law = ENNReal.ofReal (∫ x, F k x ∂law) :=
    (ofReal_integral_eq_lintegral_ofReal (hir k) (ae_of_all _ (hpos k))).symm
  have hmeas (k : ℕ) : Measurable fun x ↦ ENNReal.ofReal (F k x) := (hF k).measurable.ennreal_ofReal
  have hfin : (∫⁻ x, ∑' k, ENNReal.ofReal (F k x) ∂law) ≠ ⊤ := by
    rw [lintegral_tsum fun k ↦ (hmeas k).aemeasurable]
    simp_rw [hl]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k ↦ integral_nonneg (hpos k)) (summable_moments h r hh hr)]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_lt_top' (AEMeasurable.tsum (fun k ↦ (hmeas k).aemeasurable)) hfin] with x hx
  have hsum : Summable (fun k ↦ ‖F k x‖) := by
    apply tsum_enorm_ne_top_iff_summable_norm.1
    simpa only [Real.enorm_of_nonneg (hpos _ _)] using hx.ne
  have ht : Tendsto (fun k ↦ F k x) atTop (𝓝 0) := by
    simpa only [Real.norm_of_nonneg (hpos _ _)] using hsum.tendsto_atTop_zero
  have := (Real.continuous_sqrt.tendsto (0:ℝ)).comp ht
  apply tendsto_zero_iff_norm_tendsto_zero.2
  simpa only [Function.comp_def,F,moment,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using this

/-- Weyl's classical characterization of normality in base two, using positive harmonics. -/
def BinaryWeylNormal (x : ℝ) : Prop :=
  ∀ h : ℕ, h ≠ 0 → Tendsto (fun N : ℕ ↦ weyl h N x) atTop (𝓝 0)

theorem ae_binaryWeylNormal : ∀ᵐ x ∂law, BinaryWeylNormal (value x) := by
  have hh : ∀ᵐ x ∂law, ∀ h r : ℕ, h ≠ 0 → 0 < r →
      Tendsto (fun k : ℕ ↦ weyl h (r*3^k) (value x)) atTop (𝓝 0) := by
    apply ae_all_iff.2; intro h
    apply ae_all_iff.2; intro r
    by_cases hh : h = 0
    · simp [hh]
    by_cases hr : 0 < r
    · simpa [hh,hr] using ae_samples h r hh hr
    · simp [hr]
  filter_upwards [hh] with x hx
  intro h h0
  exact tendsto_of_ternary_samples _ (fun n ↦ (phase_norm h n _).le) (fun r hr ↦ hx h r h0 hr)

theorem uncountable_binaryWeylNormal_cantor_liouville :
    ¬ {x : ℝ | x ∈ cantorSet ∧ Liouville x ∧ BinaryWeylNormal x}.Countable := by
  intro hc
  have hpre := hc.preimage value_injective
  have : (𝓝[≠] (0 : Bits)).NeBot := by
    constructor
    intro h
    have ho : IsOpen ({0} : Set Bits) := (isOpen_singleton_iff_punctured_nhds _).2 h
    let := discreteTopology_of_isOpen_singleton_zero ho
    have := finite_of_compact_of_discrete (X := Bits)
    exact not_finite Bits
  have ha := hpre.ae_notMem law
  obtain ⟨x,hx,hout⟩ := (ae_binaryWeylNormal.and ha).exists
  exact hout ⟨(value_cantor_liouville x).1,(value_cantor_liouville x).2,hx⟩

end

/-! ## From Fourier cancellation to equidistribution -/

section

open Finset Filter MeasureTheory MeasureTheory.Measure Complex AddCircle Set
open scoped Topology ComplexConjugate ENNReal
local notation "𝕋" => AddCircle (1 : ℝ)

private def orbit (x : ℝ) (n : ℕ) : 𝕋 := (((2:ℝ)^n*x : ℝ) : 𝕋)

private def empirical (x : ℝ) (N : ℕ) : Measure 𝕋 :=
  (↑(N+1 : ℕ) : ℝ≥0∞)⁻¹ • ∑ n ∈ range (N+1), Measure.dirac (orbit x n)

private instance (x : ℝ) (N : ℕ) : IsProbabilityMeasure (empirical x N) := by
  constructor
  simp [empirical,Measure.finsetSum_apply,ENNReal.inv_mul_cancel]

private lemma integral_empirical (x : ℝ) (N : ℕ) (g : C(𝕋,ℂ)) :
    ∫ z, g z ∂empirical x N = mean (fun n ↦ g (orbit x n)) (N+1) := by
  rw [empirical,integral_smul_measure,integral_finsetSum_measure]
  · simp [mean,ENNReal.toReal_inv,Algebra.smul_def,div_eq_inv_mul,ENNReal.toReal_add]
  · intro i hi
    exact integrable_dirac (by simp)

private def haar : ProbabilityMeasure 𝕋 := ⟨haarAddCircle,inferInstance⟩
private def sample (x : ℝ) (N : ℕ) : ProbabilityMeasure 𝕋 := ⟨empirical x N,inferInstance⟩

private lemma haar_fourier (z : ℤ) (hz : z ≠ 0) :
    (∫ t : 𝕋, fourier z t ∂(haar : Measure 𝕋)) = 0 := by
  have he := congrFun (fourierCoeff_fourier (T := 1) z) 0
  simpa [haar, fourierCoeff, fourier_zero, Pi.single_eq_of_ne (Ne.symm hz)] using he

private lemma test_character {x : ℝ} (hx : BinaryWeylNormal x) (z : ℤ) :
    Tendsto (fun N : ℕ ↦ ∫ t : 𝕋, fourier z t ∂(sample x N : Measure 𝕋)) atTop
      (𝓝 (∫ t : 𝕋, fourier z t ∂(haar : Measure 𝕋))) := by
  have he (N : ℕ) : (∫ t : 𝕋, fourier z t ∂(sample x N : Measure 𝕋)) =
      mean (fun n ↦ fourier z (orbit x n)) (N+1) := integral_empirical x N (fourier z)
  simp_rw [he]
  rcases eq_or_ne z 0 with rfl | hz
  · have hc (N : ℕ) : mean (fun n ↦ fourier 0 (orbit x n)) (N+1) = 1 := by
      simp only [mean, fourier_zero, sum_const,card_range,nsmul_eq_mul,mul_one]
      exact div_self (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero N))
    simp_rw [hc]
    simp
  rw [haar_fourier z hz]
  have hpos (h : ℕ) (hh : h ≠ 0) :
      Tendsto (fun N : ℕ ↦ mean (fun n ↦ fourier (h:ℤ) (orbit x n)) (N+1)) atTop (𝓝 0) := by
    have hf (n : ℕ) : fourier (h : ℤ) (orbit x n) = phase h n x := by
      rw [orbit, fourier_coe_apply,phase]
      push_cast
      ring_nf
    simp_rw [hf]
    exact (hx h hh).comp (tendsto_add_atTop_nat 1)
  cases z with
  | ofNat h => exact hpos h (fun he ↦ hz (by subst h; rfl))
  | negSucc h =>
    change Tendsto (fun N : ℕ ↦ mean (fun n ↦ fourier (-(↑(h+1) : ℤ)) (orbit x n)) (N+1)) atTop (𝓝 0)
    have hn (N : ℕ) : mean (fun n ↦ fourier (-(↑(h+1) : ℤ)) (orbit x n)) (N+1) =
        conj (mean (fun n ↦ fourier (↑(h+1) : ℤ) (orbit x n)) (N+1)) := by
      simp only [mean, fourier_neg, map_div₀, _root_.map_sum, map_natCast]
    simp_rw [hn]
    simpa only [Function.comp_def,map_zero] using
      (Complex.continuous_conj.tendsto 0).comp (hpos (h+1) (by omega))

private lemma integral_dist_le (μ : ProbabilityMeasure 𝕋) (f g : C(𝕋,ℂ)) :
    dist (∫ t, f t ∂(μ : Measure 𝕋)) (∫ t, g t ∂(μ : Measure 𝕋)) ≤ dist f g := by
  rw [dist_eq_norm, ← integral_sub
    (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  simpa [dist_eq_norm] using (norm_integral_le_of_norm_le_const (μ := (μ : Measure 𝕋))
    (ae_of_all _ (fun t ↦ ContinuousMap.norm_coe_le_norm (f-g) t)))

private theorem weak_orbit {x : ℝ} (hx : BinaryWeylNormal x) :
    Tendsto (sample x) atTop (𝓝 haar) := by
  let S := Submodule.span ℂ (Set.range (fourier (T:=1)))
  let P (f : C(𝕋,ℂ)) := Tendsto (fun n ↦ ∫ t, f t ∂(sample x n : Measure 𝕋)) atTop
    (𝓝 (∫ t, f t ∂(haar : Measure 𝕋)))
  have hi (f : C(𝕋,ℂ)) (μ : ProbabilityMeasure 𝕋) : Integrable f (μ : Measure 𝕋) :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hS (f : C(𝕋,ℂ)) (hf : f ∈ S) : P f := by
    induction hf using Submodule.span_induction with
    | mem f hf => obtain ⟨z,rfl⟩ := hf; exact test_character hx z
    | zero => simp [P]
    | add f g _ _ ihf ihg =>
      simpa [P,integral_add (hi f _) (hi g _)] using ihf.add ihg
    | smul c f _ ih => simpa [P,integral_const_mul] using ih.const_smul c
  apply (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).2
  intro ff
  let f : C(𝕋,ℂ) := ff.toContinuousMap
  change P f
  dsimp [P]
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hf : f ∈ closure (S : Set C(𝕋,ℂ)) := by
    change f ∈ S.topologicalClosure
    rw [show S.topologicalClosure = ⊤ from span_fourier_closure_eq_top]
    trivial
  obtain ⟨g,hg,hfg⟩ := Metric.mem_closure_iff.1 hf (ε/3) (by positivity)
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.1 (hS g hg) (ε/3) (by positivity)
  refine ⟨N, fun n hn ↦ ?_⟩
  have h1 := integral_dist_le (sample x n) f g
  have h2 := integral_dist_le haar g f
  rw [dist_comm g f] at h2
  have h3 := dist_triangle (∫ t, g t ∂(sample x n : Measure 𝕋))
    (∫ t, g t ∂(haar : Measure 𝕋)) (∫ t, f t ∂(haar : Measure 𝕋))
  have h4 := dist_triangle (∫ t, f t ∂(sample x n : Measure 𝕋))
    (∫ t, g t ∂(sample x n : Measure 𝕋)) (∫ t, f t ∂(haar : Measure 𝕋))
  exact h4.trans_lt (by linarith [hN n hn])

end

/-! ## Binary block frequencies -/

section

open Filter Finset Set MeasureTheory AddCircle
open scoped Topology
local notation "𝕋" => AddCircle (1 : ℝ)
local notation "π₁" => ((↑) : ℝ → 𝕋)

private def arc (a b : ℝ) : Set 𝕋 := π₁ '' Ico a b

private lemma open_inner (a b : ℝ) : IsOpen (π₁ '' Ioo a b) :=
  QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo

private lemma arc_measurable {a b : ℝ} (h : a < b) : MeasurableSet (arc a b) := by
  have eq : arc a b = insert (π₁ a) (π₁ '' Ioo a b) := by
    ext z
    constructor
    · rintro ⟨y,⟨hy,hb⟩,rfl⟩
      rcases hy.eq_or_lt with rfl | hh
      · exact Or.inl rfl
      · exact Or.inr ⟨y,⟨hh,hb⟩,rfl⟩
    · rintro (rfl | ⟨y,hy,rfl⟩)
      · exact ⟨a,⟨le_rfl,h⟩,rfl⟩
      · exact ⟨y,⟨hy.1.le,hy.2⟩,rfl⟩
  rw [eq]
  exact (open_inner a b).measurableSet.insert _

private lemma arc_boundary (a b : ℝ) : (haar : Measure 𝕋) (frontier (arc a b)) = 0 := by
  have hclosed : IsClosed (π₁ '' Icc a b) := (isCompact_Icc.image (by fun_prop : Continuous π₁)).isClosed
  have hs : closure (arc a b) ⊆ π₁ '' Icc a b := closure_minimal (Set.image_mono Ico_subset_Icc_self) hclosed
  have hi : π₁ '' Ioo a b ⊆ interior (arc a b) :=
    interior_maximal (Set.image_mono Ioo_subset_Ico_self) (open_inner a b)
  have hb : frontier (arc a b) ⊆ ({π₁ a, π₁ b} : Set 𝕋) := by
    rintro z ⟨hz,hno⟩
    obtain ⟨y,⟨ha,hb⟩,rfl⟩ := hs hz
    rcases ha.eq_or_lt with rfl | ha
    · simp
    rcases hb.eq_or_lt with rfl | hb
    · simp
    exact (hno (hi ⟨y,⟨ha,hb⟩,rfl⟩)).elim
  have hH : (haar : Measure 𝕋) = volume := by simp [haar,AddCircle.volume_eq_smul_haarAddCircle]
  have hz (z : 𝕋) : (volume : Measure 𝕋) {z} = 0 := by
    rw [← Metric.closedBall_zero, AddCircle.volume_closedBall]
    norm_num
  rw [hH]
  exact measure_mono_null hb (measure_union_null (hz (π₁ a)) (hz (π₁ b)))

private lemma fract_proj (y : ℝ) : π₁ (Int.fract y) = π₁ y := by
  have hi : π₁ ((⌊y⌋ : ℤ) : ℝ) = 0 := by
    simp
  rw [← Int.self_sub_floor, AddCircle.coe_sub,hi,sub_zero]

private lemma arc_mem {a b y : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    π₁ y ∈ arc a b ↔ Int.fract y ∈ Ico a b := by
  constructor
  · rintro ⟨z,hz,he⟩
    have h1 : z ∈ Ico (0:ℝ) (0+1) := ⟨ha.trans hz.1,by simpa using hz.2.trans_le hb⟩
    have h2 : Int.fract y ∈ Ico (0:ℝ) (0+1) := ⟨Int.fract_nonneg _,by simpa using Int.fract_lt_one y⟩
    rwa [← (AddCircle.coe_eq_coe_iff_of_mem_Ico h1 h2).1 (he.trans (fract_proj y).symm)]
  · intro hy
    exact ⟨_,hy,fract_proj y⟩

private lemma arc_mass {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    (haar : Measure 𝕋) (arc a b) = ENNReal.ofReal (b-a) := by
  have hH : (haar : Measure 𝕋) = volume := by simp [haar, AddCircle.volume_eq_smul_haarAddCircle]
  have hp : MeasurePreserving π₁ (volume.restrict (Ico (0:ℝ) 1)) volume := by
    rw [restrict_Ico_eq_restrict_Ioc]
    simpa using AddCircle.measurePreserving_mk (1:ℝ) 0
  rw [hH, ← hp.map_eq, Measure.map_apply hp.measurable (arc_measurable hab),
    Measure.restrict_apply (hp.measurable (arc_measurable hab))]
  have hs : π₁ ⁻¹' arc a b ∩ Ico (0:ℝ) 1 = Ico a b := by
    ext y
    constructor
    · rintro ⟨hy,hy'⟩
      simpa [Int.fract_eq_self.mpr hy'] using (arc_mem ha hb).1 hy
    · intro hy
      exact ⟨⟨y,hy,rfl⟩,ha.trans hy.1,hy.2.trans_le hb⟩
  rw [hs,Real.volume_Ico]

/-- The dyadic interval for a word of length d and integer value w is
    [w/2^d, (w+1)/2^d). Its occurrences are counted with overlap. -/
def BinaryNormal (x : ℝ) : Prop :=
  ∀ d w : ℕ, w < 2^d →
    Tendsto (fun N : ℕ ↦ (((range N).filter (fun n ↦
      Int.fract ((2:ℝ)^n*x) ∈ Ico ((w:ℝ)/2^d) (((w:ℝ)+1)/2^d))).card : ℝ)/N)
      atTop (𝓝 ((1:ℝ)/2^d))

theorem binaryNormal_of_weyl {x : ℝ} (hx : BinaryWeylNormal x) : BinaryNormal x := by
  classical
  intro d w hw
  let a : ℝ := w/2^d
  let b : ℝ := (w+1)/2^d
  have hp : 0 < (2:ℝ)^d := by positivity
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hab : a < b := by dsimp [a,b]; gcongr; linarith
  have hb : b ≤ 1 := by
    dsimp [b]; rw [div_le_iff₀ hp,one_mul]; exact_mod_cast hw
  have he := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    (weak_orbit hx) (arc_boundary a b)
  rw [arc_mass ha hab hb] at he
  have he' := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp he
  rw [ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le)] at he'
  have hcount (N : ℕ) :
      ((sample x N : Measure 𝕋) (arc a b)).toReal =
      (((range (N+1)).filter (fun n ↦ Int.fract ((2:ℝ)^n*x) ∈ Ico a b)).card : ℝ)/(N+1) := by
    change ((empirical x N) (arc a b)).toReal = _
    simp only [empirical,Measure.smul_apply,Measure.finsetSum_apply,
      Measure.dirac_apply' _ (arc_measurable hab), Set.indicator_apply, Pi.one_apply,orbit,arc_mem ha hb,
      smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    rw [← sum_filter]
    simp [div_eq_inv_mul]
  simp only [Function.comp_def,hcount] at he'
  have hb' : b-a = (1:ℝ)/2^d := by dsimp [a,b]; ring
  rw [hb'] at he'
  apply (Filter.tendsto_add_atTop_iff_nat 1).1
  simpa [a,b] using he'

theorem uncountable_binaryNormal_cantor_liouville :
    ¬ {x : ℝ | x ∈ cantorSet ∧ Liouville x ∧ BinaryNormal x}.Countable := by
  intro hc
  apply uncountable_binaryWeylNormal_cantor_liouville
  apply hc.mono
  intro x hx
  change x ∈ cantorSet ∧ Liouville x ∧ BinaryWeylNormal x at hx
  exact ⟨hx.1,hx.2.1,binaryNormal_of_weyl hx.2.2⟩

theorem exists_binaryNormal_cantor_liouville :
    ∃ x : ℝ, x ∈ cantorSet ∧ Liouville x ∧ BinaryNormal x := by
  change Set.Nonempty {x : ℝ | x ∈ cantorSet ∧ Liouville x ∧ BinaryNormal x}
  by_contra he
  apply uncountable_binaryNormal_cantor_liouville
  rw [Set.not_nonempty_iff_eq_empty.mp he]
  exact Set.countable_empty

end

end
end CantorNormal

#print axioms CantorNormal.uncountable_binaryNormal_cantor_liouville
#print axioms CantorNormal.exists_binaryNormal_cantor_liouville
