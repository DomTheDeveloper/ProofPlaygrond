module

public import FreePoles
public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
public import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
public import Mathlib.NumberTheory.LSeries.SumCoeff
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

@[expose] public section

namespace PowerFree

open Complex Filter Finset
open scoped Topology Classical

/-- No prime k-th power divides n. For k > 0 this excludes zero. -/
def KFree (k n : ℕ) : Prop := ∀ p, Nat.Prime p → ¬ p ^ k ∣ n

theorem kFree_two_iff (n : ℕ) : KFree 2 n ↔ Squarefree n := by
  simp only [KFree, Nat.squarefree_iff_prime_squarefree, pow_two]

private theorem kFree_one {k : ℕ} (hk : 0 < k) : KFree k 1 := by
  intro p hp h
  have hlarge : 1 < p ^ k := one_lt_pow₀ hp.one_lt hk.ne'
  exact (not_lt_of_ge (Nat.le_of_dvd (by decide) h)) hlarge

private theorem kFree_mul {k a b : ℕ} (hk : 0 < k) (h : a.Coprime b) :
    KFree k (a*b) ↔ KFree k a ∧ KFree k b := by
  constructor
  · intro hfree
    exact ⟨fun p hp hpa ↦ hfree p hp (dvd_mul_of_dvd_left hpa b),
      fun p hp hpb ↦ hfree p hp (dvd_mul_of_dvd_right hpb a)⟩
  · rintro ⟨ha,hb⟩ p hp hdiv
    have hpow : IsPrimePow (p ^ k) := (isPrimePow_nat_iff _).mpr ⟨p, k, hp, hk, rfl⟩
    exact ((h.isPrimePow_dvd_mul hpow).mp hdiv).elim (ha p hp) (hb p hp)

private theorem kFree_prime_pow {k p e : ℕ} (hk : 0 < k) (hp : p.Prime) :
    KFree k (p ^ e) ↔ e < k := by
  constructor
  · intro h
    exact lt_of_not_ge (fun he ↦ h p hp (pow_dvd_pow p he))
  · intro he q hq hd
    have hqp := Nat.prime_eq_prime_of_dvd_pow hq hp ((dvd_pow_self q hk.ne').trans hd)
    subst q
    exact (Nat.not_le.mpr he) ((Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hd)

/-- The Dirichlet series with the actual indicator of k-free integers as coefficients. -/
noncomputable def kFreeSeries (k : ℕ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, if KFree k n then (n : ℂ) ^ (-s) else 0

private theorem geometric_factor {t : ℂ} {k : ℕ} (hk : 0 < k) (ht : ‖t‖ < 1) :
    (∑ j ∈ range k, t ^ j) * (1 - t ^ k)⁻¹ = (1 - t)⁻¹ := by
  have h₁ : 1 - t ≠ 0 := sub_ne_zero.mpr (fun h ↦ by simp [← h] at ht)
  have h₂ : 1 - t ^ k ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    have ht' : ‖t ^ k‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) ht hk.ne'
    simp [← h] at ht'
  field_simp
  simpa [mul_comm] using geom_sum_mul_neg t k

/-- Equality on the half-plane of absolute convergence, for every k ≥ 2. -/
theorem kFreeSeries_eq_quotient {k : ℕ} (hk : 2 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    kFreeSeries k s = zetaQuotient k s := by
  have hk' : 0 < k := by omega
  have hks : 1 < ((k : ℂ) * s).re := by
    simp only [mul_re, natCast_re, natCast_im, zero_mul, sub_zero]
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    exact hs.trans_le (le_mul_of_one_le_left (by linarith) hkR)
  let z := riemannZetaSummandHom (ne_zero_of_one_lt_re hs)
  let f := fun n : ℕ ↦ if KFree k n then z n else 0
  have hsum : Summable (fun n ↦ ‖f n‖) :=
    (summable_riemannZetaSummand hs).of_nonneg_of_le (fun _ ↦ norm_nonneg _) (by
      intro n
      by_cases h : KFree k n <;> simp [f, z, h])
  have h₁ : f 1 = 1 := by simp [f,kFree_one hk']
  have hmul {a b : ℕ} (hab : a.Coprime b) : f (a*b) = f a * f b := by
    by_cases ha : KFree k a <;> by_cases hb : KFree k b <;> simp [f,kFree_mul hk' hab,ha,hb]
  have h₀ : f 0 = 0 := by simp [f]
  have hprod := EulerProduct.eulerProduct_hasProd h₁ (fun h ↦ hmul h) hsum h₀
  have atPrime (p : Nat.Primes) :
      (∑' e : ℕ, f (p ^ e)) = ∑ j ∈ range k, (z p) ^ j := by
    rw [tsum_eq_sum (s := range k) (fun e he ↦ by
      simp only [Finset.mem_range] at he
      simp [f, kFree_prime_pow hk' p.property, he])]
    apply sum_congr rfl
    intro i hi
    simp [f, kFree_prime_pow hk' p.property, Finset.mem_range.mp hi]
  have hzprod := riemannZeta_eulerProduct_hasProd hks
  have finalp : HasProd (fun p : Nat.Primes ↦ (1 - (p : ℂ) ^ (-s))⁻¹)
      ((∑' n : ℕ, f n) * riemannZeta ((k : ℂ)*s)) := by
    convert hprod.mul hzprod using 1
    funext p
    rw [atPrime]
    have hn : ‖z p‖ < 1 := (summable_riemannZetaSummand hs).of_norm.norm_lt_one
      (f := z.toMonoidHom) p.property.one_lt
    have hpows : (p : ℂ) ^ (-((k : ℂ) * s)) = (z p) ^ k := by
      rw [← mul_neg, cpow_nat_mul]
      rfl
    rw [hpows]
    exact (geometric_factor hk' hn).symm
  have equal := finalp.unique (riemannZeta_eulerProduct_hasProd hs)
  change (∑' n : ℕ, f n) = riemannZeta s / riemannZeta ((k : ℂ) * s)
  exact (eq_div_iff (riemannZeta_ne_zero_of_one_le_re hks.le)).mpr equal

end PowerFree

namespace PowerFree

open Complex Finset Filter Asymptotics MeasureTheory
open scoped Classical Topology

/-- The number of positive k-free integers up to and including n. -/
noncomputable def kFreeCount (k n : ℕ) : ℕ :=
  ((Icc 1 n).filter (KFree k)).card

/-- On its half-plane of convergence the Mellin integral of the actual counting
function is the zeta quotient divided by s. -/
theorem mellin_kFreeCount {k : ℕ} (hk : 2 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    (∫ t in Set.Ioi (1 : ℝ), (kFreeCount k ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1))) =
      zetaQuotient k s / s := by
  let f := fun n : ℕ ↦ if KFree k n then (1 : ℂ) else 0
  have hO : (fun n ↦ ∑ j ∈ Icc 1 n, ‖f j‖) =O[atTop] fun n ↦ (n : ℝ) ^ (1 : ℝ) := by
    apply isBigO_of_le
    intro n
    have hnorm (j : ℕ) : ‖f j‖ ≤ 1 := by by_cases h : KFree k j <;> simp [f,h]
    simp only [Real.rpow_one, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n),
      abs_of_nonneg (Finset.sum_nonneg (fun j _ ↦ norm_nonneg (f j)))]
    calc
      ∑ j ∈ Icc 1 n, ‖f j‖ ≤ ∑ _j ∈ Icc 1 n, (1 : ℝ) := sum_le_sum (fun j _ ↦ hnorm j)
      _ = n := by simp
  have hseries : LSeries f s = kFreeSeries k s := by
    apply tsum_congr
    intro n
    rw [LSeries.term_of_ne_zero' (ne_zero_of_one_lt_re hs)]
    by_cases hn : KFree k n <;> simp [f, hn, cpow_neg]
  have hsum (n : ℕ) : ∑ j ∈ Icc 1 n, f j = (kFreeCount k n : ℂ) := by
    simp [f, kFreeCount]
  have hi := LSeries_eq_mul_integral' f (by norm_num : (0 : ℝ) ≤ 1) hs hO
  simp_rw [hsum] at hi
  rw [hseries, kFreeSeries_eq_quotient hk hs] at hi
  exact (eq_div_iff (ne_zero_of_one_lt_re hs)).mpr (by simpa [mul_comm] using hi.symm)

end PowerFree

namespace PowerFree

open Complex Filter Finset
open scoped Topology

/-- A zero of order m has analytic factor g with m! g(x) = f⁽ᵐ⁾(x). -/
private theorem analytic_zero_factor {f : ℂ → ℂ} {x : ℂ} {m : ℕ}
    (hf : AnalyticAt ℂ f x) (hm : analyticOrderAt f x = m) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g x ∧ g x ≠ 0 ∧
      (f =ᶠ[𝓝 x] fun z ↦ (z-x)^m * g z) ∧
      iteratedDeriv m f x = (m.factorial : ℂ) * g x := by
  obtain ⟨g, hg, hg₀, eqn⟩ := hf.analyticOrderAt_eq_natCast.mp hm
  have he : f =ᶠ[𝓝 x] fun z ↦ (z - x) ^ m * g z := by
    filter_upwards [eqn] with z hz
    simpa only [smul_eq_mul] using hz
  refine ⟨g, hg, hg₀, he, ?_⟩
  have shifted (i : ℕ) : iteratedDeriv i (fun z : ℂ ↦ (z-x)^m) x =
      if i = m then (m.factorial : ℂ) else 0 := by
    have d := congrFun (iteratedDeriv_comp_sub_const i (fun v : ℂ ↦ v ^ m) x) x
    simp only [sub_self, iteratedDeriv_fun_pow_zero] at d
    by_cases h : i = m <;> simpa [h] using d
  rw [he.iteratedDeriv_eq m, iteratedDeriv_fun_mul (by fun_prop) hg.contDiffAt]
  rw [sum_eq_single m]
  · simp [shifted]
  · intro i _ him
    simp [shifted, him]
  · simp

private theorem scaled_regular (rh : RiemannHypothesis) {k : ℕ} (hk : 2 ≤ k) {ρ : ℂ}
    (hρ : 0 < ρ.re) (hz : riemannZeta ρ = 0) :
    AnalyticAt ℂ riemannZeta (ρ / (k : ℂ)) ∧ riemannZeta (ρ / (k : ℂ)) ≠ 0 := by
  let x := ρ / (k : ℂ)
  have hline : x.re = 1 / (2 * (k : ℝ)) := (multiplicity_of_RH rh hk hρ hz).1
  have hpos : 0 < x.re := by rw [hline]; positivity
  have hkR : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hlt : x.re < 1/2 := by
    rw [hline]
    apply one_div_lt_one_div_of_lt (by norm_num)
    linarith
  have h₁ : x ≠ 1 := by
    intro e
    rw [e] at hlt
    norm_num at hlt
  refine ⟨analyticOn_riemannZeta _ h₁, ?_⟩
  intro h
  apply hlt.ne
  apply rh x h _ h₁
  rintro ⟨n, e⟩
  rw [e] at hpos
  have hnon : (-2 * ((n : ℂ) + 1)).re ≤ 0 := by
    norm_num [mul_re]
    positivity
  exact (not_lt_of_ge hnon) hpos

/-- Each positive-real-part zeta zero has a positive, finite analytic order. -/
theorem analytic_order_at_zero (rh : RiemannHypothesis) {ρ : ℂ}
    (hρ : 0 < ρ.re) (hz : riemannZeta ρ = 0) :
    0 < analyticOrderNatAt riemannZeta ρ ∧
    analyticOrderAt riemannZeta ρ = (analyticOrderNatAt riemannZeta ρ : ℕ) := by
  have h₁ : ρ ≠ 1 := fun e ↦ riemannZeta_one_ne_zero (e ▸ hz)
  have ha := analyticOn_riemannZeta ρ h₁
  have hp := (multiplicity_of_RH rh (k := 2) le_rfl hρ hz).2.1
  have hfin : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
    intro ht
    simp [zetaOrder, ha.meromorphicOrderAt_eq, ht] at hp
  have hcast := (Nat.cast_analyticOrderNatAt hfin).symm
  refine ⟨Nat.pos_of_ne_zero (fun he ↦ ?_), hcast⟩
  rw [he, Nat.cast_zero] at hcast
  exact (ha.analyticOrderAt_eq_zero.mp hcast) hz

/-- The normalized quotient tends to its exact nonzero leading Laurent coefficient.
The order m is attached to the individual zero and may exceed one. -/
theorem leading_coefficient_of_RH (rh : RiemannHypothesis)
    {k : ℕ} (hk : 2 ≤ k) {ρ : ℂ} (hρ : 0 < ρ.re) (hz : riemannZeta ρ = 0)
    {m : ℕ} (hm : analyticOrderAt riemannZeta ρ = m) :
    let x := ρ / (k : ℂ)
    let c := (m.factorial : ℂ) * riemannZeta x /
      ((k : ℂ) ^ m * iteratedDeriv m riemannZeta ρ)
    c ≠ 0 ∧ Tendsto (fun s : ℂ ↦ (s-x)^m * zetaQuotient k s) (𝓝[≠] x) (𝓝 c) := by
  let x := ρ / (k : ℂ)
  have h₁ : ρ ≠ 1 := fun e ↦ riemannZeta_one_ne_zero (e ▸ hz)
  have hk₀ : (k : ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hkx : (k : ℂ) * x = ρ := by dsimp [x]; field_simp
  obtain ⟨g, hg, hg₀, hfg, hder⟩ := analytic_zero_factor (analyticOn_riemannZeta _ h₁) hm
  obtain ⟨hx, hnum⟩ := scaled_regular rh hk hρ hz
  have hfac : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hscale : Tendsto (fun s : ℂ ↦ (k : ℂ) * s) (𝓝[≠] x) (𝓝 ρ) := by
    rw [← hkx]
    exact (continuousAt_const.mul continuousAt_id).continuousWithinAt.tendsto
  have hlim : Tendsto (fun s : ℂ ↦ riemannZeta s / ((k : ℂ)^m * g ((k : ℂ)*s)))
      (𝓝[≠] x) (𝓝 (riemannZeta x / ((k : ℂ)^m * g ρ))) :=
    hx.continuousAt.continuousWithinAt.tendsto.div
      (tendsto_const_nhds.mul (hg.continuousAt.tendsto.comp hscale)) (mul_ne_zero (pow_ne_zero _ hk₀) hg₀)
  dsimp only
  change _ ≠ 0 ∧ Tendsto _ (𝓝[≠] x) _
  rw [hder]
  constructor
  · exact div_ne_zero (mul_ne_zero hfac hnum) (mul_ne_zero (pow_ne_zero _ hk₀) (mul_ne_zero hfac hg₀))
  · have hc : (m.factorial : ℂ) * riemannZeta x /
          ((k : ℂ)^m * ((m.factorial : ℂ) * g ρ)) = riemannZeta x / ((k : ℂ)^m * g ρ) := by
      field_simp
    rw [show (m.factorial : ℂ) * riemannZeta (ρ / (k : ℂ)) /
      ((k : ℂ)^m * ((m.factorial : ℂ) * g ρ)) = _ from hc]
    apply hlim.congr'
    filter_upwards [hscale.eventually hfg, hscale.eventually (hg.continuousAt.eventually_ne hg₀),
      self_mem_nhdsWithin] with s hs hn hsx
    have hd : s - x ≠ 0 := sub_ne_zero.mpr hsx
    have he : (k : ℂ)*s - ρ = (k : ℂ)*(s-x) := by rw [mul_sub, hkx]
    change riemannZeta s / ((k : ℂ)^m * g ((k : ℂ)*s)) =
      (s-x)^m * (riemannZeta s / riemannZeta ((k : ℂ)*s))
    rw [hs, he, mul_pow]
    field_simp

/-- The simple-zero specialization gives the residue of the generating series. -/
theorem residue_at_scaled_zero_of_RH (rh : RiemannHypothesis) {k : ℕ} (hk : 2 ≤ k)
    {ρ : ℂ} (hρ : 0 < ρ.re) (hz : riemannZeta ρ = 0) (hd : deriv riemannZeta ρ ≠ 0) :
    let x := ρ / (k : ℂ)
    let c := riemannZeta x / ((k : ℂ) * deriv riemannZeta ρ)
    c ≠ 0 ∧ Tendsto (fun s : ℂ ↦ (s-x) * zetaQuotient k s) (𝓝[≠] x) (𝓝 c) := by
  have h₁ : ρ ≠ 1 := fun e ↦ riemannZeta_one_ne_zero (e ▸ hz)
  have hm := (analyticOn_riemannZeta _ h₁).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hz hd
  simpa using leading_coefficient_of_RH rh hk hρ hz (m := 1) (by simpa using hm)

/-- At a simple zero this is the residue of the continued Mellin integral
of the counting function, the coefficient in the explicit formula. -/
theorem perron_residue_of_RH (rh : RiemannHypothesis) {k : ℕ} (hk : 2 ≤ k)
    {ρ : ℂ} (hρ : 0 < ρ.re) (hz : riemannZeta ρ = 0) (hd : deriv riemannZeta ρ ≠ 0) :
    let x := ρ / (k : ℂ)
    let c := riemannZeta x / (ρ * deriv riemannZeta ρ)
    c ≠ 0 ∧ Tendsto (fun s : ℂ ↦ (s-x) * (zetaQuotient k s / s)) (𝓝[≠] x) (𝓝 c) := by
  let x := ρ / (k : ℂ)
  have hk₀ : (k : ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hρ₀ : ρ ≠ 0 := by intro e; simp [e] at hρ
  have hx₀ : x ≠ 0 := div_ne_zero hρ₀ hk₀
  obtain ⟨hn, ht⟩ := residue_at_scaled_zero_of_RH rh hk hρ hz hd
  have hc : riemannZeta x / ((k : ℂ) * deriv riemannZeta ρ) / x =
      riemannZeta x / (ρ * deriv riemannZeta ρ) := by dsimp [x]; field_simp
  constructor
  · rw [← hc]
    exact div_ne_zero hn hx₀
  · have hi : Tendsto (fun s : ℂ ↦ s) (𝓝[≠] x) (𝓝 x) := continuousAt_id.continuousWithinAt
    change Tendsto (fun s : ℂ ↦ (s-x) * (zetaQuotient k s / s)) (𝓝[≠] x)
      (𝓝 (riemannZeta x / (ρ * deriv riemannZeta ρ)))
    rw [← hc]
    have ht' : Tendsto (fun s : ℂ ↦ (s-x) * zetaQuotient k s) (𝓝[≠] x)
        (𝓝 (riemannZeta x / ((k : ℂ) * deriv riemannZeta ρ))) := ht
    simpa only [Pi.div_def, ← mul_div_assoc] using ht'.div hi hx₀

/-- The main-term residue at 1 is independent of RH. -/
theorem residue_at_one {k : ℕ} (hk : 2 ≤ k) :
    Tendsto (fun s : ℂ ↦ (s-1) * zetaQuotient k s) (𝓝[≠] 1) (𝓝 (1 / riemannZeta k)) := by
  have hkR : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hk₁ : (k : ℂ) ≠ 1 := by
    intro e
    have := congrArg Complex.re e
    simp at this
    linarith
  have hs : Tendsto (fun s : ℂ ↦ (k : ℂ) * s) (𝓝[≠] 1) (𝓝 (k : ℂ)) := by
    simpa only [Pi.mul_def, id_eq, mul_one] using (continuousAt_const.mul (continuousAt_id (x := (1 : ℂ)))).continuousWithinAt.tendsto
  have hden := (analyticOn_riemannZeta _ hk₁).continuousAt.tendsto.comp hs
  have hne := riemannZeta_ne_zero_of_one_le_re (s := (k : ℂ)) (by simpa using hkR.le)
  simpa only [zetaQuotient, Pi.div_def, Function.comp_apply, ← mul_div_assoc] using
    riemannZeta_residue_one.div hden hne

end PowerFree

namespace PowerFree.Target

open Complex Filter
open scoped Topology

def analytic_order_at_zero : Prop :=
  ∀ {ρ : ℂ} (_ : 0 < ρ.re) (_ : riemannZeta ρ = 0),
    0 < analyticOrderNatAt riemannZeta ρ ∧
    analyticOrderAt riemannZeta ρ = (analyticOrderNatAt riemannZeta ρ : ℕ)

def leading_coefficient : Prop :=
  ∀ {k : ℕ} (_ : 2 ≤ k) {ρ : ℂ} (_ : 0 < ρ.re) (_ : riemannZeta ρ = 0)
    {m : ℕ} (_ : analyticOrderAt riemannZeta ρ = m),
    let x := ρ / (k : ℂ)
    let c := (m.factorial : ℂ) * riemannZeta x / ((k : ℂ)^m * iteratedDeriv m riemannZeta ρ)
    c ≠ 0 ∧ Tendsto (fun s : ℂ ↦ (s-x)^m * zetaQuotient k s) (𝓝[≠] x) (𝓝 c)

def simple_residue : Prop :=
  ∀ {k : ℕ} (_ : 2 ≤ k) {ρ : ℂ} (_ : 0 < ρ.re) (_ : riemannZeta ρ = 0)
    (_ : deriv riemannZeta ρ ≠ 0),
    let x := ρ / (k : ℂ)
    let c := riemannZeta x / ((k : ℂ) * deriv riemannZeta ρ)
    c ≠ 0 ∧ Tendsto (fun s : ℂ ↦ (s-x) * zetaQuotient k s) (𝓝[≠] x) (𝓝 c)

def perron_residue : Prop :=
  ∀ {k : ℕ} (_ : 2 ≤ k) {ρ : ℂ} (_ : 0 < ρ.re) (_ : riemannZeta ρ = 0)
    (_ : deriv riemannZeta ρ ≠ 0),
    let x := ρ / (k : ℂ)
    let c := riemannZeta x / (ρ * deriv riemannZeta ρ)
    c ≠ 0 ∧ Tendsto (fun s : ℂ ↦ (s-x) * (zetaQuotient k s / s)) (𝓝[≠] x) (𝓝 c)

end PowerFree.Target
