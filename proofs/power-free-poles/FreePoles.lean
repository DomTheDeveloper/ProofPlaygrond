module

public import PoleDescent
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

@[expose] public section

/-!
# The poles of the Dirichlet series for power-free integers

For an integer k ≥ 2 the generating function of k-free integers on Re(s) > 1
continues as ζ(s)/ζ(k s). Orders below are meromorphic orders of germs, so
the values assigned by Lean to quotients at individual singularities play no role.
-/
set_option autoImplicit false

namespace PowerFree

open Complex Filter Set WithTop.LinearOrderedAddCommGroup
open scoped Topology

/-- The meromorphic continuation ζ(s)/ζ(k s). -/
noncomputable def zetaQuotient (k : ℕ) : ℂ → ℂ :=
  riemannZeta / (riemannZeta ∘ fun s : ℂ ↦ (k : ℂ) * s)

private theorem zeta_analytic {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s :=
  analyticOn_riemannZeta s hs

private theorem at_one_factor :
    riemannZeta =ᶠ[𝓝[≠] (1 : ℂ)] fun z ↦ (z - 1)⁻¹ * riemannZeta₁ z := by
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact riemannZeta_eq_inv_sub_mul hz

private theorem zeta_meromorphic (s : ℂ) : MeromorphicAt riemannZeta s := by
  rcases eq_or_ne s 1 with rfl | hs
  · exact (((analyticAt_id.sub analyticAt_const).meromorphicAt.inv).mul
      ((differentiable_riemannZeta₁.analyticAt 1).meromorphicAt)).congr at_one_factor.symm
  · exact (zeta_analytic hs).meromorphicAt

private theorem order_at_one : meromorphicOrderAt riemannZeta 1 = -1 := by
  apply (meromorphicOrderAt_eq_int_iff (n := -1) (zeta_meromorphic 1)).mpr
  exact ⟨riemannZeta₁, differentiable_riemannZeta₁.analyticAt 1, by simp,
    by
      filter_upwards [at_one_factor] with z hz
      simpa only [zpow_neg_one, smul_eq_mul] using hz⟩

private theorem finite_order (s : ℂ) : meromorphicOrderAt riemannZeta s ≠ ⊤ := by
  have hm : MeromorphicOn riemannZeta univ := fun z _ ↦ zeta_meromorphic z
  exact hm.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (mem_univ (1 : ℂ)) (mem_univ s) (by simp [order_at_one])

/-- The signed integer order of ζ. Its only pole is counted with order −1. -/
noncomputable def zetaOrder (s : ℂ) : ℤ := (meromorphicOrderAt riemannZeta s).untop₀

private theorem cast_order (s : ℂ) :
    (zetaOrder s : WithTop ℤ) = meromorphicOrderAt riemannZeta s :=
  WithTop.coe_untop₀_of_ne_top (finite_order s)

private theorem order_one : zetaOrder 1 = -1 := by
  unfold zetaOrder
  rw [order_at_one]
  rfl

private theorem order_nonneg {s : ℂ} (hs : s ≠ 1) : 0 ≤ zetaOrder s := by
  have h := (zeta_analytic hs).meromorphicOrderAt_nonneg
  rw [← cast_order] at h
  exact_mod_cast h

private theorem order_zero {s : ℂ} (hs : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    zetaOrder s = 0 := by
  have a := zeta_analytic hs
  have h : meromorphicOrderAt riemannZeta s = 0 := by
    simp [a.meromorphicOrderAt_eq, a.analyticOrderAt_eq_zero.mpr hz]
  exact_mod_cast (cast_order s).trans h

private theorem order_pos {s : ℂ} (hz : riemannZeta s = 0) : 0 < zetaOrder s := by
  have hs : s ≠ 1 := fun e ↦ riemannZeta_one_ne_zero (e ▸ hz)
  have ht : Tendsto riemannZeta (𝓝[≠] s) (𝓝 0) := by
    simpa only [hz] using (zeta_analytic hs).continuousAt.continuousWithinAt.tendsto
  have h := (tendsto_zero_iff_meromorphicOrderAt_pos (zeta_meromorphic s)).mp ht
  rw [← cast_order] at h
  exact_mod_cast h

/-- Scaling by a nonzero integer preserves the denominator's order. -/
theorem quotient_order {k : ℕ} (hk : 0 < k) (s : ℂ) :
    meromorphicOrderAt (zetaQuotient k) s =
      ((zetaOrder s - zetaOrder ((k : ℂ) * s) : ℤ) : WithTop ℤ) := by
  let scale := fun z : ℂ ↦ (k : ℂ) * z
  have ha : AnalyticAt ℂ scale s := analyticAt_const.mul analyticAt_id
  have hd : deriv scale s ≠ 0 := by
    have h := (hasDerivAt_id s).const_mul (k : ℂ)
    simpa [scale, h.deriv] using (show (k : ℂ) ≠ 0 by exact_mod_cast hk.ne')
  change meromorphicOrderAt (riemannZeta / (riemannZeta ∘ scale)) s = _
  rw [meromorphicOrderAt_div (zeta_meromorphic s) ((zeta_meromorphic _).comp_analyticAt ha),
      meromorphicOrderAt_comp_of_deriv_ne_zero ha hd, WithTop.LinearOrderedAddCommGroup.coe_sub,
      cast_order, cast_order]

private theorem re_of_zero (rh : RiemannHypothesis) {s : ℂ}
    (hs : 0 < s.re) (hz : riemannZeta s = 0) : s.re = 1 / 2 := by
  apply rh s hz _ (fun e ↦ riemannZeta_one_ne_zero (e ▸ hz))
  rintro ⟨n, rfl⟩
  have hneg : (-2 * ((n : ℂ) + 1)).re ≤ 0 := by
    norm_num [mul_re]
    positivity
  exact (not_lt_of_ge hneg) hs

private theorem scaled_re (k : ℕ) (s : ℂ) :
    ((k : ℂ) * s).re = (k : ℝ) * s.re := by simp [mul_re]

private theorem re_div_nat {k : ℕ} (s : ℂ) :
    (s / (k : ℂ)).re = s.re / (k : ℝ) := by
  rw [show (k : ℂ) = ((k : ℝ) : ℂ) by norm_cast, Complex.div_ofReal_re]

private theorem cancel_scale {k : ℕ} (hk : 0 < k) (s : ℂ) :
    (k : ℂ) * (s / (k : ℂ)) = s := by
  have h : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  field_simp

private theorem scaled_facts (rh : RiemannHypothesis) {k : ℕ} (hk : 2 ≤ k) {s : ℂ}
    (hs : 0 < s.re) (hz : riemannZeta ((k : ℂ) * s) = 0) :
    s.re = 1 / (2 * (k : ℝ)) ∧ zetaOrder s = 0 := by
  have h₁ : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have h₂ : (k : ℝ) * s.re = 1 / 2 := by
    rw [← scaled_re]
    exact re_of_zero rh (by rw [scaled_re]; positivity) hz
  have hlt : s.re < 1 / 2 := calc
    s.re < (k : ℝ) * s.re := lt_mul_of_one_lt_left hs h₁
    _ = _ := h₂
  refine ⟨(eq_div_iff (by positivity)).mpr (by nlinarith), ?_⟩
  apply order_zero
  · rintro rfl
    norm_num at hlt
  · exact fun h ↦ hlt.ne (re_of_zero rh hs h)

private theorem order_nat {k : ℕ} (hk : 2 ≤ k) : zetaOrder (k : ℂ) = 0 := by
  have h : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  apply order_zero
  · exact fun e ↦ h.ne' (by simpa using congrArg Complex.re e)
  · exact riemannZeta_ne_zero_of_one_le_re (by simpa using h.le)

private theorem pole_iff_lt {k : ℕ} (hk : 0 < k) {s : ℂ} :
    meromorphicOrderAt (zetaQuotient k) s < 0 ↔
      zetaOrder s < zetaOrder ((k : ℂ) * s) := by
  rw [quotient_order hk]
  exact_mod_cast (sub_neg : zetaOrder s - zetaOrder ((k : ℂ) * s) < 0 ↔ _)

/-- In the right half-plane the only poles are 1 and the scaled zeta zeros. -/
theorem poles_of_RH (rh : RiemannHypothesis) {k : ℕ} (hk : 2 ≤ k) {s : ℂ} (hs : 0 < s.re) :
    meromorphicOrderAt (zetaQuotient k) s < 0 ↔
      s = 1 ∨ riemannZeta ((k : ℂ) * s) = 0 := by
  rw [pole_iff_lt (by omega : 0 < k)]
  by_cases he : s = 1
  · subst s
    simp [order_one, order_nat hk]
  by_cases hz : riemannZeta ((k : ℂ) * s) = 0
  · simp [hz, (scaled_facts rh hk hs hz).2, order_pos hz]
  · simp only [he, hz, or_self, iff_false, not_lt]
    have hn := order_nonneg he
    rcases eq_or_ne ((k : ℂ) * s) 1 with e | e
    · rw [e, order_one]
      omega
    · simpa only [order_zero e hz] using hn

/-- Every zero with positive real part gives a pole of exactly its multiplicity. -/
theorem multiplicity_of_RH (rh : RiemannHypothesis) {k : ℕ} (hk : 2 ≤ k) {ρ : ℂ}
    (hρ : 0 < ρ.re) (hz : riemannZeta ρ = 0) :
    (ρ / (k : ℂ)).re = 1 / (2 * (k : ℝ)) ∧
      0 < zetaOrder ρ ∧
      meromorphicOrderAt (zetaQuotient k) (ρ / (k : ℂ)) = (-(zetaOrder ρ) : ℤ) := by
  have hk' : 0 < k := by omega
  have hpos : 0 < (ρ / (k : ℂ)).re := by rw [re_div_nat]; positivity
  have h := scaled_facts rh hk hpos (by simpa only [cancel_scale hk'] using hz)
  refine ⟨h.1, order_pos hz, ?_⟩
  rw [quotient_order hk', h.2, cancel_scale hk', zero_sub]

/-- At 1 the quotient has a simple pole. -/
theorem main_pole {k : ℕ} (hk : 2 ≤ k) :
    meromorphicOrderAt (zetaQuotient k) 1 = -1 := by
  simp [quotient_order (by omega : 0 < k), order_one, order_nat hk]

/-- A pole criterion testing only the strip 0 < Re(s) < 1/k. -/
def PoleLine (k : ℕ) : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 / (k : ℝ) →
    meromorphicOrderAt (zetaQuotient k) s < 0 → s.re = 1 / (2 * (k : ℝ))

private theorem nontrivial_zero_pos {s : ℂ} (hz : riemannZeta s = 0)
    (hnt : ¬ ∃ n : ℕ, s = -2 * (n + 1)) (h1 : s ≠ 1) : 0 < s.re := by
  by_contra! hs
  have h0 : s ≠ 0 := by
    rintro rfl
    norm_num [riemannZeta_zero] at hz
  have hg : Complex.Gammaℝ s ≠ 0 := by
    intro h
    obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp h
    cases n with
    | zero => exact h0 (by simpa using hn)
    | succ n => exact hnt ⟨n, by simpa only [Nat.cast_add_one, neg_mul] using hn⟩
  have hc : completedRiemannZeta s = 0 :=
    (div_eq_zero_iff.mp ((riemannZeta_def_of_ne_zero h0).symm.trans hz)).resolve_right hg
  apply riemannZeta_ne_zero_of_one_le_re (s := 1 - s) (by simp [sub_re]; linarith)
  rw [riemannZeta_def_of_ne_zero (sub_ne_zero.mpr h1.symm), completedRiemannZeta_one_sub, hc, zero_div]

/-- If an off-line zero gives no pole at its scaled point, the numerator must vanish there. -/
private theorem descend {k : ℕ} (hk : 2 ≤ k) (hl : PoleLine k)
    {z : ℂ} (hp : 0 < z.re) (hlt : z.re < 1) (hoff : z.re ≠ 1 / 2)
    (hz : riemannZeta z = 0) :
    0 < (z / (k : ℂ)).re ∧ (z / (k : ℂ)).re < 1 / 2 ∧
      riemannZeta (z / (k : ℂ)) = 0 := by
  have hk' : 0 < k := by omega
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkP : (0 : ℝ) < k := by positivity
  have htpos : 0 < (z / (k : ℂ)).re := by rw [re_div_nat]; positivity
  have htstrip : (z / (k : ℂ)).re < 1 / (k : ℝ) := by
    rw [re_div_nat]
    exact div_lt_div_of_pos_right hlt hkP
  have hhalf : (z / (k : ℂ)).re < 1 / 2 :=
    htstrip.trans_le (one_div_le_one_div_of_le (by norm_num) hkR)
  refine ⟨htpos, hhalf, ?_⟩
  by_contra hn
  have ht1 : z / (k : ℂ) ≠ 1 := by
    intro e
    rw [e] at hhalf
    norm_num at hhalf
  have hpol := (pole_iff_lt (s := z / (k : ℂ)) hk').mpr (by
    rw [cancel_scale hk', order_zero ht1 hn]
    exact order_pos hz)
  have e := hl _ htpos htstrip hpol
  rw [re_div_nat] at e
  apply hoff
  calc
    z.re = 1 / (2 * (k : ℝ)) * k := (div_eq_iff hkP.ne').mp e
    _ = 1 / 2 := by field_simp

/-- The reverse implication uses only the pole criterion, with no use of RH. -/
theorem RH_of_poleLine {k : ℕ} (hk : 2 ≤ k) (hl : PoleLine k) : RiemannHypothesis := by
  intro s hz hnt h1
  by_contra hoff
  have hpos := nontrivial_zero_pos hz hnt h1
  have hlt : s.re < 1 := lt_of_not_ge (fun h ↦ riemannZeta_ne_zero_of_one_le_re h hz)
  let u : ℕ → ℂ := fun n ↦ ((k : ℂ)⁻¹) ^ n * s
  have hu : ∀ n, 0 < (u n).re ∧ (u n).re < 1 ∧ (u n).re ≠ 1 / 2 ∧ riemannZeta (u n) = 0 := by
    intro n
    induction n with
    | zero => simpa only [u, pow_zero, one_mul] using And.intro hpos ⟨hlt, hoff, hz⟩
    | succ n ih =>
      obtain ⟨hp, hh, hzero⟩ := descend hk hl ih.1 ih.2.1 ih.2.2.1 ih.2.2.2
      have e : u (n + 1) = u n / (k : ℂ) := by
        simp only [u, pow_succ, div_eq_mul_inv]
        ac_rfl
      rw [e]
      exact ⟨hp, hh.trans (by norm_num), hh.ne, hzero⟩
  have hsmall : ‖(k : ℂ)⁻¹‖ < 1 := by
    have hlarge : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
    simpa using (inv_lt_one_of_one_lt₀ hlarge)
  have lim : Tendsto u atTop (𝓝 0) := by
    simpa [u] using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hsmall).mul_const s
  have hnz : riemannZeta (0 : ℂ) ≠ 0 := by norm_num [riemannZeta_zero]
  obtain ⟨n, hn⟩ := (lim.eventually ((zeta_analytic zero_ne_one).continuousAt.eventually_ne hnz)).exists
  exact hn (hu n).2.2.2

/-- For each fixed k, the pole-line condition characterizes the Riemann hypothesis. -/
theorem RH_iff_poleLine {k : ℕ} (hk : 2 ≤ k) : RiemannHypothesis ↔ PoleLine k := by
  refine ⟨?_, RH_of_poleLine hk⟩
  intro rh s hpos hlt hpol
  have hi : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  rcases (poles_of_RH rh hk hpos).mp hpol with e | hz
  · subst s
    have hsmall : 1 / (k : ℝ) < 1 :=
      (div_lt_iff₀ (by positivity)).mpr (by simpa using hi)
    exact False.elim (lt_asymm hsmall (by simpa using hlt))
  · exact (scaled_facts rh hk hpos hz).1


/-- The zero being tested after n successive divisions by k. -/
noncomputable def scaledPoint (k : ℕ) (ρ : ℂ) (n : ℕ) : ℂ :=
  ((k : ℂ)⁻¹) ^ n * ρ

private theorem scaledPoint_succ (k : ℕ) (ρ : ℂ) (n : ℕ) :
    scaledPoint k ρ (n + 1) = scaledPoint k ρ n / (k : ℂ) := by
  simp only [scaledPoint, pow_succ, div_eq_mul_inv]
  ac_rfl

/-- Every zero in the critical strip produces a pole somewhere on its
geometric sequence of scaled points, independently of RH. At the first
nonzero numerator the full multiplicity of the preceding zero survives. -/
theorem first_pole_on_chain {k : ℕ} (hk : 2 ≤ k) {ρ : ℂ}
    (hp : 0 < ρ.re) (hlt : ρ.re < 1) (hz : riemannZeta ρ = 0) :
    ∃ j : ℕ, (∀ i ≤ j, riemannZeta (scaledPoint k ρ i) = 0) ∧
      riemannZeta (scaledPoint k ρ (j + 1)) ≠ 0 ∧
      0 < zetaOrder (scaledPoint k ρ j) ∧
      meromorphicOrderAt (zetaQuotient k) (scaledPoint k ρ (j + 1)) =
        (-(zetaOrder (scaledPoint k ρ j)) : ℤ) := by
  have hkn : 0 < k := by omega
  have hkR : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hn : ‖(k : ℂ)⁻¹‖ < 1 := by simpa using inv_lt_one_of_one_lt₀ hkR
  have lim : Tendsto (scaledPoint k ρ) atTop (𝓝 0) := by
    change Tendsto (fun n : ℕ ↦ ((k : ℂ)⁻¹) ^ n * ρ) atTop (𝓝 0)
    simpa only [zero_mul] using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hn).mul_const ρ
  have hzero : riemannZeta (0 : ℂ) ≠ 0 := by norm_num [riemannZeta_zero]
  obtain ⟨N, hN⟩ := (lim.eventually
    ((zeta_analytic zero_ne_one).continuousAt.eventually_ne hzero)).exists
  have atStart : riemannZeta (scaledPoint k ρ 0) = 0 := by simpa [scaledPoint] using hz
  obtain ⟨j, _, initialZeros, after⟩ := first_exit (P := fun n ↦ riemannZeta (scaledPoint k ρ n) = 0)
    atStart hN
  have strip (n : ℕ) : 0 < (scaledPoint k ρ n).re ∧ (scaledPoint k ρ n).re < 1 := by
    induction n with
    | zero => simpa [scaledPoint] using And.intro hp hlt
    | succ n ih =>
      rw [scaledPoint_succ, re_div_nat]
      exact ⟨div_pos ih.1 (by positivity), (div_lt_one (by positivity)).mpr (ih.2.trans hkR)⟩
  have hne : scaledPoint k ρ (j + 1) ≠ 1 := by
    intro e
    have h := (strip (j + 1)).2
    simp only [e, one_re, lt_self_iff_false] at h
  refine ⟨j, initialZeros, after, order_pos (initialZeros j le_rfl), ?_⟩
  rw [quotient_order hkn, order_zero hne after, scaledPoint_succ, cancel_scale hkn, zero_sub]

/-- The pole line for the squarefree case. -/
theorem squarefree_pole_line_of_RH (rh : RiemannHypothesis) {s : ℂ} (h₀ : 0 < s.re)
    (h₁ : s.re < 1 / 2) (h : meromorphicOrderAt (zetaQuotient 2) s < 0) : s.re = 1 / 4 := by
  have hl := (RH_iff_poleLine (k := 2) (by decide)).mp rh
  convert hl s h₀ h₁ h using 1
  norm_num

end PowerFree
