module

public import FreePoles
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

@[expose] public section

namespace PowerFree

open Complex Filter
open scoped Topology Classical

/-- The negative even integers, written in Mathlib's convention for trivial zeros. -/
def TrivialZero (s : ℂ) : Prop := ∃ n : ℕ, s = -2 * ((n : ℂ) + 1)

private theorem trivial_re_neg {s : ℂ} (h : TrivialZero s) : s.re < 0 := by
  obtain ⟨n, rfl⟩ := h
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  norm_num [mul_re]
  linarith

private theorem positive_avoids_neg_nat {u : ℂ} (h : 0 < u.re) (n : ℕ) : u ≠ -n := by
  intro e
  rw [e] at h
  simp only [neg_re, natCast_re] at h
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-- On the open left half-plane the functional equation exhibits any zeta zero as a
simple cosine zero multiplied by an analytic, nonzero function. -/
theorem negative_zero_deriv {x : ℂ} (hx : x.re < 0) (hz : riemannZeta x = 0) :
    deriv riemannZeta x ≠ 0 := by
  let u := fun z : ℂ ↦ 1 - z
  let p : ℂ := Real.pi
  let A := fun z : ℂ ↦ 2 * (2*p) ^ (-u z) * Gamma (u z) * riemannZeta (u z)
  let t := fun z : ℂ ↦ p * u z / 2
  have hright {z : ℂ} (h : z.re < 0) : 1 < (u z).re := by
    dsimp [u, sub_re]
    linarith
  have hu1 {z : ℂ} (h : z.re < 0) : u z ≠ 1 := fun e ↦ (hright h).ne' (by rw [e]; simp)
  have he : riemannZeta =ᶠ[𝓝 x] fun z ↦ A z * cos (t z) := by
    filter_upwards [(isOpen_lt continuous_re continuous_const).mem_nhds hx] with z hz'
    have e := riemannZeta_one_sub (positive_avoids_neg_nat (lt_trans zero_lt_one (hright hz'))) (hu1 hz')
    calc
      riemannZeta z = riemannZeta (1-u z) := by dsimp [u]; congr 1; ring
      _ = _ := e
      _ = A z * cos (t z) := by dsimp [A,t,p,u]; ring
  have hp : p ≠ 0 := by dsimp [p]; exact_mod_cast Real.pi_ne_zero
  have hb : 2*p ≠ 0 := mul_ne_zero two_ne_zero hp
  have hgn := positive_avoids_neg_nat (lt_trans zero_lt_one (hright hx))
  have hn : A x ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero
    (cpow_ne_zero_iff.mpr (Or.inl hb))) (Gamma_ne_zero hgn))
    (riemannZeta_ne_zero_of_one_le_re (hright hx).le)
  have hcos : cos (t x) = 0 := (mul_eq_zero.mp (he.eq_of_nhds.symm.trans hz)).resolve_left hn
  have hsin : sin (t x) ≠ 0 := by
    intro e
    have h := sin_sq_add_cos_sq (t x)
    simp [e,hcos] at h
  have hu : HasDerivAt u (-1) x := by
    simpa [u, Pi.sub_def] using (hasDerivAt_const x (1 : ℂ)).sub (hasDerivAt_id x)
  have ht : HasDerivAt t (-p/2) x := by
    simpa [t] using (hu.const_mul p).div_const 2
  have hA : DifferentiableAt ℂ A x :=
    (((differentiableAt_const (c := (2 : ℂ))).mul
      (hu.neg.const_cpow (c := 2*p) (Or.inl hb)).differentiableAt).mul
      ((differentiableAt_Gamma _ hgn).comp x hu.differentiableAt)).mul
      ((differentiableAt_riemannZeta (hu1 hx)).comp x hu.differentiableAt)
  have hC := (hasDerivAt_cos (t x)).comp x ht
  have hD := (hA.hasDerivAt.mul hC).congr_of_eventuallyEq he
  rw [hD.deriv, Function.comp_apply, hcos, mul_zero, zero_add]
  simpa using mul_ne_zero hn (mul_ne_zero (neg_ne_zero.mpr hsin) (div_ne_zero (neg_ne_zero.mpr hp) two_ne_zero))

private theorem left_ne_one {s : ℂ} (hs : s.re ≤ 0) : s ≠ 1 := by
  rintro rfl
  norm_num at hs

private theorem left_zero_iff (rh : RiemannHypothesis) {s : ℂ} (hs : s.re ≤ 0) :
    riemannZeta s = 0 ↔ TrivialZero s := by
  constructor
  · intro hz
    by_contra ht
    have h := rh s hz ht (left_ne_one hs)
    linarith
  · rintro ⟨n,rfl⟩
    exact riemannZeta_neg_two_mul_nat_add_one n

private theorem left_zeta_order (rh : RiemannHypothesis) {s : ℂ} (hs : s.re ≤ 0) :
    zetaOrder s = if TrivialZero s then 1 else 0 := by
  have ha := analyticOn_riemannZeta s (left_ne_one hs)
  by_cases h : TrivialZero s
  · have hz := (left_zero_iff rh hs).2 h
    have hm := ha.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hz (negative_zero_deriv (trivial_re_neg h) hz)
    simp [zetaOrder, ha.meromorphicOrderAt_eq, h, hm]
  · have hz : riemannZeta s ≠ 0 := fun hz ↦ h ((left_zero_iff rh hs).1 hz)
    simp [zetaOrder, ha.meromorphicOrderAt_eq, ha.analyticOrderAt_eq_zero.mpr hz, h]

/-- On and to the left of the imaginary axis, the orders are the difference of two indicators. -/
theorem left_order_of_RH (rh : RiemannHypothesis) {k : ℕ} (hk : 2 ≤ k) {s : ℂ} (hs : s.re ≤ 0) :
    meromorphicOrderAt (zetaQuotient k) s =
      (((if TrivialZero s then 1 else 0) - (if TrivialZero ((k : ℂ)*s) then 1 else 0) : ℤ) : WithTop ℤ) := by
  have hks : ((k : ℂ)*s).re ≤ 0 := by simpa [mul_re] using mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg (α := ℝ) k) hs
  rw [quotient_order (by omega : 0 < k), left_zeta_order rh hs, left_zeta_order rh hks]

/-- Every pole in the complex plane. The final case is exactly an uncancelled trivial zero. -/
theorem global_poles_of_RH (rh : RiemannHypothesis) {k : ℕ} (hk : 2 ≤ k) (s : ℂ) :
    meromorphicOrderAt (zetaQuotient k) s < 0 ↔
      s = 1 ∨ (0 < s.re ∧ riemannZeta ((k : ℂ)*s) = 0) ∨ (TrivialZero ((k : ℂ)*s) ∧ ¬ TrivialZero s) := by
  by_cases hs : 0 < s.re
  · have hks : 0 < ((k : ℂ)*s).re := by
      simp only [mul_re, natCast_re, natCast_im, zero_mul, sub_zero]
      exact mul_pos (by exact_mod_cast (show 0 < k by omega)) hs
    have ht : ¬TrivialZero ((k : ℂ)*s) := fun h ↦ (trivial_re_neg h).asymm hks
    rw [poles_of_RH rh hk hs]
    simp [hs,ht]
  · rw [left_order_of_RH rh hk (le_of_not_gt hs)]
    have hn := left_ne_one (le_of_not_gt hs)
    by_cases h₁ : TrivialZero s <;> by_cases h₂ : TrivialZero ((k : ℂ)*s) <;>
      norm_num [h₁,h₂,hs,hn]
    change ((-1 : ℤ) : WithTop ℤ) < ((0 : ℤ) : WithTop ℤ)
    exact WithTop.coe_lt_coe.mpr (show (-1 : ℤ) < 0 by decide)

/-- A negative denominator zero cancels precisely at the specified divisibility indices. -/
theorem trivial_on_grid_iff {n k : ℕ} (hn : 0 < n) (hk : 2 ≤ k) :
    TrivialZero ((-2 : ℂ)*n/k) ↔ k ∣ n := by
  have hk₀ : (k : ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  constructor
  · rintro ⟨m, e⟩
    have h := (div_eq_iff hk₀).mp e
    have h' : (-2 : ℂ)*n = -2*((k : ℂ)*((m : ℂ)+1)) := h.trans (by ring)
    have hc := mul_left_cancel₀ (by norm_num : (-2 : ℂ) ≠ 0) h'
    exact ⟨m+1, by exact_mod_cast hc⟩
  · rintro ⟨m,rfl⟩
    cases m with
    | zero => simp at hn
    | succ m =>
      refine ⟨m, ?_⟩
      push_cast
      field_simp

/-- The full negative grid, including the removable points. -/
theorem negative_grid_order_of_RH (rh : RiemannHypothesis) {k n : ℕ} (hk : 2 ≤ k) (hn : 0 < n) :
    meromorphicOrderAt (zetaQuotient k) ((-2 : ℂ)*n/k) =
      (if k ∣ n then 0 else -1 : WithTop ℤ) := by
  let s : ℂ := (-2 : ℂ)*n/k
  have hk₀ : (k : ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hs : s.re ≤ 0 := by
    have e : s = (((-2 : ℝ)*n/k : ℝ) : ℂ) := by push_cast; rfl
    rw [e, ofReal_re]
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have hks : (k : ℂ)*s = -2*(n : ℂ) := by dsimp [s]; field_simp
  have ht : TrivialZero ((k : ℂ)*s) := by
    rw [hks]
    cases n with
    | zero => omega
    | succ j => exact ⟨j, by push_cast; rfl⟩
  change meromorphicOrderAt _ s = _
  rw [left_order_of_RH rh hk hs]
  have hs' : TrivialZero s ↔ k ∣ n := trivial_on_grid_iff hn hk
  by_cases h : k ∣ n <;> simp [hs', ht, h]

private theorem scaled_zero_slope {k : ℕ} {s : ℂ} (hz : riemannZeta ((k : ℂ)*s) = 0) :
    Tendsto (fun z : ℂ ↦ riemannZeta ((k : ℂ)*z)/(z-s)) (𝓝[≠] s)
      (𝓝 ((k : ℂ)*deriv riemannZeta ((k : ℂ)*s))) := by
  have h₁ : (k : ℂ)*s ≠ 1 := fun e ↦ riemannZeta_one_ne_zero (e ▸ hz)
  have hD : HasDerivAt (fun z : ℂ ↦ riemannZeta ((k : ℂ)*z))
      ((k : ℂ)*deriv riemannZeta ((k : ℂ)*s)) s := by
    simpa only [mul_one, Function.comp_def, mul_comm (deriv riemannZeta _)] using
      (differentiableAt_riemannZeta h₁).hasDerivAt.comp s ((hasDerivAt_id s).const_mul (k : ℂ))
  have ht := hasDerivAt_iff_tendsto_slope.mp hD
  have he : slope (fun z : ℂ ↦ riemannZeta ((k : ℂ)*z)) s =
      fun z : ℂ ↦ riemannZeta ((k : ℂ)*z)/(z-s) := by
    funext z
    rw [slope_def_field, hz, sub_zero]
  rwa [he] at ht

/-- A noncancelled simple denominator zero gives the residue by differentiation. -/
theorem simple_ratio_residue {k : ℕ} (hk : 2 ≤ k) {s : ℂ} (hs : s ≠ 1)
    (hz : riemannZeta ((k : ℂ)*s) = 0) (hd : deriv riemannZeta ((k : ℂ)*s) ≠ 0)
    (hn : riemannZeta s ≠ 0) :
    let c := riemannZeta s / ((k : ℂ) * deriv riemannZeta ((k : ℂ)*s))
    c ≠ 0 ∧ Tendsto (fun z : ℂ ↦ (z-s) * zetaQuotient k z) (𝓝[≠] s) (𝓝 c) := by
  have hk₀ : (k : ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have ht := scaled_zero_slope hz
  have hne := mul_ne_zero hk₀ hd
  refine ⟨div_ne_zero hn hne, ?_⟩
  have hlim := (analyticOn_riemannZeta s hs).continuousAt.continuousWithinAt.tendsto.div ht hne
  apply hlim.congr
  intro z
  change riemannZeta z / (riemannZeta ((k : ℂ)*z)/(z-s)) = (z-s)*(riemannZeta z/riemannZeta ((k : ℂ)*z))
  rw [div_div_eq_mul_div, mul_comm (riemannZeta z), mul_div_assoc]

/-- Residue at every uncancelled trivial zero of the denominator. -/
theorem negative_residue_of_RH (rh : RiemannHypothesis) {k : ℕ} (hk : 2 ≤ k) {s : ℂ}
    (hs : s.re ≤ 0) (ht : TrivialZero ((k : ℂ)*s)) (hn : ¬TrivialZero s) :
    let c := riemannZeta s / ((k : ℂ) * deriv riemannZeta ((k : ℂ)*s))
    c ≠ 0 ∧ Tendsto (fun z : ℂ ↦ (z-s) * zetaQuotient k z) (𝓝[≠] s) (𝓝 c) := by
  have hneg := trivial_re_neg ht
  have hz := (left_zero_iff rh hneg.le).2 ht
  exact simple_ratio_residue hk (left_ne_one hs) hz (negative_zero_deriv hneg hz) (fun h ↦ hn ((left_zero_iff rh hs).1 h))

/-- The actual limit at a cancelled pair of trivial zeros, where the continued germ
has order zero. This calculation is independent of RH. -/
theorem cancelled_trivial_limit {k : ℕ} (hk : 2 ≤ k) {s : ℂ}
    (hs : TrivialZero s) (ht : TrivialZero ((k : ℂ)*s)) :
    let c := deriv riemannZeta s / ((k : ℂ)*deriv riemannZeta ((k : ℂ)*s))
    c ≠ 0 ∧ Tendsto (zetaQuotient k) (𝓝[≠] s) (𝓝 c) := by
  have trivial_vanishes {x : ℂ} (h : TrivialZero x) : riemannZeta x = 0 := by
    obtain ⟨n,rfl⟩ := h
    exact riemannZeta_neg_two_mul_nat_add_one n
  have hz := trivial_vanishes hs
  have hd := trivial_vanishes ht
  have hk₀ : (k : ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hne := mul_ne_zero hk₀ (negative_zero_deriv (trivial_re_neg ht) hd)
  have hn := hasDerivAt_iff_tendsto_slope.mp (differentiableAt_riemannZeta (left_ne_one (trivial_re_neg hs).le)).hasDerivAt
  have he : slope riemannZeta s = fun z : ℂ ↦ riemannZeta z/(z-s) := by
    funext z
    rw [slope_def_field, hz, sub_zero]
  rw [he] at hn
  refine ⟨div_ne_zero (negative_zero_deriv (trivial_re_neg hs) hz) hne, ?_⟩
  apply (hn.div (scaled_zero_slope hd) hne).congr'
  filter_upwards [self_mem_nhdsWithin] with z hzs
  exact div_div_div_cancel_right₀ (sub_ne_zero.mpr hzs) (riemannZeta z) (riemannZeta ((k : ℂ)*z))

/-- Explicit coordinates of every pole, with the divisibility condition built into the statement. -/
theorem pole_locations_of_RH (rh : RiemannHypothesis) {k : ℕ} (hk : 2 ≤ k) (s : ℂ) :
    meromorphicOrderAt (zetaQuotient k) s < 0 ↔
      s = 1 ∨ (∃ ρ : ℂ, 0 < ρ.re ∧ riemannZeta ρ = 0 ∧ s = ρ / (k : ℂ)) ∨
      (∃ n : ℕ, 0 < n ∧ ¬k ∣ n ∧ s = (-2 : ℂ)*n/k) := by
  have hk₀ : (k : ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hkR : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hreal (z : ℂ) : ((k : ℂ)*z).re = (k : ℝ)*z.re := by simp [mul_re]
  constructor
  · intro h
    rcases (global_poles_of_RH rh hk s).mp h with h1 | ⟨hpos,hz⟩ | ⟨⟨m,he⟩,hc⟩
    · exact Or.inl h1
    · right; left
      exact ⟨(k : ℂ)*s, by rw [hreal]; exact mul_pos hkR hpos, hz, by field_simp⟩
    · right; right
      have hgrid : s = (-2 : ℂ)*(m+1 : ℕ)/k := (eq_div_iff hk₀).mpr (by
        rw [mul_comm]; simpa using he)
      refine ⟨m+1, by omega, ?_, hgrid⟩
      intro hd
      exact hc (hgrid ▸ (trivial_on_grid_iff (by omega : 0 < m+1) hk).2 hd)
  · rintro (h1 | ⟨ρ,hρ,hz,e⟩ | ⟨n,hn,hd,e⟩)
    · exact (global_poles_of_RH rh hk s).2 (Or.inl h1)
    · have he : (k : ℂ)*s = ρ := by rw [e]; field_simp
      have hpos : 0 < (k : ℝ)*s.re := by rw [← hreal,he]; exact hρ
      exact (global_poles_of_RH rh hk s).2 (Or.inr (Or.inl ⟨(mul_pos_iff_of_pos_left hkR).mp hpos, he ▸ hz⟩))
    · rw [e, negative_grid_order_of_RH rh hk hn, ite_eq_right hd]
      change ((-1 : ℤ) : WithTop ℤ) < ((0 : ℤ) : WithTop ℤ)
      exact WithTop.coe_lt_coe.mpr (by decide)

end PowerFree

namespace PowerFree.Target

open Filter
open scoped Topology Classical

def all_pole_locations : Prop :=
  ∀ {k : ℕ} (_ : 2 ≤ k) (s : ℂ), meromorphicOrderAt (zetaQuotient k) s < 0 ↔
    s = 1 ∨ (∃ ρ : ℂ, 0 < ρ.re ∧ riemannZeta ρ = 0 ∧ s = ρ / (k : ℂ)) ∨
    (∃ n : ℕ, 0 < n ∧ ¬ k ∣ n ∧ s = (-2 : ℂ) * n / k)

def negative_grid_order : Prop :=
  ∀ {k n : ℕ} (_ : 2 ≤ k) (_ : 0 < n), meromorphicOrderAt (zetaQuotient k) ((-2 : ℂ)*n/k) =
    (if k ∣ n then 0 else -1 : WithTop ℤ)

def negative_residue : Prop :=
  ∀ {k : ℕ} (_ : 2 ≤ k) {s : ℂ} (_ : s.re ≤ 0) (_ : TrivialZero ((k : ℂ)*s)) (_ : ¬TrivialZero s),
    let c := riemannZeta s / ((k : ℂ) * deriv riemannZeta ((k : ℂ)*s))
    c ≠ 0 ∧ Tendsto (fun z : ℂ ↦ (z-s) * zetaQuotient k z) (𝓝[≠] s) (𝓝 c)

end PowerFree.Target
