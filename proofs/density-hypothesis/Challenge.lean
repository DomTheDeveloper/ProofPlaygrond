/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.PSeriesComplex
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Tactic
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.NumberTheory.LSeries.ZetaZeros

/-!
# Challenge: what is claimed, from Mathlib alone

The statements of the three theorems of `DensityHypothesis/Main.lean`, with their proofs left out
on purpose, in a file that imports nothing but Mathlib. `Solution.lean` proves statements with the
same names. Comparator (`lake comparator`, configured by `comparator.json`) checks that the two
sets of statements and the definitions they mention are the same constants, which axioms the
proofs use, and that Lean's kernel and the external kernels accept the proofs.

The definitions are copied from `DensityHypothesis/Defs.lean`, which copies them from
google-deepmind/formal-conjectures at commit `9097e2f90e66d2f6244209cb1c07f7120d17ec53`; the notice
above is theirs. The three theorem statements are this project's. Like the files it mirrors, this
file is a `module` with the same Mathlib imports, so that Lean elaborates every statement here as
it does there (Comparator matches constants by name and requires identical terms).

Building this file reports "declaration uses `sorry`" three times. That is intended here and in
`comparator/CatalogChallenge.lean`, and nowhere else in the project.
-/

@[expose] public section

namespace Complex

/-- The multiplicity-weighted count of zeros of `f : ℂ → ℂ` in `S : Set ℂ`, summing
`analyticOrderNatAt f s` over `s ∈ S`. Points where `f s ≠ 0` or `f` is not analytic contribute
`0`. -/
noncomputable def zeroCountOn (f : ℂ → ℂ) (S : Set ℂ) : ℕ :=
  ∑ᶠ s ∈ S, analyticOrderNatAt f s

@[simp]
theorem zeroCountOn_empty (f : ℂ → ℂ) : zeroCountOn f ∅ = 0 :=
  finsum_mem_empty

@[simp]
theorem zeroCountOn_singleton (f : ℂ → ℂ) (s : ℂ) :
    zeroCountOn f {s} = analyticOrderNatAt f s :=
  finsum_mem_singleton

theorem analyticOrderNatAt_eq_zero_of_ne_zero {f : ℂ → ℂ} {s : ℂ} (h : f s ≠ 0) :
    analyticOrderNatAt f s = 0 := by
  simp [analyticOrderNatAt, analyticOrderAt_eq_zero.mpr (.inr h)]

theorem zeroCountOn_eq_zero_of_forall_ne_zero {f : ℂ → ℂ} {S : Set ℂ}
    (h : ∀ s ∈ S, f s ≠ 0) : zeroCountOn f S = 0 :=
  finsum_mem_eq_zero_of_forall_eq_zero fun _ hs =>
    analyticOrderNatAt_eq_zero_of_ne_zero (h _ hs)

theorem zeroCountOn_sep_eq_zero (f : ℂ → ℂ) (S : Set ℂ) :
    zeroCountOn f {s ∈ S | f s = 0} = zeroCountOn f S := by
  refine finsum_mem_inter_support_eq' _ _ _ fun s hs => ⟨And.left, fun hsS => ⟨hsS, ?_⟩⟩
  by_contra hnz
  exact Function.mem_support.mp hs (analyticOrderNatAt_eq_zero_of_ne_zero hnz)

end Complex

theorem Bornology.IsBounded.finite_riemannZeta_zeros {S : Set ℂ} (hS : Bornology.IsBounded S) :
    {s ∈ S | riemannZeta s = 0}.Finite :=
  hS.isCompact_closure.inter_riemannZetaZeros_finite.subset fun _ hs =>
    ⟨subset_closure hs.1, hs.2⟩

namespace DensityHypothesis

/-- Multiplicity-weighted count $N(\sigma, T)$ of zeros of $\zeta(s)$ inside
$\{s \in \mathbb{C} \mid \sigma \le \operatorname{Re}(s) \le 1 \text{ and } 0 <
\operatorname{Im}(s) \le T\}$ (half the symmetric count $|\operatorname{Im}(s)| \le T$). -/
noncomputable abbrev zetaZeroCount (σ T : ℝ) : ℕ :=
  Complex.zeroCountOn riemannZeta
    {s : ℂ | σ ≤ s.re ∧ s.re ≤ 1 ∧ 0 < s.im ∧ s.im ≤ T}

/-- **The Density Hypothesis, assuming the Riemann Hypothesis.** -/
theorem density_hypothesis_zeta_zeros_of_riemannHypothesis (hRH : RiemannHypothesis)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → 2 ≤ T →
      (zetaZeroCount σ T : ℝ) ≤ C * T ^ (2 * (1 - σ) + ε) := by
  sorry

/-- The zero-density bound with exponent `30/13`, assuming the Riemann Hypothesis. -/
theorem guth_maynard_zero_density_of_riemannHypothesis (hRH : RiemannHypothesis)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → 2 ≤ T →
      (zetaZeroCount σ T : ℝ) ≤ C * T ^ ((30 / 13 : ℝ) * (1 - σ) + ε) := by
  sorry

/-- **Unconditional**: at most `C T log T` zeros with `1/2 ≤ Re s ≤ 1`, `0 < Im s ≤ T`. -/
theorem zetaZeroCount_half_le_mul_log :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → (zetaZeroCount (1 / 2) T : ℝ) ≤ C * T * Real.log T := by
  sorry

end DensityHypothesis
