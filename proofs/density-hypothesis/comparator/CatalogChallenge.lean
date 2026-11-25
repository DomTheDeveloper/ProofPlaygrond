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

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.NumberTheory.LSeries.ZetaZeros
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Challenge: the catalog's two statements, with no hypothesis

`DensityHypothesis.density_hypothesis_zeta_zeros` and `DensityHypothesis.guth_maynard_zero_density`
as google-deepmind/formal-conjectures states them (`FormalConjectures/Wikipedia/DensityHypothesis.lean`
at commit `9097e2f90e66d2f6244209cb1c07f7120d17ec53`), with the definitions they mention, in a file
that imports nothing but Mathlib. The catalog's `@[category ...]` and `@[AMS ...]` attributes are
left out, because they come from the catalog's own utility library; nothing else is changed.
`verification/README.md` records that these statements are the same terms as the ones in the
unmodified catalog file.

The solution is `DensityHypothesis/Unconditional.lean`, which needs a build of
leanprover-community/riemann-hypothesis. Comparator on this pair needs an export of that whole
proof (about 60 GB) and a machine with a few hundred GB of memory; see `verification/README.md`
for what was checked instead on a 16 GB machine.
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

/-- Density Hypothesis: for every $\varepsilon > 0$, there exists $C > 0$ such that
$N(\sigma, T) \le C \, T^{2(1 - \sigma) + \varepsilon}$ for all $\frac{1}{2} \le \sigma \le 1$
and $T \ge 2$. -/
theorem density_hypothesis_zeta_zeros (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → 2 ≤ T →
      (zetaZeroCount σ T : ℝ) ≤ C * T ^ (2 * (1 - σ) + ε) := by
  sorry

/-- Guth–Maynard zero-density bound (2024): for every $\varepsilon > 0$, there exists $C > 0$ such
that $N(\sigma, T) \le C \, T^{\frac{30}{13}(1 - \sigma) + \varepsilon}$ for all
$\frac{1}{2} \le \sigma \le 1$ and $T \ge 2$. -/
theorem guth_maynard_zero_density (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → 2 ≤ T →
      (zetaZeroCount σ T : ℝ) ≤ C * T ^ ((30 / 13 : ℝ) * (1 - σ) + ε) := by
  sorry

end DensityHypothesis
