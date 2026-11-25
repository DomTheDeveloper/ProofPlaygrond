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

/-!
# Definitions for the density hypothesis statement

Everything in this file is copied, with the same names, from
`google-deepmind/formal-conjectures` at commit `9097e2f90e66d2f6244209cb1c07f7120d17ec53`:

* `Complex.zeroCountOn` and its lemmas, and `Bornology.IsBounded.finite_riemannZeta_zeros`, from
  `FormalConjecturesForMathlib/NumberTheory/RiemannZetaZeros.lean`;
* `DensityHypothesis.zetaZeroCount`, from `FormalConjectures/Wikipedia/DensityHypothesis.lean`.

Those files carry the copyright and licence notice reproduced at the top of this file. The
declarations are unchanged, and so is their setting: like the catalog's files this is a `module`
with the same three `public import`s as `RiemannZetaZeros.lean` and an `@[expose] public section`,
so that Lean elaborates `Complex.zeroCountOn` here exactly as it does there. They are reproduced
only so that this project, which does not depend on formal-conjectures, can state the theorem with
the catalog's own definitions.

`verification/` records the comparison of the compiled constants with the catalog's, and the file
`InSitu.lean` checks the same proof against the unmodified catalog module, where no copy is
involved.
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

end DensityHypothesis
