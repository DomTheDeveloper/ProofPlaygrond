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

public import DensityHypothesis.ZeroCount

/-! The counting rectangle of the Formal Conjectures density hypothesis. -/
@[expose] public section

namespace DensityHypothesis

/-- Multiplicity-weighted count $N(\sigma, T)$ of zeros of $\zeta(s)$ inside
$\{s \in \mathbb{C} \mid \sigma \le \operatorname{Re}(s) \le 1 \text{ and } 0 <
\operatorname{Im}(s) \le T\}$ (half the symmetric count $|\operatorname{Im}(s)| \le T$). -/
noncomputable abbrev zetaZeroCount (σ T : ℝ) : ℕ :=
  Complex.zeroCountOn riemannZeta
    {s : ℂ | σ ≤ s.re ∧ s.re ≤ 1 ∧ 0 < s.im ∧ s.im ≤ T}

end DensityHypothesis
