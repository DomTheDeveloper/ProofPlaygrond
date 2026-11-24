import Challenge
import DensityHypothesis

/-!
# Composing with `riemannHypothesis`

This file is NOT part of the Lake project in this directory and does not compile in it. It
belongs inside a checkout of `leanprover-community/riemann-hypothesis` (Lean `v4.37.0-rc1`),
with `DensityHypothesis.lean` and `DensityHypothesis/` copied next to it and declared as a
library. See "Compatibility with the RH repository's toolchain" in `README.md`.

`Challenge` here is that repository's statements-only module `src/Challenge.lean`, in which
`riemannHypothesis : RiemannHypothesis` has its proof omitted. With this import, the theorem
below typechecks and its dependency list contains `sorryAx`, coming from that omitted proof.
Replacing `import Challenge` by `import Main` uses the repository's actual proof of
`riemannHypothesis` instead; that variant was not built by the author of this file.
-/

theorem density_hypothesis_zeta_zeros (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → 2 ≤ T →
      (DensityHypothesis.zetaZeroCount σ T : ℝ) ≤ C * T ^ (2 * (1 - σ) + ε) :=
  DensityHypothesis.density_hypothesis_zeta_zeros_of_riemannHypothesis riemannHypothesis ε hε

#print axioms density_hypothesis_zeta_zeros
#print axioms DensityHypothesis.density_hypothesis_zeta_zeros_of_riemannHypothesis
