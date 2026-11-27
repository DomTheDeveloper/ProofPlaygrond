import Main
import SchoenfeldRH.Main

/-!
# Solution: Schoenfeld's bound for the Chebyshev function `ψ`

`riemannHypothesis : RiemannHypothesis` is the theorem of `Main.lean` in `grh-lean/grh-compact`;
the equivalence is that of `SchoenfeldRH/Main.lean`.
-/

theorem schoenfeld_strict_bound :
    ∀ x : ℝ, 73.2 ≤ x → |Chebyshev.psi x - x| < Real.sqrt x * Real.log x ^ 2 / (8 * Real.pi) :=
  SchoenfeldRH.schoenfeldBoundStrict_iff_riemannHypothesis.mpr riemannHypothesis
