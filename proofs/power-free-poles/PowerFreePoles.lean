import FreePoles
import Main

/-! Pole theorems using the compact project's proof of Mathlib's Riemann hypothesis. -/

namespace PowerFree

/-- Complete pole classification in the open right half-plane. -/
theorem poles :
    ∀ {k : ℕ} (_ : 2 ≤ k) {s : ℂ} (_ : 0 < s.re),
      meromorphicOrderAt (zetaQuotient k) s < 0 ↔ s = 1 ∨ riemannZeta ((k : ℂ) * s) = 0 :=
  @poles_of_RH riemannHypothesis

/-- Every scaled zero contributes a pole of exactly its multiplicity. -/
theorem scaled_zero_multiplicity :
    ∀ {k : ℕ} (_ : 2 ≤ k) {ρ : ℂ} (_ : 0 < ρ.re) (_ : riemannZeta ρ = 0),
      (ρ / (k : ℂ)).re = 1 / (2 * (k : ℝ)) ∧
        0 < zetaOrder ρ ∧
        meromorphicOrderAt (zetaQuotient k) (ρ / (k : ℂ)) = (-(zetaOrder ρ) : ℤ) :=
  @multiplicity_of_RH riemannHypothesis

/-- The squarefree pole line inside the strip 0 < Re(s) < 1/2. -/
theorem squarefree_pole_line :
    ∀ {s : ℂ} (_ : 0 < s.re) (_ : s.re < 1 / 2)
      (_ : meromorphicOrderAt (zetaQuotient 2) s < 0), s.re = 1 / 4 :=
  @squarefree_pole_line_of_RH riemannHypothesis

end PowerFree
