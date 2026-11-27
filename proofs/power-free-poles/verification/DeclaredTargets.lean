module

public import FreePoles

@[expose] public section

namespace PowerFree.Target

def poles : Prop :=
  ∀ {k : ℕ} (_ : 2 ≤ k) {s : ℂ} (_ : 0 < s.re),
    meromorphicOrderAt (zetaQuotient k) s < 0 ↔ s = 1 ∨ riemannZeta ((k : ℂ) * s) = 0

def scaled_zero_multiplicity : Prop :=
  ∀ {k : ℕ} (_ : 2 ≤ k) {ρ : ℂ} (_ : 0 < ρ.re) (_ : riemannZeta ρ = 0),
    (ρ / (k : ℂ)).re = 1 / (2 * (k : ℝ)) ∧
      0 < zetaOrder ρ ∧
      meromorphicOrderAt (zetaQuotient k) (ρ / (k : ℂ)) = (-(zetaOrder ρ) : ℤ)

def squarefree_pole_line : Prop :=
  ∀ {s : ℂ} (_ : 0 < s.re) (_ : s.re < 1 / 2)
    (_ : meromorphicOrderAt (zetaQuotient 2) s < 0), s.re = 1 / 4

end PowerFree.Target
