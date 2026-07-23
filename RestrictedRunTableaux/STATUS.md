# Status

The proof package now has three layers:

1. `check_model.py` — exact rational verification of the six-state model, covariance, harmonic polynomials, exit signs, Poisson correctors, path weights, and initial values. It passes locally.
2. `Proof.md` — exact combinatorial reduction and construction of the positive killed harmonic function.
3. `FinitePhaseConeBridge.md` — a complete human proof of the finite-phase survival/local/fixed-endpoint transfer obtained by combining the Denisov–Zhang martingale-FCLT method, a finite-state multidimensional local limit theorem, and the Denisov–Wachtel convolution/time-reversal argument.

The resulting human proof concludes

`G(n) ~ C₁ · 8ⁿ / n⁴` with `C₁ > 0`.

Current classification: **candidate complete human proof, exact finite layer checked, analytic transfer awaiting independent probability-theory audit**. It is not yet a kernel-verified Lean proof and must not be promoted to Formal Conjectures as solved until that audit and a no-`sorry` Lean development are complete.
