/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
https://www.apache.org/licenses/LICENSE-2.0
-/
import V2Solution
import SimplePropLtTransfer

/-!
# Strict simple-zero proportion in the dyadic window

This applies Thomas Lince's registered unconditional three-point estimate to the
exact statement of `riemannZeta.simple_prop_lt` in Google DeepMind's Formal Conjectures.
The bound and its analytic proof are due to the cited formalization. The transfer
identifies both zero counts, proves the strict margin and constructs the error function.

To replay, copy the two Lean files from this directory into `lean/bridge` at commit
`84312e4477dfeb7e0d8a91c38897f225f5a52f19` of `teal-sea/zeta-lab`. In that directory run

```sh
lake exe cache get
lake build V2Solution
lake env lean -o .lake/build/lib/lean/SimplePropLtTransfer.olean SimplePropLtTransfer.lean
lake env lean SimplePropLt.lean
```

[Registered analytic proof](https://palomar-registry.org/entry.html?id=PALOMAR-2026-08-25-000005).
-/

open Filter ZetaZeros

theorem riemannZeta.simple_prop_lt : ∃ c > 2 - montgomeryTaylorConst⁻¹, ∃ o : ℝ → ℝ,
    o =o[atTop] (1 : ℝ → ℝ) ∧
      ∀ T > 0, (c - o T) * N riemannZeta T (2 * T) ≤ Ns riemannZeta T (2 * T) :=
  SimplePropLtProof.of_three_point Zeta23Ext.PalomarV2.three_point_bound

#print axioms riemannZeta.simple_prop_lt
