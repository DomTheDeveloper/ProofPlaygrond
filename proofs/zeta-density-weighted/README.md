# Density of zeta zeros from a weighted sum

@domthedeveloper independently proved the zeta density hypothesis and formalized the proof in Lean. Only afterward did @domthedeveloper discover Steven Enamakel’s earlier Lean proof. This version bounds the endpoint using a sum over zeros weighted by multiplicity. Codex assisted with cleanup and verification.

For p = 1 + ε, let Sₚ be the sum of m(z) ‖z‖⁻ᵖ over the zeros of ξ, with multiplicity m(z). Salvatore Mercuri’s summability theorem proves that this sum converges for every p > 1. In the counting rectangle a zero has 0 < ‖z‖ ≤ 2T and its multiplicities for ζ and ξ agree. Consequently m(z) ≤ (2T)ᵖ m(z) ‖z‖⁻ᵖ. Sum over the finite rectangle and use positivity to bound the finite subsum by Sₚ. The constant 1 + 2ᵖ Sₚ works for every T ≥ 2. RH gives count zero when σ > 1/2.

The advantage is in the application. It uses one weighted sum at the requested exponent and a finite-subsum inequality. Enamakel builds a stronger counting library and applies its O(T log T) strip bound. The imported summability theorem itself uses a disk-count estimate. The underlying mathematical consequence and Enamakel's earlier formalization are established work.

## Reproduce

Use Lean 4.35.0. The two dependencies are pinned in lakefile.toml and share Mathlib commit 56a005855ea17e0b0958f73ec801ae140b0a1679. The final module imports the compact RH project's Main and the unconditional ξ summability theorem. Building the RH dependency from source requires substantial resources.

    lake update
    lake exe cache get
    lake build DensityHypothesis

The endpoint and full theorem print their axioms. To compare the upstream multiplicity module, counting rectangle and goal signature against Google DeepMind's pinned source, run the following with an existing checkout containing commit f606af160664c5a10952e9a957b100a1cd45bbeb.

    python3 check_statement.py /path/to/formal-conjectures

[Prior Lean proof](https://github.com/senamakel/density-rh/blob/91ffb87856da458ef93fcc139af0d1d389a82af2/Unconditional/DensityUnconditional.lean) · [Weighted summability theorem](https://github.com/smmercuri/zeta/blob/4704234df2d97563936adcaf0b89e2f8955389f9/Zeta/Hadamard/ZeroSummability.lean#L318-L323) · [Compact RH](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact)
