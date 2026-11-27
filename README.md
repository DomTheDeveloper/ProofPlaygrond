# Strict simple-zero proportion on the critical line

`SimplePropLt.lean` derives `riemannZeta.simple_prop_lt` from Thomas Lince’s unconditional three-point estimate. It uses the dyadic window `(T, 2T]` in both counts. The transfer is by @domthedeveloper.

## Replay

From this directory, with elan installed, run

```sh
lake exe cache get
lake build SimplePropLt
lake env lean SimplePropLt.lean
```

The last command prints the axiom report for the unconditional theorem. The project includes the complete 166-module source dependency chain above Mathlib and its standard dependencies. The Lean toolchain and Mathlib revision are pinned. The four-point certificate is unnecessary for this theorem.

## Sources

- The 140 modules under `Zeta23/` are from [Anthropic's pinned development](https://github.com/anthropics/formal-math/tree/3635e74826a4c1fcece7d1cd2b6fa75e43a00510).
- The 17 modules under `Zeta23Ext/` and nine under `ThreePoint/` are from [Zeta Lab's pinned bridge](https://github.com/teal-sea/zeta-lab/tree/84312e4477dfeb7e0d8a91c38897f225f5a52f19/lean/bridge).
- The target and its counting definitions follow the [Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66/FormalConjectures/Paper/RiemannZetaZeros.lean#L125-L128).
- Licenses and notices are in `licenses/`. The [Proof Playground PR](https://github.com/DomTheDeveloper/ProofPlaygrond/pull/180) contains the adaptation to the exact Left to Solve declaration and a separate [replay against the original project configuration](https://github.com/DomTheDeveloper/ProofPlaygrond/actions/runs/46043650767).

Left to Solve requires its catalog import followed only by Mathlib imports and enforces a 512 KiB file limit. This project is a standalone source distribution.
