# The Density Hypothesis for ζ in Lean 4

## What is proved

Let `N(σ, T)` be the number of zeros of the Riemann zeta function, counted with multiplicity, in
the rectangle `σ ≤ Re s ≤ 1`, `0 < Im s ≤ T`. The **Density Hypothesis** says that for every
`ε > 0` there is a constant `C > 0` with

    N(σ, T) ≤ C · T ^ (2 (1 − σ) + ε)      for all 1/2 ≤ σ ≤ 1 and T ≥ 2.

This is the statement `DensityHypothesis.density_hypothesis_zeta_zeros` of
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
(`FormalConjectures/Wikipedia/DensityHypothesis.lean`), "the catalog" below, where it is tagged
`research open` and its proof is `sorry`.

| Declaration | Statement | Depends on |
|---|---|---|
| `DensityHypothesis.density_hypothesis_zeta_zeros_of_riemannHypothesis` | `RiemannHypothesis →` the catalog statement | Mathlib |
| `DensityHypothesis.guth_maynard_zero_density_of_riemannHypothesis` | `RiemannHypothesis →` the catalog's `guth_maynard_zero_density` (exponent `30/13`). Under RH this is a corollary of the line above, because `30/13 ≥ 2`; it is **not** Guth and Maynard's unconditional theorem | Mathlib |
| `DensityHypothesis.zetaZeroCount_half_le_mul_log` | `N(1/2, T) ≤ C · T · log T` for `T ≥ 2`, with no hypothesis | Mathlib |
| `DensityHypothesis.density_hypothesis_zeta_zeros` (`DensityHypothesis/Unconditional.lean`) | the catalog statement, with no hypothesis | Mathlib and the Lean proof of RH |
| `DensityHypothesis.guth_maynard_zero_density` (same file) | the catalog's `guth_maynard_zero_density`, with no hypothesis | Mathlib and the Lean proof of RH |

"The Lean proof of RH" is the theorem `riemannHypothesis : RiemannHypothesis` of
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
(module `Main`), pinned here at commit `fcb6eac7534875d32d68030967e2deae6d686151`.
`RiemannHypothesis` is Mathlib's definition.

## What this is, and what it is not

* **No new mathematics.** "RH implies the Density Hypothesis" is classical and short, and the
  catalog's own docstring says so. Once RH is a theorem, so is the Density Hypothesis.
* **Not the first formalization.** [dickie81/number-theory](https://github.com/dickie81/number-theory) has `RHClaim.densityHypothesis (h : RiemannHypothesis) : CrossCriteria.DensityHypothesis`, proved through the Lindelöf hypothesis, and `RHJoin.densityHypothesis`, the same statement with no hypothesis, joined to the Lean proof of RH. Both are in its commit `1f11af9` of 2026-11-24 13:10 UTC, about seven hours before this project's first push (2026-11-24 20:25 UTC). The statement there is in that library's own normalisation, not the catalog's. See [Has anyone else claimed it?](#has-anyone-else-claimed-it).
* **What is specific to this project:** the theorem is the catalog's own statement, checked against
  the catalog's declaration in both toolchains; the implication was judged by Comparator and
  four kernels; and the composition with the proof of RH was re-checked on a small machine, as far
  as that is possible there (next section).
* **The unconditional theorem is exactly as good as the Lean proof of RH.** This project adds four
  small modules on top of about 60,000.
* **Who wrote it.** The Lean code, the tools and this document were written by an AI model (Claude,
  in Claude Code sessions) at the repository owner's request. No human has read the proof line by
  line. Separately prompted model instances audited the method and the claims in this document;
  what they found is in `verification/results/audit.md`.

## How far it was verified

[`verification/README.md`](verification/README.md) is the full record. In short:

| Part | Checked with | Outcome |
|---|---|---|
| RH ⇒ Density Hypothesis, and `N(1/2, T) ≪ T log T` (61,639 declarations including what they use from Mathlib) | `lake build` (Lean 4.33.1); in situ against the unmodified catalog module; on Lean 4.37.0-rc1 `lake comparator` (Lean's kernel, its paranoid kernel, nanoda), `con-leche`, `con-ron`, `leanchecker` | accepted by all; axioms `propext`, `Classical.choice`, `Quot.sound` |
| The statement is the catalog's | structural comparison of the compiled terms on Lean 4.33.1 and 4.37.0-rc1; `type_of%` against the catalog's own file, also inside the RH proof's toolchain | identical |
| Composition with the proof of RH | `Unconditional.lean` and `InSituUnconditional.lean` compiled against the compiled `Main` | compiles; axioms as above |
| What the unconditional theorem depends on | a scan of every constant of the 71,602 compiled modules involved | 1,411,007 declarations in 64,311 of the 70,917 modules of its import closure; the only axioms among them are `propext`, `Classical.choice`, `Quot.sound`; no axiom is declared in any module of the RH proof |
| Every declaration it depends on is accepted by Lean's kernel | a module-by-module replay of all compiled modules through the kernel, on this machine | **in progress when this was written**: 20,482 of the 59,723 modules of the RH proof replayed so far, none rejected; this project's modules and the in-situ chain: accepted |

**Not done:** the official check of the unconditional theorem (`lake comparator` on an export of the
whole RH proof, which needs a machine with hundreds of GB of memory); any kernel other than Lean's
own on the RH proof; a rebuild of the RH proof from its sources. The replay above is a custom,
module-by-module procedure with tools written for this project. `verification/README.md`, section 7,
spells out what follows from it and what does not.

## Proof outline (the Mathlib-only part)

1. **Continuation and growth of `(s − 1) ζ(s)`.** Put
   `cₙ(s) = (1 − s)(n+1)^(−s) − ((n+2)^(1−s) − (n+1)^(1−s))`. Two applications of the mean value
   inequality give `‖cₙ(s)‖ ≤ ‖s‖ ‖1 − s‖ (n+1)^(−Re s − 1)` for `Re s > 0`, so `∑ cₙ` converges
   locally uniformly and is holomorphic on `Re s > 0`. For `Re s > 1` the series telescopes to
   `(1 − s) ζ(s) + 1`. By the identity theorem, Mathlib's entire function `riemannZeta₁`
   (`= (s − 1) ζ(s)`) equals `1 − ∑ cₙ` on `Re s > 0`, hence
   `‖riemannZeta₁ s‖ ≤ 1 + ‖s‖ ‖1 − s‖ K` on `Re s ≥ 1/5`, with `K = ∑ (n+1)^(−6/5)`.
2. **A lower bound at the centre.** `‖ζ(s) − 1‖ ≤ π²/6 − 1 < 2/3` on `Re s = 2`, so
   `‖riemannZeta₁ (2 + iτ)‖ ≥ 1/3`.
3. **Jensen.** Mathlib's `AnalyticOnNhd.sum_divisor_le` on the discs of radii `8/5 < 9/5` about
   `2 + iτ` bounds the number of zeros of `riemannZeta₁` in the smaller disc by
   `log (3 (1 + (|τ| + 4)² K)) / log (9/8)`.
4. **From divisors to `Complex.zeroCountOn`.** Away from `s = 1` the analytic order of
   `riemannZeta₁` equals that of `ζ`, so the divisor of `riemannZeta₁` on a closed disc dominates
   the catalog's multiplicity count on any subset of the disc that avoids `1`.
5. **Summation.** The box `1/2 ≤ Re s ≤ 1`, `k < Im s ≤ k + 1` lies in the disc of radius `8/5`
   about `2 + i(k + 1/2)`. Adding the boxes gives `N(1/2, T) ≤ (T + 1) · O(log T)`.
6. **RH.** For `σ > 1/2` a zero in the rectangle would have `Re s = 1/2 < σ`; it is not a
   trivial zero and not `1` because `Im s > 0`. So the count is `0`. For `σ = 1/2` the exponent
   is `1 + ε` and step 5 applies.

The unconditional zero count of step 5 is not new either:
[anthropics/zeta-23-lean](https://github.com/anthropics/zeta-23-lean) has a local zero count
(`zeta_local_zero_count`) and a full Riemann–von Mangoldt formula. The proof here does not use that
development; it re-derives the bound from Mathlib alone, in the catalog's vocabulary.

## Files

This directory is a self-contained Lake project on Lean `v4.33.1` and Mathlib `v4.33.1`, the
versions the catalog pins at `9097e2f`. It does not touch the repository's root `lakefile.lean`.
All Lean files are `module`s, as the catalog's and the RH proof's are; the same sources compile
unchanged on Lean `v4.37.0-rc1` with Mathlib `31ce06e`, the versions of the RH proof.

| File | Contents |
|---|---|
| `DensityHypothesis/Defs.lean` | The catalog's definitions `Complex.zeroCountOn`, `DensityHypothesis.zetaZeroCount` and their lemmas, copied with their licence notice; the compiled terms are identical to the catalog's |
| `DensityHypothesis/ZeroCount.lean` | The whole proof (steps 1–6) |
| `DensityHypothesis/Main.lean` | The three theorems that need only Mathlib |
| `DensityHypothesis/Audit.lean` | `#print axioms` for them |
| `DensityHypothesis/Unconditional.lean` | The two theorems with no hypothesis. Imports `Main` of the RH proof, so it is **not** a target of this Lake project: it compiles only next to a build of that repository (`verification/tools/build_437.sh`) |
| `InSitu.lean`, `InSituUnconditional.lean`, `make_insitu.py` | The same proof text behind an import of the catalog's own module, with final theorems of type `type_of% @density_hypothesis_zeta_zeros` and `type_of% @guth_maynard_zero_density`; generated from `ZeroCount.lean` |
| `Challenge.lean`, `Solution.lean`, `comparator.json`, `export-targets.txt` | Comparator inputs for the Mathlib-only part: statements with `sorry` on purpose, the module that proves them, the configuration that was run |
| `comparator/` | Comparator inputs for the unconditional theorem (the catalog's two statements). Not run: see above |
| `verification/` | Tools, controls, results and the record of what was run |
| `formal-conjectures-status.patch` | A possible change to the catalog entry |
| `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` | The pins; the manifest's package revisions are the catalog's at `9097e2f` |

To build the Mathlib-only part:

```bash
cd proofs/density-hypothesis && lake exe cache get && lake build && lake env lean DensityHypothesis/Audit.lean
```

## Has anyone else claimed it?

**The search is still running; this section will be replaced.** So far:

* **A formal proof by someone else, earlier, of a differently normalised statement.** [dickie81/number-theory](https://github.com/dickie81/number-theory), commit `1f11af9` (2026-11-24 13:10 UTC): `RHClaim.densityHypothesis` (from `RiemannHypothesis`, through the Lindelöf hypothesis) and `RHJoin.densityHypothesis` (no hypothesis, joined to the Lean proof of RH). Its `CrossCriteria.DensityHypothesis` is `∀ ε > 0, ∃ B, ShortWeil.DensityXi (2 + ε) B`, that library's own form of the bound. It is not the catalog's theorem and the repository does not mention the catalog.
* **The catalog entry is unclaimed.** At `google-deepmind/formal-conjectures` `9097e2f` (still the head of `main` on 2026-11-25 04:22 UTC) the entry is tagged `research open` with a `sorry` proof, and none of the 5,509 pull-request heads changes that file.
* **No registry entry.** Among the 1,357 entries of the Palomar registry as of 2026-11-25 04:47 UTC, none registers the Density Hypothesis.

## Proposing it upstream

The catalog asks that a `research solved` entry with a formal proof link to an entry of the
[Palomar registry](https://palomar-registry.org), which records a Lean formalization at one pinned
commit. Neither a registry entry nor a pull request to the catalog has been made for this project.
`formal-conjectures-status.patch` shows the status change the catalog entry would need; the
registry link would go into a `formal_proof using lean4 at "…"` attribute.
