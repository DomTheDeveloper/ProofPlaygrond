# The Density Hypothesis for ζ, from the Riemann Hypothesis — Lean 4 proof

## What is proved

Let `N(σ, T)` be the number of zeros of the Riemann zeta function, counted with multiplicity,
in the rectangle `σ ≤ Re s ≤ 1`, `0 < Im s ≤ T`. The **Density Hypothesis** says that for every
`ε > 0` there is a constant `C > 0` with

    N(σ, T) ≤ C · T ^ (2 (1 − σ) + ε)      for all 1/2 ≤ σ ≤ 1 and T ≥ 2.

This is the statement `DensityHypothesis.density_hypothesis_zeta_zeros` of
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
(`FormalConjectures/Wikipedia/DensityHypothesis.lean`).

The library `DensityHypothesis` in this directory proves, with no `sorry`:

| Declaration | Statement | Uses RH |
|---|---|---|
| `DensityHypothesis.density_hypothesis_zeta_zeros_of_riemannHypothesis` | `RiemannHypothesis →` the catalog statement above, word for word | yes |
| `DensityHypothesis.guth_maynard_zero_density_of_riemannHypothesis` | `RiemannHypothesis →` the catalog's `guth_maynard_zero_density` (exponent `30/13`) | yes |
| `DensityHypothesis.zetaZeroCount_half_le_mul_log` | `N(1/2, T) ≤ C · T · log T` for `T ≥ 2` | **no** |
| `DensityHypothesisProof.zeroCountOn_strip_le_rpow` | `N(1/2, T) ≤ C_ε · T ^ (1 + ε)` for `T ≥ 2` | **no** |
| `DensityHypothesisProof.norm_riemannZeta₁_le` | `‖(s − 1) ζ(s)‖ ≤ 1 + ‖s‖ ‖1 − s‖ K` on `Re s ≥ 1/5` | **no** |

`RiemannHypothesis` is Mathlib's definition, the one proved as `riemannHypothesis` in
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
(`src/Main.lean`).

## What this is, and what it is not

* The implication "RH ⇒ Density Hypothesis" is classical and easy; the catalog's own docstring
  says so. Nothing here is new mathematics. What is new is a complete machine-checked proof of the
  catalog statement from `RiemannHypothesis`, including the unconditional zero-counting bound
  that the case `σ = 1/2` needs and that Mathlib does not contain.
* The theorem here carries `RiemannHypothesis` as a hypothesis. Removing it is the one-line
  composition

  ```lean
  theorem density_hypothesis_zeta_zeros (ε : ℝ) (hε : 0 < ε) : … :=
    DensityHypothesis.density_hypothesis_zeta_zeros_of_riemannHypothesis riemannHypothesis ε hε
  ```

  inside a build of `leanprover-community/riemann-hypothesis`. **That composition was not
  compiled here**: the RH proof is about 60 000 modules on Lean `v4.37.0-rc1` and could not be
  rebuilt in the container this was written in. Whether the Density Hypothesis is a theorem
  therefore rests on that repository's proof of RH, exactly as the catalog's other
  "solved because RH is proved" entries do.

## Proof outline

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

## Files

This directory is a self-contained Lake project (Lean `v4.33.1`, Mathlib `v4.33.1`, the versions
pinned by formal-conjectures at `9097e2f`). It does not touch the repository's root `lakefile.lean`.

| File | Contents |
|---|---|
| `DensityHypothesis/Defs.lean` | The catalog's definitions `Complex.zeroCountOn`, `DensityHypothesis.zetaZeroCount` and their lemmas, copied byte for byte from formal-conjectures `9097e2f` |
| `DensityHypothesis/ZeroCount.lean` | The whole proof (steps 1–6) |
| `DensityHypothesis/Main.lean` | The three headline theorems, stated with `zetaZeroCount` |
| `DensityHypothesis/Audit.lean` | `#print axioms` for the headline theorems |
| `InSitu.lean` | The same proof text behind `import FormalConjectures.Wikipedia.DensityHypothesis`; its final theorems have type `type_of% @density_hypothesis_zeta_zeros` and `type_of% @guth_maynard_zero_density` |
| `make_insitu.py` | Regenerates `InSitu.lean` from `DensityHypothesis/ZeroCount.lean` |
| `formal-conjectures-status.patch` | Proposed status change for the catalog entry |
| `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` | The pins; the manifest is formal-conjectures' own at `9097e2f` |

## Verification

### 1. Local, against the catalog's Mathlib (Lean 4.33.1, Mathlib `v4.33.1`)

The prebuilt Mathlib cache was not reachable from the container this was written in, so the 3801
modules that the proof needs were compiled from source. Then:

```text
$ lean DensityHypothesis/Defs.lean        # exit 0, no output
$ lean DensityHypothesis/ZeroCount.lean   # exit 0, no output (no errors, no warnings)
$ lean DensityHypothesis/Main.lean        # exit 0, no output
$ lean DensityHypothesis/Audit.lean
'DensityHypothesis.density_hypothesis_zeta_zeros_of_riemannHypothesis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DensityHypothesis.guth_maynard_zero_density_of_riemannHypothesis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DensityHypothesis.zetaZeroCount_half_le_mul_log' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### 2. In situ, against the unmodified catalog file

_Not yet run when this revision was committed; this section is updated once the full build of the catalog module finishes._

To reproduce:

```bash
git clone https://github.com/google-deepmind/formal-conjectures
```

```bash
cd formal-conjectures && git checkout 9097e2f90e66d2f6244209cb1c07f7120d17ec53
```

```bash
lake exe cache get && lake build FormalConjectures.Wikipedia.DensityHypothesis
```

```bash
lake env lean /path/to/ProofPlaygrond/proofs/density-hypothesis/InSitu.lean
```

### 3. Not done: an independent CI run

The repository's `Manual Lean audit` workflow could not be started from the session that wrote
this (the integration token has no permission to dispatch workflows), and the proof was not
compiled against the root project's Lean `v4.32.0`. Every Mathlib theorem the proof uses was
checked by name to exist in Mathlib `v4.32.0` as well, but that is not a compile.

To rebuild from scratch on a machine with normal network access:

```bash
cd proofs/density-hypothesis && lake exe cache get && lake build && lake env lean DensityHypothesis/Audit.lean
```

## Was this already done? Evidence as of 2026-11-24

Nobody can prove a negative. This is what was checked.

1. **The catalog lists it as open.** At `google-deepmind/formal-conjectures` commit
   `9097e2f90e66d2f6244209cb1c07f7120d17ec53` (2026-11-24 14:16 UTC, the head of `main` when this
   was written), `density_hypothesis_zeta_zeros` carries `@[category research open, AMS 11 30]`,
   its proof is `sorry`, and it has no `formal_proof` attribute. The file was added on 2026-11-23
   (commit `f9b3868`, PR 8057), three days after the proof of RH was released, and has not been
   touched since.
2. **The maintainers' RH sweep missed it.** Commit `6bc2f74` (PR 8111, 2026-11-24 09:39 UTC),
   "set the status of the (generalized) Riemann hypothesis to solved", moved eleven files'
   statements to `research solved` (Robin, Lagarias, Li, idoneal numbers, Erdős 233 and 985, Mills,
   powerful numbers, and others). `Wikipedia/DensityHypothesis.lean` is not among them.
3. **No pending pull request touches it.** The heads of all 139 pull requests numbered 8057 to
   8265 were fetched on 2026-11-24 at about 19:35 UTC. None changes
   `FormalConjectures/Wikipedia/DensityHypothesis.lean`, and none mentions
   `density_hypothesis_zeta_zeros`, `zetaZeroCount` or `DensityHypothesis` in any other file.
4. **The RH repository does not contain it.** `leanprover-community/riemann-hypothesis` at
   `9282d3a` proves five theorems in `src/Main.lean` (RH and four statements about Dirichlet
   L-functions) and its README says files not needed for those are out of scope.
5. **Related formal work found by web search does not cover it.**
   * [mrklwk/zeta-zero-density-lean](https://github.com/mrklwk/zeta-zero-density-lean) (October
     2026): an unconditional bound `N(σ, T) ≪ T^(2(1−σ)+ε)` for each fixed `3/4 < σ < 1`, with a
     constant depending on `σ`. Not uniform down to `1/2`.
   * [finndoolan-m/rh-lindelof](https://github.com/finndoolan-m/rh-lindelof) (2026-11-22): RH
     implies the Lindelöf hypothesis. No zero-density statement.
   * [anthropics/zeta-23-lean](https://github.com/anthropics/zeta-23-lean): contains a
     Riemann–von Mangoldt formula in its own setting. It does not state the catalog's Density
     Hypothesis.

What this evidence does not exclude: a proof that is unpublished, unindexed, or posted after the
times above. And, as said at the top, mathematicians regard the Density Hypothesis as settled the
moment RH is; the gap that was open is the formal one.

## Proposing the status change upstream

`formal-conjectures-status.patch` is the corresponding edit to the catalog entry. The catalog
requires a `formal_proof` link for a research problem to point at a
[Palomar](https://palomar-registry.org/) entry, so registering the proof there comes first.
