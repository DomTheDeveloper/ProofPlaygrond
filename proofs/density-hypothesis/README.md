# The Density Hypothesis for ζ, from the Riemann Hypothesis — Lean 4 proof

## What is proved

Let `N(σ, T)` be the number of zeros of the Riemann zeta function, counted with multiplicity,
in the rectangle `σ ≤ Re s ≤ 1`, `0 < Im s ≤ T`. The **Density Hypothesis** says that for every
`ε > 0` there is a constant `C > 0` with

    N(σ, T) ≤ C · T ^ (2 (1 − σ) + ε)      for all 1/2 ≤ σ ≤ 1 and T ≥ 2.

This is the statement `DensityHypothesis.density_hypothesis_zeta_zeros` of
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
(`FormalConjectures/Wikipedia/DensityHypothesis.lean`), "the catalog" below.

The library `DensityHypothesis` in this directory proves, with no `sorry`:

| Declaration | Statement | Uses RH |
|---|---|---|
| `DensityHypothesis.density_hypothesis_zeta_zeros_of_riemannHypothesis` | `RiemannHypothesis →` the catalog statement above | yes |
| `DensityHypothesis.guth_maynard_zero_density_of_riemannHypothesis` | `RiemannHypothesis →` the catalog's statement `guth_maynard_zero_density` (exponent `30/13`). Under RH this is a corollary of the line above because `30/13 ≥ 2`; it is **not** Guth and Maynard's unconditional theorem | yes |
| `DensityHypothesis.zetaZeroCount_half_le_mul_log` | `N(1/2, T) ≤ C · T · log T` for `T ≥ 2` | **no** |
| `DensityHypothesisProof.zeroCountOn_strip_le_rpow` | `N(1/2, T) ≤ C_ε · T ^ (1 + ε)` for `T ≥ 2` | **no** |
| `DensityHypothesisProof.norm_riemannZeta₁_le` | `‖(s − 1) ζ(s)‖ ≤ 1 + ‖s‖ ‖1 − s‖ K` on `Re s ≥ 1/5` | **no** |

`RiemannHypothesis` is Mathlib's definition, the statement of the theorem `riemannHypothesis` in
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
(`src/Main.lean`). That repository's proof was not rebuilt or examined for this project, which
takes no position on it.

## What this is, and what it is not

* **No new mathematics.** The implication "RH ⇒ Density Hypothesis" is classical and easy; the
  catalog's own docstring says so. Mathematicians regard the Density Hypothesis as settled the
  moment RH is.
* **The unconditional ingredient was already formalized elsewhere.** The case `σ = 1/2` needs
  `N(1/2, T) ≪ T log T`. Mathlib has no such bound, but
  [anthropics/zeta-23-lean](https://github.com/anthropics/zeta-23-lean) does: its
  `zeta_local_zero_count` (`zeta23/Zeta23/RvM/LocalCount.lean`) bounds the zeros in each window
  `t < Im ρ ≤ t + 1`, with the same multiplicity convention, by `A₀ log (|t| + 3)`, and it proves a
  full Riemann–von Mangoldt formula. The proof here does not use that development; it re-derives
  the bound from Mathlib alone, in the catalog's vocabulary.
* **What is new**, as far as could be determined (see the evidence section): a machine-checked
  proof of the catalog's Density Hypothesis statement from `RiemannHypothesis`, checked against the
  catalog's own declaration.
* **RH remains a hypothesis of the theorem.** Removing it is the one-line composition

  ```lean
  theorem density_hypothesis_zeta_zeros (ε : ℝ) (hε : 0 < ε) : … :=
    DensityHypothesis.density_hypothesis_zeta_zeros_of_riemannHypothesis riemannHypothesis ε hε
  ```

  inside a build of `leanprover-community/riemann-hypothesis`. **That composition was not
  compiled against their proof here**: the RH proof is about 60 000 files on Lean `v4.37.0-rc1`
  and could not be rebuilt in the container this was written in. It was compiled against their
  statements-only file on their toolchain (Verification, part 4). Whether the Density Hypothesis
  is a theorem therefore rests on that repository's proof of RH, exactly as the catalog's other
  "solved because RH is proved" entries do.
* **Who wrote it.** The Lean code and this document were written by an AI model (Claude, in a
  Claude Code session) at the repository owner's request. No human has read the proof line by
  line. A second, separately prompted model instance audited the claims in this document; its
  corrections are incorporated.

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
pinned by the catalog at `9097e2f`). It does not touch the repository's root `lakefile.lean`.

| File | Contents |
|---|---|
| `DensityHypothesis/Defs.lean` | The catalog's definitions `Complex.zeroCountOn`, `DensityHypothesis.zetaZeroCount` and their lemmas: the same source text as the catalog at `9097e2f`, with its licence notice |
| `DensityHypothesis/ZeroCount.lean` | The whole proof (steps 1–6) |
| `DensityHypothesis/Main.lean` | The three headline theorems, stated with `zetaZeroCount` |
| `DensityHypothesis/Audit.lean` | `#print axioms` for the headline theorems |
| `InSitu.lean` | The same proof text behind `import FormalConjectures.Wikipedia.DensityHypothesis`; its final theorems have type `type_of% @density_hypothesis_zeta_zeros` and `type_of% @guth_maynard_zero_density` |
| `make_insitu.py` | Regenerates `InSitu.lean` from `DensityHypothesis/ZeroCount.lean` |
| `Challenge.lean`, `Solution.lean`, `comparator.json` | Statements only (Mathlib-only, proofs omitted on purpose), the module that proves them, and an untested comparator configuration |
| `formal-conjectures-status.patch` | A possible status change for the catalog entry |
| `RHComposition.lean` | The one-line composition with `riemannHypothesis`; for use inside the RH repository, not part of this Lake project |
| `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` | The pins; the manifest's package revisions are the catalog's at `9097e2f` |

A caveat about `Defs.lean`. The catalog's files use Lean's module system and this project does
not. The copied definitions have the same source text, but outside the module system Lean
resolves one instance inside `Complex.zeroCountOn` along a different path, so the elaborated
term is not literally the catalog's. The two are definitionally equal (`rfl` proves it), and
`InSitu.lean` avoids the question by using the catalog's own declarations.

## Verification

Everything below was run on 2026-11-24. The prebuilt Mathlib cache was not reachable from the
container this was written in, so Mathlib was compiled from source for each toolchain.

### 1. The project itself (Lean `4.33.1`, Mathlib `v4.33.1`)

```text
$ lake build
✔ [3793/3797] Built DensityHypothesis.Defs (2.2s)
✔ [3794/3797] Built DensityHypothesis.ZeroCount (8.2s)
✔ [3795/3797] Built DensityHypothesis.Main (2.4s)
✔ [3796/3797] Built DensityHypothesis (1.0s)
Build completed successfully (3797 jobs).

$ lake env lean DensityHypothesis/Audit.lean
'DensityHypothesis.density_hypothesis_zeta_zeros_of_riemannHypothesis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DensityHypothesis.guth_maynard_zero_density_of_riemannHypothesis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DensityHypothesis.zetaZeroCount_half_le_mul_log' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No errors and no warnings. The compiled declarations of the four modules were also replayed
through the kernel with the `leanchecker` that ships with Lean (`lake env leanchecker
DensityHypothesis.Defs DensityHypothesis.ZeroCount DensityHypothesis.Main DensityHypothesis`,
exit code 0).

The intended way to reproduce this is

```bash
cd proofs/density-hypothesis && lake exe cache get && lake build && lake env lean DensityHypothesis/Audit.lean
```

but that exact command was **not** run here, because `lake exe cache get` needs the cache host.
What was run is `lake build` with the packages directory pointing at the Mathlib compiled from
source, once in the working tree and once in a fresh clone of the pushed branch.

### 2. In situ, against the unmodified catalog file

In a clean checkout of the catalog at `9097e2f`, after
`lake build FormalConjectures.Wikipedia.DensityHypothesis` (8987 jobs, all of Mathlib included):

```text
$ lake env lean InSitu.lean
'DensityHypothesis.density_hypothesis_zeta_zeros_of_riemannHypothesis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DensityHypothesis.guth_maynard_zero_density_of_riemannHypothesis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DensityHypothesisProof.zeroCountOn_strip_le_mul_log' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`InSitu.lean` imports the catalog module and states its two theorems as
`(hRH : RiemannHypothesis) : type_of% @density_hypothesis_zeta_zeros` and
`… : type_of% @guth_maynard_zero_density`, so the statements are supplied by Lean from the
catalog's own declarations, not retyped. For comparison, in the same checkout
`#print axioms DensityHypothesis.density_hypothesis_zeta_zeros` (the catalog's theorem) lists
`sorryAx`.

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

### 3. Statements-only challenge file

`Challenge.lean` imports only Mathlib and states the three headline theorems with their proofs
omitted; `Solution.lean` re-exports the proved ones. Both modules build
(`lake build Challenge Solution`: the three intended `sorry` warnings in `Challenge.lean` and
nothing else). The types of the three theorems were dumped from each module; their hashes and
printed forms agree. `comparator.json` is written after the configurations of other projects and
has **never been run**: the comparator tool (kernel replay, second kernel, sandbox) was not
available here.

### 4. Compatibility with the RH repository's toolchain

`leanprover-community/riemann-hypothesis` (at `9282d3a`) uses Lean `v4.37.0-rc1` and Mathlib
`31ce06e`. In a scratch Lake workspace with exactly those pins:

* `lake build DensityHypothesis` succeeds with the library files of this directory unchanged. The
  only warnings are Lake's reminders that these files import Mathlib without using the module
  system.
* `RHComposition.lean` typechecks against that repository's statements-only module:

  ```text
  $ lake env lean RHComposition.lean
  'density_hypothesis_zeta_zeros' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
  'DensityHypothesis.density_hypothesis_zeta_zeros_of_riemannHypothesis' depends on axioms: [propext,
   Classical.choice,
   Quot.sound]
  ```

  The `sorryAx` is the omitted proof of `riemannHypothesis` in their `src/Challenge.lean` (used
  here with its `import Mathlib` narrowed to the two Mathlib modules it needs, so that all of
  Mathlib did not have to be compiled a second time). Importing their `Main` instead of
  `Challenge` replaces it by their proof. That last step needs their full build and was not run.

### 5. The root project's toolchain (Lean `4.32.0`, Mathlib `v4.32.0`)

_A build with these versions was still running when this revision was committed; this section is
updated with its result._ Until then: of the 451 Mathlib theorems the proof terms use, 420 occur
by name in the `v4.32.0` sources and the other 31 are generated names (instances, additive
versions, projections) that a source search cannot confirm.

### 6. Not done

* **No independent CI run.** The repository's `Manual Lean audit` workflow could not be started
  from the session that wrote this: the integration token is not allowed to dispatch workflows.
* **Not composed with the actual proof of RH**, only with its statement (part 4).
* **The comparator tool was not run** (part 3).
* **`lake exe cache get` was never executed** (part 1).

## Was this already done? Evidence as of 2026-11-24

Nobody can prove a negative. This is what was checked.

1. **The catalog lists it as open.** At `google-deepmind/formal-conjectures` commit
   `9097e2f90e66d2f6244209cb1c07f7120d17ec53` (2026-11-24 14:16 UTC, still the head of `main` when
   re-fetched at 22:09 UTC that day), `density_hypothesis_zeta_zeros` carries
   `@[category research open, AMS 11 30]`, its proof is `sorry`, and it has no `formal_proof`
   attribute. The file was added on 2026-11-23 (commit `f9b3868`, PR 8057), three days after the
   proof of RH was released, and that is its only commit.
2. **The commit that marked RH as solved did not touch it.** Commit `6bc2f74` (PR 8111,
   2026-11-24 09:39 UTC), "set the status of the (generalized) Riemann hypothesis to solved",
   edited eleven files. Among other things it moved Robin's and Lagarias's inequalities, Li's
   criterion, the idoneal number list, Erdős 985 and the powerful-number error term to
   `research solved`, and added a solved variant for Mills' constant.
   `Wikipedia/DensityHypothesis.lean` is not among the files it changed. Whether that was an
   oversight is a guess: the same commit also left other files that mention RH untouched.
3. **No pull request touches it.** On 2026-11-24 at 22:10 UTC the head commits of all 5,496
   pull requests ever opened on the repository (open or closed) were fetched. 61 of them contain
   `FormalConjectures/Wikipedia/DensityHypothesis.lean`, every one with exactly the version on
   `main`. For the 143 pull requests numbered 8057 to 8269, the ones opened since the file
   existed, no other file mentions `density_hypothesis_zeta_zeros`, `zetaZeroCount` or
   `DensityHypothesis` either.
4. **It is not among the RH repository's headline theorems.**
   `leanprover-community/riemann-hypothesis` at `9282d3a` proves five theorems in `src/Main.lean`:
   `riemannHypothesis`, its restatement `riemannZeta_eq_zero_re`, and three statements about
   Dirichlet L-functions. Its README says files not needed for those are out of scope. The other
   roughly 60 000 files of that repository were **not** examined, only their path names, so a
   zero-density lemma somewhere inside it cannot be ruled out.
5. **Related formal work found by web search.**
   * [anthropics/zeta-23-lean](https://github.com/anthropics/zeta-23-lean) (`zeta23/`, at
     `11b6c7e`): already contains the unconditional zero count that step 5 needs, as described
     above. No file in that repository mentions a zero-density statement or the Density
     Hypothesis.
   * [mrklwk/zeta-zero-density-lean](https://github.com/mrklwk/zeta-zero-density-lean) (October
     2026): an unconditional bound `N(σ, T) ≪ T^(2(1−σ)+ε)` for each fixed `3/4 < σ < 1`, with a
     constant depending on `σ`. Not uniform down to `1/2`.
   * [finndoolan-m/rh-lindelof](https://github.com/finndoolan-m/rh-lindelof) (2026-11-22): RH
     implies the Lindelöf hypothesis. No zero-density statement.

What this evidence does not exclude: a proof that is unpublished, unindexed, inside the RH
repository's 60 000 files, or posted after the times above.

## Proposing the status change upstream

Two routes exist in the catalog, and neither has been started.

* **As a conditional formal proof.** The catalog's attribute
  `@[conditional formal_proof using lean4 at "<link>" assuming <decl>]` is made for a proof that
  takes an unproved statement as a hypothesis, which is exactly what this library provides.
* **As a solved statement.** `formal-conjectures-status.patch` changes the entry to
  `research solved` and adds a docstring. Its sentence "which is proved [Al26]" copies the wording
  commit `6bc2f74` used for the other RH corollaries; it is the catalog's convention, not a claim
  this project has checked. The patch adds no `formal_proof` attribute.

Either way the catalog requires the link for a research problem to point at a
[Palomar](https://palomar-registry.org/) entry. `Challenge.lean`, `Solution.lean` and
`comparator.json` follow that registry's layout as seen in other projects, untested; a
`formalization.yaml` with authorship and licence metadata is still to be written by whoever
submits it. This repository has no `LICENSE` file of its own; the definitions copied from the
catalog keep their Apache-2.0 notice.
