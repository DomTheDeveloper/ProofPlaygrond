# Reducing the Riemann hypothesis proof in Lean

`OrdinaryRH` proves Mathlib’s `RiemannHypothesis` with no hypotheses. `AllClaims` preserves all five statements in Levent Alpöge’s original release, including the Dirichlet L-function results. Both targets reuse the pinned arithmetic archive. The counts below include every reachable project source and exclude Lean and Mathlib throughout.

| Target | Imported archive files | New Lean files | New lines | Complete source lines |
| --- | ---: | ---: | ---: | ---: |
| Original release | 175,187 | 0 | 0 | 17,374,215 |
| Earlier ordinary-RH specialization by David Sanftenberg | 165,070 | 31 | 4,024 | 16,646,436 |
| Ordinary RH in this branch | 164,424 | 2 | 2,533 | 16,599,659 |
| All five original statements in this branch | 175,128 | 1 | 52 | 17,371,572 |

## Ordinary RH

The arithmetic produces intervals `[Y, Y^(3/2)]` starting arbitrarily far out. On each interval the principal-character error is bounded above by `x^θ`, for each fixed exponent strictly between one half and one. If a zeta zero lay to the right of the critical line, one could choose such an exponent below its real part. The archive’s zero-free criterion excludes that zero. The functional equation for completed zeta reflects a nontrivial zero on the left into the same excluded region.

The 33-line analytic file applies the criterion directly to the character modulo one. The geometric file uses Sanftenberg’s single-family construction to supply the rank, divisibility and spectral estimates together. It keeps the declarations used by the endpoint. At 38 theorem references it selects a proof of the same type that permits a smaller set of imports. These replacements remove another 645 archive modules from the first version of this branch.

[Analytic deduction](PrincipalWindows.lean) · [Geometric proof and closed theorem](OrdinaryRH.lean)

## All five statements

The literature hypotheses construct the arithmetic windows for every character. The archived comparison then gives zero-freeness for every Dirichlet L-function to the right of one half. From this the reduced file derives both zeta statements, the critical-strip statement for every character, and its primitive-character specialization. It type-checks each result against the original release’s statement file and audits their combined axioms.

[Five-statement proof](AllClaims.lean)

## Verification

The workflow uses stock Lean 4.33.1, the release’s pinned Mathlib and a SHA-256 verified archive of previously compiled dependencies. Each target compiles its new Lean files at trust level zero with warnings treated as errors, checks the standard axiom set, and replays the new modules with `leanchecker`. A green job for the target and commit records its verification. The original archive also has independent kernel replays.

[GitHub Actions](https://github.com/DomTheDeveloper/ProofPlaygrond/actions/workflows/riemann-proof-reduction.yml) · [Independent checks of the original release](https://math.mit.edu/~drew/grh/) · [Earlier principal-character verification](https://github.com/leanprover-community/riemann-hypothesis/pull/38)

## Rebuild a complete source project

From this directory, the following commands create a native Lake project containing the two ordinary-RH files and every archive source they import. The materializer checks the original commit and dependency pins. It rejects local changes or untracked files in the archive source directory.

```sh
git init archive
git -C archive fetch --depth=1 https://github.com/leanprover-community/riemann-hypothesis.git 40e56bab026552e089d7afcfeff08d2defb9c005
git -C archive checkout --detach FETCH_HEAD
python3 source.py archive --target OrdinaryRH --output reduced
cd reduced
lake exe mathlib/cache get
lake build OrdinaryRH
lake env leanchecker -v OrdinaryRH
```

To build the five-statement version, choose `--target AllClaims` and use `AllClaims` in the two final commands. For counts alone omit `--output reduced`. With previously compiled archive dependencies, `bash verify.sh /path/to/archive /path/to/archive/.lake/build/lib/lean OrdinaryRH` rechecks the ordinary proof. Its last argument also accepts `AllClaims`.

The ordinary specialization adapts David Sanftenberg’s Apache-2.0 code at commit `d7857c26d332c8ebcd30d98e96acaee67b61715d`. The underlying mathematical proof is due to Levent Alpöge, working with Claude. [Original announcement](https://alpo.ge/remark.pdf) · [Specialization source](https://github.com/dbsanfte/riemann-hypothesis/tree/d7857c26d332c8ebcd30d98e96acaee67b61715d/src/PrincipalRH) · [License for the adapted source](LICENSE)
