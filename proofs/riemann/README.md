# An ordinary Riemann hypothesis reduction in Lean

The target is Mathlib’s `RiemannHypothesis`, with no hypotheses in the theorem’s type. The proof specializes Levent Alpöge’s arithmetic argument to the principal Dirichlet character using David Sanftenberg’s single-family construction. The local files contain the analytic deduction and the geometric assembly. Their imported arithmetic is part of the proof.

| Source | Lean files | Physical source lines |
| --- | ---: | ---: |
| Alpöge’s original release, including the Dirichlet statements | 175,187 | 17,374,215 |
| Original modules imported by this reduction | 165,069 | 16,642,350 |
| PrincipalWindows and OrdinaryRH, including the axiom check | 2 | 2,549 |
| Complete ordinary-RH source over Lean and Mathlib | 165,071 | 16,644,899 |

The local assembly keeps the route that produces one principal-character family with compatible rank, divisibility and spectral estimates. The principal-level window theorem applies the archive’s zero-free criterion at the trivial character directly. A zero to the right of the critical line would violate the criterion at an exponent strictly between one half and its real part. The functional equation for completed zeta reflects a nontrivial zero on the left into that same excluded region.

[Principal-window deduction](PrincipalWindows.lean) · [Geometric assembly and closed theorem](OrdinaryRH.lean)

## Verification

Lean 4.33.1 accepted the local principal-window deduction. The branch workflow checks both files using the release’s exact toolchain, the pinned Mathlib and a SHA-256 checked archive of compiled imports. It checks that the closed declaration has Mathlib’s RH type, enforces the standard three axioms, and replays each local module with `leanchecker`. A green run for the specific commit is the full check of the combined source.

[Branch workflow](../../.github/workflows/riemann-proof-reduction.yml) · [Verification of the original archive](https://math.mit.edu/~drew/grh/) · [Earlier principal-character check](https://github.com/leanprover-community/riemann-hypothesis/pull/38)

## Rebuild from the reduced source

From this directory, with Git, Python 3, and elan installed, the following creates a native Lake project containing both local files and each imported archive source. The script checks the original commit, rejects modified or untracked archive sources, and counts every file it copies. Lean and Mathlib are external dependencies in both line counts.

```sh
git init archive
git -C archive fetch --depth=1 https://github.com/leanprover-community/riemann-hypothesis.git 40e56bab026552e089d7afcfeff08d2defb9c005
git -C archive checkout --detach FETCH_HEAD
python3 source.py archive --output reduced
cd reduced
lake exe mathlib/cache get
lake build OrdinaryRH
lake env leanchecker -v OrdinaryRH
```

With a previously built original archive, `bash verify.sh /path/to/archive /path/to/archive/.lake/build/lib/lean` checks the two local files against those imports. Use `python3 source.py /path/to/archive` for the source count alone.

The ordinary-RH specialization is derived from David Sanftenberg’s Apache-2.0 code at commit `d7857c26d332c8ebcd30d98e96acaee67b61715d`. This edition combines the geometric declarations used by the endpoint, replaces the principal-window argument, and performs one axiom audit on the closed theorem. The earlier specialization reports 165,070 archive modules plus 31 local modules. Credit for the underlying mathematical proof belongs to Levent Alpöge, working with Claude. [Original announcement](https://alpo.ge/remark.pdf) · [Specialization source](https://github.com/dbsanfte/riemann-hypothesis/tree/d7857c26d332c8ebcd30d98e96acaee67b61715d/src/PrincipalRH) · [License for the adapted source](LICENSE)
