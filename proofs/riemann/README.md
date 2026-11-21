# One Lean file for the five Riemann hypothesis statements

[CompactRH.lean](CompactRH.lean) uses 482 lines of new Lean to close the five statements of Levent Alpöge’s release, including Mathlib’s `RiemannHypothesis`. Its complete project contains **16,595,972 lines**, after counting every imported arithmetic source. Lean and Mathlib are external dependencies on both sides of the comparison.

| Source | Lean files | Source lines |
| --- | ---: | ---: |
| Original release, all five statements | 175,187 | 17,374,215 |
| Original arithmetic imported by this version | 164,429 | 16,595,490 |
| New proof and axiom audit | 1 | 482 |
| Complete reduced project, all five statements | 164,430 | 16,595,972 |
| Removed from the release | 10,757 | 778,243 |

## The argument

The same local theta identities, covolume bound, Galois representation and local Langlands existence results can feed the archive’s comparison theorem for **every** Dirichlet character. The proof constructs the arithmetic-window hypothesis for every character from a single collection of proved results. Applying the comparison once yields zero-freeness to the right of one half. Reflection gives the critical-strip statements. Specializing to the principal character gives ordinary RH.

The hard mathematics lies in proving the arithmetic estimates and identities. The 482-line file supplies each one using the imported results. Selecting shorter routes to those inputs and reusing them across all five conclusions removes 778,243 lines from the complete source. The five declarations at the end have the names and types used by the original release. The joint axiom audit traverses the proofs of all five.

[Earlier 33-line principal-window deduction](https://github.com/DomTheDeveloper/ProofPlaygrond/blob/43cff8aa194597b2f4ae674aa7d6d991a8ed9283/proofs/riemann/PrincipalWindows.lean) · [Earlier ordinary-RH project in this repository](https://github.com/DomTheDeveloper/ProofPlaygrond/tree/43cff8aa194597b2f4ae674aa7d6d991a8ed9283/proofs/riemann)

## Verification

GitHub Actions uses stock Lean 4.33.1, the release’s pinned Mathlib, and a SHA-256 checked archive of previously compiled dependencies. It compiles `CompactRH.lean` with trust level zero and warnings treated as errors. The audit enforces an axiom set consisting of `propext`, `Classical.choice` and `Quot.sound`. A separate step replays the newly compiled module with `leanchecker`. The compiled proof, reference data and compiler log are attached to the run. A green run records both checks for its exact commit.

[GitHub Actions](https://github.com/DomTheDeveloper/ProofPlaygrond/actions/workflows/riemann-proof-reduction.yml) · [Independent verification of the original archive](https://math.mit.edu/~drew/grh/)

## Rebuild the complete reduced project

From this directory, with Git, Python 3 and elan installed, run these commands. The materializer checks the source commit and dependency pins, follows the imports, and copies the exact files it counts.

```sh
git init archive
git -C archive fetch --depth=1 https://github.com/leanprover-community/riemann-hypothesis.git 40e56bab026552e089d7afcfeff08d2defb9c005
git -C archive checkout --detach FETCH_HEAD
python3 source.py archive --output reduced
cd reduced
lake exe mathlib/cache get
lake build CompactRH
lake env leanchecker -v CompactRH
```

For source counts alone, run `python3 source.py archive`. With a previously built archive, `bash verify.sh /path/to/archive /path/to/archive/.lake/build/lib/lean` checks the new file and replays it.

The mathematical proof is due to Levent Alpöge, working with Claude. The arithmetic-input assembly adapts David Sanftenberg’s Apache-2.0 principal-character specialization at commit `d7857c26d332c8ebcd30d98e96acaee67b61715d`. This version removes the intermediate principal-only geometric constructions and supplies the general comparison theorem directly. [Original announcement](https://alpo.ge/remark.pdf) · [Previous specialization](https://github.com/leanprover-community/riemann-hypothesis/pull/38) · [License for adapted source](LICENSE)
