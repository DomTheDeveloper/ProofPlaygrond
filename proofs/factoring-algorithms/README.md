# Deterministic factor searches

These four Lean developments specify the algorithms and the inputs on which their bounds hold.

| File | Result | Environment |
| --- | --- | --- |
| `CertifiedTrialFactor.lean` | Correct trial division, a superpolynomial family for its sequential search, and a separate bit-machine bound for extracting factors 2 and 3. | Lean and mathlib 4.33.1 |
| `BinarySmoothFactor.lean` | Correct factorization on every input at least two. The binary machine has polynomial transition cost when every prime factor is bounded by a fixed power of the input bit length. Prime squares give a superpolynomial family for this machine. | Lean 4.19.0 with Std |
| `CubeRootFactor.lean` | Correct deterministic factorization with a cube-root-scale probe bound. The file also proves a superpolynomial lower bound for this search on a balanced input family. A probe counts a divisibility or square test. | Lean 4.19.0 with Std |
| `FactorMidpointSearch.lean` | For odd semiprimes, a power-of-two midpoint search succeeds under a bound on the odd part of the factor sum or difference. The formal results include soundness, a finite coverage guarantee and limits of complete modular filters. | Lean and mathlib 4.33.1 |

The first three files analyze particular algorithms. The fourth file explains the bit-cost deduction for its restricted family and the root-count estimate it uses. Deterministic classical polynomial-time factorization on all inputs is still open.

For each Std file, run `lean FileName.lean` with Lean 4.19.0. For each mathlib file, run `lake env lean FileName.lean` in a mathlib 4.33.1 project. The earlier bounded-divisor oracle and factor-ratio results are in [PR #133](https://github.com/DomTheDeveloper/ProofPlaygrond/pull/133).
