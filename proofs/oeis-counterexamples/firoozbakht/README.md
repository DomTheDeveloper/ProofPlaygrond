# A086766 verification

The decimal block **109890** gives a composite for every positive number of concatenations followed by a final digit 1. It refutes both Farideh Firoozbakht’s 2015 conjecture and the revision proposed on MersenneForum in 2022.

## Priority

The 2015 conjecture asserts that every positive block other than a power of ten eventually yields a prime. On July 10, 2022, MersenneForum user **sweety439** explicitly refuted it using 1010 and 100100. The post then proposed excluding all repeated blocks of the form 1 followed by one or more zeros. Its discussion also uses difference-of-squares arguments in other bases. The digits 8 and 9 in 109890 put it outside the proposed exclusion. [OEIS A086766](https://oeis.org/A086766/internal) · [MersenneForum discussion](https://archive.ph/zao2Y)

As of November 24, 2026, searches of the sequence and its companion, the indexed mathematical literature and public proof records located no earlier decimal counterexample to the revised claim. The conclusion about priority is provisional. OEIS records computational lower bounds for 47 and 67 and leaves open whether either sequence value is zero. The public 492-question OEIS Open catalog includes a different question from A086766, concerning powers of ten. The number 109890 also occurs in A393794 for a digit-reversal property. [Companion sequence](https://oeis.org/A087403) · [OEIS Open catalog](https://github.com/epoch-research/LeanOpenProblems-results/blob/main/metadata/oeis/conjectures.json) · [A393794](https://oeis.org/A393794)

Grantham, Jarnicki, Rickert, and Wagon studied another way to generate composites by concatenation. Their construction fixes an initial integer and appends repetitions of one digit. Here the repeating part is the six-digit block and the fixed part is the final 1. [2019 paper](https://arxiv.org/abs/1903.05023)

## Proof

Write N(r) for the number formed from r copies of 109890 followed by 1. The geometric sum gives 91 N(r) = (10·1000ʳ)² − 9. For x = 10·1000ʳ and s = (−1)ʳ, the two integers (x − 3s)/7 and (x + 3s)/13 multiply to N(r). Indeed, 1000 ≡ −1 modulo 91, and 10 ≡ 3 modulo 7 and −3 modulo 13. Each factor exceeds one for r ≥ 1. The first case is 1,098,901 = 1,429 × 769.

## Formal verification

The certificate proves that the sequence takes value zero at 109890 and that the block satisfies the hypotheses of both claims. The target checker imports DeepMind’s module, proves by reflexivity that the sequence definitions agree, and reads the actual type of OeisA86766.conjecture2 from Lean’s environment. It uses the saved certificate to prove the negation of that type. The positive statement in DeepMind’s repository has a placeholder proof. The axiom report for the negation contains only propext, Classical.choice, and Quot.sound.

The audited repository revision is `9097e2f90e66d2f6244209cb1c07f7120d17ec53`. It pins Lean 4.33.1 and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. The saved proof has SHA-256 `be7accd682caac54e79008e809487bdd2a3d939376ef1fe9f44c75f6a7cb7117`. [Pinned DeepMind file](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/OEIS/86766.lean)

From a checkout of that revision with its dependencies installed, run the following. Replace the path on the second line with the location of the extracted script.

```sh
lake build FormalConjectures/OEIS/86766.lean:olean
lake env bash /path/to/replay.sh
```

The verifier requires both files to compile with warnings treated as errors. It then uses Lean’s kernel replay tool on both generated modules. The attached verification log records the observed outputs.
