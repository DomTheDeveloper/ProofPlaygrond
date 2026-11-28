# A245211 through least prime 467

For every positive integer $n$ having a prime divisor at most 467,
$$
\sum_{d\mid n,\ d<n} d\,\tau(d)=n \quad\Longleftrightarrow\quad n=21.
$$
There is no upper bound on $n$. Any other fixed point has least prime at least 479.

This computer-assisted partial result extends the previous all-support certificate through least prime 463. At least prime 467 both exact programs exhaust 25,345 ordered exponent patterns. The integer search visits 67,262 nodes after its exact filters. Both searches return an empty list. Together with the previous 754,883 patterns this gives 780,228 ordered exponent patterns through 467. The unrestricted conjecture remains open.

## Arithmetic certificate

Put $T_e(p)=\sum_{j=0}^{e}(j+1)p^j$. At a fixed point, the full divisor moment is $n(\tau(n)+1)$. Therefore a prime factor of a local moment whose multiplicity cannot be absorbed by the known prime powers or $\tau(n)+1$ must occur in a remaining prime-power component.

The hard branches have leading exponents 9 and 57. The first uses the complete factorization
$$
T_9(467)=7083499\cdot782494331\cdot1909680203.
$$
For the second it is enough to certify the exact divisor
$$
76160799733\mid T_{57}(467).
$$
Every displayed factor is prime. Both checkers verify complete recursive Lucas certificates for the factors above 10 million. A complete factorization of the remaining cofactor of $T_{57}(467)$ is not assumed or needed.

The integer checker verifies each full-order witness by modular exponentiation. The rational checker independently verifies that the corresponding residues minus one are coprime to $q$. Leaves are checked by exact trial division.

The search methods remain independent. One uses integer inequalities, congruence filters and an ordered prime search. The other works with exact fractions and places forced factors directly. Both enumerate the same exponent budget but traverse the prime choices differently. [Previous certificate through 463](https://github.com/DomTheDeveloper/ProofPlaygrond/tree/55f5276d74ea850db5590dd059c30980c6f28cfe/proofs/oeis-divisor-sums/A245211/least-prime-463) · [Lean two-prime reduction #12841](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/12841)

## Reproduction

Run the strict verifier with Python 3.10 or later.

```sh
python3 -I verify_467.py
```

Expected output

```text
467 25345 67262 [] 25345 []
780,228 ordered exponent patterns through least prime 467. The sole fixed point is 21.
```

Jaroslav Křížek posed the original conjecture. Exact computation and continuation by @DomTheDeveloper. Research priority is unestablished. [OEIS A245211](https://oeis.org/A245211)
