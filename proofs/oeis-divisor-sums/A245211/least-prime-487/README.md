# A245211 through least prime 487

For every positive integer $n$ having a prime divisor at most 487,
$$
\sum_{d\mid n,\ d<n} d\,\tau(d)=n \quad\Longleftrightarrow\quad n=21.
$$
There is no upper bound on $n$. Any other fixed point has least prime at least 491.

This computer-assisted partial result extends the previous all-support certificate through least prime 479. At least prime 487 both exact programs exhaust 28,189 ordered exponent patterns. The integer search visits 45,637 nodes after its exact filters. Both searches return an empty list. Together with the previous 806,151 patterns this gives 834,340 ordered exponent patterns through 487. The unrestricted conjecture remains open.

## Arithmetic certificate

Put $T_e(p)=\sum_{j=0}^{e}(j+1)p^j$. At a fixed point, the full divisor moment is $n(\tau(n)+1)$. Therefore a prime factor of a local moment whose multiplicity cannot be absorbed by the known prime powers or $\tau(n)+1$ must occur in a remaining prime-power component.

The hard branches have leading exponents 9 and 60. They are closed by the certified prime divisors
$$
10985291\mid T_9(487),
\qquad
2278303\mid T_{60}(487).
$$
No assumption is made about either cofactor. Both checkers prove the two displayed divisors prime from complete Lucas certificates: they multiply the listed prime factors of $q-1$ back exactly, verify a full-order witness modulo $q$, and check the leaves by exact trial division.

The integer checker verifies each full-order witness by modular exponentiation. The rational checker independently verifies that the corresponding residues minus one are coprime to $q$. Leaves are checked by exact trial division.

The search methods remain independent. One uses integer inequalities, congruence filters and an ordered prime search. The other works with exact fractions and places forced factors directly. Both enumerate the same exponent budget but traverse the prime choices differently. [Previous certificate through 479](https://github.com/DomTheDeveloper/ProofPlaygrond/tree/5d323af623b77a28aa71334e00d09eb3da5ad72c/proofs/oeis-divisor-sums/A245211/least-prime-479) · [Merged Lean reduction #12841](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/12841)

## Reproduction

Run the strict verifier with Python 3.10 or later.

```sh
python3 -I verify_487.py
```

Expected output

```text
487 28189 45637 [] 28189 []
834,340 ordered exponent patterns through least prime 487. The sole fixed point is 21.
```

Jaroslav Křížek posed the original conjecture. Exact computation and continuation by @DomTheDeveloper. Research priority is unestablished. [OEIS A245211](https://oeis.org/A245211)
