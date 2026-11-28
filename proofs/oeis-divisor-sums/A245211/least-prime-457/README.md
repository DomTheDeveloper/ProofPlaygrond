# A245211 through least prime 457

For every positive integer $n$ having a prime divisor at most 457,
$$
\sum_{d\mid n,\ d<n} d\,\tau(d)=n \quad\Longleftrightarrow\quad n=21.
$$
There is no upper bound on $n$. Any other fixed point has least prime at least 461.

This computer-assisted partial result extends the previous all-support certificate through least prime 449. At least prime 457 both exact programs exhaust 24,937 ordered exponent patterns. The integer search visits 247,007 nodes after its exact filters. Both searches return an empty list. Together with the previous 679,658 patterns this gives 704,595 ordered exponent patterns through 457. The unrestricted conjecture remains open.

## Arithmetic certificate

Put $T_e(p)=\sum_{j=0}^{e}(j+1)p^j$. At a fixed point, the full divisor moment is $n(\tau(n)+1)$. Therefore a prime factor of a local moment whose multiplicity cannot be absorbed by the known prime powers or $\tau(n)+1$ must occur in a remaining prime-power component.

No new local-moment factorization is required at least prime 457: the exact inequalities, congruence filters, and previously embedded complete primality certificates close every branch.

The integer checker verifies each full-order witness by modular exponentiation. The rational checker independently verifies that the corresponding residues minus one are coprime to $q$. Leaves are checked by exact trial division.

The search methods remain independent. One uses integer inequalities, congruence filters and an ordered prime search. The other works with exact fractions and places forced factors directly. Both enumerate the same exponent budget but traverse the prime choices differently. [Previous certificate through 449](https://github.com/DomTheDeveloper/ProofPlaygrond/tree/3d49e789c73f176acb911f4d2b5e70d917da5316/proofs/oeis-divisor-sums/A245211/least-prime-449) · [Lean two-prime reduction #12841](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/12841)

## Reproduction

Run the strict verifier with Python 3.10 or later.

```sh
python3 -I verify_457.py
```

Expected output

```text
457 24937 247007 [] 24937 []
704,595 ordered exponent patterns through least prime 457. The sole fixed point is 21.
```

Jaroslav Křížek posed the original conjecture. Exact computation and continuation by @DomTheDeveloper. Research priority is unestablished. [OEIS A245211](https://oeis.org/A245211)
