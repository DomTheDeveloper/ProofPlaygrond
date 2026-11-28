# A245211 through least prime 463

For every positive integer $n$ having a prime divisor at most 463,
$$
\sum_{d\mid n,\ d<n} d\,\tau(d)=n \quad\Longleftrightarrow\quad n=21.
$$
There is no upper bound on $n$. Any other fixed point has least prime at least 467.

This computer-assisted partial result extends the previous all-support certificate through least prime 461. At least prime 463 both exact programs exhaust 25,219 ordered exponent patterns. The integer search visits 2,366 nodes after its exact filters. Both searches return an empty list. Together with the previous 729,664 patterns this gives 754,883 ordered exponent patterns through 463. The unrestricted conjecture remains open.

## Arithmetic certificate

Put $T_e(p)=\sum_{j=0}^{e}(j+1)p^j$. At a fixed point, the full divisor moment is $n(\tau(n)+1)$. Therefore a prime factor of a local moment whose multiplicity cannot be absorbed by the known prime powers or $\tau(n)+1$ must occur in a remaining prime-power component.

No new local-moment factorization is required at least prime 463: the exact inequalities, congruence filters, and previously embedded complete primality certificates close every branch.

The integer checker verifies each full-order witness by modular exponentiation. The rational checker independently verifies that the corresponding residues minus one are coprime to $q$. Leaves are checked by exact trial division.

The search methods remain independent. One uses integer inequalities, congruence filters and an ordered prime search. The other works with exact fractions and places forced factors directly. Both enumerate the same exponent budget but traverse the prime choices differently. [Previous certificate through 461](https://github.com/DomTheDeveloper/ProofPlaygrond/tree/aa0ba32468ce0b6b558988df5af61661cd0c685d/proofs/oeis-divisor-sums/A245211/least-prime-461) · [Lean two-prime reduction #12841](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/12841)

## Reproduction

Run the strict verifier with Python 3.10 or later.

```sh
python3 -I verify_463.py
```

Expected output

```text
463 25219 2366 [] 25219 []
754,883 ordered exponent patterns through least prime 463. The sole fixed point is 21.
```

Jaroslav Křížek posed the original conjecture. Exact computation and continuation by @DomTheDeveloper. Research priority is unestablished. [OEIS A245211](https://oeis.org/A245211)
