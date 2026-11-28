# A245211 through least prime 479

For every positive integer $n$ having a prime divisor at most 479,
$$
\sum_{d\mid n,\ d<n} d\,\tau(d)=n \quad\Longleftrightarrow\quad n=21.
$$
There is no upper bound on $n$. Any other fixed point has least prime at least 487.

This computer-assisted partial result extends the previous all-support certificate through least prime 467. At least prime 479 both exact programs exhaust 25,923 ordered exponent patterns. The integer search visits 3,836 nodes after its exact filters. Both searches return an empty list. Together with the previous 780,228 patterns this gives 806,151 ordered exponent patterns through 479. The unrestricted conjecture remains open.

## Arithmetic certificate

Put $T_e(p)=\sum_{j=0}^{e}(j+1)p^j$. At a fixed point, the full divisor moment is $n(\tau(n)+1)$. Therefore a prime factor of a local moment whose multiplicity cannot be absorbed by the known prime powers or $\tau(n)+1$ must occur in a remaining prime-power component.

The hard branches have leading exponents 4, 12, and 25. They use the complete factorizations
$$
T_4(479)=3\cdot9439\cdot9310879,
$$
$$
T_{12}(479)=23957\cdot79318556486132556604693560491,
$$
and
$$
T_{25}(479)=68281\cdot236707\cdot2263228226288717\cdot7260968101982946665652131488052126390641693.
$$
Every displayed factor is prime. Both checkers verify complete recursive Lucas certificates for the factors above 10 million.

The integer checker verifies each full-order witness by modular exponentiation. The rational checker independently verifies that the corresponding residues minus one are coprime to $q$. Leaves are checked by exact trial division.

The search methods remain independent. One uses integer inequalities, congruence filters and an ordered prime search. The other works with exact fractions and places forced factors directly. Both enumerate the same exponent budget but traverse the prime choices differently. [Previous certificate through 467](https://github.com/DomTheDeveloper/ProofPlaygrond/tree/b4a3c2ceac746bbfeef4cf58ea11b52a29066d67/proofs/oeis-divisor-sums/A245211/least-prime-467) · [Merged Lean reduction #12841](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/12841)

## Reproduction

Run the strict verifier with Python 3.10 or later.

```sh
python3 -I verify_479.py
```

Expected output

```text
479 25923 3836 [] 25923 []
806,151 ordered exponent patterns through least prime 479. The sole fixed point is 21.
```

Jaroslav Křížek posed the original conjecture. Exact computation and continuation by @DomTheDeveloper. Research priority is unestablished. [OEIS A245211](https://oeis.org/A245211)
