# A245211 through least prime 449

For every positive integer $n$ having a prime divisor at most 449,
$$
\sum_{d\mid n,\ d<n} d\,\tau(d)=n \quad\Longleftrightarrow\quad n=21.
$$
There is no upper bound on $n$. Any other fixed point has least prime at least 457.

This computer-assisted partial result extends the previous all-support certificate through least prime 443. At least prime 449 both exact programs exhaust 24,267 ordered exponent patterns. The integer search visits 115,939 nodes after its exact filters. Both searches return an empty list. Together with the previous 655,391 patterns this gives 679,658 ordered exponent patterns through 449. The unrestricted conjecture remains open.

## Arithmetic certificate

Put $T_e(p)=\sum_{j=0}^{e}(j+1)p^j$. At a fixed point, the full divisor moment is $n(\tau(n)+1)$. Therefore a prime factor of a local moment whose multiplicity cannot be absorbed by the known prime powers or $\tau(n)+1$ must occur in a remaining prime-power component.

The two hard least-prime branches have exponents 25 and 28. Their complete local-moment factorizations are
$$
T_{25}(449)=1003019\cdot1270103\cdot32851801\cdot175265246899\cdot7188856581307871918843714684616645809
$$
and
$$
T_{28}(449)=3\cdot5\cdot627033833\cdot8293215599\cdot68253551466812881771107551041923103554447956989416451003.
$$
Every displayed factor is prime. The checkers prove the large factors recursively with complete Lucas certificates, including complete factorizations of every intermediate $q-1$.

The integer checker verifies each full-order witness by modular exponentiation. The rational checker independently verifies that the corresponding residues minus one are coprime to $q$. Leaves are checked by exact trial division.

The search methods remain independent. One uses integer inequalities, congruence filters and an ordered prime search. The other works with exact fractions and places forced factors directly. Both enumerate the same exponent budget but traverse the prime choices differently. [Previous certificate through 443](https://github.com/DomTheDeveloper/ProofPlaygrond/tree/87c8ce9f91f1ec1f7a9a9c383614c37536ecc1a6/proofs/oeis-divisor-sums/A245211/least-prime-443) · [Lean two-prime reduction #12841](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/12841)

## Reproduction

Run the strict verifier with Python 3.10 or later.

```sh
python3 -I verify_449.py
```

Expected output

```text
449 24267 115939 [] 24267 []
679,658 ordered exponent patterns through least prime 449. The sole fixed point is 21.
```

Jaroslav Křížek posed the original conjecture. Exact computation and continuation by @DomTheDeveloper. Research priority is unestablished. [OEIS A245211](https://oeis.org/A245211)
