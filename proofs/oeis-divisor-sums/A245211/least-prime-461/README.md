# A245211 through least prime 461

For every positive integer $n$ having a prime divisor at most 461,
$$
\sum_{d\mid n,\ d<n} d\,\tau(d)=n \quad\Longleftrightarrow\quad n=21.
$$
There is no upper bound on $n$. Any other fixed point has least prime at least 463.

This computer-assisted partial result extends the previous all-support certificate through least prime 457. At least prime 461 both exact programs exhaust 25,069 ordered exponent patterns. The integer search visits 3,180 nodes after its exact filters. Both searches return an empty list. Together with the previous 704,595 patterns this gives 729,664 ordered exponent patterns through 461. The unrestricted conjecture remains open.

## Arithmetic certificate

Put $T_e(p)=\sum_{j=0}^{e}(j+1)p^j$. At a fixed point, the full divisor moment is $n(\tau(n)+1)$. Therefore a prime factor of a local moment whose multiplicity cannot be absorbed by the known prime powers or $\tau(n)+1$ must occur in a remaining prime-power component.

The two hard least-prime branches have exponents 25 and 28. Their complete local-moment factorizations are
$$
T_{25}(461)=477647899\cdot213449622406948886201024974616126238622162775909475855225749
$$
and
$$
T_{28}(461)=3\cdot5\cdot70158841\cdot9007375573716328043\cdot1175337272633976315693605334810791115007970821343.
$$
Every displayed factor is prime. The checkers prove the large factors recursively with complete Lucas certificates, including complete factorizations of every intermediate $q-1$.

The integer checker verifies each full-order witness by modular exponentiation. The rational checker independently verifies that the corresponding residues minus one are coprime to $q$. Leaves are checked by exact trial division.

The search methods remain independent. One uses integer inequalities, congruence filters and an ordered prime search. The other works with exact fractions and places forced factors directly. Both enumerate the same exponent budget but traverse the prime choices differently. [Previous certificate through 457](https://github.com/DomTheDeveloper/ProofPlaygrond/tree/b164106ab57bcde397528bbbef9227c4fecd4e33/proofs/oeis-divisor-sums/A245211/least-prime-457) · [Lean two-prime reduction #12841](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/12841)

## Reproduction

Run the strict verifier with Python 3.10 or later.

```sh
python3 -I verify_461.py
```

Expected output

```text
461 25069 3180 [] 25069 []
729,664 ordered exponent patterns through least prime 461. The sole fixed point is 21.
```

Jaroslav Křížek posed the original conjecture. Exact computation and continuation by @DomTheDeveloper. Research priority is unestablished. [OEIS A245211](https://oeis.org/A245211)
