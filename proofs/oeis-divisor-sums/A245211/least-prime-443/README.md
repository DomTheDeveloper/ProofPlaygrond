# A245211 through least prime 443

For every positive integer $n$ having a prime divisor at most 443,
$$
\sum_{d\mid n,\ d<n} d\,\tau(d)=n \quad\Longleftrightarrow\quad n=21.
$$
There is no upper bound on $n$. Any other fixed point has least prime at least 449.

This computer-assisted partial result extends the previous all-support certificate through least prime 439. At least prime 443 both exact programs exhaust 23,653 ordered exponent patterns. The integer search visits 32,453 nodes after its exact filters. Both searches return an empty list. Together with the previous 631,738 patterns this gives 655,391 ordered exponent patterns through 443. The unrestricted conjecture remains open.

## Arithmetic certificate

Put $T_e(p)=\sum_{j=0}^{e}(j+1)p^j$. At a fixed point, the full divisor moment is $n(\tau(n)+1)$. Therefore a prime factor of a local moment whose multiplicity cannot be absorbed by the known prime powers or $\tau(n)+1$ must occur in a remaining prime-power component.

The new layer checks complete factorizations of the local moments at exponents 4, 5, 6, 7, 8, 9 and 13. The only six expensive branches are the six orderings of one exponent 4 among six exponent-1 components after the least component. Exponent 1 at 443 forces the next prime to be 887, and
$$
T_4(887)=3\cdot4817\cdot214367249.
$$
The final factor is prime by a complete Lucas certificate because
$$
214367249-1=2^4\cdot101\cdot109\cdot1217.
$$

Every large prime used by either search is proved recursively with a complete factorization of $q-1$. The integer checker verifies a full-order witness by modular exponentiation. The rational checker independently verifies that the corresponding residues minus one are coprime to $q$. Leaves are checked by exact trial division.

The search methods remain independent. One uses integer inequalities, congruence filters and an ordered prime search. The other works with exact fractions and places forced factors directly. Both enumerate the same exponent budget but traverse the prime choices differently. [Previous certificate through 439](https://github.com/DomTheDeveloper/ProofPlaygrond/tree/add1faae0607bc656897a158a34424ff2c50ff74/proofs/oeis-divisor-sums/A245211/least-prime-439) · [Lean two-prime theorem through 439](https://github.com/DomTheDeveloper/open-math-agents/blob/3c789e162ce0afbca110affd0f615e9ae0195c27/reductions/OeisA245211.conjecture.R3.lean)

## Reproduction

Run the strict verifier with Python 3.10 or later.

```sh
python3 -I verify_443.py
```

Expected output

```text
443 23653 32453 [] 23653 []
655,391 ordered exponent patterns through least prime 443. The sole fixed point is 21.
```

Jaroslav Křížek posed the original conjecture. Exact computation and continuation by @DomTheDeveloper. Research priority is unestablished. [OEIS A245211](https://oeis.org/A245211)
