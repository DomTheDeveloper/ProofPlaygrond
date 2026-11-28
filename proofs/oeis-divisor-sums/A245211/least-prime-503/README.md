# A245211 through least prime 503

For every positive integer $n$ having a prime divisor at most 503,
$$
\sum_{d\mid n,\ d<n} d\,\tau(d)=n \quad\Longleftrightarrow\quad n=21.
$$
There is no upper bound on $n$. Any other fixed point has least prime at least 509.

This computer-assisted partial result extends the previous all-support certificate through least prime 499. At least prime 503 both exact programs exhaust 28,813 ordered exponent patterns. The integer search visits 27,241 nodes after its exact filters. Both searches return an empty list. Together with the previous 891,312 patterns this gives 920,125 ordered exponent patterns through 503. The unrestricted conjecture remains open.

## Arithmetic certificate

Put $T_e(p)=\sum_{j=0}^{e}(j+1)p^j$. At a fixed point, the full divisor moment is $n(\tau(n)+1)$. Therefore a prime factor of a local moment whose multiplicity cannot be absorbed by the known prime powers or $\tau(n)+1$ must occur in a remaining prime-power component.

At least prime 503 the small prime divisors $10899209\mid T_{21}(503)$ and $8147,1216541551\mid T_{24}(503)$ close three hard shapes. The remaining shape $(28,1,1,1,1)$ is closed by
$$
T_{28}(503)=3\cdot42659401646883945868279443474872264567866037127544366454869197799153118141861.
$$
The large factor $q$ is proved prime by a complete recursive Lucas certificate. Its forced successor has the complete factorization
$$
2q+1=31\cdot1167821\cdot15191381593\cdot2055442091367457571\cdot235811280239852564927\cdot320066105936828222533,
$$
again with recursive Lucas certificates for every large factor. Since four tail slots cannot absorb all six distinct forced primes, the shape is impossible. The inherited certificates are also replayed before either checker uses a previously certified large prime divisor.

The integer checker verifies each full-order witness by modular exponentiation. The rational checker independently verifies that the corresponding residues minus one are coprime to the candidate prime. Leaves are checked by exact trial division.

The search methods remain independent. One uses integer inequalities, congruence filters and an ordered prime search. The other works with exact fractions and places forced factors directly. Both enumerate the same exponent budget but traverse the prime choices differently. [Previous certificate through 499](https://github.com/DomTheDeveloper/ProofPlaygrond/tree/adaeac4a9d94cf2f55e2641fbb1618e44c8ba126/proofs/oeis-divisor-sums/A245211/least-prime-499) · [Merged Lean reduction #12841](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/12841)

## Reproduction

Run the strict verifier with Python 3.10 or later.

```sh
python3 -I verify_503.py
```

Expected output

```text
503 28813 27241 [] 28813 []
920,125 ordered exponent patterns through least prime 503. The sole fixed point is 21.
```

Jaroslav Křížek posed the original conjecture. Exact computation and continuation by @DomTheDeveloper. Research priority is unestablished. [OEIS A245211](https://oeis.org/A245211)
