# A245211 through least prime 499

For every positive integer $n$ having a prime divisor at most 499,
$$
\sum_{d\mid n,\ d<n} d\,\tau(d)=n \quad\Longleftrightarrow\quad n=21.
$$
There is no upper bound on $n$. Any other fixed point has least prime at least 503.

This computer-assisted partial result extends the previous all-support certificate through least prime 491. At least prime 499 both exact programs exhaust 28,651 ordered exponent patterns. The integer search visits 399,572 nodes after its exact filters. Both searches return an empty list. Together with the previous 862,661 patterns this gives 891,312 ordered exponent patterns through 499. The unrestricted conjecture remains open.

## Arithmetic certificate

Put $T_e(p)=\sum_{j=0}^{e}(j+1)p^j$. At a fixed point, the full divisor moment is $n(\tau(n)+1)$. Therefore a prime factor of a local moment whose multiplicity cannot be absorbed by the known prime powers or $\tau(n)+1$ must occur in a remaining prime-power component.

At least prime 499 the standard exact inequalities, congruence filters, and forced-prime rules close every exponent pattern. No new local-moment factorization or primality assumption is required for this layer. The inherited recursive Lucas certificates are still replayed before either checker uses any previously certified large prime divisor.

The integer checker verifies each full-order witness by modular exponentiation. The rational checker independently verifies that the corresponding residues minus one are coprime to $q$. Leaves are checked by exact trial division.

The search methods remain independent. One uses integer inequalities, congruence filters and an ordered prime search. The other works with exact fractions and places forced factors directly. Both enumerate the same exponent budget but traverse the prime choices differently. [Previous certificate through 491](https://github.com/DomTheDeveloper/ProofPlaygrond/tree/397d39f62106e34fa60e1f90cb299bb4f8637ac3/proofs/oeis-divisor-sums/A245211/least-prime-491) · [Merged Lean reduction #12841](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/12841)

## Reproduction

Run the strict verifier with Python 3.10 or later.

```sh
python3 -I verify_499.py
```

Expected output

```text
499 28651 399572 [] 28651 []
891,312 ordered exponent patterns through least prime 499. The sole fixed point is 21.
```

Jaroslav Křížek posed the original conjecture. Exact computation and continuation by @DomTheDeveloper. Research priority is unestablished. [OEIS A245211](https://oeis.org/A245211)
