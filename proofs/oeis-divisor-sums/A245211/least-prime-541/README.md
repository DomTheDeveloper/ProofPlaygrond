# A245211 through least prime 541

For every positive integer $n$ having a prime divisor at most 541,
$$
\sum_{d\mid n,\ d<n} d\,\tau(d)=n \quad\Longleftrightarrow\quad n=21.
$$
There is no upper bound on $n$. Any other fixed point has least prime at least 547.

This computer-assisted partial result extends the previous all-support certificate through least prime 523. At least prime 541 both exact programs exhaust 33,553 ordered exponent patterns. The integer search visits 170,533 nodes after its exact filters. Both searches return an empty list. Together with the previous 1,012,656 patterns this gives 1,046,209 ordered exponent patterns through 541. The unrestricted conjecture remains open.

## Arithmetic certificate

Put $T_e(p)=\sum_{j=0}^{e}(j+1)p^j$. At a fixed point, the full divisor moment is $n(\tau(n)+1)$. Therefore a prime factor of a local moment whose multiplicity cannot be absorbed by the known prime powers or $\tau(n)+1$ must occur in a remaining prime-power component.

No new exceptional large-prime factorization is needed at 541. The exact parity, congruence, local-moment and ordered-support filters close every exponent pattern. Before using a previously certified large divisor, both programs replay the complete inherited recursive Lucas certificates through the 523 layer.

The search methods remain independent. The integer checker uses integer inequalities, congruence filters and an ordered prime search. The rational checker works with exact fractions and places forced factors directly. Both enumerate the same exponent budget but traverse the prime choices differently. Leaves are checked by exact trial division. [Previous certificate through 523](https://github.com/DomTheDeveloper/ProofPlaygrond/tree/8f262e22da36d63c53a6feeb06d50a49e0e8df29/proofs/oeis-divisor-sums/A245211/least-prime-523) · [Merged Lean reduction #12841](https://github.com/lefttosolve2/open-math-agents/pull/12841)

## Reproduction

Run the strict verifier with Python 3.10 or later.

```sh
python3 -I verify_541.py
```

Expected output

```text
541 33553 170533 [] 33553 []
1,046,209 ordered exponent patterns through least prime 541. The sole fixed point is 21.
```

Jaroslav Křížek posed the original conjecture. Exact computation and continuation by @DomTheDeveloper. Research priority is unestablished. [OEIS A245211](https://oeis.org/A245211)
