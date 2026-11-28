# A245211 through least prime 523

For every positive integer $n$ having a prime divisor at most 523,
$$
\sum_{d\mid n,\ d<n} d\,\tau(d)=n \quad\Longleftrightarrow\quad n=21.
$$
There is no upper bound on $n$. Any other fixed point has least prime at least 541.

This computer-assisted partial result extends the previous all-support certificate through least prime 521. At least prime 523 both exact programs exhaust 31,269 ordered exponent patterns. The integer search visits 64 nodes after its exact filters. Both searches return an empty list. Together with the previous 981,387 patterns this gives 1,012,656 ordered exponent patterns through 523. The unrestricted conjecture remains open.

## Arithmetic certificate

Put $T_e(p)=\sum_{j=0}^{e}(j+1)p^j$. At a fixed point, the full divisor moment is $n(\tau(n)+1)$. Therefore a prime factor of a local moment whose multiplicity cannot be absorbed by the known prime powers or $\tau(n)+1$ must occur in a remaining prime-power component.

The unique difficult shape is $(12,1,1,1,1,1)$. It is closed by the complete factorization
$$T_{12}(523)=2028001589\cdot2689444028197928641384331$$
and the forced successors
$$2\cdot2028001589+1=593\cdot6839803,$$
$$2\cdot2689444028197928641384331+1=31\cdot37\cdot7349\cdot6140531\cdot103918988891.$$
Both programs replay complete recursive Lucas certificates for every new large prime before using these factorizations.

The search methods remain independent. The integer checker uses integer inequalities, congruence filters and an ordered prime search. The rational checker works with exact fractions and places forced factors directly. Both enumerate the same exponent budget but traverse the prime choices differently. Leaves are checked by exact trial division. [Previous certificate through 521](https://github.com/DomTheDeveloper/ProofPlaygrond/tree/9f0e37689c4fb87d586545aec0e97e83023f6946/proofs/oeis-divisor-sums/A245211/least-prime-521) · [Merged Lean reduction #12841](https://github.com/lefttosolve2/open-math-agents/pull/12841)

## Reproduction

Run the strict verifier with Python 3.10 or later.

```sh
python3 -I verify_523.py
```

Expected output

```text
523 31269 64 [] 31269 []
1,012,656 ordered exponent patterns through least prime 523. The sole fixed point is 21.
```

Jaroslav Křížek posed the original conjecture. Exact computation and continuation by @DomTheDeveloper. Research priority is unestablished. [OEIS A245211](https://oeis.org/A245211)
