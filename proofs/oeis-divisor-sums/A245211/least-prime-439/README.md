# A245211 through least prime 439

For every positive integer $n$ having a prime divisor at most 439,
$$
\sum_{d\mid n,\ d<n} d\,\tau(d)=n \quad\Longleftrightarrow\quad n=21.
$$
There is no upper bound on $n$. Any other fixed point has least prime at least 443.

This computer-assisted partial result extends the previous all-support certificate through least prime 433. At least prime 439 both exact programs exhaust 23,313 ordered exponent patterns. The integer search visits 131 nodes after its exact filters. Both searches return an empty list. Together with the previous 608,425 patterns this gives 631,738. The separate Lean result covers all two-prime inputs through smaller prime 439 and several families for arbitrary primes. The unrestricted conjecture remains open. [Lean proof and two-prime arguments](../two-prime-height/README.md)

## Arithmetic certificate

Let $T_e(p)=\sum_{j=0}^{e}(j+1)p^j$. At a fixed point $n$ the full divisor moment is $n(\tau(n)+1)$. Thus a prime factor of a chosen local moment whose multiplicity exceeds its multiplicity in the product of the known prime powers and $\tau(n)+1$ must divide a remaining prime power. The new layer supplies the following complete factorizations.

| $e$ | $T_e(439)$ as a product of primes |
|---|---|
| 4 | $3\cdot117563\cdot527507$ |
| 6 | $2^2\cdot495571\cdot25326082891$ |
| 10 | $2\cdot3\cdot4453357970557\cdot109672890951493$ |
| 12 | $667469961894052368039509630751847$ (prime) |

Both checkers recompute the local moments, multiply back their factors and verify primality. Leaves are checked by exact trial division. Larger primes have recursive Lucas certificates using complete factorizations of $q-1$. For every distinct prime factor $r$ of $q-1$, the integer verifier checks that its witness raised to $(q-1)/r$ is different from $1$ modulo $q$. The rational verifier checks that the resulting residue minus $1$ is coprime to $q$. Both check the full exponent congruence.

The inherited search methods differ. One uses integer comparisons and congruence filters with exact ordered searches for the remaining primes. The other uses exact fractions and places forced factors directly. The earlier note explains why the exponent budget and the prime searches are exhaustive. [Earlier certificate](https://github.com/DomTheDeveloper/ProofPlaygrond/tree/363b000af1d2dfcba9eee561dc2e6994e1e07d9e/proofs/oeis-divisor-sums/A245211/least-prime-433) · [Proof index](https://github.com/DomTheDeveloper/ProofPlaygrond/issues/121)

## Reproduction

With Python 3.10 or later, run the following command in this directory.

```sh
python3 -I verify_439.py
```

Expected output

```text
439 23313 131 [] 23313 []
631,738 ordered exponent patterns through least prime 439. The sole fixed point is 21.
```

Jaroslav Křížek posed the original conjecture. Exact computation and continuation by @DomTheDeveloper. Research priority is unestablished. [OEIS A245211](https://oeis.org/A245211)
