# A245211 through least prime 547

For every positive integer $n$ having a prime divisor at most 547,
$$
\sum_{d\mid n,\ d<n} d\,\tau(d)=n \quad\Longleftrightarrow\quad n=21.
$$
There is no upper bound on $n$. Any other fixed point has least prime at least 557.

This computer-assisted partial result extends the previous all-support certificate through least prime 541. At least prime 547 both exact programs exhaust 33,941 ordered exponent patterns. The integer search visits 153,655 nodes after its exact filters. Both searches return an empty list. Together with the previous 1,046,209 patterns this gives 1,080,150 ordered exponent patterns through 547. The unrestricted conjecture remains open.

## Arithmetic certificate

Put $T_e(p)=\sum_{j=0}^{e}(j+1)p^j$. At a fixed point, the full divisor moment is $n(\tau(n)+1)$. Therefore a prime factor of a local moment whose multiplicity cannot be absorbed by the known prime powers or $\tau(n)+1$ must occur in a remaining prime-power component.

The only difficult branches are the three orderings of exponent shape $(9,13,1,1)$. They are closed by the complete factorizations
$$T_9(547)=17\cdot23978780431\cdot107727122583581,$$
$$T_{13}(547)=3\cdot7\cdot23\cdot4728181\cdot1393354351\cdot1729809749469080801,$$
and the forced successor factorizations embedded in both programs. Complete recursive Lucas certificates establish every new large prime before it is used.

The search methods remain independent. The integer checker uses integer inequalities, congruence filters and an ordered prime search. The rational checker works with exact fractions and places forced factors directly. Both enumerate the same exponent budget but traverse the prime choices differently. Leaves are checked by exact trial division. [Previous certificate through 541](https://github.com/DomTheDeveloper/ProofPlaygrond/tree/b6f946ca20a82a97dcbc0fa9b3e770cd46950c6b/proofs/oeis-divisor-sums/A245211/least-prime-541) · [Merged Lean reduction #12841](https://github.com/lefttosolve2/open-math-agents/pull/12841)

## Reproduction

Run the strict verifier with Python 3.10 or later.

```sh
python3 -I verify_547.py
```

Expected output

```text
547 33941 153655 [] 33941 []
1,080,150 ordered exponent patterns through least prime 547. The sole fixed point is 21.
```

Jaroslav Křížek posed the original conjecture. Exact computation and continuation by @DomTheDeveloper. Research priority is unestablished. [OEIS A245211](https://oeis.org/A245211)
