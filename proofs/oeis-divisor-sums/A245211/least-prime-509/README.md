# A245211 through least prime 509

For every positive integer $n$ having a prime divisor at most 509,
$$
\sum_{d\mid n,\ d<n} d\,\tau(d)=n \quad\Longleftrightarrow\quad n=21.
$$
There is no upper bound on $n$. Any other fixed point has least prime at least 521.

This computer-assisted partial result extends the previous all-support certificate through least prime 503. At least prime 509 both exact programs exhaust 30,081 ordered exponent patterns. The integer search visits 1,762,123 nodes after its exact filters. Both searches return an empty list. Together with the previous 920,125 patterns this gives 950,206 ordered exponent patterns through 509. The unrestricted conjecture remains open.

## Arithmetic certificate

Put $T_e(p)=\sum_{j=0}^{e}(j+1)p^j$. At a fixed point, the full divisor moment is $n(\tau(n)+1)$. Therefore a prime factor of a local moment whose multiplicity cannot be absorbed by the known prime powers or $\tau(n)+1$ must occur in a remaining prime-power component.

The difficult branches follow the forced Cunningham chain
$$
509\to1019\to2039\to4079\to8159\to16319\to32639.
$$
The certificate supplies complete factorizations and recursive Lucas proofs for the required $T_4,T_{12},T_{13}$ and $T_{21}$ moments along this chain. For the exponent-28 branches it verifies enough distinct prime divisors of $T_{28}(1019)$, $T_{28}(2039)$ and $T_{28}(4079)$ to exceed the available support after exact cancellation. In particular it proves the new divisors $57580356307\mid T_{28}(1019)$ and
$$
87367747323221\cdot18427674270439283\mid T_{28}(2039)
$$
prime by complete recursive Lucas certificates. The three orderings of $(4,13,1,1,1)$ are closed using
$$
T_4(509)=3\cdot112047696661,
$$
with a recursive Lucas certificate for the large prime and exact forcing through its exponent-13 moment. Every inherited large-prime certificate is replayed before use.

The integer checker verifies each full-order witness by modular exponentiation. The rational checker independently verifies that the corresponding residues minus one are coprime to the candidate prime. Leaves are checked by exact trial division.

The search methods remain independent. One uses integer inequalities, congruence filters and an ordered prime search. The other works with exact fractions and places forced factors directly. Both enumerate the same exponent budget but traverse the prime choices differently. [Previous certificate through 503](https://github.com/DomTheDeveloper/ProofPlaygrond/tree/158f8e920b0611878e7312e5e789193caccbd36b/proofs/oeis-divisor-sums/A245211/least-prime-503) · [Merged Lean reduction #12841](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/12841)

## Reproduction

Run the strict verifier with Python 3.10 or later.

```sh
python3 -I verify_509.py
```

Expected output

```text
509 30081 1762123 [] 30081 []
950,206 ordered exponent patterns through least prime 509. The sole fixed point is 21.
```

Jaroslav Křížek posed the original conjecture. Exact computation and continuation by @DomTheDeveloper. Research priority is unestablished. [OEIS A245211](https://oeis.org/A245211)
