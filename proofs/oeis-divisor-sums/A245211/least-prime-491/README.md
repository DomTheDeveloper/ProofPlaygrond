# A245211 through least prime 491

For every positive integer $n$ having a prime divisor at most 491,
$$
\sum_{d\mid n,\ d<n} d\,\tau(d)=n \quad\Longleftrightarrow\quad n=21.
$$
There is no upper bound on $n$. Any other fixed point has least prime at least 499.

This computer-assisted partial result extends the previous all-support certificate through least prime 487. At least prime 491 both exact programs exhaust 28,321 ordered exponent patterns. The integer search visits 1,051,788 nodes after its exact filters. Both searches return an empty list. Together with the previous 834,340 patterns this gives 862,661 ordered exponent patterns through 491. The unrestricted conjecture remains open.

## Arithmetic certificate

Put $T_e(p)=\sum_{j=0}^{e}(j+1)p^j$. At a fixed point, the full divisor moment is $n(\tau(n)+1)$. Therefore a prime factor of a local moment whose multiplicity cannot be absorbed by the known prime powers or $\tau(n)+1$ must occur in a remaining prime-power component.

The four hard branches have leading exponent 1 at 491 and one exponent 12 among the five later prime components. The exponent-1 identity forces the next prime to be 983. Every ordering is then closed by the certified prime divisor
$$
74505131977\mid T_{12}(983).
$$
No assumption is made about the cofactor. Both checkers prove the displayed divisor prime from a complete Lucas certificate: they multiply the listed prime factors of $q-1$ back exactly, verify a full-order witness modulo $q$, and check the leaves by exact trial division.

The integer checker verifies each full-order witness by modular exponentiation. The rational checker independently verifies that the corresponding residues minus one are coprime to $q$. Leaves are checked by exact trial division.

The search methods remain independent. One uses integer inequalities, congruence filters and an ordered prime search. The other works with exact fractions and places forced factors directly. Both enumerate the same exponent budget but traverse the prime choices differently. [Previous certificate through 487](https://github.com/DomTheDeveloper/ProofPlaygrond/tree/aae5e1bbcb98745c132de9d61a990cae2e2ae057/proofs/oeis-divisor-sums/A245211/least-prime-487) · [Merged Lean reduction #12841](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/12841)

## Reproduction

Run the strict verifier with Python 3.10 or later.

```sh
python3 -I verify_491.py
```

Expected output

```text
491 28321 1051788 [] 28321 []
862,661 ordered exponent patterns through least prime 491. The sole fixed point is 21.
```

Jaroslav Křížek posed the original conjecture. Exact computation and continuation by @DomTheDeveloper. Research priority is unestablished. [OEIS A245211](https://oeis.org/A245211)
