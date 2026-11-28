# A245211 through least prime 563

For every positive integer $n$ having a prime divisor at most 563,
$$
\sum_{d\mid n,\ d<n} d\,\tau(d)=n \quad\Longleftrightarrow\quad n=21.
$$
There is no upper bound on $n$. Any other fixed point has least prime at least 569.

This computer-assisted partial result extends the previous all-support certificate through least prime 557. At least prime 563 both exact programs exhaust 35,235 ordered exponent patterns. The integer search visits 2,031 nodes after its exact filters. Both searches return an empty list. Together with the previous 1,114,527 patterns this gives 1,149,762 ordered exponent patterns through 563. The unrestricted conjecture remains open.

## Arithmetic certificate

Put $T_e(p)=\sum_{j=0}^{e}(j+1)p^j$. At a fixed point, the full divisor moment is $n(\tau(n)+1)$. Therefore a prime factor of a local moment whose multiplicity cannot be absorbed by the known prime powers or $\tau(n)+1$ must occur in a remaining prime-power component.

The difficult local moments have the complete factorizations
$$T_4(563)=3\cdot167687167009,$$
$$T_{12}(563)=63433604086292339\cdot208179199835170301,$$
$$T_{13}(563)=11\cdot17\cdot5449\cdot413734799322601\cdot18992125938919187,$$
$$T_{20}(563)=215338890507830948627271247366058246150659483337584900331,$$
$$T_{21}(563)=756641\cdot19794762341\cdot8479998243019482820514808384553046533104457.$$

The two expensive orderings of $(4,33,1,1)$ reduce to the same exact bilinear equation as in the preceding layer. With $q=167687167009$ forced by $T_4(563)$, the ordering $q<r<s$ contradicts positivity. In the remaining ordering $r<q<s$, monotonicity bounds the intermediate prime by $r<20980$; exact division over this finite interval gives no prime solution.

Complete recursive Lucas certificates establish every new large prime before it is used. The search methods remain independent: the integer checker uses integer inequalities, congruence filters and ordered prime search, while the rational checker uses exact fractions and places forced factors directly. Both enumerate the same exponent budget but traverse prime choices differently. Leaves are checked by exact trial division. [Previous certificate through 557](https://github.com/DomTheDeveloper/ProofPlaygrond/tree/bbbd3c8a47bcceab0029d0d475aabf0508c73c87/proofs/oeis-divisor-sums/A245211/least-prime-557) · [Merged Lean reduction #12841](https://github.com/lefttosolve2/open-math-agents/pull/12841)

## Reproduction

Run the strict verifier with Python 3.10 or later.

```sh
python3 -I verify_563.py
```

Expected output

```text
563 35235 2031 [] 35235 []
1,149,762 ordered exponent patterns through least prime 563. The sole fixed point is 21.
```

Jaroslav Křížek posed the original conjecture. Exact computation and continuation by @DomTheDeveloper. Research priority is unestablished. [OEIS A245211](https://oeis.org/A245211)
