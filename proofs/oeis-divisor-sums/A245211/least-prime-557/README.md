# A245211 through least prime 557

For every positive integer $n$ having a prime divisor at most 557,
$$
\sum_{d\mid n,\ d<n} d\,\tau(d)=n \quad\Longleftrightarrow\quad n=21.
$$
There is no upper bound on $n$. Any other fixed point has least prime at least 563.

This computer-assisted partial result extends the previous all-support certificate through least prime 547. At least prime 557 both exact programs exhaust 34,377 ordered exponent patterns. The integer search visits 242,194 nodes after its exact filters. Both searches return an empty list. Together with the previous 1,080,150 patterns this gives 1,114,527 ordered exponent patterns through 557. The unrestricted conjecture remains open.

## Arithmetic certificate

Put $T_e(p)=\sum_{j=0}^{e}(j+1)p^j$. At a fixed point, the full divisor moment is $n(\tau(n)+1)$. Therefore a prime factor of a local moment whose multiplicity cannot be absorbed by the known prime powers or $\tau(n)+1$ must occur in a remaining prime-power component.

The difficult local moments have the complete factorizations
$$T_4(557)=3\cdot160654792213,$$
$$T_9(557)=42394295929\cdot1219246775147143,$$
$$T_{28}(557)=3\cdot79601\cdot9312304158704552410728341941717457119840870664004687487146354658536155089.$$

The two expensive orderings of $(4,33,1,1)$ reduce to an exact bilinear equation. If $C=T_4(557)T_{33}(q)/(557^4q^{33})=c/m$ and $q=160654792213$, the two exponent-one primes $r<s$ satisfy
$$
\delta rs=c(2r+2s+1),\qquad \delta=681m-4c.
$$
The ordering $q<r<s$ contradicts positivity. In the remaining ordering $r<q<s$, monotonicity gives $2c/\delta<r<4c/\delta<30923$; exact division over this finite interval gives no prime solution.

Complete recursive Lucas certificates establish every new large prime. The 73-digit factor of $T_{28}(557)$ is established by a complete Lucas $n+1$ certificate with parameters $(P,Q)=(1,11)$ and discriminant $-43$.

The search methods remain independent. The integer checker uses integer inequalities, congruence filters and an ordered prime search. The rational checker works with exact fractions and places forced factors directly. Both enumerate the same exponent budget but traverse the prime choices differently. Leaves are checked by exact trial division. [Previous certificate through 547](https://github.com/DomTheDeveloper/ProofPlaygrond/tree/d80c77720a4dd81cd5ab6124a8fe8fc8957428dc/proofs/oeis-divisor-sums/A245211/least-prime-547) · [Merged Lean reduction #12841](https://github.com/lefttosolve2/open-math-agents/pull/12841)

## Reproduction

Run the strict verifier with Python 3.10 or later.

```sh
python3 -I verify_557.py
```

Expected output

```text
557 34377 242194 [] 34377 []
1,114,527 ordered exponent patterns through least prime 557. The sole fixed point is 21.
```

Jaroslav Křížek posed the original conjecture. Exact computation and continuation by @DomTheDeveloper. Research priority is unestablished. [OEIS A245211](https://oeis.org/A245211)
