# A245211 fixed points through least prime 251

If a positive integer has a prime divisor at most 251, its A245211 proper-divisor sum equals the integer exactly when it equals 21. Every other fixed point has least prime at least 257. This is a computer-assisted bound with unrestricted exponents and no upper bound on the integer.

The [earlier proof, page 5](../../A245212/A245212-Density-Zero.pdf) proves the finiteness and completeness of the search. The [original programs and records](../) establish the range through 199. The extension covers 60,410 more ordered exponent patterns. The cumulative total is 149,849.

## Certificate

Let $T_e(p)=\sum_{j=0}^e(j+1)p^j$ and $D=\tau(n)$. A fixed point must satisfy $\prod T_e(p)=n(D+1)$. If the least prime is $p$ with exponent $a$, then $a\prod_{q>p}(e_q+1)\le p-1$. For each such ordered exponent vector, the strictly decreasing normalized factors $T_e(q)/q^e$ bound each successive prime separately. This gives a finite exhaustive search even though the initial conjecture has no upper bound on $n$.

The integer search now tests 96,893 as an additional possible prime divisor, checking its primality by trial division and its divisibility before use. The rational search independently trial-divides numerators using every prime through 100,000. For example, $96,893$ divides $T_9(227)$. For four further exponent-one factors, $D+1=161$. The fixed-point equation would force $96,893$ to divide $n$, then force a prime below 227 since $2(96,893)+1=11\cdot79\cdot223$. This rules out that exponent pattern.

A larger forced prime is $Q=T_{13}(227)=59,737,124,597,292,648,185,414,913,209,393$. The integer program certifies a unit of multiplicative order $Q-1$ using the complete factorization $Q-1=2^4\cdot227\cdot15308633\cdot4576002647\cdot234787945631$. The rational program independently verifies a Pocklington certificate using the last two prime factors and base 2. Their product exceeds $\sqrt Q$. Since $131$ divides $2Q+1$ and does not divide $225$, the exponent pattern $(13,1,1,1,1)$ at least prime $227$ is impossible. Both programs retain their exhaustive fallback whenever available partial factors do not settle a case.

| Least prime | Ordered exponent patterns | Fixed points |
|---:|---:|---|
| 211 | 6,399 | None |
| 223 | 7,065 | None |
| 227 | 7,345 | None |
| 229 | 7,433 | None |
| 233 | 7,523 | None |
| 239 | 7,661 | None |
| 241 | 8,397 | None |
| 251 | 8,587 | None |

## Reproduce

Use Python 3 with the standard library. The first two commands reproduce the baseline. The third independently reruns both extension searches and checks the cumulative count.

```sh
python3 A245211/search_fixed_points.py 199
python3 A245211/check_fixed_points.py 199
python3 A245211/extension/verify.py
```

Jaroslav Krizek posed the [original conjecture](https://oeis.org/A245211). The [earlier product argument](https://github.com/umaia1234/agentic-conjectures/blob/main/problems/oeis-a245211/DETAILS.md) and [Mar Allen Sugui's earlier results](https://github.com/google-deepmind/formal-conjectures/pull/8119) give related restrictions. This certificate resolves the specified least-prime range. Global uniqueness and research priority remain open.
