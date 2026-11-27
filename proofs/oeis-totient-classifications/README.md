# Five classifications involving Euler’s totient

Dominic A. Dabish · November 26, 2026 · Mathematical work with OpenAI Codex

For positive integers $n$, let $\varphi(n)$ count the integers from 1 to $n$ coprime to $n$, and let $\sigma_r(n)=\sum_{d\mid n}d^r$. Two arguments answer five sequence questions. The first classifies the solutions of a totient equation for every $x\ge7$. The second gives a computable upper bound on every solution of each of four divisor inequalities. Two independent integer calculations then recover the complete lists.

## The Pierpont-prime characterization

**Theorem.** For every integer $x\ge7$,

$$
\varphi(x)+\varphi(x-1)=\left\lfloor\frac{4x-3}{3}\right\rfloor
\quad\Longleftrightarrow\quad x\text{ is prime and }x=1+2^a3^b\text{ for some }a,b\ge1.
$$

Benoit Cloitre proposed this characterization in 2018. The first solutions are $7,13,19,37,73$. Both exponents must be positive. [OEIS A058383](https://oeis.org/A058383)

**Proof.** The two totients are even since their arguments exceed 2. For $x=3k,3k+1,3k+2$, the right-hand side is respectively $4k-1,4k,4k+1$. Thus a solution satisfies $x\equiv1\pmod3$, and its right-hand side is $4(x-1)/3$.

If $x$ were even, then $\varphi(x)\le x/2$ and $\varphi(x-1)\le 2(x-1)/3$, since $3\mid x-1$. Their sum is strictly less than $4(x-1)/3$ for $x>4$. Thus $x$ is odd and $6\mid x-1$.

Now $\varphi(x)\le x-1$, with equality exactly when $x$ is prime. Euler’s product gives $\varphi(x-1)\le (x-1)(1-1/2)(1-1/3)=(x-1)/3$. Equality here holds exactly when $x-1$ has no prime factor besides 2 and 3. The required sum is the sum of these two upper bounds, so both are equalities. Conversely, a prime of the stated form attains both bounds. This proves the equivalence.

## Four divisor-sum classifications

**Theorem.** For $r=1,2,3,4$, respectively, there are exactly $7,15,38,111$ positive integers satisfying $\sigma_r(n)>\varphi(n)^{r+1}$. The largest solutions are $30,60,420,2310$, respectively. In every case the solution set agrees term for term with the corresponding published list.

| $r$ | OEIS list | First excluded number of distinct prime factors | Inclusive search bound | Solutions | Largest |
|---:|---|---:|---:|---:|---:|
| 1 | [A064374](https://oeis.org/A064374) | 4 | 52 | 7 | 30 |
| 2 | [A064375](https://oeis.org/A064375) | 5 | 366 | 15 | 60 |
| 3 | [A064376](https://oeis.org/A064376) | 6 | 2,581 | 38 | 420 |
| 4 | [A064377](https://oeis.org/A064377) | 6 | 12,422 | 111 | 2,310 |

**Proof of the bounds.** Write $R(n)=n/\varphi(n)$. For $r\ge1$, the prime-power formula for the divisor sum gives

$$
\frac{\sigma_r(n)}{n^r}
=\prod_{p^a\parallel n}(1+p^{-r}+\cdots+p^{-ar})
\le\prod_{p\mid n}(1-p^{-1})^{-1}=R(n).
$$

Consequently $\varphi(n)^{r+1}<\sigma_r(n)\le n^r R(n)$ implies $n<R(n)^{r+2}$. The strict inequality also excludes $n=1$.

Let $p_i$ be the $i$-th prime, $P_k=\prod_{i=1}^k p_i$, and $Q_k=\prod_{i=1}^k p_i/(p_i-1)$, with both empty products equal to 1. If $n$ has $k$ distinct prime factors then $n\ge P_k$ and $R(n)\le Q_k$. Indeed the $i$-th smallest prime factor of $n$ is at least $p_i$, and $p/(p-1)$ decreases as $p$ increases.

Put $e=r+2$. At the first excluded index $j$ in the table, $P_j\ge Q_j^e$ and $p_j\ge (p_j/(p_j-1))^e$. For every prime $p>p_j$, the second comparison also holds, because its left side increases and its right side decreases. Multiplying by these factors shows $P_k\ge Q_k^e$ for all $k\ge j$. A solution must therefore have $k<j$ and $n<Q_{j-1}^e$.

All numerical comparisons use rational arithmetic. The successive values of $Q_k$ for $k=1$ through 6 are $2,3,15/4,35/8,77/16,1001/192$. For example, at $r=4$ the product of the first six primes is $30{,}030>(1001/192)^6$. No solution can have six or more distinct prime factors. Every possible solution satisfies $n<(77/16)^6$, hence $n\le12{,}422$.

### Why the three largest fourth-power solutions are 2310, 1680, and 1470

There is a short way to find the largest terms without enumerating all candidates. For $d\ge2$, $d^3\ge 8(d-1)$, so

$$
\frac1{d^4}\le\frac18\left(\frac1{d-1}-\frac1d\right).
$$

Summing this telescoping bound gives $\sigma_4(n)/n^4=\sum_{d\mid n}d^{-4}<9/8$. Every solution therefore satisfies $n<(9/8)R(n)^5$.

- **Five distinct prime factors.** The general proof already excludes six or more. If the five primes are $2,3,5,7,11$, then $2310\mid n$ and $n<(9/8)(77/16)^5<2905$. Thus $n=2310$. For any other set of five primes the largest is at least 13, so $n\ge 2\cdot3\cdot5\cdot7\cdot13=2730$ and $R(n)\le(35/8)(13/12)=455/96$. But $(9/8)(455/96)^5<2691$. This rules out every other five-prime case.
- **At most four distinct prime factors.** Unless the prime set is exactly $\{2,3,5,7\}$, we have $R(n)\le(15/4)(11/10)=33/8$. This also covers all sets with at most three primes. Consequently $n<(9/8)(33/8)^5<1344$. For the exceptional set, $210\mid n$ and $n<(9/8)(35/8)^5<1804$. The only multiples of 210 from 1344 through 1803 are 1470 and 1680.

The strict inequality holds at each of the three candidates by direct substitution. For example, $\varphi(2310)=480$ and $\sigma_4(2310)=30{,}690{,}962{,}782{,}096>480^5=25{,}480{,}396{,}800{,}000$. Thus the ordering of the top three follows from the bounds alone and three evaluations.

**Finite verification.** One calculation adds $d^r$ to every multiple of $d$ and sieves the totients. A second calculation trial-factors each integer and evaluates both functions by their prime-power formulas. The values of both functions must agree for every integer through the relevant bound. The program then compares the ordered solution list with the entries transcribed from OEIS. It runs with Python’s standard library.

```sh
python3 verify_divisor_sums.py
```

The data and the two calculations are in [oeis-lists.json](oeis-lists.json) and [verify_divisor_sums.py](verify_divisor_sums.py).

**Earlier work.** Benoit Cloitre recorded the completeness of the $r=1$ list in 2002. Charles R. Greathouse IV gave finiteness arguments for the other three lists in 2015. The fourth-power entry explicitly conjectures that the displayed 111 solutions exhaust the list. The proof here supplies an explicit cutoff and exact verification for each list. Historical priority for the other classifications has not been established. [A064374](https://oeis.org/A064374) · [A064375](https://oeis.org/A064375) · [A064376](https://oeis.org/A064376) · [A064377](https://oeis.org/A064377)
