# Totients, prime counts, and two square-root sequences

The last positive integer satisfying $\varphi(n)\le 3\pi(n)$ is **223,092,870**. There are exactly **25** equality cases, the last at **731,280**. Here $\varphi$ counts reduced residues and $\pi(n)$ counts primes at most $n$. A bound for every larger integer and two independent integer computations give the following complete counts.

| Multiplier $c$ | Count with $\varphi(n)<c\pi(n)$ | Count with equality | Last equality | Last $n$ with $\varphi(n)\le c\pi(n)$ |
|---:|---:|---:|---:|---:|
| 1 | 7 | 8 | 90 | 90 |
| 2 | 644 | 20 | 12,012 | 90,090 |
| 3 | 33,738 | 25 | 731,280 | 223,092,870 |

The prime-counting results below use a published analytic estimate and reproducible exhaustive integer arithmetic. The two square-root results in the last section also have Lean proofs. No claim of research priority is made.

## An upper bound covering all remaining integers

Write $p_i$ for the $i$-th prime, $P_k=\prod_{i=1}^kp_i$, and $R_k=P_k/\varphi(P_k)$. If $P_k\le n<P_{k+1}$, then $n$ has at most $k$ distinct prime factors. In the product $n/\varphi(n)=\prod_{p\mid n}p/(p-1)$, each factor decreases as $p$ increases. Hence $n/\varphi(n)\le R_k$.

Put $B=5\cdot2^{26}=335,544,320$. We prove $\varphi(n)>3\pi(n)$ for every $n\ge B$. Dusart's inequality (6.6) gives $\pi(x)\le x/(\log x-1.1)$ for $x>60,184$. It is enough to prove $\log n-1.1>3n/\varphi(n)$. [Pierre Dusart, *Estimates of some functions over primes without R.H.* (2010), equation (6.6)](https://arxiv.org/pdf/1002.0442)

For $B\le n<P_{10}$ there are at most nine distinct prime divisors. We have $R_9=223092870/36495360<6.12$. Also $\log B=28\log 2+\log(5/4)>28(0.69)+0.2=19.52$. The lower bounds follow from $\log 2>2(1/3+1/81)>0.69$ by the power series for $2\operatorname{arctanh}(1/3)$, and $\log(5/4)>1/5$ by integration. Thus $\log n-1.1>18.42>3R_9$.

For $n\ge P_{10}$ the sequence $(\log P_k-1.1)/R_k$ is strictly increasing. Indeed, putting $q=p_{k+1}$, the increase is equivalent to $(q-1)\log q>\log P_k-1.1$. This follows from $P_k<q^k$ and $k\le q-2$. At the starting point, $P_{10}=6469693230>2^{32}$ and $R_{10}=6469693230/1021870080<6.34$. Therefore $(\log P_{10}-1.1)>32(0.69)-1.1>3(6.34)$. Taking $P_k\le n<P_{k+1}$ proves the claim over the entire infinite tail.

## Finite verification and the equality cases

The first verifier factors every $n$ from 1 through $B$ in blocks. It starts each totient at $n$ and subtracts its current value divided by $p$ once for each distinct prime factor $p$. After it has removed all primes up to the square root of the block's upper endpoint, each remaining factor greater than 1 is prime. It increments $\pi(n)$ exactly when $n\ge2$ and $\varphi(n)=n-1$. At $n=1$ we have $\varphi(1)=1$ and $\pi(1)=0$.

The second verifier counts primes independently with the sieve of Eratosthenes. It computes exact totients using Euler's linear sieve on smaller cofactors. The following divisibility filters justify its shorter table. For $n\le B<P_{10}$, if a prime $p\in\{2,3,5\}$ does not divide $n$, then $n/\varphi(n)\le R_{10}(p-1)/p$, since the nine smallest admissible primes are among the first ten. If $n\ge2^{20}$ and $p=2$ or $3$ is missing, then
$3n/\varphi(n)<3(6.34)(2/3)<20(0.69)-1.1$.
Likewise, if $n\ge2^{24}$ and $5$ is missing, then
$3n/\varphi(n)<3(6.34)(4/5)<24(0.69)-1.1$.
Dusart's inequality rules out these inputs. Thus candidates below $2^{20}$ require no divisibility assumption, candidates in the next band must be multiples of 6, and candidates from $2^{24}$ through $B$ must be multiples of 30. For $n=d k$ with $d=6$ or $30$, multiply $\varphi(k)$ by $p$ for each $p\mid d$ that divides $k$, and by $p-1$ for each remaining $p\mid d$. This is Euler's product formula.

Both verifiers emitted precisely the same **33,763** triples $(n,\varphi(n),\pi(n))$ satisfying $\varphi(n)\le3\pi(n)$, byte for byte. Both obtained $\pi(B)=18,067,928$. At the final exception, $\varphi(223092870)=36,495,360$ and $\pi(223092870)=12,283,531$.

For $c=3$ the equality cases, in increasing order, are
```text
37, 43, 91, 95, 175, 1082, 1084, 1168, 1444, 1786, 3304, 3416,
22960, 24306, 24732, 24912, 35844, 37398, 41616, 50544, 50934,
100122, 165354, 228870, 731280
```

For $c=2$ the twenty equality cases are exactly the list in A067786. Donovan Johnson recorded the completeness conjecture in 2013. A separate 2003 entry by Luke Pebody already states $\varphi(n)>2\pi(n)$ for all $n>90090$. Together with a finite check, that earlier bound also settles Johnson's question. [A067786](https://oeis.org/A067786) · [A080289](https://oeis.org/A080289)

## Fifty-six certified terms of A080289

An integer $m\ge2$ is a term if $\varphi(m)/\pi(m)$ is strictly smaller than $\varphi(n)/\pi(n)$ for every $n>m$. The OEIS displays 38 terms. Giovanni Resta described terms 25 through 38 as empirical, based on testing up to $10^9$. [A080289, including Resta's 2017 comment](https://oeis.org/A080289)

Scan the 33,763 triples backwards. Keep a triple exactly when its ratio is strictly below the smallest ratio already seen, keeping the last triple to start. Every retained ratio is at most 3. Every omitted integer with ratio above 3, including the entire infinite tail, exceeds every retained ratio. Conversely any such omitted integer before the last triple fails the record test because that later triple has ratio less than 3. Thus the retained triples in increasing order give an exact initial segment, with no missing terms. The ratio comparisons use exact rational numbers.

The first 38 match the published table. Terms 39 through 56 are

```text
2552550, 3063060, 3573570, 4084080, 9699690, 11741730, 13123110,
19399380, 23483460, 29099070, 38798760, 48498450, 58198140,
67897830, 77597520, 87297210, 96996900, 223092870
```

## A069187 and A034097

**Squarefree part and the ceiling square root.** Write $n=t^2d$ with $d$ squarefree, $t\ge1$. The condition $d=\lceil\sqrt n\rceil$ is equivalent to $(d-1)^2<t^2d\le d^2$. Dividing by $d$ gives $d-2+1/d<t^2\le d$. Hence $t^2=d$ or $t^2=d-1$. In the first case the squarefree square $d$ must equal 1, giving $n=1$. The second case gives $n=t^2(t^2+1)$ with $t^2+1$ squarefree. Conversely each such positive $t$ satisfies the two inequalities, as does $n=1$. Thus the polynomial formula in Ralf Stephan's 2004 conjecture describes every term after the initial 1. Taken literally as a description of every term it misses 1. The Lean file proves both the counterexample and the corrected equivalence. [A069187](https://oeis.org/A069187) · [A071253](https://oeis.org/A071253) · [A049532](https://oeis.org/A049532)

**Runs with first fractional square-root digit 1.** In the block with $k=\lfloor\sqrt n\rfloor$, the condition is $k+0.1\le\sqrt n<k+0.2$. Squaring gives the integer interval from $k^2+\lfloor k/5\rfloor+1$ through $k^2+\lfloor2k/5\rfloor$, a characterization Robert Israel recorded in 2016. Its length is $\lfloor2k/5\rfloor-\lfloor k/5\rfloor$. Writing $k=5q+r$, the five possible lengths are $q,q,q,q+1,q+1$. These are exactly $\operatorname{round}(k/5+1/25)$. Consecutive blocks are separated by a perfect square. The Lean theorem proves both neighbors fail the digit test, every member of the interval passes it, and its length is exactly Dimitri Papadopoulos's proposed formula. [A034097](https://oeis.org/A034097)

As a separate check, these formulas reproduce the published 300-term table for A069187 and the 10,000-term table for A034097.

## Reproduce

From this directory, with a C++17 compiler and Python 3, run

```sh
c++ -O3 -std=c++17 segmented.cpp -o segmented
c++ -O3 -std=c++17 crosscheck.cpp -o crosscheck
./segmented > segmented.tsv
./crosscheck > crosscheck.tsv
cmp segmented.tsv crosscheck.tsv
python3 analyze.py segmented.tsv > computed.json
cmp computed.json results.json
```

The raw stream's SHA-256 is `cfd64d3d71e1b90047f1056b2e246abcbcff8b4a638af6de52f05c908315037c`. The complete lists of equality cases and records are in [results.json](results.json).

With Lean 4.33.1 and the pinned Mathlib dependency, run `lake update`, `lake exe cache get`, then `lake env lean SquareRootSequences.lean`. Each printed theorem uses at most `propext`, `Classical.choice`, and `Quot.sound`. The file contains no proof placeholders. The prime-counting proof and integer sieves are independent of the Lean file.
