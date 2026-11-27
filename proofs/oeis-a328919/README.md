# When do divisor-power sums become periodic?

Dominic A. Dabish · November 26, 2026 · Proof developed with Codex

For a positive integer $n$, write $s_k(n)=\sum_{d\mid n}d^k\pmod n$, starting at $k=0$. Let $a(n)$ be the smallest index from which $s_k(n)$ is periodic. Jianing Song posed two conjectures about this preperiod in [OEIS A328919](https://oeis.org/A328919).

**Theorem 1.** The sequence is periodic from index zero precisely for $n=1$ and $n=12$.

**Theorem 2.** For each $e\ge0$, the first positive integer $n$ satisfying $a(n)=e$ is $2^e$.

## A necessary divisibility condition

Write $n=\prod_{p\mid n}p^{e_p}$ and $D=\tau(n)=\prod_{p\mid n}(e_p+1)$. Suppose the sequence is periodic from index zero with period $T>0$. Fix $p^e\parallel n$, put $m=n/p^e$, and take an arbitrarily large common multiple $L$ of $T$ and $\varphi(p^e)$. Each divisor coprime to $p$ contributes 1 to $s_L(n)\bmod p^e$, by Euler's theorem. Each divisor divisible by $p$ contributes zero for $L\ge e$. Thus $s_L(n)\equiv\tau(m)\pmod {p^e}$. At zero, $s_0(n)=(e+1)\tau(m)$. Periodicity implies
$$
p^e\mid e\,\tau(m).
$$
This local condition is Song's observation in the OEIS entry. To use all the conditions at once, let $E=\prod_{p\mid n}e_p$. Each $p^e$ divides $DE$, since $e\mid E$ and $\tau(m)\mid D$. The prime powers are pairwise coprime. Hence $n\mid DE$, giving the global bound
$$
\prod_{p\mid n}p^{e_p}\ \le\ \prod_{p\mid n}e_p(e_p+1). \tag{1}
$$

## What the bound allows

For each prime power define $R(p,e)=p^e/[e(e+1)]$, for $e\ge1$. Inequality (1) requires the product of these ratios to be at most one.

* For every odd prime, $R(p,e)\ge 3/2$. Equality occurs exactly for $p=3$ and $e\in\{1,2\}$. Indeed $3^1/2=3^2/6=3/2$, and the ratio of successive values for base 3 is $3e/(e+2)>1$ for $e>1$.
* For $p=2$, the minimum ratio is $2/3$ and it occurs exactly at $e=2,3$. The ratio of successive values is $2e/(e+2)$, which is below one at $e=1$, equals one at $e=2$, and exceeds one thereafter.

Odd $n>1$ is excluded. For a power $n=2^e>1$, the local condition would require $2^e\mid e$, which is impossible. If $n$ has both an even and an odd prime factor, the preceding bounds force exactly one odd prime factor, and both bounds must be equalities. The candidates are $12,24,36,72$. For $24,36,72$ respectively, the condition at $2$ would require $8\mid6, 4\mid6, 8\mid9$. This leaves $12$.

Modulo 1 the sequence is constant. For 12 its residues alternate $6,4,6,4,\ldots$. One direct verification uses $\sigma_k(12)=(1+2^k+4^k)(1+3^k)$. At $k=0$ it is 6. For $k\ge1$, its residues modulo 3 are $0$ for even $k$ and $1$ for odd $k$, since $2\equiv-1$ and $4\equiv1$. Its residues modulo 4 are $2$ for positive even $k$ and zero for odd $k$. The Chinese remainder theorem gives the stated cycle.

## First occurrences

Let $M=\max_{p\mid n} e_p$ for $n>1$. For $k\ge M$, each divisor divisible by $p$ contributes zero modulo $p^{e_p}$, while each unit repeats after $\varphi(p^{e_p})$ steps. Taking a common multiple of these periods shows $a(n)\le M$. In particular $n\ge2^{a(n)}$.

For $n=2^e$, $e\ge1$, the residue is (1) whenever $k\ge e$. If $e\ge2$, at $k=e-1$ the first two divisors contribute $1+2^{e-1}$, and every larger divisor contributes zero modulo $2^e$. For $e=1$, the two divisors contribute $1+1\equiv0\pmod2$ at $k=0$. Thus $a(2^e)=e$. Finally $a(1)=0$ handles $e=0$. This proves Theorem 2.

## Reproduction

`verify.py` checks the classifications for $1\le n\le100{,}000$. It finds exactly $1,12$ with preperiod zero and first occurrences $2^e$ for $0\le e\le16$. It also computes the full finite-state cycle independently for the first 500 inputs. Run `python3 verify.py` to reproduce these checks.
