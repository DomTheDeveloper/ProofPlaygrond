# Two divisor identities conjectured by Velin Yanev

Two 2019 formulas in the OEIS follow from looking at one prime at a time. The first works for arbitrary additive weights. The second extends to every positive order of the Jordan totient.

## A063956 · Primes occurring exactly once

Let $U(n)=\sum_{v_p(n)=1}p$, summed over primes. For all positive integers $m,n$,

$$
U(mn)+U(\gcd(m^2,n))+U(\gcd(m,n^2))=U(m)+U(n).
$$

Yanev's proposed subtraction formula is this equality rearranged. More generally, replace each prime's contribution with any weight $w(p)$ in a commutative additive monoid.

**Proof.** Fix a prime $p$ and write $e=v_p(m)$ and $f=v_p(n)$. Its exponents in the three arguments on the left are $e+f$, $\min(2e,f)$, and $\min(e,2f)$. When either $e$ or $f$ is zero, the product supplies the only possible contribution. When both are positive, the product's exponent is at least two. Then $\min(2e,f)=1$ exactly when $f=1$, and $\min(e,2f)=1$ exactly when $e=1$. Each side therefore counts $w(p)$ equally often. Sum over the prime divisors of $mn$.

For $m=12$ and $n=18$, the product $216=2^3 3^3$ contributes zero. The two gcds are 18 and 12, contributing 2 and 3. [OEIS A063956, including Yanev's February 2019 conjecture](https://oeis.org/A063956)

## A055210 · Totients of square divisors

Let $L$ be the largest square dividing $n$, and let $\sigma_r(t)=\sum_{d\mid t}d^r$. Then

$$
\sum_{d^2\mid n}\varphi(d^2)=\frac{\sigma_2(L)}{\sigma_1(L)}.
$$

**Proof.** Write $n=\prod_p p^{a_p}$ and $b_p=\lfloor a_p/2\rfloor$. Then $L=\prod_p p^{2b_p}$. Both sides factor over primes. For $p^{2b}\Vert L$, the local factor of the sum is
$$
1+\sum_{j=1}^b(p^{2j}-p^{2j-1})=\frac{p^{2b+1}+1}{p+1}.
$$
The ratio of divisor sums gives the same factor, since
$$
\frac{\sum_{j=0}^{2b}p^{2j}}{\sum_{j=0}^{2b}p^j}
=\frac{p^{2(2b+1)}-1}{p^{2b+1}-1}\cdot\frac{p-1}{p^2-1}
=\frac{p^{2b+1}+1}{p+1}.
$$
The empty product covers $n=1$. Vladeta Jovovic recorded the equivalent prime-power formula in 2001. Yanev proposed the ratio in October 2019. [OEIS A055210](https://oeis.org/A055210)

For example, $360=2^3 3^2 5$ has largest square divisor $36$. Its square divisors are $1,4,9,36$, with totients $1,2,6,12$. Their sum is $21=1911/91=\sigma_2(36)/\sigma_1(36)$.

### All positive Jordan orders

For any integer $r\ge1$, the Jordan totient $J_r$ is multiplicative, with $J_r(1)=1$ and $J_r(p^a)=p^{ra}-p^{r(a-1)}$ for $a\ge1$. Set $x=p^r$ in the preceding local calculations. This gives
$$
\sum_{d^2\mid n}J_r(d^2)
=\frac{\sigma_{2r}(L)}{\sigma_r(L)}
=\prod_{p^{2b}\Vert L}\frac{p^{r(2b+1)}+1}{p^r+1}.
$$

In particular, for every positive square $L$, $\sigma_r(L)$ divides $\sigma_{2r}(L)$ with **odd quotient**. Each local factor is $1-x+x^2-\cdots-x^{2b-1}+x^{2b}$. For even $x$ the constant term determines its parity. For odd $x$ there are an odd number of odd terms modulo two.

## Reproducible arithmetic checks

Run the supplied Python script with Python 3. It checks all 22,500 ordered pairs in $[1,150]^2$ for the unitary-prime formula, and the first 16,384 integers at Jordan orders 1, 2, and 3. Independent comparisons also matched all 10,000 published A063956 terms and all 16,384 published A055210 terms. To repeat them, pass the two downloaded b-files to the script in that order. [A063956 table](https://oeis.org/A063956/b063956.txt) · [A055210 table](https://oeis.org/A055210/b055210.txt)
