# Both supercongruences for every row of Bala’s Legendre array

Dominic A. Dabish, with AI assistance, 27 November 2026.

Let $T(R,n)=[x^n](1-x)^{-1}P_n((1+x)/(1-x))^R$ as in A364113. Peter Bala conjectured the following two congruences. For every row $R\ge0$, prime $p\ge5$, and integers $m,r\ge1$, put $N=mp^r$. Then

$$T(R,N)\equiv T(R,N/p)\pmod{p^{3r}},\qquad T(R,N-1)\equiv T(R,N/p-1)\pmod{p^{3r}}.$$

We prove both statements. The rows $R=1,2$ are the classical Apéry rows. The proof below uses binomial scaling and summation by parts in the tradition of Gessel, Beukers and Straub. The two different end weights in the coefficient formula require attention to adjacent partial sums. [Bala’s conjecture](https://oeis.org/A364113) · [Straub, *Multivariate Apéry numbers and supercongruences of rational functions*, especially §§3, 5](https://doi.org/10.2140/ant.2014.8.1985)

## 1. Two sums with squared binomial factors

The row $R=0$ is identically one. For $R\ge1$ put $K=\sum_{i=1}^R u_i$ with all $u_i\ge0$, and $M=N-K$. Use the following notation.

| | $C(N,u)$ | $D(N,M)$ | Domain |
| --- | --- | --- | --- |
| Unshifted | $\binom Nu$ | $\binom{RN+M}{M}$ | $M\ge0$ |
| Shifted | $\binom{N+u-1}{u}$ | $(-1)^{M-1}\binom{RN-1}{M-1}$ | $M\ge1$ |

In each case the row value is

$$\sum_{\boldsymbol u} D(N,M)\prod_{i=1}^R C(N,u_i)^2.\tag{1}$$

For the first line use $H_N(x)=\sum_u\binom Nu^2 x^u$ and $T(R,N)=[x^N](1-x)^{-RN-1}H_N(x)^R$. For the shifted line, Euler’s hypergeometric transformation (or its finite binomial specialization) gives the formal series identity

$$\sum_{u\ge0}\binom{N+u-1}{u}^2 x^u=(1-x)^{1-2N}H_{N-1}(x).$$

Substitution in $T(R,N-1)$ leaves the factor $(1-x)^{RN-1}$ and gives precisely the signed coefficient in the table. The power of $x$ for that coefficient is $M-1$. The shift of one in its lower binomial entry is used again in Section 4. [NIST DLMF, Euler transformation 15.8.1](https://dlmf.nist.gov/15.8#E1) · [Legendre coefficient formulas](README.md#1-two-coefficient-formulas)

## 2. A product estimate and two prefix estimates

All fractions with denominators prime to $p$ are taken in $\mathbb Z_{(p)}$. Fix $s\ge1$. In a complete block of length $p^s$, restricted to indices prime to $p$, the reciprocal squares sum to zero modulo $p^s$. Indeed multiplication by 2 permutes the units modulo $p^s$ and $4-1$ is a unit. In the block from $bp^s+1$ to $(b+1)p^s$, pair each unit $i$ with $c-i$ for $c=(2b+1)p^s$. The expansion $1/(c-i)\equiv-1/i-c/i^2\pmod{p^{2s}}$ shows that reciprocal first powers sum to zero modulo $p^{2s}$. The second elementary symmetric sum of reciprocals vanishes modulo $p^s$, by the identity $2e_2=e_1^2-\sum i^{-2}$.

It follows that whenever $p^s\mid L$ and $p^r\mid a$ with $1\le s\le r$,

$$\prod_{\substack{1\le i\le L\\p\nmid i}}(1+a/i)\equiv1\pmod {p^{r+2s}}.\tag{2}$$

In each block the linear, quadratic and remaining terms have valuation at least $r+2s$, $2r+s$ and $3r$, respectively. The estimate also holds with $i<L$ because the endpoint is a multiple of $p$. An empty product is one.

Define $h(j)=\sum_{1\le u\le j,\ p\nmid u} u^{-2}$. The same complete-block argument gives both useful implications

$$p^s\mid j\implies p^s\mid h(j),\qquad p^s\mid j+1\implies p^s\mid h(j).\tag{3}$$

For the second implication $h(j)=h(j+1)$ since the added term is omitted. Valuations of integers include $v_p(0)=+\infty$ throughout.

## 3. Terms with all indices divisible by the prime

If every $u_i$ is divisible by $p$, divide all the indices and $N$ by $p$. This is a bijection with the entire smaller sum in (1), including the strict endpoint in the shifted case. Put $s=\min(r,v_p(u_1),\ldots,v_p(u_R))$. Thus $p^s\mid M$.

Each corresponding pair of $C$ factors differs by a multiplicative factor congruent to one modulo $p^{r+2s}$. For $u>0$, use the product forms

$$\binom{N}{u}=(-1)^{u-1}\frac Nu\prod_{i<u}(1-N/i),\qquad \binom{N+u-1}{u}=\frac Nu\prod_{i<u}(1+N/i),$$

where product indices start at 1. Cancelling the multiples of $p$ leaves (2) with $a=\pm N$. The sign agrees at $u$ and $u/p$ since $p$ is odd. At $u=0$ both factors are one. For $D$ the corresponding products are $\prod_{i\le M}(1+RN/i)$ and $\prod_{i<M}(1-RN/i)$, again starting at 1. Removing multiples of $p$ gives (2) with $a=\pm RN$.

If $s<r$, choose $u_i$ of valuation $s$. In the smaller summand the corresponding factor $C(N/p,u_i/p)$ is $N/u_i$ times an integer, as follows from the elementary binomial identity extracting the first factor. Its square supplies valuation at least $2(r-s)$. If $s=r$ the required additional valuation is zero. Multiplying by the estimate $r+2s$ for the product of scaling factors shows that each pair of summands is congruent modulo $p^{3r}$.

## 4. Terms with an index prime to the prime

If at least two indices are prime to $p$, the two squared $C$ factors supply valuation at least $4r$. It remains to sum terms having exactly one such index $u$. Fix its position and fix all other indices. Set

$$t=\min\big(\{r\}\cup\{v_p(u_i):i\text{ is another position}\}\big),\qquad L=N-\sum_{i\text{ in other positions}}u_i.$$

Here $1\le t\le r$ and $p^t\mid L$. Empty ranges contribute zero, so assume there are eligible unit indices. The fixed squared factors supply at least $2(r-t)$ in valuation by the previous binomial identity, also when $t=r$. On removing the factor $N^2/u^2$ from $C(N,u)^2$, the remaining integer $V(u)$ is $\binom{N-1}{u-1}^2$ in the unshifted case and $\binom{N+u-1}{u-1}^2$ in the shifted case. Set $W(u)=D(N,L-u)$. It suffices to prove

$$\sum_{\substack{1\le u\le J\\ p\nmid u}}\frac{V(u)W(u)}{u^2}\equiv0\pmod{p^t},\tag{4}$$

where $J=L$ in the unshifted case and $J=L-1$ in the shifted case. Indeed the total valuation will then be at least $2(r-t)+2r+t=4r-t\ge3r$.

For both choices of $J$, (3) gives $p^t\mid h(J)$. By finite summation by parts, it is enough to prove that $h(j)$ times the first difference of $V(j)W(j)$ is divisible by $p^t$ for each $1\le j<J$. Split the difference by the product rule; the undifferenced factors are integers.

* For $V$, its successive ratio is $(1-N/j)^2$ or $(1+N/j)^2$, respectively. Put $a=\min(t,v_p(j))$. If $a=t$, (3) supplies the full modulus. Otherwise $V(j+1)-V(j)$ is divisible by $p^{r-a}$, and $h(j)$ supplies $p^a$.
* For the unshifted $W$, the backward relation is $W(j)=(1+RN/(L-j))W(j+1)$. If $a<t$, $v_p(L-j)=v_p(j)=a$ because $p^t\mid L$. The difference again supplies $p^{r-a}$, with the entire modulus already in $h(j)$ when $a=t$.
* For the shifted $W$, the backward relation is $W(j)=(1-RN/(L-j-1))W(j+1)$. These denominators are positive for $j<J$. This time take $a=\min(t,v_p(j+1))$. The second implication in (3) supplies $p^a$ in $h(j)$. If $a<t$, $v_p(L-j-1)=v_p(j+1)=a$ and the difference supplies $p^{r-a}$.

This proves (4), finishes the unit-index terms and establishes both congruences for all rows and multipliers. In particular the two congruences for rows 3 and 4 are instances of the theorem. [A364114](https://oeis.org/A364114) · [A364115](https://oeis.org/A364115)

## Reproduction

Run `python3 verify_towers.py` alongside `verify.py`. It compares exact coefficient extraction with the independent Legendre recurrence, tests both congruences at multiple primes, multipliers and levels, and tests the divisibilities for the two separate groups in (1). `Certificate.lean` contains kernel-checked finite examples. The universal proof is the argument above. Earlier proofs for the classical rows and the limited scope of the finite checks are part of the attribution.
