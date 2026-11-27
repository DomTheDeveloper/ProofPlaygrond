# A totient bound for the divisor-sum difference in A245212

Let $a(n)$ be [Krizek's A245212](https://oeis.org/A245212). Here $\tau$ counts the positive divisors, $\sigma$ sums them, and $\varphi$ is Euler's totient. Every positive integer with at least two distinct prime divisors satisfies

$$
\varphi(n)(a(n)-\sigma(n)) \ge n(2\varphi(n)-n)(\tau(n)-1).
$$

In particular, an odd integer in this class satisfying $n\le2\varphi(n)$ has $a(n)>\sigma(n)$. Oddness makes the bound on $n$ strict, and $\tau(n)>1$.

## Proof

Set $T(n)=\sum_{d\mid n}d\tau(d)$, so $a(n)=2n\tau(n)-T(n)$. Write $n=\prod p^e$ over its distinct prime divisors. On each factor, write $E=e+1$. A geometric sum and a weighted geometric sum give

$$
(p-1)\sigma(p^e)\le p\,p^e,\qquad (p-1)T(p^e)\le(pE-1)p^e .
$$

For the second inequality, the term of degree $e$ in $T(p^e)$ is $Ep^e$. The remaining coefficients are at most $e$. After multiplying their geometric sum by $p-1$, their contribution is at most $e(p^e-1)$. The first inequality follows directly from the geometric series.

Define $A=\prod p$, $B=\prod(p-1)$, $F=\prod pE=A\tau(n)$ and $C=\prod(pE-1)$. Multiplicativity of both divisor sums gives $B(T(n)+\sigma(n))\le n(C+A)$.

To compare $F-C$ and $A-B$, telescope the difference between each product and the product obtained by decreasing every factor by one. Order the prime divisors in the same way in both telescoping sums. In a term indexed by $i$, every other factor in the first sum is at least twice its counterpart in the second, since $pE\ge 2p$ and $pE-1\ge 2(p-1)$. There is at least one other factor. Therefore $F-C\ge2(A-B)$. It follows that

$$
B(T(n)+\sigma(n))+nA\le n(A\tau(n)+2B).
$$

Using $\varphi(n)A=nB$ gives $\varphi(n)(T(n)+\sigma(n))+n^2\le n^2\tau(n)+2n\varphi(n)$. Substitute the defining identity for $a(n)$ and rearrange to obtain the displayed theorem.

## Verification and attribution

[Permanent Lean proof](https://github.com/DomTheDeveloper/open-math-agents/blob/ef13d3fa91ba444a4a5843fbad96bb5f3731f7f5/proofs/OeisA245212.conjecture.R1.H1.R1.H1.lean#L162). The final declaration in that file proves the exact Left to Solve hypothesis. From this directory, `python3 check_totient_gap.py` independently checks the formula using the defining divisor sums on all eligible integers through 200,000.

Jaroslav Krizek posed the original conjecture. BetAdmin237 gave the [odd/even reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/488). Dominic Aziz Dabish (DomTheDeveloper) gave the [earlier odd-input split, two-prime bound and local estimates](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1048). This inequality gives a uniform quantitative proof of the totient branch for every supported factorization.
