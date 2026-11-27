# A sharp four-prime inequality for A245212

Let $p<q<r$ be primes greater than three, let $e,f,g\ge1$, and set $n=3p^e q^f r^g$. For Krizek's sequence $a=$ [OEIS A245212](https://oeis.org/A245212),

$$
288\bigl(a(n)-\sigma(n)\bigr)\ge37n\tau(n).
$$

The constant $37/288$ is optimal. This excludes every odd number with exactly four distinct prime factors in which 3 occurs to the first power. It includes numbers with $n>2\varphi(n)$, for instance every $3\cdot5^e7^f11^g$. Here $n/\varphi(n)=77/32>2$ irrespective of the exponents.

## Proof

Write $T(m)=\sum_{d\mid m}d\tau(d)$. Then $a(n)=2n\tau(n)-T(n)$. Each of $T,\sigma,\tau$ is multiplicative. Put $m=p^e q^f r^g$ and $E=e+1$, $F=f+1$, $G=g+1$. Since $n=3m$ and $3$ is coprime to $m$,

$$T(n)=7T(m),\quad \sigma(n)=4\sigma(m),\quad n\tau(n)=6mEFG.$$

If $t$ is prime and $c+1\le t$, the geometric sum gives $c\sigma(t^h)\le(c+1)t^h$. Separating the leading term of the weighted sum gives
$$ cT(t^h)\le ((c+1)(h+1)-1)t^h.$$
Use $c=4,6,10$ at $p,q,r$, respectively. These choices are valid since $p\ge5$, $q\ge7$ and $r\ge11$. Retain the subtraction of one at $p$ and drop it at the other two primes. Multiplication yields

$$240T(m)\le m(5E-1)(7F)(11G),\qquad 240\sigma(m)\le385m.$$

Consequently
$$240(T(n)+\sigma(n))\le m\bigl(2695EFG-539FG+1540\bigr)\le2695mEFG,$$
because $F,G\ge2$. Since $2695/1440=539/288$, subtraction from $2n\tau(n)$ proves the claim.

## Sharpness

Take $n_h=3(5\cdot7\cdot11)^h$. For each fixed prime $t$,
$$\frac{T(t^h)}{(h+1)t^h}=\sum_{j=0}^h\left(1-\frac{j}{h+1}\right)t^{-j}\longrightarrow\frac{t}{t-1}.$$
The discarded geometric tail is $t^{-h}/(t-1)$ and the weighted correction is at most $t/((h+1)(t-1)^2)$. Also $\sigma(n_h)/(n_h\tau(n_h))\to0$, by the geometric bound above. The normalized gap tends to
$$2-\frac76\frac54\frac76\frac{11}{10}=\frac{37}{288}.$$

## Consequence for the open conjecture

Every odd counterexample with exactly four distinct prime factors must be divisible by 9. Indeed, if 3 is absent, the four prime factors are at least $5,7,11,13$, so $\varphi(n)/n\ge 2880/5005>1/2$. The [uniform totient inequality](../totient-gap.md) excludes this case. If 3 occurs exactly once, the displayed four-prime bound gives $a(n)>\sigma(n)$. The case $9\mid n$ remains a separate question.

## Verification and sources

[FourPrimes.lean](FourPrimes.lean) proves the displayed four-prime inequality from the defining divisor sums in Mathlib. The short limiting argument above establishes optimality in ordinary mathematics. The companion [exact checker](check_four_primes.py) uses prime-power moments and, on the small cases, an independent divisor sieve.

Run from this directory inside a Lean 4.33.1 checkout with the Mathlib revision in the Left to Solve [formal-conjectures pin](https://github.com/google-deepmind/formal-conjectures/tree/9097e2f90e66d2f6244209cb1c07f7120d17ec53).

```sh
lake env lean FourPrimes.lean
python3 check_four_primes.py
```

Jaroslav Krizek posed the original conjecture in 2014. The geometric estimates and the sharp two-prime bound appeared in [DomTheDeveloper's earlier reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1048), following [BetAdmin237's odd/even reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/488). The four-prime inequality is a partial result by Dominic Aziz Dabish (DomTheDeveloper). Research priority has not been established.
