# The exponent-two case at 3 for A245212

Let $a(n)=2n\tau(n)-T(n)$, where $T(n)=\sum_{d\mid n}d\tau(d)$, and let $\sigma(n)$ denote the sum of divisors. Suppose $n$ is odd and has exactly four distinct prime factors. If $a(n)=\sigma(n)$, then **$27\mid n$**.

The new step excludes every $n=9p^e q^f r^g$ for distinct primes $3<p<q<r$ and positive exponents. We prove a sharp positive gap when $r\ge13$. For the single remaining support $\{5,7,11\}$, two exact exhaustive computations exclude equality. On that support the gap can have either sign. The conclusion concerns equality and makes no upper-bound assumption on $n$ or its exponents.

## The gap when the largest prime is at least 13

Set $m=p^e q^f r^g$, $E=e+1$, $F=f+1$ and $G=g+1$. The three multiplicative functions give

$$T(9m)=34T(m),\qquad \sigma(9m)=13\sigma(m),\qquad (9m)\tau(9m)=27mEFG.$$

For any prime $t\ge c+1$, summing the geometric progression gives $c\sigma(t^h)\le(c+1)t^h$. Also $T(t^h)=\sum_{j=0}^h(j+1)t^j\le(h+1)t^h+h\sum_{j=0}^{h-1}t^j$, so $cT(t^h)\le((c+1)(h+1)-1)t^h$. Apply these bounds with $c=4,6,12$ at $p,q,r$. Keep the subtraction of one at $p$. Then

$$288T(m)\le m(5E-1)(7F)(13G),\qquad 288\sigma(m)\le455m.$$

Multiplying by the factors at 9 gives

$$288(T(n)+\sigma(n))\le m(15470EFG-3094FG+5915)\le15470mEFG,$$

since $FG\ge4$. Consequently

$$3888\bigl(a(n)-\sigma(n)\bigr)\ge41n\tau(n).$$

The coefficient is optimal. Along $n_h=9(5\cdot7\cdot13)^h$, each $T(t^h)/(t^h(h+1))$ tends to $t/(t-1)$ by the reversed geometric sum, and $\sigma(n_h)/(n_h\tau(n_h))$ tends to zero. Thus the normalized gap tends to $2-(34/27)(5/4)(7/6)(13/12)=41/3888$.

## Exceptional support and the first certificate

The only other ordered support is $5,7,11$. The equation to solve is $T(n)+\sigma(n)=2n\tau(n)$. For $p$ prime and $i=e+1$, put $z_p(i)=(1-p^{-i})/i$ and $\alpha_p=1/(p-1)$. Summing the prime-power formulas yields

$$\frac{T(p^e)}{p^e i}=\frac{p}{p-1}(1-\alpha_p z_p(i)),\qquad \frac{\sigma(p^e)}{p^e i}=\frac{p}{p-1}z_p(i).$$

Try all six orders of the support primes, assigning indices $2\le i\le j\le k$. With $x=z_p(i)$, $y=z_q(j)$ and $z=z_r(k)$, equality becomes

$$(1-\alpha_px)(1-\alpha_qy)(1-\alpha_rz)+\lambda xyz=t,$$

where $\lambda=13/34$ and $t=(54/34)\prod_{s\in\{5,7,11\}}(s-1)/s<1$. Since $z_s(h)\le1/h$ and $1-\prod(1-u_s)\le\sum u_s$ for $0\le u_s\le1$, we have $i\le\sum_s\alpha_s/(1-t)$. Put $B=1-\alpha_p x$, $D=B\alpha_q\alpha_r+\lambda x$. After expansion the equation is $B-t=B(\alpha_qy+\alpha_rz)-Dyz$. For $B>t$ this gives $j\le B(\alpha_q+\alpha_r)/(B-t)$. For $B\le t$, division by $yz$ gives $j\le D/[B(\alpha_q+\alpha_r)]$. For each remaining pair the equation is linear in $z$ and the program checks the zero-coefficient case. If a positive $z$ is required, $k=\lfloor 1/z\rfloor$ because $k<k/(1-r^{-k})<k+1$ for $k\ge2$. Its reduced denominator is divisible by $r^k$. The program tests the resulting candidate exactly.

The [rational checker](rational_check.py) obtained $i\le52$, a largest second-index bound of 2721 and 19,606 ordered prefixes. It found zero equalities.

## Independent integer certificate

Normalize each prime-power moment as $W_s(h)=T(s^h)/(s^h(h+1))$ and $V_s(h)=\sigma(s^h)/(s^h(h+1))$. The reversed sum $W_s(h)=\sum_{d=0}^h(1-d/(h+1))s^{-d}$ increases to $s/(s-1)$. The average $V_s(h)$ of $1,s^{-1},\ldots,s^{-h}$ decreases to zero. For all remaining exponents at least $H$, insert the endpoints in the products to bound $T(n)/(n\tau(n))+\sigma(n)/(n\tau(n))$. Whenever the resulting interval excludes 2, the entire tail is eliminated. The program doubles $H$ until each tail has been certified.

After fixing $m=9p^a q^b$, the last exponent $c$ must satisfy $r^c\mid T(m)-(r-1)\sigma(m)$. Indeed, multiply the original equation by $(r-1)^2$ and reduce modulo $r^c$. The two local factors $(r-1)^2T(r^c)$ and $(r-1)^2\sigma(r^c)$ reduce to $1$ and $-(r-1)$ respectively. If the difference vanishes, $(r-1)T(r^c)+\sigma(r^c)=(c+1)r^{c+1}$ leaves the condition $r\sigma(m)=2m\tau(m)$, which is checked explicitly. Otherwise the valuation bounds the last exponent. The two programs use different tail arguments and different final-exponent tests.

The [integer checker](interval_check.py) certified the common tail from exponent 64 and all second tails by exponent 4096. In its 31,912 ordered prefixes the divisibility and degenerate-case tests eliminated every last exponent. It found zero equalities.

## Consequence and reproduction

If 3 is absent, the four smallest possible primes give $\varphi(n)/n\ge2880/5005>1/2$. The earlier [totient-gap inequality](../totient-gap.md) excludes equality. If 3 occurs once, the [four-prime inequality](../four-primes/README.md) gives a positive gap. The present result excludes exponent two at 3, leaving $27\mid n$ as a necessary condition. It leaves the exponent-three-and-higher case open.

Run `python3 rational_check.py` and `python3 interval_check.py` with stock Python 3.9 or later. The expected outputs are [rational.txt](rational.txt) and [interval.txt](interval.txt). The infinite-family gap and its optimality have written proofs. The exceptional support is a computer-assisted result.

Jaroslav Krizek posed [OEIS A245212](https://oeis.org/A245212) in 2014. The two exact algorithms adapt Dominic Aziz Dabish's earlier [three-prime certificates and totient argument](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1048) to the fixed factor 9. The earlier odd/even split is [BetAdmin237's reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/488). This additional partial result is published by Dominic Aziz Dabish (DomTheDeveloper).
