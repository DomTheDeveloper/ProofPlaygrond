# Effective finiteness for odd four-prime equalities in OEIS A245212

For Jaroslav Krizek's sequence put
\[
 T(n)=\sum_{d\mid n}d\tau(d),\qquad a(n)=2n\tau(n)-T(n).
\]
Here \(\tau\) counts divisors and \(\sigma\) sums them. The following are computer-assisted partial results for the [2014 conjecture](https://oeis.org/A245212).

1. Among odd integers with exactly four distinct prime factors, the set satisfying \(a(n)=\sigma(n)\) is **finite and effectively computable**, allowing the four primes and all their exponents to vary.
2. Every such equality requires \(243\mid n\). The new exclusions are the cases \(v_3(n)=3,4\), each proved for all exponents at the other three primes.

The proof of (1) supplies a terminating algorithm. Its global finite search has not been executed. The two individual exponent layers in (2) have been exhaustively classified.

## An explicit bound on the largest prime

The [totient inequality](../totient-gap.md) implies that an odd equality candidate with at least two prime factors has \(n/\varphi(n)>2\). Let \(r\) be its largest prime and suppose it has exactly four distinct primes. The least prime must be 3, since \((5/4)(7/6)(11/10)(13/12)<2\). If \(r\ge257\), the first three primes must be \(P=(3,5,q)\) with \(q=7,11,13\). Indeed \((3/2)(7/6)(11/10)(257/256)<2\), and \((3/2)(5/4)(17/16)(257/256)=65535/32768<2\).

For an exponent \(e\ge1\) write \(i=e+1\), \(z_p(i)=(1-p^{-i})/i\), and \(\alpha_p=1/(p-1)\). The geometric sums give
\[
 \frac{T(p^e)}{p^e i}=\frac p{p-1}(1-\alpha_p z_p(i)),\qquad
 \frac{\sigma(p^e)}{p^e i}=\frac p{p-1}z_p(i).
\]
The first normalized factor increases with the index, the second decreases. For example \(z_p(i)=(1-p^{-1})(1+p^{-1}+\cdots+p^{1-i})/i\) decreases as the average of an initial segment of a strictly decreasing sequence.

For the triple \(P\), let \(B=\prod_{p\in P}(1-\alpha_p z_p(i_p))\), \(C=\prod_{p\in P}z_p(i_p)\) and \(t=2\prod_{p\in P}(1-1/p)\). If the fourth prime has index \(j\), equality is equivalent to
\[
 B(1-\alpha_r z_r(j))+Cz_r(j)=t(1-1/r).
\]
Replacing one or more base indices by infinity sets their \(z\)'s to zero. Every resulting product \(B^*\) satisfies
\[
     |B^*-t|>1/20{,}000{,}000. \tag{1}
\]
Two exact proofs of this finite calculation are in [check_faces.py](check_faces.py). Here are their bounds. Write \([L,U]=[t-1/20{,}000{,}000,t+1/20{,}000{,}000]\). At most two indices remain finite. For a product in this interval, the smaller remaining index is at most \(\sum\alpha_p/(1-U)\), since the product is at least \(1-\sum\alpha_p/i_{\min}\). For a two-index product fix the first factor \(b\). The one-index check places \(b\) outside the interval. If \(b<L\) all completions are smaller, and if \(b>U\) the last index is at most \(b\alpha_q/(b-U)\). This exhausts each face. The independent calculation uses unnormalised increasing moments, brackets each crossing by doubling, and tests the two adjacent integer indices by bisection.

| Base primes | \(t\) | Direct index tests | Monotone tests |
|---|---:|---:|---:|
| 3, 5, 7 | 32/35 | 600 | 76 |
| 3, 5, 11 | 32/33 | 1,539 | 210 |
| 3, 5, 13 | 64/65 | 6,834 | 418 |

Let \(I\) be the largest base index, and form \(B^*\) by replacing that index with infinity. We have \(0<B^*-B\le1/(2I)\), \(B\alpha_r z_r(j)\le1/[2(r-1)]\), and \(Cz_r(j)\le1/(8I)\). The equality equation gives
\[
 -\frac{1}{8I}-\frac1r < B^*-t
 \le \frac1{2I}+\frac1{2(r-1)} .
\]
Consequently, if \(r>25{,}000{,}000\), then \(I<25{,}000{,}000\) by (1). Write \(n=mr^{j-1}\). Modulo \(r\), both local divisor sums at \(r^{j-1}\) are 1, so \(r\mid T(m)+\sigma(m)\). This is a positive integer. For \(M=25{,}000{,}000\) we have \(m<195^M\), \(\tau(m)<M^3\), \(\sigma(m)<3m\), and \(T(m)\le\tau(m)\sigma(m)\). Hence, in every case,
\[
             r<6M^3 195^M < 10^{57{,}500{,}024}.
\]
The final inequality follows from \(195^{10}<10^{23}\) and \(6M^3<10^{24}\). This intentionally loose bound suffices to make the list of possible prime supports finite.

The [fixed-support theorem and its algorithm](../fixed-support/README.md) give finitely many points and explicitly described rays on each support. A ray \(mp^e\) requires \(T(m)=(p-1)\sigma(m)\) and \(2m\tau(m)=p\sigma(m)\), which give \(a(m)=\sigma(m)\). Here \(m\) would have exactly three distinct odd prime factors. The [earlier three-prime exclusion](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1048) rules this out. Enumerating the bounded supports and their finite classifications proves (1) of the introduction.

## Excluding exponents three and four at 3

Let \(n=3^h p^a q^b r^c\), with \(3<p<q<r\), all exponents positive and \(h=3,4\). Put \(W=T(3^h)/(3^h(h+1))\) and \(w=\sigma(3^h)/T(3^h)\). The normalized left side \((T(n)+\sigma(n))/(n\tau(n))\) decreases in each prime at fixed exponents by the positive reciprocal-power sums. At a support whose smallest remaining prime is \(p\), if \(w/4<1/(p-1)\), then
\[
 \prod_{s=p,q,r}(1-\alpha_s z_s)+wz_pz_qz_r <1,
\]
since \(z_qz_r<1/4\). Thus the normalized left side is less than \(W\prod s/(s-1)\). This estimate at the minimal triples \((7,11,13)\) and \((5,13,17)\), followed by monotonicity, excludes every larger triple in those two classes. For the remaining triples \((5,7,r),(5,11,r)\), the same bound excludes equality whenever it is at most 2. The residual lists are:

| \(h\) | First two primes after 3 | Possible last primes |
|---|---|---|
| 3 | 5, 7 | 11, 13, 17, 19, 23 |
| 4 | 5, 7 | 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61 |
| 4 | 5, 11 | 13 |

The normalized equation for these three remaining primes has target \(u=(2/W)\prod(1-1/s)<1\). Try all orders of indices \(2\le i\le j\le k\), permuting their primes \(p,q,r\). The first index is at most \(\sum\alpha_s/(1-u)\). Once \(x=z_p(i)\) and \(b=1-\alpha_px\) are fixed, the equation reads
\[
 b-u=b(\alpha_q y+\alpha_r v)-(b\alpha_q\alpha_r+w x)yv,
 \qquad y=z_q(j),\quad v=z_r(k).
\]
For \(b>u\), \(j\le b(\alpha_q+\alpha_r)/(b-u)\). Otherwise dividing by \(yv\) gives \(j\le(b\alpha_q\alpha_r+wx)/(b(\alpha_q+\alpha_r))\).

[check_layers.py](check_layers.py) uses these bounds. For the known cofactor \(m\), equality at \(mr^e\) requires \(r^e\mid T(m)-(r-1)\sigma(m)\) by multiplying by \((r-1)^2\) and reducing modulo \(r^e\). The program sieves small powers by recurrences, tests the full valuation and handles the zero-difference ray separately.

[check_intervals.py](check_intervals.py) instead doubles the common lower index until bounds on the two normalized products exclude the whole tail. After fixing two indices the equation is linear in \(z_r(k)\). Its reciprocal is a ratio of two affine functions of \(q^{-j}\). For \(j\ge12\), bracketing that quantity between 0 and \(q^{-12}\), and using \(1-r^{-12}\le1-r^{-k}<1\), gives rigorously outward bounds on the integer \(k\). The exact rational equation tests surviving rows, including denominator-crossing cases. Neither program found a solution.

| \(h\) | Ordered prefixes, divisibility search | Ordered prefixes, interval search |
|---|---:|---:|
| 3 | 375,354 | 584,672 |
| 4 | 1,791,552 | 2,878,892 |

[Earlier work](../three-squared/README.md) already proved \(27\mid n\). Excluding these two further layers gives \(3^5=243\mid n\). Krizek proposed the original equivalence. BetAdmin237 supplied the [odd/even project split](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/488). Dominic Aziz Dabish (DomTheDeveloper) published the cited prior certificates and this extension. The four-prime case with higher exponents and the unrestricted conjecture remain open.

Run the public certificates with Python 3.9 or later, with assertions enabled:

```sh
python3 check_faces.py
python3 check_layers.py
python3 check_intervals.py
```
