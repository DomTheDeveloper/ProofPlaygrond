# A height bound and classification by divisor count for OEIS A245212

Let \(T(n)=\sum_{d\mid n}d\tau(d)\), \(a(n)=2n\tau(n)-T(n)\), and let \(\sigma(n)\) be the sum of divisors. Here \(\tau(n)\) and \(\omega(n)\) count divisors and distinct prime divisors respectively. These are partial results for [Jaroslav Krizek's A245212 conjecture](https://oeis.org/A245212).

**Theorem.** For every integer \(n\ge2\) satisfying \(a(n)=\sigma(n)\), put \(D=\tau(n)\), \(r=\omega(n)\). Then
\[
     n\le(2rD)^{D-1},\qquad n<(8r)^{2D}.
\]
Every fixed divisor count therefore has an effectively computable finite equality set. For **all positive integers with at most 512 divisors**, without a bound on their size, the equality holds exactly at \(1,2,2^2,\ldots,2^{511}\). Two exhaustive integer programs certify this last assertion.

## Bounding the next prime

Write an equality input as an increasing product of prime powers. At any proper prefix, let \(m\) be the product already chosen, \(d=\tau(m)\), \(h=D/d\), \(k\) the number of remaining primes, and \(p\) the least of them. Use the empty prefix \(m=d=1\). Put \(b=2md-T(m)\).

For a remaining prime power \(s^e\), both \(T(s^e)/s^e\) and \(\sigma(s^e)/s^e\) are positive polynomials in \(1/s\). Their constant coefficients are \(e+1\) and 1. Each sum is less than its constant coefficient times \(s/(s-1)\), by comparison with a geometric series. Multiplicativity and the equality give
\[
 A=hT(m)+\sigma(m)<2mD<A\left(\frac p{p-1}\right)^k .
\]
Hence \(G=2mD-A=hb-\sigma(m)\) is a positive integer, and
\[
  \frac{G}{2mD}<1-(1-1/p)^k\le \frac{k}{p}.
\]
In particular \(pG\le2rmD\), \(p\le2rmD\), and \(b\ge1\). If \(hb\ge2\sigma(m)\), also \(p\le4rmd\).

Whenever \(p\le Cm\), adding \(p^e\) gives \(C m p^e\le(Cm)^{e+1}\). Taking \(C=2rD\) and iterating from the empty prefix proves the first bound.

For the second bound, call a prefix good when \(hb\ge2\sigma(m)\). As long as the preceding prefixes have been good, write \(U=md\); induction gives \(U\le(8r)^{d-1}\). Indeed \(p\le4rU\) at a good prefix, so with \(i=e+1\) one has
\[
   U'=Uip^e\le (8r)^e U^i\le(8r)^{id-1}
\]
because \(e+1\le2^e\). If every proper prefix is good this already gives the result. Otherwise take the first bad one. Then \(D=dh<2d\sigma(m)\le2md^2\). Therefore \(2rDm<4rU^2<(8r)^{2d}\). Applying the first iteration just to the remaining factors gives
\[
       2rD n\le(2rD m)^{D/d}<(8r)^{2D}.
\]
This argument bounds the size of the integer itself, for both parities and arbitrary factorizations.

For fixed \(r\) it implies \(D>\log n/[2\log(8r)]\). Without fixing \(r\), use \(r\le\log D/\log2\). When \(D\le\log n\), this gives \(\log(8r)\le\log\log\log n+\log(8/\log2)\); when \(D>\log n\) the following asymptotic consequence is immediate. Along any sequence of equality inputs tending to infinity,
\[
 \liminf \frac{\tau(n)\log\log\log n}{\log n}\ge\tfrac12 .
\]
All logarithms are natural. The height bounds alone do not determine whether exceptional equality inputs exist above the certified divisor cutoff.

## Two independent classifications

For the first program enumerate every ordered tuple of local divisor counts \(i_s=e_s+1\ge2\) having product at most 512; their order specifies increasing prime bases. At a prefix, the inequality \(A p^k\ge 2mD(p-1)^k\) gives a finite range for the next prime by bisection. With just one prime left, the exact equation is
\[
  G=\sum_{j=1}^{e}\frac{(e+1-j)T(m)+\sigma(m)}{p^j}.
\]
Thus \(B/p\le G<B/(p-1)\), where \(B=eT(m)+\sigma(m)\). The sole candidate is \(p=\lceil B/G\rceil\). The program tests the original integer equality and primality.

[classify.py](classify.py) uses two-adic pruning. For odd \(p\), \(v_2(T(p^e))=v_2((e+1)(e+2)/2)\), and \(v_2(\sigma(p^e))\ge v_2(e+1)\) (with equality when \(e\) is even). The first identity has a [published elementary proof](https://github.com/umaia1234/agentic-conjectures/blob/main/problems/oeis-a245211/DETAILS.md); the second follows by pairing or the factorization of an even-length geometric sum. The power-of-two factors of \(T(2^k)\) and \(\sigma(2^k)\) are both trivial. The equality forces \(v_2(T(n))\ge v_2(\tau(\text{odd part of }n))\), hence \(\sum_{p^e\parallel n,\ p\text{ odd}}v_2(e+2)\ge\#\{p:p\mid n,\ p\text{ odd}\}\). At a partially assigned tuple the program also compares the valuations of the two sides of \(\sigma(n)=2n\tau(n)-T(n)\). These are necessary conditions only.

[bisect_check.py](bisect_check.py) generates unordered multiplicative partitions separately for each divisor count and tries their distinct permutations. It computes reachability modulo 32 by direct sums over **every odd residue class**, without the valuation formula. It bounds the next prime by evaluating the full normalized expression with all remaining prime bases replaced by the same trial integer. The expression is strictly decreasing in that integer. A distinct increasing completion has normalized value no greater than this comparison. With just one prime left, the zero of the monotone difference is found by integer bisection. All final equalities are checked exactly.

Both programs include \(n=1\) from the empty factorization. Each checks that its returned set is precisely the indicated 512 powers of two.

| Certificate | Ordered exponent patterns | Prefixes visited | Final candidate or crossing tests |
|---|---:|---:|---:|
| Leading coefficient and valuations | 15,629 | 966,631 | 143,155 |
| Full polynomial and residues modulo 32 | 15,629 | 478,695 | 127,332 |

Run the following with Python 3.9 or later and assertions enabled.

```sh
python3 classify.py 512
python3 bisect_check.py 512
```

Dominic Aziz Dabish (DomTheDeveloper). The [earlier density proof](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1376) establishes uniqueness of a prime base at fixed exponent and cofactor. The [previous fixed-support result](../fixed-support/README.md) fixes the primes and varies their exponents. Here the primes vary, and the divisor-count cutoff covers all supports, both odd and even. The height argument is a written proof; the cutoff classification is computer-assisted.
