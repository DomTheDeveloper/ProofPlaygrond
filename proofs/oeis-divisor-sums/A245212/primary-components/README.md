# Two bounded prime-power factors for odd A245212 equalities

For a positive integer \(n\), put \(T(n)=\sum_{d\mid n}d\tau(d)\) and \(a(n)=2n\tau(n)-T(n)\). Jaroslav Krizek asked whether \(a(n)=\sigma(n)\) holds exactly at powers of two. A primary component means the entire factor \(p^e\) with \(p^e\parallel n\). [OEIS A245212](https://oeis.org/A245212)

**Theorem.** For each \(r\ge2\) there is a computable \(C(r)\) such that every odd equality input with exactly \(r\) distinct prime divisors has two primary components, at distinct primes, each at most \(C(r)\). The primes and exponents may all vary.

More generally one can produce two finite lists for each \(r\). Every such equality input is either on the first list or has a proper unitary divisor \(m\) on the second. Every \(m\) on the second list has at least two distinct prime divisors and satisfies
\[
 T(m)\prod_{s\in S}s=2m\tau(m)\prod_{s\in S}(s-1)
\]
for some set \(S\) of at most \(r-\omega(m)\) odd primes coprime to \(m\). In particular \(m\mid T(m)\). The finite lists in this general algorithm may be extremely large.

## A rational separation argument

Fix a product \(m\) of already selected primary components, possibly \(m=1\), and let \(k=r-\omega(m)>0\). Put \(A=T(m)/(m\tau(m))\) and \(C=\sigma(m)/(m\tau(m))\). Consider the rational numbers
\[
 A\prod_{s\in S}\frac{s}{s-1},
\]
for all sets \(S\) of at most \(k\) odd primes outside \(m\), including the empty set. This set of real numbers is compact. Along any sequence pass to a subsequence of constant cardinality and list each set in increasing order. Each of the finitely many coordinates can successively be made constant or tending to infinity. The constant coordinates remain distinct odd primes outside \(m\), and all other factors tend to 1.

Whether the set contains 2 is decidable. At a partial product \(x<2\) with \(j>0\) places left, the next prime \(p\) must satisfy \(x(p/(p-1))^j\ge2\) to reach 2. This gives a finite increasing-prime search. At \(x=2\) return the witness, and at \(x>2\) stop that branch. The search includes the empty product.

Suppose 2 is absent. Then the distance from 2 to the compact set is positive. For each integer \(Q\ge3\) compute \(d_Q\), the minimum distance using just primes at most \(Q\). Try successive \(Q\) until
\[
 Qd_Q>A k(3/2)^{k-1}+C(3/2)^k.
\]
This terminates because every \(d_Q\) is at least the positive distance just proved. It uses only finite rational arithmetic.

Let
\[
 B(m,k)=\max\!\left\{Q^Q,(8r)^{\,2\tau(m)Q^k}\right\}.
\]
We claim every equality extension has a remaining primary component at most \(B(m,k)\). Suppose all were larger. If every remaining exponent were less than \(Q\), then \(\tau(n)\le\tau(m)Q^k\), contradicting the published height bound \(n<(8r)^{2\tau(n)}\). Hence at least one remaining exponent is at least \(Q\). [Height proof](../divisor-count/README.md)

For a remaining prime \(p\) with exponent \(e\), put \(i=e+1\), \(z=(1-p^{-i})/i\). The geometric sums give the normalized factors
\[
 W=\frac{T(p^e)}{p^e i}=\frac{p}{p-1}\left(1-\frac{z}{p-1}\right),\qquad
 V=\frac{\sigma(p^e)}{p^e i}=\frac{p}{p-1}z.
\]
They satisfy \(1\le W\le3/2\), \(0<V\le(3/2)/(e+1)\), and equality for \(n\) says \(2=A\prod W+C\prod V\).

If \(p>Q\), then \(|W-1|\le1/Q\). If \(p\le Q\), the assumed \(p^e>Q^Q\) gives \(e>Q\) and \(|W-p/(p-1)|<1/Q\). Let \(L\) be the product of \(p/(p-1)\) over the remaining primes at most \(Q\). Telescoping the products bounds \(|\prod W-L|\le k(3/2)^{k-1}/Q\). The exponent at least \(Q\) gives \(\prod V\le(3/2)^k/Q\). Thus \(|2-AL|<d_Q\), contradicting the definition of \(d_Q\).

At \(m=1\) the target 2 is absent because every product of odd primes has odd numerator before cancellation. At \(m=p^e\) it is absent because \(T(p^e)\equiv1\pmod p\) and all primes in \(S\) differ from \(p\), whereas \(2m\tau(m)\prod(s-1)\) is divisible by \(p\). Starting with \(m=1\) therefore bounds one component. There are finitely many choices for it, and the preceding argument at each of these choices bounds a second component. The maximum of these computable bounds proves the theorem.

For the finite-list version, continue along every bounded component whenever 2 is absent. When \(k=0\), test \(m\) for equality and put successes on the first list. When \(k>0\) and 2 occurs, put \(m\) and its witness \(S\) on the second. Each extension uses a new prime and the depth is at most \(r\). Since \(S\) is coprime to \(m\), the displayed identity implies \(m\mid T(m)\). This proves the stated alternative without assuming the lists are empty.

## A sharp four-prime constant

For a set of at most four distinct odd primes, the smallest value of \(F=\prod p/(p-1)\) strictly above 2 is \(12801/6400\), attained at \(\{3,5,17,251\}\).

The Python certificate enumerates the first prefixes that cross 2 in increasing-prime order. If a partial product \(x<2\) has \(j\) places left, a next base \(p\) with \(x(p/(p-1))^j\le2\) rules out this and every larger continuation. Each crossing prefix is valid on its own and all its strict extensions have larger product. The search finds 79 crossing prefixes and checks the unique minimizer.

Here is an independent finite reduction for four primes. The least prime must be 3, since \((5/4)(7/6)(11/10)(13/12)<2\). The second must be 5 or 7, since \((3/2)(11/10)(13/12)(17/16)<2\). If it is 5, the third is at most 31 by \((3/2)(5/4)(33/32)^2<2\). If it is 7, the third is at most 13 by \((3/2)(7/6)(17/16)^2<2\). For a triple of ratio \(u/v<2\), its fourth prime \(s\) must satisfy \(s\le\lfloor(2v-1)/(2v-u)\rfloor\). The Lean table verifies that all these bounds are at most 256 and checks every eligible prime. Trial division by 2 through 16 suffices in this range. Triples already above 2 are checked directly, their extensions raise the ratio, and sets of at most two cannot cross 2. The attaining product is checked separately.

For an odd A245212 equality with exactly four distinct prime factors, the previous totient bound gives \(F=n/\varphi(n)>2\). Thus \(1-2/F\ge1/12801\). The normalized product identity above gives
\[
 1-\frac{2}{F}
 =1-\prod_{p^e\parallel n}\left(1-\frac{z_p}{p-1}\right)-\prod_{p^e\parallel n}z_p
 <\sum_{p^e\parallel n}\frac1{(p-1)(e+1)}.
\]
One of its four primary components therefore satisfies \((p-1)(e+1)<51\,204\). The sharpness claim concerns the ratio \(F\); its attaining support need not contain an equality input. [Earlier totient bound](../totient-gap.md)

Run with Python 3.9 or later and Lean 4.33.1.

~~~sh
python3 -I odd_support.py
lean SharpGap.lean
~~~

Lean's kernel checks the finite arithmetic table and attainment with no axioms. The coverage of the table, the formula for \(C(r)\), and the application to A245212 have written proofs above.

Dominic Aziz Dabish (DomTheDeveloper). The use of compactness in finiteness questions for multiplicative arithmetic functions has classical precedents. Paul Pollack gives a compactness proof of Dickson's finiteness theorem for odd perfect numbers. The equality treated here uses a different divisor sum. [Pollack, *Finiteness theorems for perfect numbers and their kin*](https://www.pollack-math.net/dickson-fixed.pdf)
