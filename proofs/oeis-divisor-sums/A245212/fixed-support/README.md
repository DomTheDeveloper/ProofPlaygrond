# Effective classification on a fixed prime support for A245212

Fix any finite set $S$ of primes. There is a terminating algorithm that determines **all** positive integers with prime support exactly $S$ for which $a(n)=\sigma(n)$ in [OEIS A245212](https://oeis.org/A245212). Its answer is a finite union of explicitly computed points and families $mp^e$ with $e\ge1$. This holds for supports of any size, including those containing 2, with no a priori bound on exponents.

A family on which an exponent can vary freely occurs precisely when $p\nmid m$ and

$$T(m)=(p-1)\sigma(m),\qquad 2m\tau(m)=p\sigma(m),$$

where $T(n)=\sum_{d\mid n}d\tau(d)$. These conditions imply $a(m)=\sigma(m)$. In particular, for any fixed support of four odd primes the solution set is finite and effectively computable, since no odd product of three distinct prime powers satisfies the equality. For the exact support $\{3,5,7,11\}$ two independent computations gave the empty set. All four exponents in that computation are unrestricted positive integers.

## Complete 11-smooth classification

For **every** positive integer $n$ whose prime divisors are at most 11,

$$a(n)=\sigma(n)\quad\Longleftrightarrow\quad n=2^e\text{ for some }e\ge0.$$

Both independent algorithms classified all 32 subsets of $\{2,3,5,7,11\}$. The rational search visited 350,181 nodes and the integer search 576,423. Both returned $n=1$ on the empty support, the entire prime-power family on support $\{2\}$, and no solutions on the other 30 supports. This includes all mixed even and odd inputs built from these primes, with arbitrarily large exponents. One further implication is that any counterexample to Krizek's conjecture must have a prime divisor at least 13.

```sh
python3 smooth_check.py rational
python3 smooth_check.py integer
```

The full per-support outputs are [smooth-rational.txt](smooth-rational.txt) and [smooth-integer.txt](smooth-integer.txt). A mismatch raises an exception. The two programs compute their mathematical bounds independently.

## Proof of termination and completeness

Write $n=\prod_{p\in S}p^{i_p-1}$, with $i_p\ge2$. Put $z_p(i)=(1-p^{-i})/i$ and $\alpha_p=1/(p-1)$. For $S=\varnothing$ the answer is $n=1$. Otherwise $T(n)+\sigma(n)=2n\tau(n)$ is equivalent, by multiplicativity and the prime-power geometric sums, to

$$\prod_{p\in S}(1-\alpha_p z_p(i_p))+\prod_{p\in S} z_p(i_p)=t,\qquad t=2\prod_{p\in S}(1-p^{-1}).$$

Indeed $T(p^{i-1})/(i p^{i-1})=p(1-\alpha_p z_p(i))/(p-1)$ and $\sigma(p^{i-1})/(i p^{i-1})=pz_p(i)/(p-1)$. The factors $1-\alpha_p z_p(i)$ are positive, including at $p=2$.

Enumerate the finitely many orders of the indices $i_p$. After a prefix has been fixed, let $B$ and $C$ be the products of its first and second kinds of factors. For a remaining set $R$ of size $k\ge2$, let $j$ be its least index. If $B>t$, then

$$ B-t\le B\left(1-\prod_{p\in R}(1-\alpha_p z_p)\right)\le B\sum_{p\in R}\alpha_p z_p\le\frac{B}{j}\sum_{p\in R}\alpha_p.$$

If $B\le t$, choose an $s\in R$ with largest $\alpha_s$. Then $B\alpha_s z_s\le B(1-\prod_{p\in R}(1-\alpha_p z_p))\le C\prod_{p\in R}z_p$. Cancellation of $z_s>0$ gives

$$j^{k-1}\le\frac{C}{B\max_{s\in R}\alpha_s}.$$

Both calculations provide a finite explicit upper bound for the next index, even when $B=t$. The recursive tree is finitely branching and has depth $|S|$.

At its last prime $p$ the equation becomes $B+(C-B\alpha_p)z_p(j)=t$. If the coefficient is nonzero, a positive required value determines at most one $j$, namely $\lfloor1/z_p(j)\rfloor$, because $j<j/(1-p^{-j})<j+1$ for $p,j\ge2$. The algorithm verifies the candidate exactly. Its reduced denominator must be divisible by $p^j$, providing an additional exact filter. If the coefficient vanishes, every index is allowed precisely when $B=t$. Returning the whole ray is valid because the terminal equation then holds for every $j\ge2$ regardless of the order used to find it. Sorting and taking unions handles ties and overlapping orders.

For $n=mp^e$ the two terminal identities follow directly from the prime-power formulas. The constant term after dividing by $p^e(e+1)$ in $T(m)T(p^e)+\sigma(m)\sigma(p^e)=2m\tau(m)p^e(e+1)$ is $pT(m)/(p-1)$. The coefficient of $z_p(e+1)$ is $[p/(p-1)](\sigma(m)-T(m)/(p-1))$. Equating the constant and setting the coefficient to zero gives exactly the identities at the start. The normalized sum varies strictly with $e$ (equivalently its reciprocal determines $e+1$), so two different exponents for a fixed cofactor already imply the full ray. Adding the identities gives $T(m)+\sigma(m)=2m\tau(m)$.

## Independent certificate

The integer algorithm bounds the two products directly. Write $W_p(e)=T(p^e)/(p^e(e+1))$ and $V_p(e)=\sigma(p^e)/(p^e(e+1))$. The first increases to $p/(p-1)$ and the second decreases to zero, by their reversed geometric sums. If $m$ is the product of the fixed prime powers and the remaining exponents are all at least $H$, these give lower and upper rational bounds for the left side of $\prod W+\prod V=2$. A bound that excludes 2 eliminates the whole tail. Doubling $H$ eventually succeeds whenever $L=[T(m)/(m\tau(m))]\prod_{p\in R}p/(p-1)$ differs from 2.

If $L=2$ and at least two primes remain, put $K=[\sigma(m)/(m\tau(m))]\prod_{p\in R}p/(p-1)$. For a remaining prime $s$, the moment product is at most $2(1-z_s/(s-1))$, and the divisor-sum product is at most $K z_s/(H+1)^{|R|-1}$, with $z_s=z_s(e_s+1)>0$. Their sum is strictly below 2 as soon as $K(s-1)<2(H+1)^{|R|-1}$. This covers the remaining possible tail limit.

For the final prime $p$ the program uses the necessary divisibility $p^e\mid T(m)-(p-1)\sigma(m)$, obtained by multiplying the original equation by $(p-1)^2$ and reducing modulo $p^e$. A nonzero difference bounds $e$ by its $p$-adic valuation. A zero difference reduces to the exact ray criterion above. The program tests surviving exponents against the original integer equation.

For $\{3,5,7,11\}$ the rational program examined 34,370 terminal ordered prefixes. The interval program examined 53,054 and made 26 final direct integer evaluations. Both gave zero solutions. The inputs and outputs can be reproduced with stock Python 3.9 or later.

```sh
python3 fixed_support.py 3 5 7 11
python3 integer_certificate.py 3 5 7 11
```

## Sources and scope

Jaroslav Krizek proposed the full conjecture in 2014. The prime-power moments and an ordered three-prime search appeared in [Dominic Aziz Dabish's earlier three-prime certificate](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1048). The [exponent-two argument at 3](https://github.com/DomTheDeveloper/ProofPlaygrond/tree/9644e2a2d2d46353a6531f88f3d67bdc4f65fd50/proofs/oeis-divisor-sums/A245212/three-squared) treated a fixed factor 9. Here the recursion works for an arbitrary finite support and detects infinite rays algebraically. The finite examples are computer-assisted partial results by Dominic Aziz Dabish (DomTheDeveloper). Global research priority is undetermined.
