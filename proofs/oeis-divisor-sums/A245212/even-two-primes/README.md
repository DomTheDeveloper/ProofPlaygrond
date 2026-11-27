# Which even and odd integers can satisfy the A245212 equality?

Dominic A. Dabish (DomTheDeveloper), 26 November 2026.

Write $\tau(n)$ and $\sigma(n)$ for the number and sum of the positive divisors. Put $T(n)=\sum_{d\mid n}d\tau(d)$ and $a(n)=2n\tau(n)-T(n)$. The conjecture on [Jaroslav Krizek's OEIS A245212](https://oeis.org/A245212) asks whether the positive solutions of $a(n)=\sigma(n)$ are precisely the powers of two, including 1. We establish the following partial results.

1. For every fixed $k\ge1$, the set of solutions $n=2^kp^a q^b$ with distinct odd primes $p<q$ and $a,b\ge1$ is finite and effectively computable. **For every $1\le k\le11$ the set is empty.** The primes and the odd exponents are unrestricted.
2. Suppose $n=2^km$ is a solution with $m>1$ odd. Set $D=\tau(m)$ and $x=k+1$. Then
   $$2^x<2D^2(2xD^2)^{D-1},\qquad x<2D(1+3\log_2 D).$$
   For every fixed $D\ge2$ there are consequently only finitely many such $n$, all effectively computable.
3. **Among all positive integers whose odd part has at most 32 divisors, precisely the powers of two are solutions.** Both the size of the integer and the exponent of two are unrestricted.

The proofs of finiteness are analytical. Two independent exact searches establish each numerical classification. An additional Lean kernel certificate checks the finite arithmetic for the entire $k=1$ case of part 1. The universal A245212 conjecture remains open.

## A prescribed power of two and two variable odd primes

The functions $T$, $\sigma$ and $n\tau(n)$ are multiplicative. For $i=e+1\ge2$, define
$$F_p=\frac p{p-1},\quad z_p(i)=\frac{1-p^{-i}}i,\quad
W_p(i)=\frac{T(p^e)}{i p^e}=F_p\left(1-\frac{z_p(i)}{p-1}\right),\quad
V_p(i)=\frac{\sigma(p^e)}{i p^e}=F_pz_p(i).$$
These identities follow by summing two finite geometric series. The sequence $z_p(i)$ strictly decreases to zero, since it equals $(1-p^{-1})$ times the mean of $1,p^{-1},\ldots,p^{1-i}$. Consequently $W_p(i)$ increases to $F_p$.

Let $H=2^{k+1}$, $w=(H-1)/(kH+1)$ and $t=1+w$. In particular $T(2^k)=kH+1$, $\sigma(2^k)=H-1$ and $2\cdot2^k\tau(2^k)=tT(2^k)$. The equality becomes
$$W_p(i)W_q(j)+wV_p(i)V_q(j)=t,\qquad i=a+1,\ j=b+1.$$
A necessary condition is $F_p^2(1+w/4)>t$, giving a finite list of smaller primes. Also $F_p\ne t$, since $1/w=k+(k+1)/(H-1)$ lies strictly between $k$ and $k+1$.

If $F_p>t$, the inequality $W_p(i)<t$ bounds $i$ effectively. If $F_p<t$, choose $I\ge2$ so that $U=F_p(1+w/(2I))<t$. For $i\ge I$ the left side is at most $UF_q$, hence $q\le t/(t-U)$. This leaves two types of searches, one with $p,i$ fixed and one with $p,q$ fixed.

**Fixed $p,i$.** Put $b=2^kp^{i-1}$, $T=T(b)$, $S=\sigma(b)$ and $c=2b\tau(b)$. Write $e=j-1$. Multiplying $T\,T(q^e)+S\sigma(q^e)=cj q^e$ by $(q-1)^2$ and reducing modulo $q^e$ gives
$$q^e\mid T-(q-1)S.$$
Indeed $(q-1)^2T(q^e)=1+((q-1)j-1)q^{e+1}$. If the difference vanishes, the identity $(q-1)T(q^e)+\sigma(q^e)=j q^{e+1}$ would force $c=qS=T+S$. This makes $b$ a solution, already excluded by the [one-odd-prime theorem](https://github.com/DomTheDeveloper/ProofPlaygrond/blob/0d4f34b5e72421de27457f886fbdd8ef018870d0/proofs/oeis-divisor-sums/A245212/A245212-Prime-Powers-and-Density.pdf). Thus $q^{j-2}\le T+S$, an effective bound on $j$ even when $q$ is unknown.

For every admissible $j$, put $G=j(c-T)-S$ and $L=(j-1)T+S$. Expansion in $1/q$ shows that $G$ is a sum with first term $L/q$ and subsequent coefficients positive and at most $L$. Hence $L/q\le G<L/(q-1)$, $G>0$ and the only possible integer $q$ is $\lceil L/G\rceil$. Test this candidate in the original identity. The same argument applies to the last prime of an arbitrary coprime prefix.

**Fixed $p,q$.** Order the two exponent indices so that $i\le j$, considering each assignment of the primes. Set $\alpha=1/(p-1)$, $\beta=1/(q-1)$, $\delta=1-t/(F_pF_q)$, $u=z_p(i)$, $v=z_q(j)$. Then
$$\delta=\alpha u+\beta v-(\alpha\beta+w)uv.$$
When $\delta>0$ we have $i<(\alpha+\beta)/\delta$. When $\delta\le0$, divide by $uv$ and use $u,v<1/i$ to get $i<(\alpha\beta+w)/(\alpha+\beta)$. For each $i$ the equation is linear in $v$. If both coefficients vanish every $j$ works, contradicting the preceding divisibility argument and the one-odd-prime theorem. A positive solution $v$ determines $j=\lfloor1/v\rfloor$, since $j<j/(1-q^{-j})<j+1$. Direct substitution finishes the algorithm.

The first checker implements these bounds. The second uses a doubling search to exclude the region $i\ge L$, $q\ge Q=\max(L,p+1)$. This region is excluded once $W_p(L)\ge t$ or $F_pF_Q(1+w/(2L))\le t$. One of these tests eventually succeeds since $F_p\ne t$. For a fixed pair, it doubles a lower cutoff on both indices until the product bounds exclude the tail. When $F_pF_q=t$, division of the displayed equation by $uv$ excludes the tail once $L(\alpha+\beta)>\alpha\beta+w$. Below the cutoff it computes the valuation of $T-(q-1)S$ exactly. For the remaining unbounded-prime rows it finds zeros by integer bisection in $q$, using the original normalized expression, which decreases as $q$ increases. Both programs give empty lists for all eleven layers.

**An additional kernel check for $k=1$.** Here $w=3/5$, $t=8/5$. At fixed indices the normalized expression is decreasing in both primes, by its positive-coefficient expansion in their reciprocals. For $(p,q)=(5,7)$ and $(3,17)$ the bound $W_pW_q+wV_pV_q\le F_pF_q$ holds for all indices. To see this, bound the bilinear expression $(1-\alpha u)(1-\beta v)+wuv$ at the four corners of $[0,1/2]^2$. Only $(1/2,1/2)$ needs a calculation, where $(1-\alpha/2)(1-\beta/2)+w/4\le1$ for either pair. Since $35/24<8/5$ and $51/32<8/5$, the only remaining pairs are $(3,5),(3,7),(3,11),(3,13)$. The positive-$\delta$ bound gives $i\le37$ for the smaller exponent index in each pair. For each orientation and $1\le i-1\le36$, the Lean file checks $0<|T-(q-1)S|<3^{100}$. Thus the last exponent is at most 99. It checks the remaining exponents outright, stopping at the first failure of the necessary divisibility condition. The theorem uses ordinary kernel reduction and its axiom list is empty.

## Bounding the power of two from the odd part

Take $k\ge0$, $m>1$ odd, $D=\tau(m)$, $H=2^{k+1}$ and $C=2(k+1)D^2$. Separating the factor at two gives
$$HL_m=T(m)-\sigma(m)>0,\qquad L_m=(k+1)mD-kT(m)-\sigma(m).$$
For a prefix $b$ of the odd prime powers in increasing prime order, write $M=m/b$, $d=\tau(b)$, $h=\tau(M)=D/d$. Define the integer $L_b=(k+1)bD-kT(b)h-\sigma(b)$. Multiplicativity gives
$$L_b=kT(b)\big(T(M)/M-h\big)+\sigma(b)\big(\sigma(M)/M-1\big)+\frac{T(m)-\sigma(m)}{MH}.$$
This is positive. If $M>1$ and $p$ is its smallest prime, every proper divisor of $M$ is at most $M/p$. Consequently $T(M)/M-h\le h(h-1)/p$ and $\sigma(M)/M-1\le(h-1)/p$. Using $T(b)\le bd^2$, $\sigma(b)\le bd$ and $T(m)\le mD^2$, we get
$$1\le L_b\le (k+1)bD^2/p+bD^2/H.$$
While $2bD^2\le H$ the next prime satisfies $p\le Cb$. Appending $p^e$ then gives $Cbp^e\le(Cb)^{e+1}$. Starting at $b=1$, every prefix up to and including the first one crossing $2bD^2>H$ therefore satisfies $b\le C^{d-1}$. Such a crossing must occur, since $H\le T(m)-\sigma(m)<mD^2$. At the crossing we obtain $H<2D^2C^{D-1}$, as claimed. More generally, if a given prefix $b$ can be completed with remaining divisor count $h$, then
$$HC<2D^2(Cb)^h.$$
If a crossing already occurred before $b$, the inequality holds directly. Otherwise iterate the same argument from $b$ to the first crossing. This provides the stronger pruning test used in both programs.

Now put $x=k+1$. Since $2^x<C^D$, writing $s=x/D$ gives $s<1+\log_2 s+3\log_2 D$. If $s\ge4$ use $\log_2 s\le s/2$. If $s<4$ the desired bound already follows from $D\ge2$. This proves the second inequality. Combining it with the earlier height bound $n<(8\omega(n))^{2\tau(n)}$, and using $\omega(n)\le1+\log_2D$, gives an explicit bound in $D$ alone,
$$n<\big[8(1+\log_2D)\big]^{4D^2(1+3\log_2D)}.$$
In particular each fixed $D\ge2$ has an effectively computable finite set of solutions. [Earlier height bound and classification by total divisor count](../divisor-count/README.md)

## Exhausting the cases with at most 32 odd divisors

For each $2\le D\le32$ enumerate the factorizations $D=\prod i_l$, $i_l=e_l+1\ge2$, for odd primes in increasing order. The first program enumerates all ordered factorizations. Its upper bound on $x$ can be found by stopping at the first failure of the exponential inequality for $x\ge2D$. From that point $2^x/x^{D-1}$ strictly increases, because $(1+1/x)^{D-1}<2$ by the binomial theorem and comparison with a geometric series. The second program uses the larger integer upper bound $2D(1+3\lceil\log_2D\rceil)$, including $k=0$.

With the power of two and some odd prime powers fixed in a prefix $b$, let $h$ be the product of the remaining indices and $r$ their number. Write $A=hT(b)+\sigma(b)$, $B=2b\tau(b)h$. The positive geometric polynomials for the normalized local factors imply
$$A<B<A(p/(p-1))^r$$
for any solution whose next prime is $p$. This bounds the next prime by integer bisection. The first program tests the one remaining prime by the formula $\lceil L/G\rceil$ above. It uses the published one-odd-prime and exponent obstructions and one direct parity test. In the latter, all odd exponents are even and one is $2\bmod4$, making $\sigma(n)$ odd and $T(n)$ even. For the earlier exponent obstruction, $v_2(\sigma(p^e))\ge v_2(e+1)$ at odd $p$. Thus $2^{v_2(D)}$ divides both $\sigma(n)$ and $2n\tau(n)$, so it divides $T(n)$. Since $T(2^k)$ is odd and $v_2(T(p^e))=v_2(e+1)+v_2(e+2)-1$, it follows that $\sum_{p^e\parallel m}v_2(e+2)\ge\omega(m)$. This works also at $k=0$. [Earlier valuation argument and sources](../divisor-count/README.md) · [Signed identity](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1376)

The second program generates unordered multiplicative partitions and permutes them, includes the one-prime cases, and computes possible triples $(n\tau(n),T(n),\sigma(n))$ modulo 32 from the defining sums over every odd residue. It bounds the next prime by substituting a common trial base in all remaining factors. After normalization these are positive-coefficient polynomials in the reciprocals and decrease as the trial base increases, so the largest trial base with nonnegative score is an upper bound on the smallest remaining prime. At the last prime the only possible equality is at that final base. It also uses $p>k/2$ for each odd prime factor, which follows by setting $U=T(m)-mD$. The signed identity gives $mD-\sigma(m)>kU$, and the terms in $U$ include $(m/p)D e/(e+1)\ge mD/(2p)$ when $p^e\parallel m$. Both programs return empty lists at each $2\le D\le32$. For $D=1$, $m=1$ and $T(2^k)+\sigma(2^k)=2^{k+1}(k+1)$ proves equality for every $k$.

## Reproduction

Use Python 3.10 or later with its standard library. The reported Lean version is 4.33.1. Each Python run prints one row per input and asserts that the solution list for that row is empty. The four programs use integer or rational arithmetic throughout.

```sh
python3 -I classify.py 1 11
python3 -I crosscheck.py 1 11
python3 -I odd_divisors.py 32
python3 -I odd_divisors_check.py 32
lean V2One.lean
```

Krizek posed the original conjecture. The one-odd-prime exclusion, the signed even-case identity, and the height bound in terms of the total divisor count are earlier work. The present classifications allow the prime support to vary. The proof for a prescribed $k$ also lets both odd exponents vary, and the 32-divisor result lets $k$ vary. [OEIS](https://oeis.org/A245212) · [Earlier project work](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1048) · [Research index](https://github.com/DomTheDeveloper/ProofPlaygrond/issues/121)
