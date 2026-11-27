# Fixed points of OEIS A245211 on two-prime support

Write $a(n)=\sum_{d\mid n,\ d<n} d\,\tau(d)$ and $T(n)=a(n)+n\tau(n)$. A fixed point satisfies $T(n)=n(1+\tau(n))$. At $21$ the proper-divisor sum is $1+6+14=21$.

## Statements proved in Lean

1. For primes $p<q$, $p\le439$, and integers $e,b\ge1$, the equality $a(p^e q^b)=p^e q^b$ holds exactly when $p^e q^b=21$. The larger prime, exponents and integer have no size cutoff.
2. For any distinct primes $p,q$ and any $e\ge1$, the only fixed point of the form $p^e q$ is $21$. There are no fixed points of the form $p^e q^2$.
3. At a fixed point with exactly two prime factors, the positive exponents satisfy $e\le3b$ and $b\le3e$. For a fixed $b$, put $K=(3b+1)(b+1)$. Every such fixed point satisfies $n\le(K^2)^{K-1}$, so its equality set is effectively computable.
4. For every positive fixed point and **each** prime divisor $p$, $n\le p^{\tau(n)-1}\le p^{2p-3}$. For every coprime factorization $n=xy$ with $x,y>1$, one has $\tau(x)<\gcd(y,T(x))$.

The unrestricted fixed-point conjecture remains open. The Lean classification through 439 applies to numbers with exactly two distinct prime factors. Two separate exact programs extend the earlier all-support computation through 433 to every input with a prime divisor at most 439. [All-support certificate through 439](../least-prime-439/README.md)

## The two-prime arguments

Let $P=p^e$, $Q=q^b$, $A=a(P)$, $B=a(Q)$, $c=b+1$, and $g=P-cA$. Multiplicativity of $T$ gives $Qg=T(P)B$. Also $P\mid T(Q)$ and $Q\mid T(P)$ because $T(p^e)\equiv1\pmod p$ and $T(q^b)\equiv1\pmod q$. The distinct proper divisors $1$ and $n/p$ give $e(b+1)<p$. Interchanging the factors gives $b(e+1)<q$.

When $b=1$, $qg=T(P)$ and $(2q+1)g=(2e+3)P$. Since $P\mid 2q+1$, it follows that $g\mid 2e+3$. For $e\ge3$ the prime-power recurrence $a(p^{j+1})=a(p^j)+(j+1)p^j$ gives $g\ge1+2p^{e-2}>2e+3$. If $e=2$, the gap $p^2-4p-2$ divides 7, forcing $p=5$, where the gap is 3. For $e=1$, $p-2$ divides 5. Substitution in $q(p-2)=2p+1$ gives $(p,q)=(3,7)$ or $(7,3)$.

For arbitrary $b$ and $e\ge2$ put $G_j=p^j-c\,a(p^j)$. Its increment is $(p-1-c(j+1))p^j$. All increments through $G_e$ are nonnegative, and the increment at $j=e-2$ is at least $cp^{e-2}$. Thus $g\ge1+cp^{e-2}$. The prime-power recurrence gives $qB\le(b+1)Q$ since $b\le q$. Multiplying $Qg=T(P)B$ by $q$ gives $qg\le cT(P)$, while $A<P$ gives $T(P)<(e+2)P$. Consequently $q<(e+2)p^2\le p^3$. Now $P\mid T(Q)<(b+2)Q$, and $b+2\le p$. Therefore $p^e<p^{3b+1}$ and $e\le3b$. The case $e=1$ is immediate. The symmetric bound follows by interchanging the factors.

When $b\ge2$, the proper prime-power sum satisfies
$$
(q-1)B < bQ < qB.
$$
Together with $Qg=T(P)B$ this gives the unique integer candidate
$$
q=\left\lfloor \frac{bT(P)}{g}\right\rfloor+1.
$$
This is the earlier two-prime interval of umaia1234, expressed using integer division. Lean proves it from the divisor definition.

For $b=2$ the exponent bound gives $e\le6$. If $p\le q$, the inequalities $pA\le(e+1)P$, $pB\le3Q$, $T(P)<(e+2)P$, and $T(P)B+3QA=PQ$ imply $p\le3(2e+3)\le45$. For $p>q$ and $e\ge3$, the inequalities $P\mid T(Q)<4q^2$ and $p\ge3e+1$ contradict $P\ge p^3$. Equal exponents can be interchanged, and $e=1$ is covered above. A kernel-checked finite table tests the unique candidate in the remaining range.

For the through-439 theorem, the preceding cases leave $e,b\ge3$. The budget $e(b+1)<p$ bounds $e\le\lfloor(p-1)/4\rfloor$ and $b<\lfloor(p-1)/e\rfloor$. For every smaller prime through 439 and every exponent pair also satisfying the two ratio inequalities, the kernel evaluates the integer candidate $z$. In every case $z\le p$ or $z^b\nmid T(P)$. This contradicts either $p<q$ or the necessary divisibility. The finite Lean computation uses `decide +kernel`.

## Height on arbitrary support

For a proper coprime split $n=xy$, expanding $T(xy)$ gives
$$
T(x)a(y)+y\tau(y)a(x)=xy.
$$
In particular $\tau(x)a(y)<y$, while $y\mid T(x)a(y)$ forces $y\le\gcd(y,T(x))\,a(y)$. Therefore $\gcd(y,T(x))>\tau(x)$. The proper divisor $n/p$ also gives $\tau(n)\le2(p-1)$.

Start with the complete $p$-component $U=p^{v_p(n)}$. It satisfies $Up=p^{\tau(U)}$. As long as $U<n$, the gcd inequality supplies a prime $q$ in the complement dividing $T(U)$. The complement has at least two divisors, so $\tau(U)\le p-1$, and the reversed split gives $a(U)<U$. Hence $q\le T(U)<pU$. Adding the complete $q$-component preserves $Up\le p^{\tau(U)}$ by multiplicativity of the divisor count. This ends at $U=n$, giving the asserted height. Writing $D=\tau(n)$, each proper divisor is at most $n/\minFac(n)$ and has at most $D$ divisors. Summing gives $\minFac(n)\le D^2$ at a fixed point and $n\le(D^2)^{D-1}$. For $n=p^eq^b$ one has $D\le K$, as claimed above.

## Verification and sources

The file imports the canonical declaration at formal-conjectures commit `9097e2f90e66d2f6244209cb1c07f7120d17ec53`. The Lean project allows `propext`, `Classical.choice` and `Quot.sound`. Its parent reduction still has two open hypotheses. The special-case and height theorems have no such hypotheses.

[Immutable Lean proof](https://github.com/DomTheDeveloper/open-math-agents/blob/3c789e162ce0afbca110affd0f615e9ae0195c27/reductions/OeisA245211.conjecture.R3.lean) · [Pinned checker on the fork](https://github.com/DomTheDeveloper/open-math-agents/actions/runs/46064095662) · [Fork pull request](https://github.com/DomTheDeveloper/open-math-agents/pull/27)

Jaroslav Křížek posed the original conjecture. desenyon's first project reduction uses the multiplicative full divisor moment. Sugui's earlier work gives a cofactor divisor-count bound and formalized special cases. Section 7 of umaia1234's earlier calculation gives the unique prime candidate for each fixed exponent pair and reports a finite enumeration through exponent 200. The bounds and Lean theorems above record work by @DomTheDeveloper. Research priority is unestablished.

[OEIS A245211](https://oeis.org/A245211) · [First Left to Solve reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/733) · [Sugui’s formalization](https://github.com/google-deepmind/formal-conjectures/pull/8119) · [Earlier two-prime calculation, section 7](https://github.com/umaia1234/agentic-conjectures/blob/96ea0039d9dc3a1940b9d5ec1cbe616ed58d1da2/problems/oeis-a245211/DETAILS.md) · [Earlier all-support computation through 433](https://github.com/DomTheDeveloper/ProofPlaygrond/issues/121#issuecomment-7226782817)
