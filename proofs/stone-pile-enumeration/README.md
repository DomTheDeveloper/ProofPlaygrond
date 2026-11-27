# Counting unreachable stone-pile positions at every total

Start with $n\ge1$ one-stone piles. A move transfers a positive number of stones between two equal piles, discarding an empty pile. Piles are unordered. Let $U(n)$ count unreachable partitions and let $T(n)$ count unreachable partitions into distinct parts. Thus A292727 is $U(n)$ and A292728 is $Q(n)-T(n)$, where $Q(n)$ counts distinct-part partitions. [A292727](https://oeis.org/A292727) · [A292728](https://oeis.org/A292728)

At the smallest even total with a coprime obstruction involving at least three piles, **there are 461,560 such positions**. The count grows by an exact cubic when the set of odd prime divisors stays fixed. The formulas below also cover arbitrary totals.

## From reverse moves to a finite count

Write $S$ for the set of odd primes dividing $n$, $P=\prod_{p\in S}p$, $D=2P$, and call a position *primitive* if its parts have no common odd prime divisor. A common odd prime prevents reachability. Primitive positions containing an even part or a repeated part are reachable. For a primitive position of at least two distinct odd parts $x_i$, the first reverse move averages a pair. It can succeed precisely when some pair leaves untouched parts whose gcd with $P$ is one. For an empty set of untouched parts, take this gcd to be $P$.

To verify the criterion, splitting an even pile in two or averaging two distinct same-parity piles gives the inverse moves, both of which decrease the sum of squares. A split preserves primitivity and makes a repeat. Given an odd repeated part $a$ and another value $b$, average one $a$ with $b$ and keep a copy of $a$. An odd prime dividing every new part must also divide $b$, so primitivity is preserved. If all odd parts are equal, primitivity makes them all ones. Descent proves the assertion about repeated or even parts. For a first averaging move on distinct odd parts, a prime common to the result must divide $n$ and every untouched part, and any odd prime dividing all of these divides the average. The earlier proof formalizes this criterion and derives the first possible exceptional totals. [Reachability proof and Lean project](https://github.com/DomTheDeveloper/ProofPlaygrond/pull/126) · [Gregory Igusa's related 2005 game](https://people.brandeis.edu/~kleinboc/47a/pilesofstones.pdf)

For a primitive tuple and $p\in S$, a pair is obstructed by $p$ exactly when its two vertices are the only nonzero coordinates modulo $p$. Those two coordinates must then be opposite. Each prime can obstruct at most one pair. In an unreachable primitive tuple of $r\ge3$ piles, every pair needs a witness, so $\binom r2\le |S|$ and $r\equiv n\bmod2$.

Write $B(n)$ for either the ordinary partition count or $Q(n)$. With the same choice, let $U_B(n)$ be $U(n)$ or $T(n)$. Define $E_r(n)$ as the number of unreachable primitive positions with exactly $r\ge3$ piles. Then

$$
U_B(n)=
\sum_{\varnothing\ne J\subseteq S}(-1)^{|J|+1} B\left(\frac{n}{\prod_{p\in J}p}\right)
+\mathbf 1_{\{2\mid n,\;P>1\}}\,\frac{\varphi(n)}2
+\sum_{\substack{r\ge3,\ r\equiv n\ (2)\\ \binom r2\le |S|}}E_r(n).
$$

The first term is inclusion–exclusion after dividing out common primes. The second term counts primitive odd pairs at even totals with $P>1$, since each unit $a\bmod n$ gives $(a,n-a)$, counted twice. In this case $n\ge6$ and the two entries are distinct. Every position contributing to the third term has distinct parts and therefore contributes to both choices of $B$.

## A residue formula for every $E_r(n)$

Use ordered coordinates temporarily. Consider residues $1\le a_i<D$, all odd. At each $p\in S$ require that $\sum a_i=0\bmod p$ and that the vector is not identically zero modulo $p$. Require every pair to be witnessed by at least one $p$ in the sense above. These conditions depend only on the residues. They also imply that the residues are pairwise distinct. To distinguish $i$ and $j$, choose a third index $k$ and a prime witnessing $(i,k)$.

Let $\rho=P$ for odd $n$ and $\rho=0$ for even $n$, and put $h=(n-\rho)/D$. For the permitted parity $r\equiv n\bmod2$, let $b_t$ count such ordered tuples whose ordinary integer sum is $\rho+tD$, for $0\le t\le r-1$. All their sums have this form by the Chinese remainder theorem. Then

$$
\boxed{E_r(n)=\frac1{r!}\sum_{t=0}^{r-1}b_t\binom{h-t+r-1}{r-1}.}
$$

Indeed every lift is uniquely $x_i=a_i+Dk_i$ with $k_i\ge0$. The required sum amounts to $\sum k_i=h-t$. Stars and bars gives the binomial coefficient, using zero when $h<t$. Distinctness makes division by $r!$ exact. This is a finite formula in residue classes for arbitrary $n$. For fixed odd radical $P$ and parity, it is an exact polynomial in $h$ on the admissible totals.

There is a closed expression for its leading coefficient. With $b=\binom r2$,

$$
W_r=\sum_t b_t
=\sum_{j=0}^{b}(-1)^j\binom bj
\prod_{p\in S}\left(p^{r-1}-1-j(p-1)\right).
$$

At a prime $p$ there are $p^{r-1}-1$ nonzero vectors in the sum-zero hyperplane. Each forbidden witness pair removes $p-1$ vectors with exactly that support, and the removed sets of vectors for distinct pairs are disjoint. Apply inclusion–exclusion over the pairs that are missing, then combine the primes and the oddness condition by CRT. If $|S|\ge b$, choose a different prime for each pair and assign opposite nonzero values on it. At any spare prime choose any nonzero sum-zero vector. Hence $W_r>0$, and the polynomial has degree exactly $r-1$ and leading coefficient $W_r/(r!(r-1)!)$.

The polynomial, written in the total $n$, has only powers of the same parity as $r-1$. To see this, put $s=2\rho/D$. Complementing every residue sends the bin $t$ to $r-s-t$, preserving its count (extend by zero outside the displayed bins). Replacing $h$ by $-h-s$ in the binomial polynomial and using $\binom{-x}{k}=(-1)^k\binom{x+k-1}{k}$ thus multiplies the answer by $(-1)^{r-1}$. This corresponds to $n\mapsto-n$. In particular the four-pile polynomial for any fixed admissible radical is an odd cubic.

## Odd triples

For $r=3$, the complement $a_i\mapsto D-a_i$ interchanges $t=0$ with $t=2$. Thus $b_0=b_2$, and substitution yields

$$
E_3(P(2h+1))=E_3(P)+\frac{W_3}{6}\binom{h+1}{2}
$$

when $P$ has at least three odd prime divisors and $P(2h+1)$ has the same odd radical. For $P=105$, $W_3/6=48$. At $n=105$ the six triples are $(3,7,95)$, $(3,25,77)$, $(5,7,93)$, $(5,9,91)$, $(5,49,51)$ and $(7,33,65)$. Consequently, for every positive odd $u$ with prime factors in $\{3,5,7\}$ (including $u=1$),

$$
E_3(105u)=6u^2 .
$$

For example, 315 stones give 54 exceptional triples. Including the common-divisor positions gives 343,919,401 unreachable positions in total, of which 688,259 are terminal. The direct checker also tests the triple formula at radicals 165, 231 and 1155.

## Four piles at 510,510 and beyond

For even $n$, any primitive obstruction with at least three parts has at least four odd parts, hence requires at least six odd primes. The smallest possible total is $D=2\cdot3\cdot5\cdot7\cdot11\cdot13\cdot17=510510$. With exactly these six odd primes, a four-pile obstruction gives a bijection from the six primes to the edges of the complete graph on four vertices. There are $6!/4!=30$ inequivalent edge assignments because the vertex action is free. An automorphism fixing each individual edge fixes every vertex. Each prime $p$ admits $p-1$ endpoint values once an orientation is fixed. This gives $30\prod(p-1)=2,764,800$ unordered residue profiles.

Enumerating those profiles by CRT gives the bins below. A second enumeration verifies the first bin by counting pairs of actual positive pile sizes with complementary sums. The accompanying program implements both methods.

| Sum of least positive residues | $D$ | $2D$ | $3D$ |
| --- | ---: | ---: | ---: |
| Unordered profiles | 461,560 | 1,841,680 | 461,560 |

For the independent integer count, fix an edge assignment and a vertex $i$. Its possible size is an odd positive multiple of the product of its three nonincident primes, coprime to the product of its three incident primes. Conversely these conditions on the four sizes, together with their sum being a multiple of $D$, force opposite nonzero residues on each edge. Count the pairs of allowed sizes at the first two vertices by sum, then use the complementary sums at the remaining two vertices.

Inserting the histogram in the residue formula yields, for $h\ge1$ whose odd prime divisors all divide $255255$,

$$
\boxed{E_4(510510h)=2{,}764{,}800\binom{h+1}{3}+461{,}560h
=460{,}800h^3+760h.}
$$

At 510,510 stones the answer is **461,560**. At 1,021,020 stones it is **3,687,920**. For these totals every primitive obstruction with at least three parts has exactly four, since six odd primes cannot cover the edges on six vertices. The common-divisor and two-pile terms in the all-position formula are counted separately.

Run `python3 count.py` to reproduce the residue histogram, the independent four-pile integer counts and the triple checks. Run `python3 count.py 315` to compute both all-position counts for any chosen positive total in place of 315. The generic algorithm is finite but can grow rapidly with the number and sizes of the prime divisors.
