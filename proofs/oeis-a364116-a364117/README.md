# Prime-power congruences for two diagonals of Bala’s Legendre array

Dominic A. Dabish, with AI assistance, 27 November 2026.

Peter Bala posed three congruences for the first subdiagonal A364117 and two pairs of congruences for the main diagonal A364116 in July 2023. We prove all three for A364117. For A364116 the first assertion has a counterexample at 3. We prove its corrected range and all the other listed congruences, including both prime-power assertions. The proof uses two congruences for entire rows of the underlying array. All coefficients and congruences below concern integers unless a localization is specified. [A364117](https://oeis.org/A364117) · [A364116](https://oeis.org/A364116) · [A364113](https://oeis.org/A364113)

Write

$$T(R,n)=[x^n]\frac{1}{1-x}P_n\!\left(\frac{1+x}{1-x}\right)^R,\qquad a(n)=T(n+1,n),\qquad b(n)=T(n,n).$$

Here $P_n$ is the Legendre polynomial with $P_n(1)=1$. Thus $a$ is A364117 and $b$ is A364116.

## The results for the two sequences

| Sequence | Indices and hypotheses | Conclusion |
| --- | --- | --- |
| A364117 | Prime $p\ge5$ | $a(p)\equiv 2p+3\pmod{p^3}$ |
| A364117 | Odd prime $p$, $k\ge1$ | $a(p^k-1)\equiv1\pmod{p^{k+3}}$, including $a(p-1)\equiv1\pmod{p^4}$ |
| A364116 | Prime $p\ge5$, $k\ge1$ | $b(p^k)\equiv2p^k+1\pmod{p^{k+3}}$, including $b(p)\equiv2p+1\pmod{p^4}$ |
| A364116 | Prime $p\ge5$, $k\ge1$ | $b((p-1)p^{k-1})\equiv1\pmod{p^{k+2}}$, including $b(p-1)\equiv1\pmod{p^3}$ |
| A364116 | $p=3$ | $b(3)=5623\equiv34\pmod{81}$. The proposed residue is $7$. |

We will prove the following row statements for every integer $R\ge1$.

1. If $p\ge5$ is prime and $m\ge1$, then $T(R,pm)\equiv T(R,m)\pmod{p^{3+v_p(R)}}$.
2. For any odd prime $p$ and $k\ge1$, put $N=p^k$. If $p\ge5$ or $p\mid R$, then $T(R,N-1)\equiv1\pmod{p^{3+v_p(R)}}$. If $p=3$ and $3\nmid R$, then $T(R,N-1)\equiv19\pmod{27}$.

The first statement supplies a uniform modulus at every dilation for a fixed row. A companion proof establishes the full $p^{3r}$ congruences for both fixed-row dilations in A364113. [Proof of both row congruences](Towers.md)

## 1. Two coefficient formulas

Put $H_n(x)=\sum_{j=0}^n\binom nj^2 x^j$ and $y=x/(1-x)$. Two standard finite expansions of the Legendre polynomial give

$$P_n\!\left(\frac{1+x}{1-x}\right)=\frac{H_n(x)}{(1-x)^n},\qquad P_n(1+2y)=\sum_{j=0}^n\binom nj\binom{n+j}{j}y^j.$$

These follow by setting both Jacobi parameters to zero in the finite binomial and hypergeometric representations. [NIST DLMF, equations 18.5.7 and 18.5.8](https://dlmf.nist.gov/18.5#E7)

In the first representation the weight on a term $x^i$ of $H_n^R$ is $D_n(n-i)$, where $D_n(h)=\binom{nR+h}{h}$. In the second representation the linear functional $F_n$ given by $F_n(y^j)=\binom nj$ (zero for $j>n$) computes $T(R,n)=F_n(P_n(1+2y)^R)$. Indeed $[x^n](1-x)^{-1}y^j=\binom nj$.

## 2. Dilation for every row and every multiplier

Fix $p\ge5$. Work in $\mathbb Z_{(p)}$, where every integer prime to $p$ has an inverse. For each block $B=\{pt+1,\ldots,pt+p-1\}$ with $t\ge0$,

$$\sum_{i\in B}i^{-1}\equiv0\pmod{p^2},\qquad \sum_{i<j\in B}(ij)^{-1}\equiv0\pmod p.$$

To see this, $\sum_{s=1}^{p-1}s^{-2}\equiv0\pmod p$, since inversion permutes the nonzero residues and $\sum s^2=p(p-1)(2p-1)/6$. Pairing $s$ with $p-s$ gives $2\sum 1/s\equiv-p\sum 1/s^2\pmod{p^2}$. Expanding $1/(pt+s)$ to first order proves the first block identity. Squaring the sum and subtracting the sum of squares proves the second. Consequently for every nonzero integer $c$,

$$\prod_{i\in B}(1+pc/i)\equiv1\pmod {p^{3+v_p(c)}}.$$

The linear, quadratic, and higher terms have the required valuation separately. For $c=0$ the product equals one.

Write $v=v_p(R)$. Removing multiples of $p$ from the product for $D_{pm}(ph)$ and using whole blocks with $c=mR$ gives $D_{pm}(ph)\equiv D_m(h)\pmod{p^{3+v}}$. With a partial final block, $D_{pm}(ph+t)\equiv D_m(h)\pmod p$ for $0\le t<p$. Likewise,

$$\binom{pm}{pj}=\binom mj\prod_{\substack{1\le i\le pj\\p\nmid i}}(1+p(m-j)/i)\equiv\binom mj\pmod {p^3}.$$

Set $H_{pm}(x)=B(x)+p^2 E(x)$, where $B(x)=H_m(x^p)$. The coefficients of $E$ at multiples of $p$ are zero modulo $p$ by the last congruence. For $0\le b<m$ and $1\le s<p$ its other coefficients satisfy

$$[x^{pb+s}]E\equiv m^2\binom{m-1}{b}^2s^{-2}\pmod p.$$

Indeed $\binom{pm}{pb+s}/p=\frac{m}{pb+s}\binom{pm-1}{pb+s-1}$, and the last binomial is $\binom{m-1}{b}(-1)^{s-1}$ modulo $p$ by expanding $(1+x)^{pm-1}\equiv(1+x^p)^{m-1}(1+x)^{p-1}$. This also proves the asserted integrality of $E$.

Modulo $p^{3+v}$ the expansion of $H_{pm}^R$ reduces to $B^R+Rp^2B^{R-1}E$. For $2\le l\le R$ use $v_p\binom Rl\ge v-v_p(l)$ and $2l-v_p(l)\ge3$. The contribution of $B^R$ after applying the weights $D_{pm}$ is $T(R,m)$ by the whole-block congruence. For a monomial $x^{ph}$ in $B^{R-1}$, all $s=1,\ldots,p-1$ contribute for a given $b$ exactly when $h+b<m$. Their weights reduce modulo $p$ to the same number $D_m(m-h-b-1)$ because the complementary degree is $p(m-h-b-1)+p-s$. The block therefore contributes a multiple of $\sum s^{-2}=0$ in $\mathbb F_p$. This proves row statement 1.

## 3. The shifted prime-power index, including the prime 3

Let $p$ be odd, $N=p^k$, $n=N-1$, and $z_j=N/j$ for $1\le j<N$. Every $z_j$ lies in $p\mathbb Z_{(p)}$. Put $F=F_{N-1}$ and $X=P_{N-1}(1+2y)-1$. Factoring the two binomials in its coefficient yields the exact identity

$$c_j=[y^j]X=(-1)^j z_j(1-z_j)\prod_{i<j}(1-z_i^2),\qquad \binom{N-1}{j}=(-1)^j\prod_{i\le j}(1-z_i).$$

In particular $v_p(c_j)=k-v_p(j)$. Modulo $p^3$ we can expand the normalized row value as

$$\frac{T(R,N-1)-1}{R}\equiv F(X)+\frac{R-1}{2}F(X^2).\tag{1}$$

For justification, the term with $l$ factors in the normalized binomial expansion has valuation at least $l-v_p(l)$ because $\binom Rl/R=\binom{R-1}{l-1}/l$. This is at least 3 for $l\ge3$, with the sole exception $p=l=3$. In that case a product of three coefficients of valuation one would have all three indices positive multiples of $3^{k-1}$, so its degree would be at least $N$ and $F$ would kill it. Every surviving cubic product has valuation at least four, sufficient even after division by 3. This also establishes that the normalized expression belongs to $\mathbb Z_{(p)}$.

Use the sums $S=\sum_{j<N}z_j$, $Q=\sum_{j<N}z_j^2$, and $A=\sum_{1\le i<j<N}z_i z_j$, with the single sums starting at 1. Multiplying the two product formulas to second order gives

$$F(X)\equiv S-2Q-A\pmod {p^3}.$$

For $F(X^2)$ only the linear term of each $c_j$ matters and the signs cancel against the sign in $\binom{N-1}{i+j}$. Thus

$$F(X^2)\equiv\sum_{i,j\ge1,\ i+j<N}z_i z_j=2A\pmod {p^3}.$$

The middle equality is exact over $\mathbb Q$. Group by $t=i+j$ and use $1/(i(t-i))=(1/i+1/(t-i))/t$.

Pairing $j$ with $N-j$ gives $z_{N-j}=-z_j/(1-z_j)\equiv-z_j-z_j^2\pmod{p^3}$, so $2S\equiv-Q$. In particular $S\in p^2\mathbb Z_{(p)}$, and $2A=S^2-Q\equiv-Q\pmod{p^3}$. Substituting in (1) gives

$$\frac{T(R,N-1)-1}{R}\equiv-\frac{R+3}{2}Q\pmod {p^3}.\tag{2}$$

Only $j=t p^{k-1}$ with $1\le t<p$ can contribute to $Q$ modulo $p^3$. Thus $Q\equiv p^2\sum_{t=1}^{p-1}t^{-2}$. For $p\ge5$ this vanishes. For $p=3$ it is $-9$ modulo 27. If $3\mid R$, the extra factor $R+3$ supplies the missing 3. If $3\nmid R$, (2) gives $T(R,N-1)\equiv1+9R(R+3)/2\equiv19\pmod{27}$. This proves row statement 2.

## 4. Specializing the row theorems

Because $P_1(1+2y)=1+2y$, we have $T(R,1)=2R+1$. Iterating row statement 1 with $R$ fixed gives $T(R,p^k)\equiv2R+1\pmod{p^{3+v_p(R)}}$. Taking $R=p+1$, $k=1$ gives the first A364117 congruence. Taking $R=p^k$ gives the first A364116 family for $p\ge5$. Taking $R=p^k$ in row statement 2 gives both shifted A364117 assertions, including $p=3$.

For the other A364116 family set $R=(p-1)p^{k-1}$. Apply row statement 1 a total of $k-1$ times to reach $T(R,p-1)$. Row statement 2 at $N=p$ gives residue one at the same modulus $p^{3+v_p(R)}=p^{k+2}$.

Finally $P_3(1+2y)=1+12y+30y^2+20y^3$. In its cube the coefficients through degree 3 are $1,36,522,3948$. Applying $F_3$ gives $1+3\cdot36+3\cdot522+3948=5623$, and $5623-7=27\cdot208$ has 3-adic valuation three. This disproves the $p=3$ case of the stated modulus $3^4$.

## Verification and attribution

Run `python3 verify.py` for independent calculations from the Legendre three-term recurrence and the exact binomial expansion in $y$. Run `lean Certificate.lean` with Lean 4.33.1 to replay finite evaluations, including the counterexample. The proofs for unbounded indices are the arguments above. Peter Bala authored the conjectures. The classical Apéry rows $R=1,2$ and multivariate supercongruences have an earlier literature, including Armin Straub’s work. This note makes no claim of historical priority. [Straub, *Multivariate Apéry numbers and supercongruences of rational functions*](https://doi.org/10.2140/ant.2014.8.1985)
