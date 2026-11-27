# Counting square-zero matrices modulo an integer

Ben Branman conjectured that the number $N(n)$ of two-by-two matrices over $\mathbb Z/n\mathbb Z$ whose square is zero equals $n^2$ exactly when $n$ is squarefree. Robert Israel proposed a formula for each prime power. The following count proves both for every positive modulus, including powers of two. Manfred Scheucher earlier proved the case of a prime modulus. [OEIS A087726](https://oeis.org/A087726) · [Scheucher's proof](https://oeis.org/A087726/a087726_4.pdf)

## Result

For any prime $p$ and any exponent $e\ge1$,

$$
N(p^e)=p^{2e}+\left\lfloor e/2\right\rfloor(p^2-1)p^{2e-2}.
$$

For arbitrary $n\ge1$ the Chinese remainder theorem gives

$$
N(n)=n^2\prod_{p^e\parallel n}
\left[1+\left\lfloor e/2\right\rfloor(1-p^{-2})\right].
$$

Every bracket is at least one, and it is strictly greater than one exactly when $e\ge2$. This proves the squarefree criterion, with $n=1$ covered by the empty product. For the even and odd exponents separately, the prime-power formula simplifies to Israel's proposed expression.

## Proof

Write $R=\mathbb Z/p^e\mathbb Z$ and $X=\begin{pmatrix}a&b\\c&d\end{pmatrix}$. Call $X$ primitive if it contains a unit entry. When $X^2=0$ and both off-diagonal entries are divisible by $p$, its diagonal entries satisfy $a^2=d^2=0$ modulo $p$. Then every entry is divisible by $p$. Thus each primitive solution has an off-diagonal unit.

If $b$ is a unit, the upper-right and upper-left entries of $X^2$ force $d=-a$ and $c=-a^2/b$. Conversely those two substitutions make all four entries of the square vanish. There are $p^e$ choices for $a$ and $p^e-p^{e-1}$ for $b$.

The remaining primitive matrices have $c$ a unit and $b$ divisible by $p$. Then $d=-a$ and $b=-a^2/c$, so $p\mid b$ exactly when $p\mid a$. This gives $p^{e-1}$ choices for $a$ and $p^e-p^{e-1}$ for $c$. Together the two disjoint cases give

$$
(p^e+p^{e-1})(p^e-p^{e-1})=(p^2-1)p^{2e-2}
$$

primitive solutions.

For $e\ge2$, every other solution is $pY$ for a unique matrix $Y$ modulo $p^{e-1}$. The condition becomes $Y^2=0$ modulo $p^{e-2}$. Every matrix modulo $p^{e-2}$ has $p^4$ lifts modulo $p^{e-1}$. Thus

$$
N(p^e)=(p^2-1)p^{2e-2}+p^4 N(p^{e-2}).
$$

The initial values are $N(1)=1$ and $N(p)=p^2$, since zero is the only nonprimitive matrix modulo $p$. Dividing by $p^{2e}$ shows that the normalized count increases by $1-p^{-2}$ every two exponents. This proves the claimed formula. The Chinese remainder theorem applies entrywise and respects matrix multiplication, so counts at relatively prime moduli multiply.

## Verification

The companion Python program directly multiplies every matrix for $1\le n\le32$, $n=49$, and $n=64$. It checks all four entries of the square against zero and compares the counts with the formula. This covers 29,788,113 matrices. For example, $N(4)=28$, $N(9)=153$, $N(12)=252$, $N(30)=900$, and $N(64)=13,312$.
