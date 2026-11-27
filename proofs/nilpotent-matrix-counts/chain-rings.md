# Counting square-zero matrices in every dimension over finite chain rings

Let $R$ be a finite commutative chain ring with residue field $\mathbb F_q$, maximal ideal $(\pi)$ and length $e$, so $(\pi)^e=0$ and $(\pi)^{e-1}\ne0$. In particular $R$ can be $\mathbb Z/p^e\mathbb Z$ or $\mathbb F_q[t]/(t^e)$. Let $N_{d,e}(q)$ count the $d\times d$ matrices over $R$ satisfying $X^2=0$. The proof shows that only $d,e,q$ matter. With $d=2$ over the integers modulo $m$, these are the counts of OEIS A087726. Scheucher's 2015 note treats two-dimensional matrices at prime moduli. [OEIS A087726](https://oeis.org/A087726) · [Scheucher's note](https://oeis.org/A087726/a087726_4.pdf) · [Earlier dimension-two calculation](https://github.com/DomTheDeveloper/ProofPlaygrond/pull/125)

## Recurrence

Write $g_r=|\mathrm{GL}_r(\mathbb F_q)|=\prod_{i=0}^{r-1}(q^r-q^i)$ and use the Gaussian binomial coefficient to count subspaces of a prescribed dimension. For $0\le r\le\lfloor d/2\rfloor$, set

$$
K_{d,r}={d\brack r}_q{d-r\brack r}_q\,g_r .
$$

The boundary values are $N_{0,e}=N_{d,0}=1$ and $N_{d,1}=\sum_r K_{d,r}$. For $e\ge2$, setting $s=d-2r$ in each summand gives

$$
\boxed{N_{d,e}(q)=\sum_{r=0}^{\lfloor d/2\rfloor}
K_{d,r}\,q^{\,2r(d-r)(e-1)+s^2}\,N_{s,e-2}(q).}
$$

For an integer modulus $m=\prod_p p^{e_p}$, multiply $N_{d,e_p}(p)$ over its prime divisors. This follows entrywise from the Chinese remainder theorem, and also covers $m=1$ by the empty product.

### Proof

Over the residue field, a rank-$r$ square-zero operator $A$ determines $\operatorname{im} A\subseteq\ker A$. Choose its kernel of dimension $d-r$, its image of dimension $r$ inside that kernel, and an isomorphism from the quotient by the kernel to the image. This gives exactly $K_{d,r}$ choices, including the rank-zero matrix.

Fix one such $A$. Choose a field basis $(\bar u_1,\ldots,\bar u_r,\bar f_1,\ldots,\bar f_r,\bar w_1,\ldots,\bar w_s)$ with $A\bar f_i=\bar u_i$ and $A\bar u_i=A\bar w_j=0$. Fix lifts of the $f_i$ and $w_j$. For a square-zero lift $X$ of $A$, the vectors $u_i=Xf_i$ reduce to $\bar u_i$. Choose these lifts freely in $q^{dr(e-1)}$ ways. The resulting $(u,f,w)$ is a basis, since its determinant is a unit. In this basis $Xu_i=0$ and $Xf_i=u_i$. Thus

$$
X=\begin{pmatrix}0&I&C\\0&0&D\\0&0&B\end{pmatrix},
\qquad C,D,B\equiv0\bmod\pi .
$$

Squaring shows that $D=-CB$ and $B^2=0$ are necessary and sufficient. The three potentially nonzero blocks of the square are $D+CB,DB,B^2$, and the middle one then vanishes. The $r\times s$ block $C$ has $q^{rs(e-1)}$ choices. Each resulting matrix yields the chosen $u_i$ back as $Xf_i$, so the change of basis creates no overcount.

Multiplication by $\pi$ identifies $R/(\pi^{e-1})$ with $(\pi)$ as additive groups. Write $B=\pi Y$. Then $B^2=0$ exactly when $Y^2=0\bmod\pi^{e-2}$. Each admissible $Y\bmod\pi^{e-2}$ has $q^{s^2}$ lifts to $R/(\pi^{e-1})$. At $e=2$ the condition is vacuous. Multiplying the counts and using $dr+rs=2r(d-r)$ proves the recurrence, by induction on length.

## Exact polynomial growth on each parity

Let $M_{d,e}=N_{d,e}/q^{\lfloor d^2 e/2\rfloor}$. Since $(d-2r)^2=d^2-4r(d-r)$, substitution cancels all length-dependent powers and gives

$$
M_{d,e}=\sum_r K_{d,r}\,q^{-2r(d-r)} M_{d-2r,e-2}.
$$

For fixed $d$, let $h=\lfloor d/2\rfloor$. For each $\epsilon\in\{0,1\}$, **$M_{d,2k+\epsilon}$ is a polynomial in $k$ of degree exactly $h$**. Both parities have leading coefficient

$$
\frac{1}{h!}\prod_{i=0}^{h-1}
K_{d-2i,1}\,q^{-2(d-2i-1)}.
$$

Indeed take the vector of all $M_{a,e}$ with $0\le a\le d$ and $a\equiv d\bmod2$. The length transition is $I+L$ where $L$ is strictly lower triangular in increasing dimension, so $L^{h+1}=0$. Expanding $(I+L)^k$ gives $\sum_{t=0}^h\binom{k}{t}L^t$. For the top component, the only path of length $h$ drops exactly two dimensions at every step. Its weight is the displayed product, times the last component of the initial vector. In dimension zero and one this initial component is one for either starting parity. Thus the leading coefficient is positive, also when $h=0$ by the empty product.

For example, $K_{3,1}=(q^2+q+1)(q^2-1)$. Over $\mathbb Z/2^e\mathbb Z$ the first four counts in dimension three are

| Modulus | 2 | 4 | 8 | 16 |
| --- | ---: | ---: | ---: | ---: |
| Square-zero $3\times3$ matrices | 22 | 1,184 | 22,016 | 950,272 |

The [verification instructions](README.md#reproducing-the-checks) include independent enumeration over $\mathbb F_2$, counts of lifts to $\mathbb Z/4\mathbb Z$, and direct tests in equal-characteristic rings and odd residue characteristic.
