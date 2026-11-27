# The co-index of a random nilpotent matrix

Geoffrey Critzer's June 2025 conjecture concerns the nilpotency index of a uniformly chosen nilpotent binary matrix. Its proposed limiting probability is correct. Its companion finite formula holds exactly when the largest Jordan block is strictly longer than half the dimension. The stated condition $j<2n$ includes cases where the proposed answer is a fraction. [OEIS A346214](https://oeis.org/A346214)

## The exact range

Let $q$ be a prime power, $g_d=|\mathrm{GL}_d(\mathbb F_q)|$, $C_d=\prod_{i=1}^d(1-q^{-i})$, and $C_\infty=\prod_{i\ge1}(1-q^{-i})$. Thus $g_d=q^{d^2}C_d$ and $g_0=C_0=1$. For $n\ge1$, let $T_q(n,L)$ count the nilpotent $n\times n$ matrices of index $L$ (least positive exponent giving zero), and put $j=n-L$.

**Theorem.** For $0\le j<n$,

$$
T_q(n,n-j)\ \le\ \frac{g_n}{(q-1)g_j}\,q^{(j-1)^2-n},
\qquad
\text{with equality exactly when } 2j<n .
$$

For $q=2,n=2,j=1$, the zero matrix is the only matrix of index one. The proposed right side is $6/4=3/2$. This gives a counterexample even before considering large dimensions.

### Counting by the longest block

Write a partition in decreasing order. Its conjugate is $\lambda'$ and $m_s(\lambda)$ denotes the number of parts of size $s$. A nilpotent matrix has a unique Jordan type $\lambda$ and its conjugacy class has size $g_n/c_q(\lambda)$, where

$$
c_q(\lambda)=q^{\sum_i(\lambda'_i)^2}\prod_{s\ge1}\prod_{a=1}^{m_s(\lambda)}(1-q^{-a}).
$$

Regard a Jordan block of length $s$ as the module $\mathbb F_q[t]/(t^s)$. A homomorphism from a block of length $s$ to one of length $u$ has $\min(s,u)$ free coefficients. Summing over ordered pairs of blocks gives $\sum_i(\lambda'_i)^2$ free coefficients. On the quotient of the whole module by $t$, the induced map is block triangular in the order of block sizes, since a map from a shorter block to a longer one has image divisible by $t$. Its diagonal blocks are arbitrary independent $m_s\times m_s$ matrices. An endomorphism is invertible exactly when its reduction modulo $t$ is invertible, since surjectivity lifts through the finite filtration by powers of $t$. The fraction of invertible endomorphisms therefore gives the product above. This classical partition count also occurs in Brawley's enumeration by nilpotency index. [Fine and Herstein, 1958](https://doi.org/10.1215/ijm/1255454112) · [Brawley, 1982, equation (7)](https://doi.org/10.1137/0603003)

We also use the total $H_j=q^{j(j-1)}$ of nilpotent $j\times j$ matrices, with $H_0=1$. To see this directly, every endomorphism of a $j$-dimensional space splits uniquely as its restriction to $\ker A^j$ and $\operatorname{im} A^j$, nilpotent and invertible respectively. For a kernel of dimension $k$, there are $g_j/(g_kg_{j-k})$ ordered complementary subspace pairs, $H_k$ choices on the kernel and $g_{j-k}$ choices on the image. Hence $q^{j^2}/g_j=\sum_{k=0}^j H_k/g_k$. Subtracting the equation for $j-1$ gives $H_j=q^{j^2-j}$ for $j\ge1$ and consequently $\sum_{\mu\vdash j}1/c_q(\mu)=H_j/g_j$.

Remove a longest block of length $L=n-j$. This is a bijection between partitions with largest part $L$ and partitions $\mu\vdash j$ having no part longer than $L$. Adding the block increases the sum of squares of column lengths by $L+2j$, since the first $L$ columns of $\mu$ contain all $j$ boxes. It follows that

$$
\frac{c_q(\mu\cup(L))}{c_q(\mu)}
=q^{L+2j}\big(1-q^{-(m_L(\mu)+1)}\big).
$$

In the orbit sum for $T_q(n,L)$, extend the sum to all $\mu\vdash j$ and bound each reciprocal factor by $1/(1-q^{-1})$. The result is

$$
\frac{g_nq^{-(L+2j)}}{1-q^{-1}}\frac{q^{j(j-1)}}{g_j}
=\frac{g_n}{(q-1)g_j}q^{(j-1)^2-n}.
$$

If $L>j$, all partitions enter and $m_L=0$ throughout. If $L=j$, the partition $(j)$ contributes strictly less than the upper bound. If $L<j$, the positive contribution assigned to $(j)$ by the upper bound is absent. This proves the equality criterion, including its boundary.

## Limiting law and speed of convergence

Let $J_n=n-\operatorname{index}(A)$ and $P_n(j)=\Pr(J_n=j)$ for a uniform nilpotent matrix. Set $P_n(j)=0$ for $j\ge n$. Dividing the exact formula by $q^{n(n-1)}$ gives, for each fixed $j\ge0$,

$$
P_\infty(j)=\lim_{n\to\infty}P_n(j)
=\frac{C_\infty q^{(j-1)^2}}{(q-1)g_j}
=\frac{C_\infty}{1-q^{-1}}\frac{q^{-2j}}{C_j}.
$$

This proves the limiting assertion in A346214 at $q=2$. The finite probabilities satisfy $P_n(j)\le(C_n/C_\infty)P_\infty(j)$, with equality throughout $2j<n$.

The probability generating function, valid for $|z|<q^2$, is

$$
\sum_{j\ge0}P_\infty(j)z^j
=\prod_{i=2}^\infty\frac{1-q^{-i}}{1-zq^{-i}}.
$$

Indeed $F(t)=\sum_{j\ge0}t^j/C_j$ satisfies $(1-t)F(t)=F(t/q)$ by comparing coefficients. Iterating and taking $t=z/q^2$ proves the formula. Setting $z=1$ shows the probabilities sum to one. The product identifies the law as a sum of independent geometric variables on $\{0,1,\ldots\}$ with respective means $1/(q^i-1)$ for $i\ge2$. Because $P_n(j)$ is bounded by a constant times $q^{-2j}$, its mean also converges. At $q=2$, the probability of a single Jordan block tends to $0.577576190173\ldots$ and the expected co-index tends to $0.606695152415\ldots$.

In fact the two distributions cross at a known index in every dimension. One has $P_n(j)>P_\infty(j)$ exactly for $2j<n$, and $P_n(j)<P_\infty(j)$ for every other $j\ge0$. Thus the total variation distance has the exact value

$$
\boxed{d_{\rm TV}(P_n,P_\infty)
=\left(\frac{C_n}{C_\infty}-1\right)
\sum_{j=0}^{\lfloor(n-1)/2\rfloor}P_\infty(j).}
$$

For the proof, write $a_n=C_n/C_\infty>1$. On $2j<n$ the equality $P_n(j)=a_nP_\infty(j)$ gives the first sign immediately. For $n/2\le j<n$, consider the partition $\mu=(j)$ in the proof of the upper bound. Its share of the upper-bound sum is $w_j=C_j/(1-q^{-1})$, since $c_q((j))=q^j(1-q^{-1})$. At $L=j$ its contribution is multiplied by $q/(q+1)$, and at $L<j$ it disappears entirely. Hence $P_n(j)/(a_nP_\infty(j))\le1-w_j/(q+1)$. The elementary product bound $\prod(1-x_i)\ge1-\sum x_i$ gives $w_j\ge1-1/(q(q-1))\ge1/2$ and $1-1/a_n\le q^{-n}/(q-1)$. For $n\ge3$, $q^{-n}/(q-1)<1/(2(q+1))$, which gives $P_n(j)<P_\infty(j)$. For $n=2$ the only such $j$ is $1$, when $w_j=1$ and $q^{-2}/(q-1)<1/(q+1)$. There are no such $j$ at $n=1$, and $P_n(j)=0$ whenever $j\ge n$. Summing exactly the positive differences proves the displayed identity.

As $n$ grows, this gives $d_{\rm TV}(P_n,P_\infty)=q^{-n}/(q-1)+O_q(q^{-2n})$. Indeed $\sum_{2j\ge n}P_\infty(j)=O_q(q^{-n})$ by the geometric bound, and the tail product gives $a_n-1=\sum_{i>n}q^{-i}+O_q((\sum_{i>n}q^{-i})^2)$.

## Reproducing the checks

`check.py` evaluates Jordan-class sizes exactly, checks both sides of the probability crossing for five field orders, and checks the separate square-zero lifting recurrence. `exhaustive.cpp` independently classifies every binary matrix through dimension five by its powers, and counts all lifts of its square-zero residues modulo four by solving the entrywise linear equations. In dimension five this checks 33,554,432 binary matrices and counts 147,832,832 square-zero matrices modulo four.

`Counterexample.lean` defines the actual finite table using matrices over `ZMod 2`, proves the count at index one, and disproves the printed finite identity. `Lifting.lean` checks the block square and its exact vanishing criterion over any ring. The distribution, exact range, and enumeration theorems are proved in the notes.

```sh
g++ -std=c++17 -O3 exhaustive.cpp -o /tmp/check-nilpotent
/tmp/check-nilpotent | python3 check.py --exhaustive
lake update
lake exe cache get Mathlib/Data/Fintype/Pi.lean Mathlib/Data/Matrix/Basic.lean Mathlib/Data/Matrix/Block.lean Mathlib/Data/ZMod/Basic.lean
lake env lean Counterexample.lean
lake env lean Lifting.lean
```

Both files compiled with Lean 4.33.1 and the pinned mathlib revision. Their reported axioms are among `propext`, `Classical.choice`, and `Quot.sound`. The recurrence and its proof appear in [Counting square-zero matrices over finite chain rings](chain-rings.md).
