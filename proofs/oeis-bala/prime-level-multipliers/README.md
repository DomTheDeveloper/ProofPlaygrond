# One multiplier controls the first cubic level of two Bala conjectures

Dominic A. Dabish (DomTheDeveloper), 26 November 2026.

Peter Bala conjectured that for each of the sequences $u=$ A362727 and $u=$ A362729 one has $u_{mp^r}\equiv u_{mp^{r-1}}\pmod{p^{3r}}$ for every prime $p\ge7$ and all $m,r\ge1$. The earlier prime-index proof established the case $m=r=1$. Here $m$ is unrestricted. [A362727](https://oeis.org/A362727) · [A362729](https://oeis.org/A362729) · [Earlier prime-index proof](https://github.com/DomTheDeveloper/formal-conjectures/blob/ba5387c1e8db8d55ef4357db33d05db279964480/research/bala-framing/PrimeIndex.md)

**Theorem 1.** For either sequence, every odd prime $p$, every $N>0$ divisible by $p$, and $t=v_p(N)$, the difference $u_N-u_{N/p}$ is divisible by $p^{2t}$.

**Theorem 2.** Fix any prime $p\ge7$. The following three conditions are equivalent.

1. For both sequences, $u_{mp}\equiv u_m\pmod{p^3}$ for all positive integers $m$.
2. For either one of the sequences, $u_{2p}\equiv8\pmod{p^3}$.
3. The explicit residue $S_p$ defined below is zero.

Whenever these conditions hold, both sequences satisfy the stronger uniform bound
$$p^{2t+1}\mid u_N-u_{N/p}\qquad(t=v_p(N)\ge1).$$
Two finite calculations prove $S_p=0$ for **every prime $7\le p\le10{,}000$**, so there are 1,226 primes for which the first cubic level is proved for *every* multiplier. The same calculations and the uniform bound also apply at arbitrarily high $p$-power indices. For the stated primes the original modulus $p^{3r}$ follows whenever $2v_p(m)+1\ge r$. At every odd prime it follows whenever $2v_p(m)\ge r$ by Theorem 1.

The full cubic conjectures at arbitrary primes and levels remain open here. These written proofs use the classical Apéry congruences and Lucas's theorem. The programs certify the prime range, and Lean checks its first eight primes directly from the binomial sums.

## The seeds and their arithmetic

Let $F_n=\sum_j\binom nj^2\binom{n+j}{j}$, the Apéry numbers for $\zeta(2)$. For $n\ge1$ the two seed sequences are
$$A_n=\sum_j\binom nj\binom{n-1}j\binom{n+j-1}j=(F_n+2F_{n-1})/5,$$
$$B_n=\sum_j\binom nj\binom{n-1}j\binom{n+j}j=(2F_n-F_{n-1})/5.$$
The binomial and contiguous formulas are recorded in the seed entries. [A208675](https://oeis.org/A208675) · [A108628](https://oeis.org/A108628) · [A005258](https://oeis.org/A005258)

Take $c=A$ or $B$. Put $b_j=2c_j$ for odd $j$ and $b_j=0$ for even $j$. Let $H(x)=\exp(\sum_{j\ge1}b_jx^j/j)$. Then $u_N=[x^N]H(x)^N$ by Bala's definition.

Coster proved the diagonal cubic congruences. Straub's Theorem 3.2 and Example 3.4 give the adjacent-index congruence of order $2t$ for $F_N$ at all primes, and order $3t$ at $p\ge5$. Applying the same theorem on negative indices and $F_{-n}=(-1)^{n-1}F_{n-1}$ gives the same bounds for $F_{N-1}$ at odd primes. Thus $v_p(b_N-b_{N/p})\ge2t$ for every odd prime, including five where division by 5 costs at most one, since $3t-1\ge2t$. At primes $p\ge7$ we have $v_p(b_N-b_{N/p})\ge3t$. At $p=2$ the mask itself gives the ordinary bound $t$, because the difference is even if $t=1$ and zero if $t\ge2$. [Straub, *Multivariate Apéry numbers and supercongruences of rational functions*, §3, especially (25)–(26)](https://arxiv.org/abs/1401.0854)

These ordinary bounds at all primes also give $H(x)\in1+x\mathbb Z[[x]]$. Indeed the Euler exponents $j^{-1}\sum_{d\mid j}\mu(j/d)b_d$ are integers, by grouping adjacent indices at every prime dividing $j$. The Euler product with these exponents agrees with $H$ after taking logarithms.

## The reduced logarithm

Set $G(x)=x^{-1}H(x)$, $M=N/p$, and
$$D(x)=\log H(x)-p^{-1}\log H(x^p).$$
Its coefficient $d_j$ is $b_j/j$ for units $j$ and $(b_j-b_{j/p})/j$ for $p\mid j$. At a positive exponent $e=v_p(j)$ it has valuation at least $e$, and at least $2e$ if $p\ge7$. All coefficients are locally integral. The constant term identity is
$$u_N-u_M=\operatorname{CT}\,G(x^p)^M\big(\exp(ND(x))-1\big).$$
In the linear term only indices $j$ divisible by $p$ contribute. The matching coefficient $g=[x^{-j/p}]G(x)^M$ has valuation at least $\max(0,t-e)$, by logarithmically differentiating $G^M$ in the division-free form $x(G^M)'=M G^{M-1}xG'$. The linear term therefore has valuation at least $2t$ at all odd primes and at least $2t+1$ at $p\ge7$. For the latter estimate use $t+2e+\max(0,t-e)\ge2t+1$.

At every odd prime and $h\ge2$, $v_p(h!)\le h-2$, so $(ND)^h/h!$ has valuation at least $2t$. This proves Theorem 1. For $p\ge7$ and $h\ge3$ the stronger bound $v_p(h!)\le h-3$ gives valuation at least $3t$. Both factorial estimates follow from Legendre's formula (check $h=2,3,4$ directly). Thus only $N^2D^2/2$ can obstruct divisibility by $p^{2t+1}$. These coefficient estimates use the earlier quadratic framing argument. [Earlier argument](https://github.com/DomTheDeveloper/formal-conjectures/blob/ba5387c1e8db8d55ef4357db33d05db279964480/research/bala-framing/IteratedAperyFranel.md) · [Schwarz, Vologodsky and Walcher, *Integrality of Framing and Geometric Origin of 2-functions*](https://arxiv.org/abs/1702.07135)

## Reducing every multiplier to one finite sum

For $1\le s<p$ and $a\ge0$, Lucas's theorem gives
$$c_{pa+s}\equiv F_a c_s\pmod p.$$
Indeed in a summand with $j=pv+w$, $0\le w<p$, the first two lower-digit binomials are $\binom sw$ and $\binom{s-1}w$. In the last binomial, a carry at $s+w-1$ or $s+w$ makes the lower digit smaller than $w$, so that summand is zero. Without a carry the upper-digit product is $\binom av^2\binom{a+v}{v}$, and summing the lower digits gives the seed at $s$.

For a chosen seed put
$$S_p(c)=\sum_{s=1}^{p-1} c_s c_{p-s}/s^2\quad\text{in }\mathbb F_p.$$
At $p\ge7$ the coefficients of $D\bmod p$ are supported on odd indices prime to $p$. If $h$ is odd then $[x^{ph}]D^2=0\bmod p$. For even $h>0$, put $j=pa+s$. Its complementary index is $p(h-1-a)+(p-s)$. The parity condition is $a+s$ odd. The summands in $S_p(c)$ at $s$ and $p-s$ coincide and have opposite index parity. Thus each choice of parity contributes half of $S_p(c)$. The opposite denominator signs and the factors of two in $b_j$ give the exact formula
$$[x^{ph}]D(x)^2\equiv-2S_p(c)\sum_{a=0}^{h-1}F_aF_{h-1-a}\pmod p.$$
It follows that $S_p(c)=0$ suffices for the extra power of $p$ at every $N$. Conversely take $N=2p$. Only $h=2$ contributes to the quadratic term, and the matching coefficient of $G(x)^2$ at degree $-2$ is 1. As $F_0=1$ and $F_1=3$, this yields
$$u_{2p}-8\equiv-24p^2 S_p(c)\pmod {p^3}.$$
The multiplier 2 is a necessary and sufficient test.

Finally $S_p(B)=-S_p(A)$, so the same single test covers the two sequences. To verify the reflection, use
$$(n+1)^2 F_{n+1}=(11n(n+1)+3)F_n+n^2 F_{n-1}.$$
The binomial sum gives $F_{p-1}=1$ and $F_{p-2}=-3$ modulo $p$. The reversed sequence $(-1)^jF_{p-1-j}$ satisfies the identical recurrence modulo $p$ and has initial values $1,3$. Induction up to $p-1$ gives $F_{p-1-j}=(-1)^jF_j$ in the field. The two contiguous formulas now give $A_{p-s}=(-1)^s B_s$ and $B_{p-s}=(-1)^{s+1} A_s$. This proves Theorem 2 with $S_p=S_p(A)$.

For $p=5$ the actual second multipliers give $3347043208-8$ and $6038588808-8$. Each difference is divisible by 25 and fails divisibility by 125. The extension to $p=5$ that works at multiplier 1 therefore fails at multiplier 2 for both sequences. This is consistent with Bala's stated lower bound $p\ge7$.

## Exact verification

The first Python program computes $F_n$ in each prime field, forms both seeds and independently sums both complete residues. The second uses exact-integer recurrences for the two *separate* seeds before reducing modulo any prime. It uses the Somos recurrence for A208675 and the Kotesovec recurrence for A108628 recorded in their OEIS entries, verifies exact division at every step, and evaluates half-sums using modular inverses. It also compares 300 seed values to the defining binomial sums and differentiates the defining exponential to check transformed coefficients. Neither check samples the multiplier in the proof of Theorem 2.

With Python 3.10 or later and Lean 4.33.1, run

```sh
python3 -I obstruction.py 10000
python3 -I independent.py 10000
lean Obstruction.lean
```

Both Python programs find zero for both seeds at every prime from 7 through 9973. The Lean certificate evaluates the two obstruction sums directly from the original binomial sums for $p=7,11,13,17,19,23,29,31$, as well as the two nonzero residues at 5. The statements about every multiplier and every index valuation have written proofs above.
