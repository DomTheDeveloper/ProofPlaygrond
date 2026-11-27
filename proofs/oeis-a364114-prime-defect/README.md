# The universal prime-level defect of Bala's Legendre rows

Dominic A. Dabish, with AI assistance, 27 November 2026.

Peter Bala conjectured enhanced congruences modulo the fifth power of a prime for rows 3 and 4 of his Legendre array. This note proves all four prime-level assertions recorded on A364114, A364118, and A364119, including both multiplicative companions. The higher-level congruences modulo `p^(3r+3)` remain open.

For integers `R,n >= 0`, put

```math
T_R(n)=[x^n]\frac1{1-x}P_n\!\left(\frac{1+x}{1-x}\right)^R.
```

Rows 3 and 4 are A364114 and A364115. We prove the stronger uniform expansion below.

## Theorem

Let `p >= 7` be prime, let `R >= 0`, and put

```math
H=\sum_{k=1}^{p-1}\frac1k\in\mathbb Z_{(p)}.
```

Then, modulo `p^5`,

```math
T_R(p)\equiv 2R+1+R(R^2-R+5)pH,
```

```math
T_R(p-1)\equiv1+R(4R-9)pH.
```

Wolstenholme's theorem gives `H == 0 (mod p^2)`, so the displayed correction terms start at `p^3`.

The specializations are

```math
T_3(p)\equiv7+33pH,\qquad T_3(p-1)\equiv1+9pH,
```

```math
T_4(p)\equiv9+68pH,\qquad T_4(p-1)\equiv1+28pH.
```

Consequently

```math
3T_3(p)-11T_3(p-1)\equiv10\pmod {p^5},
```

```math
T_3(p)^{21}\equiv7^{21}T_3(p-1)^{11}\pmod {p^5},
```

```math
7T_4(p)-17T_4(p-1)\equiv46\pmod {p^5},
```

```math
T_4(p)^{63}\equiv9^{63}T_4(p-1)^{17}\pmod {p^5}.
```

The first two are the two assertions on A364114, and the linear one is equivalently the first assertion on A364118. The last two are the prime-level assertions on A364119.

## Proof

Put `y=x/(1-x)` and define the linear functional

```math
F_n(y^j)=\binom nj\quad(0\le j\le n),\qquad F_n(y^j)=0\quad(j>n).
```

The finite hypergeometric expansion

```math
P_n(1+2y)=\sum_{j=0}^n\binom nj\binom{n+j}{j}y^j
```

and `[x^n]y^j/(1-x)=binom(n,j)` give

```math
T_R(n)=F_n(P_n(1+2y)^R).
```

Write `X_n=P_n(1+2y)-1` and

```math
M_{n,l}=F_n(X_n^l).
```

The calculation rests on the following finite moment lemma.

### Finite moment lemma

For every prime `p >= 7`, modulo `p^5`,

| `l` | `M_(p,l)` | `M_(p-1,l)` |
| ---: | ---: | ---: |
| 1 | `2+5pH` | `-5pH` |
| 2 | `4pH` | `8pH` |
| 3 | `6pH` | `0` |
| `l >= 4` | `0` | `0` |

Only `l<=p` can contribute, so the last row has its literal finite meaning.

Here are details of the reduction. For `1<=k<p`, the two coefficient products are exactly

```math
[y^k]X_p=(-1)^{k-1}\frac pk\left(1+\frac pk\right)
 \prod_{j<k}\left(1-\frac{p^2}{j^2}\right),
```

```math
[y^k]X_{p-1}=(-1)^k\frac pk\left(1-\frac pk\right)
 \prod_{j<k}\left(1-\frac{p^2}{j^2}\right).
```

The remaining endpoint in the first line is `[y^p]X_p=binom(2p,p)`. The two functional weights are

```math
F_p(y^s)=(-1)^{s-1}\frac ps\prod_{j<s}\left(1-\frac pj\right)\qquad(1\le s<p)
```

and

```math
F_{p-1}(y^s)=(-1)^s\prod_{j\le s}\left(1-\frac pj\right).
```

For `p >= 11`, expand these four products only through total `p`-adic degree four. The reductions used after summing are

```math
H\equiv0\pmod {p^2},\qquad 2H+pH^{(2)}\equiv0\pmod {p^4},
```

```math
H^{(2a)}\equiv0\pmod p,\qquad H^{(2a+1)}\equiv0\pmod {p^2}
```

whenever the displayed weight is at most five, together with the stuffle rule for strict finite multiple harmonic sums. Here `H^(a)=sum k^(-a)`. The first assertion is Wolstenholme. The second follows by pairing `k` with `p-k` and expanding through degree three. The last two follow because inversion permutes the nonzero residues and by the same pairing for odd weight. The single boundary prime `p=7` is evaluated directly from the finite integer sums. This gives the same moment table, and the accompanying Lean certificate checks the resulting row values without axioms.

For completeness, if

```math
H(s_1,\ldots,s_d)=\sum_{1\le k_1<\cdots<k_d<p}
 k_1^{-s_1}\cdots k_d^{-s_d},
```

then multiplying two such sums and separating equal indices gives the stuffle reduction. Replacing every `k_i` by `p-k_(d+1-i)` gives the reversal reduction, one power of `p` at a time. Applying those two identities to the expanded products gives the following audit table.

| moment | endpoint term | strict interior terms after stuffle and reversal | total |
| --- | ---: | ---: | ---: |
| `M_(p,1)` | `2+4pH` | `pH` | `2+5pH` |
| `M_(p,2)` | `0` | `4pH` | `4pH` |
| `M_(p,3)` | `0` | `6pH` | `6pH` |
| `M_(p,l), l>=4` | `0` | `0` | `0` |
| `M_(p-1,1)` | `0` | `-5pH` | `-5pH` |
| `M_(p-1,2)` | `0` | `8pH` | `8pH` |
| `M_(p-1,l), l>=3` | `0` | `0` | `0` |

Every entry is modulo `p^5`. Products with at least five nonconstant factors vanish by valuation. At the two boundary cases where the factor count alone gives only `p^3` or `p^4`, reversal supplies respectively two or one additional powers. This proves the finite moment lemma.

Finally, the binomial theorem gives

```math
T_R(n)=1+\sum_{l\ge1}\binom Rl M_{n,l}.
```

For `n=p`, the coefficient of `pH` is

```math
5R+4\binom R2+6\binom R3=R(R^2-R+5).
```

For `n=p-1`, it is

```math
-5R+8\binom R2=R(4R-9).
```

This proves the theorem. In the four displayed applications, terms quadratic in `pH` vanish modulo `p^5`. Their linear coefficients cancel because

```math
3\cdot33=11\cdot9,
\qquad 21\cdot33=11\cdot7\cdot9,
```

```math
7\cdot68=17\cdot28,
\qquad 63\cdot68=17\cdot9\cdot28.
```

## Reproduction and scope

Run `python3 verify.py`. It evaluates `T_R(n)` in two independent ways, verifies the seven moment congruences, checks the universal formulas for many rows, and checks all four applications. Run `lean Certificate.lean` with Lean 4.33.1 or later for kernel-checked finite certificates. The finite checks guard the transcription; the unbounded proof is the harmonic calculation above.

Peter Bala posed the conjectures. Classical Apéry supercongruences and the general cubic baseline have earlier literature. No historical-priority claim is made for the uniform prime-level expansion. The `p^(3r+3)` towers for `r>=2` and the corresponding multiplicative towers remain open.

Sources: [A364114](https://oeis.org/A364114), [A364118](https://oeis.org/A364118), [A364119](https://oeis.org/A364119), [NIST DLMF 18.5.7--18.5.8](https://dlmf.nist.gov/18.5), [Straub, *Multivariate Apéry numbers and supercongruences of rational functions*](https://doi.org/10.2140/ant.2014.8.1985).
