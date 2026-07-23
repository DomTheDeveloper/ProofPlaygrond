# Restricted-run tableaux Conjecture 2a: proof development

## Target

Let `G(n)` be the number of words `w_1...w_{3n}` over `{1,2,3}` such that

1. each letter occurs exactly `n` times;
2. in every prefix, `N_1 >= N_2 >= N_3`;
3. every maximal constant run has length at least two.

The target is

\[
G(n) \sim C_1\frac{8^n}{n^4},\qquad C_1>0.
\]

This note proves the exact finite-state reduction, constructs an explicit
positive harmonic function for the killed process, and isolates the remaining
finite-state cone local-limit theorem needed for the final asymptotic.

## 1. Equal-weight six-state chain

Use states `A_i` (the first letter of a run of `i`) and `B_i` (the second or a
later letter of that run). Start in `A_i` with probability `1/3`, and use

\[
 A_i\to B_i \quad(1),\qquad
 B_i\to B_i \quad(1/2),\qquad
 B_i\to A_j \quad(1/4)\quad(j\ne i).
\]

If a word of length `3n` has `m` runs, all of length at least two, its path
probability is

\[
 \frac13\left(\frac12\right)^{3n-2m}
 \left(\frac14\right)^{m-1}
 =\frac{4}{3\,8^n}.
\]

Consequently

\[
 \mathbb P(\text{ballot bridge of length }3n)
 =\frac{4G(n)}{3\,8^n}. \tag{1}
\]

This identity is exact and removes all combinatorial weights from the problem.

## 2. Martingale corrector

Let

\[
Y=(N_1-N_2,N_2-N_3),
\]

so the three letter increments are

\[
v_1=(1,0),\qquad v_2=(-1,1),\qquad v_3=(0,-1).
\]

Define the phase corrector

\[
\begin{array}{c|cccccc}
s&A_1&B_1&A_2&B_2&A_3&B_3\\ \hline
q(s)&(0,0)&(-1,0)&(-2,1)&(-1,0)&(-1,-1)&(-1,0).
\end{array}
\]

Set

\[
X=Y+q(J)+(2,1).
\]

The corrected transition increments are

\[
\begin{array}{c|c}
\text{transition}&\Delta X\\ \hline
A_i\to B_i&(0,0)\\
B_1\to B_1&(1,0)\\
B_1\to A_2&(-2,2)\\
B_1\to A_3&(0,-2)\\
B_2\to B_2&(-1,1)\\
B_2\to A_1&(2,0)\\
B_2\to A_3&(0,-2)\\
B_3\to B_3&(0,-1)\\
B_3\to A_1&(2,0)\\
B_3\to A_2&(-2,2).
\end{array}
\]

Their conditional mean is zero in every phase. Thus `(X_k)` is a martingale
additive process.

Every complete admissible word begins with `11` and ends with `33`. After the
first letter its state/position is

\[
(A_1,(3,1)),
\]

and at time `3n` it is

\[
(B_3,(1,1)).
\]

The ballot condition is exactly survival in the corresponding phase-dependent
quadrant, with states that cannot be extended to a complete ballot word killed
immediately.

## 3. Covariance and the cone exponent

The stationary phase distribution is

\[
\pi(A_i)=\frac19,\qquad \pi(B_i)=\frac29.
\]

Because the corrected increments are martingale differences, the asymptotic
covariance is the stationary average of their conditional second moments:

\[
\Sigma=
\begin{pmatrix}
10/9&-5/9\\
-5/9&10/9
\end{pmatrix}
=\frac59
\begin{pmatrix}2&-1\\-1&2\end{pmatrix}. \tag{2}
\]

The correlation is `-1/2`. Whitening therefore sends the quadrant to a wedge
of angle

\[
\theta=\arccos(-(-1/2))=\frac\pi3.
\]

The Brownian cone exponent is

\[
p=\frac\pi\theta=3. \tag{3}
\]

For the generator associated with (2), a positive homogeneous harmonic
polynomial is

\[
u(x,y)=xy(x+y).
\]

Indeed

\[
u_{xx}=2y,\quad u_{xy}=2x+2y,\quad u_{yy}=2x,
\]

and

\[
\frac12\Sigma:\nabla^2u=0.
\]

Since `d=2`, a fixed-endpoint cone local limit has exponent

\[
p+d/2=3+1=4. \tag{4}
\]

## 4. Exact cubic phase-harmonic polynomial

For both phases `A_i` and `B_i`, assign the polynomial `H_i` below:

\[
\begin{aligned}
H_1(x,y)&=x^2y+xy^2+\frac23x-\frac43y,\\
H_2(x,y)&=x^2y+xy^2+\frac43x,\\
H_3(x,y)&=x^2y+xy^2-\frac23y.
\end{aligned} \tag{5}
\]

Direct substitution into the ten transitions gives the polynomial identities

\[
H_i(x,y)=\sum_{(j,\delta)}P(i,j,\delta)
H_j((x,y)+\delta). \tag{6}
\]

Thus `H_{J_k}(X_k)` is an exact martingale, not merely an asymptotic Brownian
approximation. Each `H_i` has leading homogeneous term `u`.

For integers `x,y>=1`, all three polynomials are positive. On the possible
exit faces,

\[
\begin{aligned}
H_2(0,y)&=0,\\
H_2(-1,y)&=-\frac{3y^2-3y+4}{3}<0,\\
H_3(x,0)&=0,\\
H_3(x,-1)&=-\frac{3x^2-3x-2}{3}\le0\quad(x\ge2).
\end{aligned} \tag{7}
\]

The only formal exception in the last formula is `x=1`. It is unreachable at
an exit: a `B_1` phase contains at least two `1`s in its current run, hence
`x=N_1-N_2+1>=3`; and a `B_2` phase with corrected `y=1` would imply that the
last `2` was appended when `N_2<N_3`, contradicting the ballot condition.
Therefore `H` is non-positive at every reachable killed overshoot.

## 5. Exit integrability and the exact killed harmonic function

Define a second phase-harmonic family `H^+=H+Q` by

\[
\begin{aligned}
H^+_1&=\frac16(6x^2y+12x^2+6xy^2+42xy+40x+9y^2+28y+21),\\
H^+_2&=\frac16(6x^2y+12x^2+6xy^2+42xy+44x+9y^2+36y+43),\\
H^+_3&=\frac16(6x^2y+12x^2+6xy^2+42xy+36x+9y^2+32y+23).
\end{aligned} \tag{8}
\]

Again the transition identities are exact. All coefficients in (8) are
positive, so `H^+` is non-negative before exit. At the four exit types,

\[
\begin{aligned}
H^+_2(0,y)&=(9y^2+36y+43)/6,\\
H^+_2(-1,y)&=(3y^2+11)/6,\\
H^+_3(x,0)&=(12x^2+36x+23)/6,\\
H^+_3(x,-1)&=x^2.
\end{aligned} \tag{9}
\]

Let `tau` be the killing time. Optional stopping applied to the non-negative
stopped martingale `H^+_{J_{k\wedge tau}}(X_{k\wedge tau})`, followed by Fatou,
gives

\[
\mathbb E_{z,s}[H^+_{J_\tau}(X_\tau);\tau<\infty]
\le H^+_s(z). \tag{10}
\]

Equations (7)--(10) imply

\[
\mathbb E_{z,s}|H_{J_\tau}(X_\tau)|<\infty.
\]

Hence the function

\[
V_s(z)=H_s(z)-
\mathbb E_{z,s}[H_{J_\tau}(X_\tau);\tau<\infty] \tag{11}
\]

is well-defined. By the Markov property and (6),

\[
V_s(z)=\mathbb E_{z,s}
[V_{J_1}(X_1);\tau>1]. \tag{12}
\]

Thus `V` is an exact harmonic function for the killed six-state process.
Furthermore, (7) shows

\[
V_s(z)>0
\]

at every reachable interior state.

The difference `Q=H^+-H` is itself a non-negative phase-harmonic quadratic.
On exits, `-H <= C Q`; optional stopping for `Q` therefore yields

\[
0\le V_s(z)-H_s(z)\le C Q_s(z)=O(1+|z|^2). \tag{13}
\]

Since `H_s(z)=u(z)+O(|z|)`, we obtain, uniformly in every closed subcone of the
quadrant,

\[
V_s(z)=u(z)+O(|z|^2),\qquad V_s(z)/u(z)\to1. \tag{14}
\]

This completes the harmonic-function part of the proof without an unproved
probabilistic ansatz.

## 6. Quadratic martingale correction

The conditional covariance depends on the phase, so the strongest covariance
hypothesis in Denisov--Zhang is not literally satisfied. For a finite phase
chain this dependence is an exact Poisson coboundary.

For each coordinate pair `i,j`, let `C_s^{ij}` be the conditional covariance
in phase `s`. Since the stationary average is `Sigma`, the finite Poisson
equation

\[
(I-P)A^{ij}=C^{ij}-\Sigma_{ij} \tag{15}
\]

has a solution. Therefore

\[
X_k^{(i)}X_k^{(j)}-k\Sigma_{ij}+A^{ij}(J_k) \tag{16}
\]

is a martingale. The correction `A^{ij}` is bounded because the phase space is
finite. This supplies the exact replacement for the quadratic martingales
used in the cone-tail proof.

The exact rational solutions of (15) are checked in `check_model.py`.

## 7. Remaining analytic theorem

The combinatorial conjecture now reduces to the following finite-phase cone
bridge theorem.

> **Finite-phase cone bridge theorem needed here.** Let `(X_k,J_k)` be a
> centered, bounded, irreducible finite-state Markov-additive process in a
> two-dimensional cone, with non-degenerate covariance, a positive killed
> harmonic function `V` satisfying (14), the quadratic Poisson correction
> (15), and the appropriate lattice aperiodicity on its communicating class.
> Then for fixed reachable interior states `(z,s)` and `(w,t)`,
> \[
> \mathbb P_{z,s}(X_N=w,J_N=t,\tau>N)
> \sim c_{s,t}(z,w)N^{-p-d/2},
> \]
> along the admissible lattice period, with `c_{s,t}(z,w)>0`.

For the present chain, (2)--(4) give `p+d/2=4`. Taking
`(z,s)=((3,1),A_1)`, `(w,t)=((1,1),B_3)`, and `N=3n`, the theorem and (1)
would give

\[
G(n)\sim C_1\frac{8^n}{n^4},\qquad C_1>0.
\]

The proof architecture for the boxed theorem is standard but must be written
for finite phases:

1. use the martingale FCLT and bounded Poisson corrections (15)--(16) to obtain
   the cone survival asymptotic `kappa V(z,s) N^{-p/2}` and the conditioned
   Brownian-meander limit;
2. use a lattice local limit theorem for finite-state Markov-additive
   processes for the unrestricted final segment;
3. repeat the decomposition in Denisov--Wachtel's cone local theorem;
4. apply the same argument to the time-reversed phase chain and split at
   `N/2`, obtaining the fixed-endpoint factor `N^{-p-d/2}`.

The first six sections are exact and machine-checked. Step 7 is the sole
remaining theorem; it must not be hidden as an axiom or described as already
proved.

## References

- M. Kauers and D. Zeilberger, *Counting Standard Young Tableaux With
  Restricted Runs*, arXiv:2006.10205.
- D. Denisov and V. Wachtel, *Random Walks in Cones*, Annals of Probability
  43 (2015), 992--1044.
- D. Denisov and J. Zhang, *Markov Chains in the Domain of Attraction of
  Brownian Motion in Cones*, Journal of Theoretical Probability 38 (2025).
- L. Herve and J. Ledoux, *A Local Limit Theorem for Densities of the Additive
  Component of a Finite Markov Additive Process*, Statistics & Probability
  Letters 83 (2013), 2119--2128.
- I. Grama, R. Lauvergnat, and E. Le Page, *Conditioned Local Limit Theorems
  for Random Walks Defined on Finite Markov Chains*, arXiv:1707.06129.
