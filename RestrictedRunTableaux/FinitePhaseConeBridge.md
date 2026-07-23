# Finite-phase cone bridge theorem for the restricted-run chain

This note supplies the analytic transfer used in Section 7 of `Proof.md`.
It is written specifically for a bounded Markov-additive process with a finite
phase space; no claim is made for arbitrary state-dependent Markov chains.

## Theorem

Let `(X_n,J_n)` be a Markov-additive chain on `Z^d x S`, where `S` is finite,
with kernel

\[
 p_{st}(z)=\Pr(J_{n+1}=t,\ X_{n+1}-X_n=z\mid J_n=s).
\]

Assume:

1. the phase chain is irreducible and aperiodic;
2. the jumps are bounded;
3. `E[Delta X | J_n=s]=0` for every phase `s`;
4. the stationary covariance `Sigma` is positive definite;
5. for every coordinate pair there is a bounded phase function `A^{ij}` with
   `(I-P)A^{ij}=C^{ij}-Sigma_ij`, where `C_s` is the conditional covariance;
6. killing is by leaving a Lipschitz star-like cone, possibly with finitely
   many phase-dependent boundary layers of bounded width;
7. the killed chain has a positive harmonic function `V_s(x)` satisfying
   `V_s(x)=u(x)+O(|x|^{p-1})` in every closed subcone, where `u` is the positive
   Brownian cone harmonic of degree `p>=1`;
8. the lattice Fourier kernel has no unit-modulus spectrum outside a finite
   period group.

Then, on each admissible lattice-period class,

\[
\Pr_{x,s}(X_n=y,J_n=t,\tau>n)
 \sim c_{\mathcal L}\,V_s(x)V_t^*(y)n^{-p-d/2}, \tag{1}
\]

for fixed reachable interior `(x,s)` and `(y,t)`. Here `V^*` is the positive
killed harmonic function of the time-reversed Markov-additive chain, and
`c_L>0` depends only on the lattice class and covariance normalization.

## Proof

### 1. Whitening and martingale structure

Apply `Sigma^{-1/2}` to the additive coordinate. The process remains a bounded
martingale additive process and has stationary covariance `I_d`.

For every `i,j`, assumption 5 gives

\[
M_n^{ij}=X_n^{(i)}X_n^{(j)}-n\delta_{ij}+A^{ij}(J_n).
\]

Indeed, conditional on `(X_n,J_n)=(x,s)`, the linear cross terms vanish by
assumption 3 and

\[
E[M_{n+1}^{ij}-M_n^{ij}\mid J_n=s]
=C_s^{ij}-\delta_{ij}+(PA^{ij})_s-A_s^{ij}=0.
\]

Thus the coordinate martingales and all quadratic martingales required in the
cone estimates are available, with only a bounded terminal correction.

The martingale functional central limit theorem applies because the jumps are
bounded, the phase chain is ergodic, and the predictable quadratic variation
satisfies

\[
n^{-1}\langle X\rangle_n\to I_d
\]

in probability by the ergodic theorem. Hence

\[
n^{-1/2}X_{\lfloor nt\rfloor}\Rightarrow B_t.
\]

### 2. Survival asymptotics

The proof of Theorem 2 of Denisov--Zhang, *Markov Chains in the Domain of
Attraction of Brownian Motion in Cones*, uses:

- the Markov property;
- a functional central limit theorem;
- uniform moment and large-deviation bounds for the increments;
- a positive killed harmonic function asymptotic to `u`;
- the martingale identity for `|X_n|^2-dn`.

The first four items hold uniformly over the finite phase space. The fifth is
replaced by

\[
|X_n|^2-dn+a(J_n),
\qquad a=\sum_i A^{ii}, \tag{2}
\]

which is a martingale by Step 1. Every optional-stopping identity in their
proof therefore acquires an error bounded by `2||a||_infinity`. Their stopping
levels are of order `sqrt(n)` and all identities are subsequently divided by
`n` or by a positive power of `n`; the bounded error is `o(1)` and does not
alter any estimate or limiting constant. Bounded jumps make their stochastic
majorization and large-jump remainders immediate. A finite number of
phase-dependent boundary layers changes the distance to the cone boundary by
at most a constant, which is likewise absorbed in their uniform estimates.

Consequently, uniformly for fixed phases and `|x|=o(sqrt(n))`,

\[
\Pr_{x,s}(\tau>n)\sim \varkappa V_s(x)n^{-p/2}, \tag{3}
\]

and, conditionally on survival,

\[
X_n/\sqrt n\Rightarrow
H_0u(z)e^{-|z|^2/2}\,dz. \tag{4}
\]

The same argument applies to the time-reversed kernel

\[
p^*_{ts}(-z)=\frac{\pi_s}{\pi_t}p_{st}(z), \tag{5}
\]

giving `(3)--(4)` with `V^*`.

### 3. Unrestricted finite-phase local limit theorem

For `theta in [-pi,pi]^d`, form the finite Fourier matrix

\[
F(\theta)_{st}=\sum_z p_{st}(z)e^{i\theta\cdot z}.
\]

Near every point of the finite period group, analytic perturbation of the
simple Perron eigenvalue gives

\[
\lambda(\theta)=1-\tfrac12\theta^T\theta+O(|\theta|^3), \tag{6}
\]

after whitening. On the complement of small neighborhoods of the period
group, the spectral radius is strictly less than one. Fourier inversion and
Laplace's method therefore give the lattice local central limit theorem,
uniformly in the finitely many initial and terminal phases:

\[
\Pr_{s}(X_m=v,J_m=t)
= c_{\mathcal L}\pi_t(2\pi m)^{-d/2}
 e^{-|v|^2/(2m)}+o(m^{-d/2}) \tag{7}
\]

on an admissible lattice class, and zero on the other classes. This is the
finite-matrix specialization of the multidimensional Nagaev--Guivarc'h local
limit theorem.

### 4. Conditioned local limit at fluctuation scale

Repeat the proof of Denisov--Wachtel Theorem 5, summing also over the
intermediate phase. Choose `m=floor(epsilon^3 n)` and split at time `n-m`:

\[
\Pr_{x,s}(X_n=y,J_n=t,\tau>n)
=\sum_{z,r}K_{n-m}((x,s),(z,r))K_m((z,r),(y,t)). \tag{8}
\]

For `|z-y|>=epsilon sqrt(n)`, bounded-increment exponential estimates make the
sum negligible compared with `n^{-p/2-d/2}`. If `z` is farther than
`epsilon sqrt(n)` from the cone boundary, replacing the killed second kernel
by the unrestricted kernel costs the same negligible amount. Insert (7) in
the remaining sum, divide the first kernel by (3), and use the conditioned
integral limit (4). Exactly the same Gaussian convolution as in
Denisov--Wachtel yields, uniformly for `y=O(sqrt(n))` away from a vanishing
boundary layer,

\[
\Pr_{x,s}(X_n=y,J_n=t,\tau>n)
\sim c_{\mathcal L}\varkappa V_s(x)n^{-p/2-d/2}
H_0u(y/\sqrt n)e^{-|y|^2/(2n)}. \tag{9}
\]

Their boundary and large-`y` estimates use only (3), bounded jumps, and the
Brownian boundary estimate, so they are unchanged and extend (9) uniformly to
all `y` in the cone.

### 5. Fixed endpoint

Fix `0<a<1`, put `m=floor((1-a)n)`, and split the killed bridge at `n-m`.
By (5),

\[
K_m((z,r),(y,t))
=\frac{\pi_t}{\pi_r}K_m^*((y,t),(z,r)). \tag{10}
\]

Insert the fluctuation-scale local limit (9) for the forward and reversed
kernels. Terms with `|z|>A sqrt(n)` are negligible by (3)--(4). On
`|z|<=A sqrt(n)`, the sum is a Riemann sum and converges to

\[
\int_K u(w)^2e^{-|w|^2/(2a(1-a))}\,dw,
\]

which is finite and strictly positive. The powers contributed by the two
local kernels and the `n^{d/2}` lattice points in the central region combine
to

\[
n^{-(p/2+d/2)}n^{-(p/2+d/2)}n^{d/2}
=n^{-p-d/2}.
\]

This proves (1). Positivity follows from positivity of `V`, `V^*`, the lattice
constant on a reachable class, and the Gaussian integral. QED.

## Specialization to restricted-run tableaux

For the six-state chain in `Proof.md`:

- the jumps are bounded and conditionally centered;
- the phase chain is irreducible and aperiodic because each `B_i` has a
  self-loop;
- the exact covariance is
  `Sigma=(5/9)*[[2,-1],[-1,2]]`;
- the Poisson correctors are rational and checked by `check_model.py`;
- Sections 4--5 of `Proof.md` construct `V` exactly and prove `V~xy(x+y)`;
- whitening gives a wedge angle `pi/3`, hence `p=3`;
- the Fourier period group has three points, so the bridge is evaluated on its
  admissible class `N=3n`.

Equation (1) therefore gives

\[
\Pr((A_1,(3,1))\to(B_3,(1,1)),\tau>3n)
\sim c n^{-4},\qquad c>0.
\]

Using the exact equal-weight identity

\[
\Pr(\text{bridge})=4G(n)/(3\,8^n)
\]

gives

\[
G(n)\sim C_1 8^n/n^4,
\qquad C_1=3c/4>0.
\]

## Sources used in the transfer

- Denisov--Wachtel, *Random Walks in Cones*, especially Theorems 5--6 and
  their proofs by short-time convolution and time reversal.
- Denisov--Zhang, *Markov Chains in the Domain of Attraction of Brownian
  Motion in Cones*, especially Theorem 2; the discussion following Assumption
  (M2) explicitly notes that the exact conditional-covariance assumption can
  be relaxed at the cost of more complicated calculations.
- Herve--Pene, *The Nagaev--Guivarc'h Method via the Keller--Liverani Theorem*,
  for multidimensional local limits of additive functionals of strongly
  ergodic Markov chains.
