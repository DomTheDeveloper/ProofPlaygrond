# Asymptotic integral rounding for checkerboard packings in finitely many directions

**Status:** complete proof draft, subject to ordinary expert review  
**Date:** 15 July 2026

## Main theorem

Let \(I_4(n,\varepsilon)\) be the largest subset of the parity class
\[
C_\varepsilon=\{(x,y)\in\{0,\dots,n-1\}^2:x+y\equiv\varepsilon\pmod2\}
\]
that contains at most two points on every row, column, slope-\(+1\) diagonal, and slope-\(-1\) diagonal. Let \(L_4(n,\varepsilon)\) be the corresponding fractional packing optimum. Let
\[
\alpha=1.576823396873808\ldots
\]
be the middle root of
\[
401\alpha^3-1744\alpha^2+2240\alpha-768=0.
\]
Using the exact continuum primal certificate and the continuum-to-finite transfer from the companion verification package, one has, in each of the odd-fat, odd-thin, and even symmetry types,
\[
L_4(n,\varepsilon)=\alpha n+o(n).
\]
The theorem proved here is
\[
\boxed{I_4(n,\varepsilon)=L_4(n,\varepsilon)-o(n)=\alpha n+o(n).}
\]
Thus the four-direction fractional relaxation has asymptotically zero additive integrality gap.

This does **not** prove the full checkerboard no-three-in-line lower bound, because lines of all other slopes remain uncontrolled.

---

## 1. Kahn's bounded-rank edge-colouring theorem

We use the following standard consequence of Kahn's asymptotically good list-colouring theorem.

> **Kahn edge-colouring theorem.** For every fixed rank bound \(k\) and every \(\epsilon>0\), there are \(\delta>0\) and \(D_0\) such that every hypergraph \(G\) with edge size at most \(k\), maximum degree at most \(D\ge D_0\), and maximum pair-codegree at most \(\delta D\), has chromatic index at most \((1+\epsilon)D\).

Equivalently, its edges can be partitioned into at most \((1+\epsilon)D\) matchings.

---

## 2. Diffuse capacitated matching rounding

### Theorem 2.1

Fix integers \(r,b,C\). Let \(H_n=(V_n,E_n)\) be finite hypergraphs satisfying:

1. every edge has size at most \(r\);
2. every vertex \(v\) has an integral capacity \(1\le b_v\le b\);
3. every pair of distinct vertices belongs together to at most \(C\) edges.

Let \(x^{(n)}=(x_e)_{e\in E_n}\) be fractional capacitated matchings:
\[
x_e\ge0,\qquad \sum_{e\ni v}x_e\le b_v.
\]
Assume
\[
\eta_n:=\max_e x_e\longrightarrow0
\]
and
\[
W_n:=\sum_e x_e=\Theta(s_n)
\]
for some \(s_n\to\infty\). Then there are sets of distinct edges \(M_n\subseteq E_n\) such that
\[
|M_n|\ge W_n-o(s_n),
\qquad
|\{e\in M_n:v\in e\}|\le b_v
\]
for every \(v\).

### Proof

Choose a sequence \(t_n\to\infty\) slowly enough that Kahn's theorem with rank \(r+2\) and error \(1/t_n\) applies whenever the codegree ratio is at most \(C\eta_n+o(1)\). This is possible by a diagonal argument because \(\eta_n\to0\).

Choose an integer \(N=N(n)\to\infty\) so large that
\[
\frac{|E_n|}{N}=o(s_n)
\]
and that the degree threshold in Kahn's theorem is met. Put
\[
m_e=\lfloor Nx_e\rfloor.
\]
Then
\[
\sum_e m_e\ge NW_n-|E_n|=NW_n-o(Ns_n).
\tag{2.1}
\]

For each original vertex \(v\), create \(b_v\) clones
\[
v^{(1)},\dots,v^{(b_v)}.
\]
There are
\[
M_v:=\sum_{e\ni v}m_e\le Nb_v
\]
copy-incidences at \(v\). Distribute these copy-incidences among the \(b_v\) clones as evenly as possible. Hence every clone has degree at most
\[
\left\lceil\frac{M_v}{b_v}\right\rceil\le N.
\tag{2.2}
\]

For every original edge \(e\), create one identity vertex \(z_e\). For every copy \(j\in\{1,\dots,m_e\}\), create one private dummy vertex \(d_{e,j}\). The blown-up edge corresponding to copy \((e,j)\) consists of:

- the assigned clone of every original vertex in \(e\);
- the identity vertex \(z_e\);
- the private dummy vertex \(d_{e,j}\).

Call the resulting simple hypergraph \(\widetilde H_n\). Its rank is at most \(r+2\). By (2.2), every constraint clone has degree at most \(N\). Also
\[
\deg(z_e)=m_e\le N\eta_n,
\]
and every dummy has degree one. Thus
\[
\Delta(\widetilde H_n)\le N
\]
for all sufficiently large \(n\).

For pair-codegrees, two constraint clones arising from distinct original vertices can occur together only in copies of original edges containing that pair. There are at most \(C\) such original edges, and each contributes at most \(\max_e m_e\). Pairs involving an identity vertex have the same bound, while every other nonzero pair-codegree is at most one. Therefore
\[
\Delta_2(\widetilde H_n)
\le C N\eta_n+C+1=o(N).
\tag{2.3}
\]

Kahn's theorem now gives
\[
\chi'(\widetilde H_n)\le(1+o(1))N.
\]
Partition the blown-up edges into that many matchings. By (2.1), one colour class \(\widetilde M_n\) has size at least
\[
\frac{NW_n-o(Ns_n)}{(1+o(1))N}
=W_n-o(s_n).
\]

Project every blown-up edge in \(\widetilde M_n\) to its original edge. The identity vertices ensure that two copies of the same original edge cannot belong to one matching, so the projection is injective. Each clone is used at most once, so at most \(b_v\) projected edges contain the original vertex \(v\). The projected set is the desired \(M_n\). \(\square\)

---

## 3. Diffuse finite checkerboard fractional solutions

The exact continuum lower certificate gives a feasible measure of mass \(\alpha\). Its smooth-interior approximation lemma says that for every \(j\) there is a bounded smooth density \(\rho_j\), compactly supported in the interior of the continuum triangle, with mass at least \(\alpha-1/j\) and with both paired projection densities bounded by four.

For each fixed \(j\), sample \(\rho_j\) on a sufficiently fine odd-fat or odd-thin mesh. After a factor \(1-o_j(1)\), this gives a feasible reduced primal solution of value
\[
(\alpha-1/j)n-o_j(n).
\]
Because \(\rho_j\) is bounded, every reduced point-orbit variable is \(O_j(1/n)\).

Unfold a reduced solution to the original parity class as follows. For every point orbit \(O\), divide its reduced mass equally among the points in \(O\). By symmetry, every line in a fixed line orbit receives the same load. The reduced primal constraint for that line orbit is exactly the sum of the capacities of all lines in the orbit; therefore every individual row, column, and principal diagonal has load at most two. Since the sampled density is supported away from the boundary, all used point orbits have a fixed positive orbit size, and the maximum unfolded point mass remains \(O_j(1/n)\).

Choose \(j=j(n)\to\infty\) sufficiently slowly that all Riemann-sum errors have already become small. This diagonal choice gives point-level fractional solutions \(x^{(n)}\) satisfying
\[
\sum_p x_p^{(n)}=\alpha n-o(n),
\qquad
\max_p x_p^{(n)}=o(1).
\tag{3.1}
\]
The even case follows by embedding the odd-fat parity class of the \((2m-1)\times(2m-1)\) grid into a parity class of the \(2m\times2m\) grid.

---

## 4. Application to the four principal directions

Create one hypergraph vertex for every row, column, slope-\(+1\) diagonal, and slope-\(-1\) diagonal meeting the parity class. Every checkerboard point is a hyperedge containing its four incident lines. The rank is four.

Two distinct line constraints lie together in at most one point-edge: parallel lines never meet, while nonparallel lines meet in at most one grid point. Thus Theorem 2.1 applies with \(r=4\), \(b=2\), and \(C=1\) to the diffuse solution (3.1). It produces a set of distinct checkerboard points satisfying all four line capacities and having size
\[
\alpha n-o(n).
\]
Hence
\[
I_4(n,\varepsilon)\ge\alpha n-o(n).
\]
The fractional upper bound already gives
\[
I_4(n,\varepsilon)\le L_4(n,\varepsilon)=\alpha n+o(n).
\]
Therefore
\[
\boxed{I_4(n,\varepsilon)=L_4(n,\varepsilon)-o(n)=\alpha n+o(n).}
\]

---

## 5. Fixed finite direction systems

The same proof gives the following general result.

> **Corollary 5.1.** Fix finitely many pairwise distinct line directions and fixed integral capacities. Any diffuse fractional packing of total mass \(W_n=\Theta(n)\) can be rounded to a distinct integral point set of size \(W_n-o(n)\), preserving every prescribed line capacity.

The incidence hypergraph has fixed rank equal to the number of directions, and any pair of line constraints meets in at most one point.

Thus no fixed finite collection of slopes can create a linear fractional-to-integral gap. The essential difficulty of the genuine no-three-in-line problem is the growing number of relevant directions.

---

## 6. A rigorous obstruction to independent all-slope rounding

Suppose a smooth sampled density is bounded below by \(c/n\) on the lattice points of a fixed open rectangle and above by \(C/n\) everywhere. Under independent Bernoulli rounding, the expected number of selected collinear triples is
\[
\Theta(n\log n).
\]

Indeed, group primitive directions into dyadic shells \(T\le\max(|a|,|b|)<2T\). Each shell contains \(\Theta(T^2)\) primitive directions. For each such direction, a positive proportion of the lines crossing the rectangle contain \(\Theta(n/T)\) eligible same-parity points, and there are \(\Theta(nT)\) such lines. Hence the shell contains \(\Theta(n^4)\) eligible collinear triples. Multiplication by probabilities of order \(n^{-3}\) gives \(\Theta(n)\) expected selected triples per dyadic shell. Summing over \(\Theta(\log n)\) shells gives the claim.

Therefore independent rounding plus a naive one-conflict-at-a-time deletion cannot yield the needed \(o(n)\) loss. A successful all-slope proof must correlate choices across slope scales.

---

## 7. Honest endpoint

The proof above fully establishes the integral four-direction limit. It does **not** establish
\[
D_{\mathrm{mono}}(n)\ge(\alpha-o(1))n.
\]
Finishing the full checkerboard conjecture requires a genuinely new growing-rank or multiscale conflict-avoidance theorem. The fixed-direction integrality gap is now eliminated; the remaining obstruction is precisely all-slope collinearity.

## References

1. J. Kahn, *Asymptotically Good List-Colorings*, Journal of Combinatorial Theory, Series A 73 (1996), 1-59.
2. N. Pippenger and J. Spencer, *Asymptotic Behavior of the Chromatic Index for Hypergraphs*, Journal of Combinatorial Theory, Series A 51 (1989), 24-42.
3. T. Prellberg, *No-three-in-line sets on the checkerboard grid*, arXiv:2605.09215 (2026).
