# Seven-team World Cup polynomial — solution to Doron Zeilberger's 2026 OEIS-donation challenge

## Problem

Let \(F_7(r)\) be the number of \(7\times 7\) matrices \(A=(a_{ij})\) of nonnegative integers such that

- \(a_{ii}=0\) for every \(i\), and
- every row sum and every column sum equals \(r\).

Equivalently, this counts seven labeled teams in a round robin when every team has exactly \(r\) goals for and \(r\) goals against. On June 30, 2026, Doron Zeilberger offered a $100 donation to the OEIS in honor of the first person to compute the polynomial for seven teams.

Challenge page: <https://sites.math.rutgers.edu/~zeilberg/mamarim/mamarimhtml/DIMACS2026.html>

Original World Cup page and GOALS package: <https://sites.math.rutgers.edu/~zeilberg/mamarim/mamarimhtml/worldcup.html>

## Result

Put \(x=r+3\) and \(y=x^2\). Then

\[
F_7(r)=\frac{x(x^2-1)(x^2-4)}{63155442812426442532454400000}\,Q(y),
\]

where

\[
\begin{aligned}
Q(y)={}&606027774191831y^{12}-3685861337229214y^{11}
+37765555858458113y^{10}\\
&+45058773949238216y^9+1570392939902887193y^8
+8739034660779266186y^7\\
&+95377188765692157983y^6+844891531636894661036y^5
+6155573446929541440848y^4\\
&+46788350432653174464576y^3+271550071954942194604032y^2\\
&+1338033873961407109939200y+3154971657218398617600000.
\end{aligned}
\]

The denominator is \(29!/140\). Since
\(x(x^2-1)(x^2-4)=(r+1)(r+2)(r+3)(r+4)(r+5)\), this is a degree-29 polynomial in \(r\).

An especially transparent exact form is the Ehrhart/binomial-basis formula

\[
F_7(r)=\sum_{j=0}^{24}h_j\binom{r+29-j}{29},
\]

where \(h_j=h_{24-j}\) and

\[
(h_0,\ldots,h_{12})=
\begin{aligned}[t]
(&1,1824,1199145,232852850,17547150075,620856948600,\\
&11670877850282,126571440305244,837957254969529,\\
&3521931467666680,9653611080929469,17561784201419010,\\
&21415558464270922).
\end{aligned}
\]

## Exact values used

\[
\begin{array}{c|r}
r&F_7(r)\\\hline
0&1\\
1&1854\\
2&1254330\\
3&269680320\\
4&25099425960\\
5&1261570701636\\
6&39660539404661\\
7&862295098189344\\
8&13926292882237119\\
9&176080027218850650\\
10&1813557723086696790\\
11&15691346140563786336\\
12&116857054129381000771
\end{array}
\]

As a quick independent check, \(F_7(1)=1854\), because a line sum of 1 forces a permutation matrix and the zero diagonal forces a derangement of seven objects.

## Why only thirteen values determine the polynomial

The allowed positions are the 42 edges of \(K_{7,7}\) after deleting a perfect matching. The row/column incidence constraints have rank \(13\), so the associated flow polytope has dimension

\[
42-13=29.
\]

The incidence matrix of a bipartite graph is totally unimodular. Hence the polytope is integral and \(F_7(r)\) is its degree-29 Ehrhart polynomial. Write its Ehrhart series as

\[
\sum_{r\ge0}F_7(r)t^r=\frac{h^*(t)}{(1-t)^{30}}.
\]

An interior integer matrix has every off-diagonal entry at least 1. Subtracting 1 from each of the six allowed entries in every row gives a bijection

\[
\operatorname{int}(rP)\cap\mathbb Z^{42}\longleftrightarrow (r-6)P\cap\mathbb Z^{42}.
\]

Thus the semigroup is Gorenstein of codegree 6. Ehrhart reciprocity gives

\[
h^*(t)=t^{24}h^*(1/t),
\]

so \(h^*\) is palindromic of degree 24. It therefore has only 13 independent coefficients. The values \(F_7(0),\ldots,F_7(12)\) determine them by

\[
h_k=\sum_{i=0}^{k}(-1)^i\binom{30}{i}F_7(k-i),\qquad 0\le k\le12.
\]

This produces the coefficients displayed above and therefore proves the stated polynomial.

Equivalently, Ehrhart reciprocity and the interior translation imply

\[
F_7(-r)=-F_7(r-6).
\]

After centering at \(r=-3\), the polynomial is odd and has roots \(-1,-2,-3,-4,-5\), explaining the compact centered factorization.

## Exact counting recurrence

For the finite values, process rows in an arbitrary order and retain only two sorted multisets of residual column sums:

- \(P\): columns whose paired forbidden-diagonal row has already been processed;
- \(U\): columns whose paired row is still unprocessed.

Let \(C(P,U)\) be the number of completions of any labeled residual problem having these two multisets. This depends only on the multisets because simultaneous permutation of the remaining row/column pairs and arbitrary permutation of processed columns preserves the problem.

If \(q=|U|>0\), sum over all \(q\) possible choices of the next row. If its paired column has residual \(d\), enumerate all allocations of total \(r\) among the other six columns, respecting their residual capacities. Subtract the allocation from the residuals, move the untouched paired column of residual \(d\) from \(U\) to \(P\), sort both multisets, and recurse. Every completed matrix is counted once for each possible first remaining row, so

\[
C(P,U)=\frac1q\sum_{\text{choice of next row}}\ \sum_{\text{legal row allocations}} C(P',U').
\]

The base case is \(C(P,\varnothing)=1\) if every entry of \(P\) is zero and 0 otherwise. The supplied C++ program implements this recurrence with exact integers and groups identical capacities by multinomial multiplicity.

## Verification

1. The recurrence was compared with direct labeled dynamic programming for small \(n,r\).
2. Applying the same recurrence and Ehrhart reconstruction to \(n=6\) reproduces Zeilberger's published degree-19 polynomial coefficient-for-coefficient. See `verify_n6.py`.
3. The two independent forms in `worldcup7_polynomial.py`—the palindromic \(h^*\) binomial form and the centered factorization—agree on all input values and on additional predicted values.

The next values are

\[
F_7(13)=763843960352898954144,
\qquad
F_7(14)=4452841840686426708039.
\]

## Files

- `worldcup7_count.cpp`: exact multiset recurrence.
- `worldcup7_polynomial.py`: exact evaluator and consistency checks.
- `verify_n6.py`: regression against the published six-team answer.
- `counts_n7.csv`: the thirteen values used for reconstruction.
