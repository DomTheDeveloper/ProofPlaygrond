# A245211 fixed points through least prime 283

Dominic A. Dabish (DomTheDeveloper), 27 November 2026.

Let

\[
T(n)=\sum_{d\mid n} d\,\tau(d).
\]

OEIS A245211 asks whether the positive solutions of

\[
T(n)=n(\tau(n)+1)
\]

consist only of \(21\).

## New certified statement

If a positive integer has a prime divisor at most \(283\), then it satisfies
the A245211 fixed-point equation exactly when it equals \(21\). Consequently
every other fixed point, if one exists, has least prime divisor at least
\(293\).

This is a computer-assisted partial result. It imposes no upper bound on the
integer, its exponents, or its largest prime factor. It does not settle the
global conjecture or establish research priority.

## Exact certificate

The earlier verified layers exhausted all least primes through \(281\),
covering 208,701 ordered exponent patterns. For least prime \(283\), the
exponent-budget inequality

\[
a\prod_{q>283}(e_q+1)\le282
\]

leaves exactly 10,483 further ordered exponent patterns.

Two independent exact programs exhaust the new layer.

* `search_fixed_points.py` uses integer arithmetic, forced prime divisors,
  modular residue filters, and monotone bounds for successive primes. It
  visits 401,419 search nodes and returns no fixed point.
* `check_fixed_points.py` uses exact rational normalized moments and
  independently bounds or forces each successive prime. It also returns no
  fixed point.

The unique hard exponent pattern is \((13,1,1,1,1)\). Its least-prime local
moment factors exactly as

\[
T_{13}(283)
=3^2\cdot33311847537949\cdot3498950330708810221.
\]

Here \(\tau(n)+1=14\cdot2^4+1=225\), so the factor \(3^2\) cancels in the
normalized equation and the two large factors are forced into remaining prime
slots. Complete Lucas certificates embedded independently in both programs
prove the two large factors prime and close the forced-prime recursion.

The cumulative count is

\[
208701+10483=219184
\]

ordered exponent patterns through least prime \(283\), with \(21\) the sole
fixed point.

## Reproduce

Run from this directory with Python 3.10 or later.

```sh
python3 -I verify_283.py
```

Expected output:

```text
283 10483 401419 [] 10483 []
219,184 exponent patterns through least prime 283; sole fixed point 21.
```

Jaroslav Krizek posed the original conjecture. This certificate extends the
previously published bound through least prime 281 by one complete least-prime
layer.
