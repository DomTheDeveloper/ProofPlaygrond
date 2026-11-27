# A245211 fixed points through least prime 317

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

If a positive integer has a prime divisor at most \(317\), then it satisfies
the A245211 fixed-point equation exactly when it equals \(21\). Consequently
every other fixed point, if one exists, has least prime divisor at least
\(331\).

This is a computer-assisted partial result. It imposes no upper bound on the
integer, its exponents, or its largest prime factor. It does not settle the
global conjecture or establish research priority.

## Exact certificate

The earlier verified layers exhausted all least primes through \(313\),
covering 268,642 ordered exponent patterns. For least prime \(317\), the
exponent-budget inequality

\[
a\prod_{q>317}(e_q+1)\le316
\]

leaves exactly 12,913 further ordered exponent patterns.

Two independent exact programs exhaust the new layer.

* `search_fixed_points.py` uses integer arithmetic, forced prime divisors,
  modular residue filters, and monotone bounds for successive primes. It
  visits 699,457 search nodes and returns no fixed point.
* `check_fixed_points.py` uses exact rational normalized moments and
  independently bounds or forces each successive prime. It also returns no
  fixed point.

The cumulative count is

\[
268642+12913=281555
\]

ordered exponent patterns through least prime \(317\), with \(21\) the sole
fixed point.

## Reproduce

Run from this directory with Python 3.10 or later.

```sh
python3 -I verify_317.py
```

Expected output:

```text
317 12913 699457 [] 12913 []
281,555 exponent patterns through least prime 317; sole fixed point 21.
```

Jaroslav Krizek posed the original conjecture. This certificate extends the
previously published bound through least prime 313 by one complete least-prime
layer.
