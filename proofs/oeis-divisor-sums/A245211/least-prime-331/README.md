# A245211 fixed points through least prime 331

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

If a positive integer has a prime divisor at most \(331\), then it satisfies
the A245211 fixed-point equation exactly when it equals \(21\). Consequently
every other fixed point, if one exists, has least prime divisor at least
\(337\).

This is a computer-assisted partial result. It imposes no upper bound on the
integer, its exponents, or its largest prime factor. It does not settle the
global conjecture or establish research priority.

## Exact certificate

The earlier verified layers exhausted all least primes through \(317\),
covering 281,555 ordered exponent patterns. For least prime \(331\), the
exponent-budget inequality

\[
a\prod_{q>331}(e_q+1)\le330
\]

leaves exactly 14,123 further ordered exponent patterns.

Two independent exact programs exhaust the new layer.

* `search_fixed_points.py` uses integer arithmetic, forced prime divisors,
  modular residue filters, and monotone bounds for successive primes. It
  visits 1,236,946 search nodes and returns no fixed point.
* `check_fixed_points.py` uses exact rational normalized moments and
  independently bounds or forces each successive prime. It also returns no
  fixed point.

The cumulative count is

\[
281555+14123=295678
\]

ordered exponent patterns through least prime \(331\), with \(21\) the sole
fixed point.

## Reproduce

Run from this directory with Python 3.10 or later.

```sh
python3 -I verify_331.py
```

Expected output:

```text
331 14123 1236946 [] 14123 []
295,678 exponent patterns through least prime 331; sole fixed point 21.
```

Jaroslav Krizek posed the original conjecture. This certificate extends the
previously published bound through least prime 317 by one complete least-prime
layer.
