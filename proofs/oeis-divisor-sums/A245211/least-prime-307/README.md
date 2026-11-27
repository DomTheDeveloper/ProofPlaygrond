# A245211 fixed points through least prime 307

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

If a positive integer has a prime divisor at most \(307\), then it satisfies
the A245211 fixed-point equation exactly when it equals \(21\). Consequently
every other fixed point, if one exists, has least prime divisor at least
\(311\).

This is a computer-assisted partial result. It imposes no upper bound on the
integer, its exponents, or its largest prime factor. It does not settle the
global conjecture or establish research priority.

## Exact certificate

The earlier verified layers exhausted all least primes through \(293\),
covering 230,873 ordered exponent patterns. For least prime \(307\), the
exponent-budget inequality

\[
a\prod_{q>307}(e_q+1)\le306
\]

leaves exactly 12,423 further ordered exponent patterns.

Two independent exact programs exhaust the new layer.

* `search_fixed_points.py` uses integer arithmetic, forced prime divisors,
  modular residue filters, and monotone bounds for successive primes. It
  visits 59 search nodes and returns no fixed point.
* `check_fixed_points.py` uses exact rational normalized moments and
  independently bounds or forces each successive prime. It also returns no
  fixed point.

The unique hard exponent pattern is \((9,1,1,1,1,1)\). Its least-prime local
moment factors exactly as

\[
T_9(307)=57427\cdot96823\cdot424967\cdot102818321.
\]

Both programs independently verify this factorization and the primality of
all four factors by deterministic trial division. Their forced appearances
among the five remaining prime slots close the recursion without a solution.

The cumulative count is

\[
230873+12423=243296
\]

ordered exponent patterns through least prime \(307\), with \(21\) the sole
fixed point.

## Reproduce

Run from this directory with Python 3.10 or later.

```sh
python3 -I verify_307.py
```

Expected output:

```text
307 12423 59 [] 12423 []
243,296 exponent patterns through least prime 307; sole fixed point 21.
```

Jaroslav Krizek posed the original conjecture. This certificate extends the
previously published bound through least prime 293 by one complete least-prime
layer.
