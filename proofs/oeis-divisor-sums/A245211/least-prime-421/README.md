# A245211 fixed points through least prime 421

Dominic A. Dabish (DomTheDeveloper), 27 November 2026.

Let \(T(n)=\sum_{d\mid n}d\,\tau(d)\). OEIS A245211 asks whether the
positive solutions of \(T(n)=n(\tau(n)+1)\) consist only of \(21\).

## New certified statement

If a positive integer has a prime divisor at most \(421\), then it satisfies
the A245211 fixed-point equation exactly when it equals \(21\). Consequently
every other fixed point, if one exists, has least prime divisor at least
\(431\).

This is a computer-assisted partial result. It imposes no upper bound on the
integer, its exponents, or its largest prime factor. It does not settle the
global conjecture or establish research priority.

## Exact certificate

The earlier verified layers exhausted all least primes through \(419\),
covering 542,016 ordered exponent patterns. At least prime \(421\), the exact
exponent budget leaves 21,511 further ordered exponent patterns.

Two independent exact programs exhaust the new layer. The integer program
visits 14,739 search nodes after exact filters and returns no fixed point. The
independent exact-rational program also returns no fixed point. No new
external or probabilistic primality assumption is used.

The cumulative count is \(542016+21511=563527\) ordered exponent patterns
through least prime \(421\), with \(21\) the sole fixed point.

## Reproduce

Run with Python 3.10 or later:

```sh
python3 -I verify_421.py
```

Expected output:

```text
421 21511 14739 [] 21511 []
563,527 exponent patterns through least prime 421; sole fixed point 21.
```

Jaroslav Krizek posed the original conjecture. This certificate extends the
previously published bound through least prime 419 by one complete least-prime
layer.
