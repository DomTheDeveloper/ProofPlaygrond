# A245211 fixed points through least prime 419

Dominic A. Dabish (DomTheDeveloper), 27 November 2026.

Let \(T(n)=\sum_{d\mid n}d\,\tau(d)\). OEIS A245211 asks whether the
positive solutions of \(T(n)=n(\tau(n)+1)\) consist only of \(21\).

## New certified statement

If a positive integer has a prime divisor at most \(419\), then it satisfies
the A245211 fixed-point equation exactly when it equals \(21\). Consequently
every other fixed point, if one exists, has least prime divisor at least
\(421\).

This is a computer-assisted partial result. It imposes no upper bound on the
integer, its exponents, or its largest prime factor. It does not settle the
global conjecture or establish research priority.

## Exact certificate

The earlier verified layers exhausted all least primes through \(409\),
covering 521,121 ordered exponent patterns. At least prime \(419\), the exact
exponent budget leaves 20,895 further ordered exponent patterns.

Two independent exact programs exhaust the new layer. The integer program
visits 137,889 search nodes after exact filters and returns no fixed point.
The independent exact-rational program also returns no fixed point.

The only slow branches are the five orderings of one exponent \(4\) among six
exponents \(1\). Their forcing chain begins with \(2\cdot419+1=839\) and uses

\[
T_4(839)=3\cdot826629447841.
\]

Both programs prove the 12-digit factor prime through the embedded complete
Lucas certificate

\[
826629447841-1=2^5\cdot3\cdot5\cdot7\cdot246020669
\]

with witness 13. No probabilistic primality result is trusted.

The cumulative count is \(521121+20895=542016\) ordered exponent patterns
through least prime \(419\), with \(21\) the sole fixed point.

## Reproduce

Run with Python 3.10 or later:

```sh
python3 -I verify_419.py
```

Expected output:

```text
419 20895 137889 [] 20895 []
542,016 exponent patterns through least prime 419; sole fixed point 21.
```

Jaroslav Krizek posed the original conjecture. This certificate extends the
previously published bound through least prime 409 by one complete least-prime
layer.
