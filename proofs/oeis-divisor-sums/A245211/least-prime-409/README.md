# A245211 fixed points through least prime 409

Dominic A. Dabish (DomTheDeveloper), 27 November 2026.

Let \(T(n)=\sum_{d\mid n}d\,\tau(d)\). OEIS A245211 asks whether the
positive solutions of \(T(n)=n(\tau(n)+1)\) consist only of \(21\).

## New certified statement

If a positive integer has a prime divisor at most \(409\), then it satisfies
the A245211 fixed-point equation exactly when it equals \(21\). Consequently
every other fixed point, if one exists, has least prime divisor at least
\(419\).

This is a computer-assisted partial result. It imposes no upper bound on the
integer, its exponents, or its largest prime factor. It does not settle the
global conjecture or establish research priority.

## Exact certificate

The earlier verified layers exhausted all least primes through \(401\),
covering 500,622 ordered exponent patterns. At least prime \(409\), the exact
exponent budget leaves 20,499 further ordered exponent patterns.

Two independent exact programs exhaust the new layer. The integer program
visits 121 search nodes after exact filters and returns no fixed point. The
independent exact-rational program also returns no fixed point.

The sole difficult exponent shape is \((12,1,1,1,1,1)\). Both programs prove
inside the certificate that

\[
T_{12}(409)=285498811742277931917137438827867
\]

is prime, using a complete recursive Lucas chain. No probabilistic primality
test is trusted.

The cumulative count is \(500622+20499=521121\) ordered exponent patterns
through least prime \(409\), with \(21\) the sole fixed point.

## Reproduce

Run with Python 3.10 or later:

```sh
python3 -I verify_409.py
```

Expected output:

```text
409 20499 121 [] 20499 []
521,121 exponent patterns through least prime 409; sole fixed point 21.
```

Jaroslav Krizek posed the original conjecture. This certificate extends the
previously published bound through least prime 401 by one complete least-prime
layer.
