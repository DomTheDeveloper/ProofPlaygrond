# A245211 fixed points through least prime 433

@DomTheDeveloper, 27 November 2026.

Let \(T(n)=\sum_{d\mid n}d\,\tau(d)\). OEIS A245211 asks whether the
positive solutions of \(T(n)=n(\tau(n)+1)\) consist only of \(21\).

## New certified statement

If a positive integer has a prime divisor at most \(433\), then it satisfies
the A245211 fixed-point equation exactly when it equals \(21\). Consequently
every other fixed point, if one exists, has least prime divisor at least
\(439\).

This is a computer-assisted partial result. It imposes no upper bound on the
integer, its exponents, or its largest prime factor. It does not settle the
global conjecture or establish research priority.

## Exact certificate

The earlier verified layers exhausted all least primes through \(431\),
covering 585,208 ordered exponent patterns. At least prime \(433\), the exact
exponent budget leaves 23,217 further ordered exponent patterns.

Two independent exact programs exhaust the new layer. The integer program
visits 2,959,613 search nodes after exact filters and returns no fixed point.
The independent exact-rational program also returns no fixed point.

The difficult branches have exponent 4 at 433. The certificate proves the
complete factorization
\[
T_4(433)=3\cdot 58695306629
\]
and proves both \(58695306629\) and its forced successor
\(117390613259=2\cdot58695306629+1\) prime by recursive Lucas certificates.
The remaining exponent-21 and exponent-24 placements are then exhausted by
the two independent exact searches. Leaf primes are checked by exact trial
division; no external or probabilistic primality assumption is used.

The cumulative count is \(585208+23217=608425\) ordered exponent patterns
through least prime \(433\), with \(21\) the sole fixed point.

## Reproduce

Run with Python 3.10 or later:

```sh
python3 -I verify_433.py
```

Expected output:

```text
433 23217 2959613 [] 23217 []
608,425 exponent patterns through least prime 433; sole fixed point 21.
```

Jaroslav Krizek posed the original conjecture. This certificate extends the
previously published bound through least prime 431 by one complete least-prime
layer.
