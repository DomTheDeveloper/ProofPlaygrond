# A245211 fixed points through least prime 431

Dominic A. Dabish (DomTheDeveloper), 27 November 2026.

Let \(T(n)=\sum_{d\mid n}d\,\tau(d)\). OEIS A245211 asks whether the
positive solutions of \(T(n)=n(\tau(n)+1)\) consist only of \(21\).

## New certified statement

If a positive integer has a prime divisor at most \(431\), then it satisfies
the A245211 fixed-point equation exactly when it equals \(21\). Consequently
every other fixed point, if one exists, has least prime divisor at least
\(433\).

This is a computer-assisted partial result. It imposes no upper bound on the
integer, its exponents, or its largest prime factor. It does not settle the
global conjecture or establish research priority.

## Exact certificate

The earlier verified layers exhausted all least primes through \(421\),
covering 563,527 ordered exponent patterns. At least prime \(431\), the exact
exponent budget leaves 21,681 further ordered exponent patterns.

Two independent exact programs exhaust the new layer. The integer program
visits 158,685 search nodes after exact filters and returns no fixed point.
The independent exact-rational program also returns no fixed point.

The difficult branches contain either an exponent 21 at 431, an exponent 25
at 431, or an exponent 4 or 21 at the forced prime 863. The certificate gives
complete factorizations of \(T_{21}(431)\), \(T_{25}(431)\),
\(T_4(863)\), and \(T_{21}(863)\), and proves every nontrivial large factor
prime by recursive Lucas certificates. The leaf primes are checked by exact
trial division. No external or probabilistic primality assumption is used.

The cumulative count is \(563527+21681=585208\) ordered exponent patterns
through least prime \(431\), with \(21\) the sole fixed point.

## Reproduce

Run with Python 3.10 or later:

```sh
python3 -I verify_431.py
```

Expected output:

```text
431 21681 158685 [] 21681 []
585,208 exponent patterns through least prime 431; sole fixed point 21.
```

Jaroslav Krizek posed the original conjecture. This certificate extends the
previously published bound through least prime 421 by one complete least-prime
layer.
