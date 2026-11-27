# A245211 fixed points through least prime 401

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

If a positive integer has a prime divisor at most \(401\), then it satisfies
the A245211 fixed-point equation exactly when it equals \(21\). Consequently
every other fixed point, if one exists, has least prime divisor at least
\(409\).

This is a computer-assisted partial result. It imposes no upper bound on the
integer, its exponents, or its largest prime factor. It does not settle the
global conjecture or establish research priority.

## Exact certificate

The earlier verified layers exhausted all least primes through \(397\),
covering 480,557 ordered exponent patterns. For least prime \(401\), the
exponent-budget inequality

\[
a\prod_{q>401}(e_q+1)\le400
\]

leaves exactly 20,065 further ordered exponent patterns.

Two independent exact programs exhaust the new layer.

* `search_fixed_points.py` uses integer arithmetic, forced prime divisors,
  modular residue filters, and monotone bounds for successive primes. It
  visits 244 search nodes after exact filters and returns no fixed point.
* `check_fixed_points.py` uses exact rational normalized moments and
  independently bounds or forces each successive prime. It also returns no
  fixed point.

The sole difficult exponent shape is \((25,1,1,1,1)\). Both programs verify
the exact factorization

\[
T_{25}(401)=2777\cdot2498137\cdot44854364709863143\cdot
10037566653262838460593813688652541806393.
\]

The two large factors and the necessary recursive factors are proved prime
inside each program by complete Lucas certificates; no probabilistic
primality test is trusted by the certificate.

The cumulative count is

\[
480557+20065=500622
\]

ordered exponent patterns through least prime \(401\), with \(21\) the sole
fixed point.

## Reproduce

Run from this directory with Python 3.10 or later.

```sh
python3 -I verify_401.py
```

Expected output:

```text
401 20065 244 [] 20065 []
500,622 exponent patterns through least prime 401; sole fixed point 21.
```

Jaroslav Krizek posed the original conjecture. This certificate extends the
previously published bound through least prime 397 by one complete least-prime
layer.
