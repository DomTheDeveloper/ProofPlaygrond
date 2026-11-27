# A245211 fixed points through least prime 313

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

If a positive integer has a prime divisor at most \(313\), then it satisfies
the A245211 fixed-point equation exactly when it equals \(21\). Consequently
every other fixed point, if one exists, has least prime divisor at least
\(317\).

This is a computer-assisted partial result. It imposes no upper bound on the
integer, its exponents, or its largest prime factor. It does not settle the
global conjecture or establish research priority.

## Exact certificate

The earlier verified layers exhausted all least primes through \(311\),
covering 255,837 ordered exponent patterns. For least prime \(313\), the
exponent-budget inequality

\[
a\prod_{q>313}(e_q+1)\le312
\]

leaves exactly 12,805 further ordered exponent patterns.

Two independent exact programs exhaust the new layer.

* `search_fixed_points.py` uses integer arithmetic, forced prime divisors,
  modular residue filters, and monotone bounds for successive primes. It
  visits 28 search nodes and returns no fixed point.
* `check_fixed_points.py` uses exact rational normalized moments and
  independently bounds or forces each successive prime. It also returns no
  fixed point.

The only initially unresolved exponent pattern is
\((13,1,1,1,1)\). Both programs independently verify

\[
T_{13}(313)
=3\cdot1295309273607968370700398258494227.
\]

The large factor is certified prime by Lucas's criterion. Its predecessor
factors completely as

\[
2\cdot3\cdot685093\cdot6144547567\cdot51284105359262441,
\]

with witness 2. The final large auxiliary prime has

\[
51284105359262441-1
=2^3\cdot5\cdot7\cdot23\cdot1032841\cdot7710161
\]

and Lucas witness 3. The remaining factors are checked by deterministic trial
division. These certificates force the large prime into a remaining
prime-power component and close the hard pattern exactly.

The cumulative count is

\[
255837+12805=268642
\]

ordered exponent patterns through least prime \(313\), with \(21\) the sole
fixed point.

## Reproduce

Run from this directory with Python 3.10 or later.

```sh
python3 -I verify_313.py
```

Expected output:

```text
313 12805 28 [] 12805 []
268,642 exponent patterns through least prime 313; sole fixed point 21.
```

Jaroslav Krizek posed the original conjecture. This certificate extends the
previously published bound through least prime 311 by one complete least-prime
layer.
