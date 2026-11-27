# A245211 fixed points through least prime 257

Dominic A. Dabish (DomTheDeveloper), 26 November 2026.

Let

\[
T(n)=\sum_{d\mid n}d\,\tau(d).
\]

OEIS A245211 asks whether the positive solutions of

\[
T(n)=n(\tau(n)+1)
\]

consist only of `21`. The earlier certificate exhausts every possible exponent pattern when the least prime divisor is at most `251`.

## New certified statement

If a positive integer has a prime divisor at most `257`, then it satisfies the A245211 fixed-point equation exactly when it equals `21`. Consequently every other fixed point, if one exists, has least prime divisor at least `263`.

This is a computer-assisted partial result. It imposes no upper bound on the integer or on any exponent.

## Exact certificate

For least prime `257`, the exponent budget inequality

\[
a\prod_{q>257}(e_q+1)\le256
\]

leaves exactly `9,229` ordered exponent patterns. Two independent programs exhaust all of them.

* `search_fixed_points.py` uses integer arithmetic, forced prime divisors, modular residue filters and monotone bounds for each successive prime. It visits `376,878` search nodes and returns no fixed point.
* `check_fixed_points.py` uses exact rational normalized moments and independently bounds or forces each successive prime. It also returns no fixed point.

The two programs and their completeness argument are in the adjacent [`extension`](../extension) directory. They previously established the bound through `251`. The verifier here calls both unchanged programs at `257` and checks their exact agreement.

The cumulative count is

\[
149,849+9,229=159,078
\]

ordered exponent patterns through least prime `257`, with `21` the sole fixed point.

## Reproduce

Run from this directory with Python 3.10 or later.

```sh
python3 -I verify_257.py
```

Expected final line:

```text
257 9229 376878 [] 9229 []
159,078 exponent patterns through least prime 257; sole fixed point 21.
```

Jaroslav Krizek posed the original conjecture. The product identity and exponent-budget argument were established in the earlier certificate. This note extends that computation by one least-prime layer. Global uniqueness and research priority remain open.
