# A245211 fixed points through least prime 263

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

If a positive integer has a prime divisor at most \(263\), then it satisfies the A245211 fixed-point equation exactly when it equals \(21\). Consequently every other fixed point, if one exists, has least prime divisor at least \(269\).

This is a computer-assisted partial result. It imposes no upper bound on the integer, its exponents, or its largest prime factor. It does not settle the global conjecture or establish research priority.

## Exact certificate

The earlier verified layers exhausted all least primes through \(257\), covering 159,078 ordered exponent patterns. For least prime \(263\), the exponent-budget inequality

\[
a\prod_{q>263}(e_q+1)\le262
\]

leaves exactly 9,367 further ordered exponent patterns.

Two independent exact programs exhaust the new layer.

* `search_fixed_points.py` uses integer arithmetic, forced prime divisors, modular residue filters, and monotone bounds for successive primes. It visits 93,727 search nodes and returns no fixed point.
* `check_fixed_points.py` uses exact rational normalized moments and independently bounds or forces each successive prime. It also returns no fixed point.

The unique hard exponent pattern is \((13,1,1,1,1)\). Its least-prime local moment has the exact factorization

\[
T_{13}(263)
=214805549993\cdot1883836937069958237217.
\]

Complete Lucas certificates embedded in both programs prove both factors prime. Their required appearances among the four remaining prime slots make the forced-prime recursion terminate without a solution.

The cumulative count is

\[
159078+9367=168445
\]

ordered exponent patterns through least prime \(263\), with \(21\) the sole fixed point.

## Reproduce

Run from this directory with Python 3.10 or later.

```sh
python3 -I verify_263.py
```

Expected output:

```text
263 9367 93727 [] 9367 []
168,445 exponent patterns through least prime 263; sole fixed point 21.
```

Jaroslav Krizek posed the original conjecture. This certificate extends the previously published bound through least prime 257 by one complete least-prime layer.
