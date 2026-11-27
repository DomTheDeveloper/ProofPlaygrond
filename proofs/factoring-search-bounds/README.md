# Bounds for integer factorization searches

`FactorizationThreshold.lean` proves that at most twice the floor of the binary logarithm of a positive input many bounded-divisor queries suffice to recover its prime factorization. The sequential factorial implementation exceeds every fixed polynomial in the bit length on arbitrarily large prime squares. The accompanying references identify the classical search reduction and factorial test.

`FactoringSearchBounds.lean` counts remainder tests for trial division and candidate midpoints for Fermat’s method. `FactorRatioBounds.lean` bounds the error and the number of candidate factors covered by a finite collection of estimates for the ratio of two factors. A general polynomial-time algorithm would require a separate construction of sufficiently accurate estimates within a polynomial budget.

The first two files check with Lean 4.19.0 and the standard library, using `lean <filename>`. The ratio file checks with the Lean 4.33.1 mathlib environment from Formal Conjectures, using `lake env lean <filename>`.
