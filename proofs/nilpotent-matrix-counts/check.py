"""Exact checks for the co-index formula and square-zero lifting. Python 3.9+."""
import csv
import sys
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import product
from math import prod


def gl(q, n):
    return prod(q**n - q**i for i in range(n))


def gaussian(q, n, k):
    return prod(q**n - q**i for i in range(k)) // gl(q, k)


def square_zero_rank(q, n, rank):
    return gaussian(q, n, rank) * gaussian(q, n - rank, rank) * gl(q, rank)


@lru_cache(None)
def square_zero(q, n, length):
    if length == 0 or n == 0:
        return 1
    total = 0
    for r in range(n // 2 + 1):
        weight = square_zero_rank(q, n, r)
        if length >= 2:
            s = n - 2 * r
            exponent = 2 * r * (n - r) * (length - 1) + s**2
            weight *= q**exponent * square_zero(q, s, length - 2)
        total += weight
    return total


def partitions(n, upper):
    if n == 0:
        yield ()
    for k in range(min(n, upper), 0, -1):
        for tail in partitions(n - k, k):
            yield (k,) + tail


def jordan_counts(q, n):
    """Orbit sum by powers of q in the centralizer, using only integer arithmetic."""
    counts = Counter()
    for parts in partitions(n, n):
        columns = [sum(s >= i for s in parts) for i in range(1, parts[0] + 1)]
        exponent = sum(c * c for c in columns)
        invertible_factor = 1
        for multiplicity in Counter(parts).values():
            exponent -= multiplicity * (multiplicity + 1) // 2
            invertible_factor *= prod(q**a - 1 for a in range(1, multiplicity + 1))
        orbit, remainder = divmod(gl(q, n), q**exponent * invertible_factor)
        assert remainder == 0
        counts[parts[0]] += orbit
    return counts


def check_fields():
    for q in (2, 3, 4, 5, 7):
        # Rigorous lower and upper bounds on the infinite product.
        cutoff = 32
        product_upper = prod(1 - Fraction(1, q**a) for a in range(1, cutoff + 1))
        product_lower = product_upper * (1 - Fraction(1, (q - 1)*q**cutoff))
        for n in range(1, 17):
            counts = jordan_counts(q, n)
            assert sum(counts.values()) == q ** (n * (n - 1))
            assert counts[1] + counts[2] == square_zero(q, n, 1)
            for j in range(n):
                bound = Fraction(gl(q, n), (q - 1) * gl(q, j)) * Fraction(q)**((j - 1)**2 - n)
                assert counts[n - j] <= bound
                assert (counts[n - j] == bound) == (2 * j < n)
                finite_mass = Fraction(counts[n - j], q**(n*(n-1)))
                scale = Fraction(q**((j-1)**2), (q-1)*gl(q,j))
                if 2*j < n:
                    assert finite_mass > product_upper * scale
                else:
                    assert finite_mass < product_lower * scale
    print("Sharp bound and finite/limiting probability crossings at q=2,3,4,5,7 and n=1..16.")


def check_polynomial():
    for q in (2, 3, 4, 5):
        for n in range(9):
            degree = n // 2
            path_weight = prod(Fraction(square_zero_rank(q, i, 1), q**(2 * (i - 1)))
                               for i in range(n, 1, -2))
            for parity in (0, 1):
                values = []
                for k in range(degree + 4):
                    e = 2 * k + parity
                    values.append(Fraction(square_zero(q, n, e), q**(n * n * e // 2)))
                for _ in range(degree):
                    values = [b - a for a, b in zip(values, values[1:])]
                assert values == [path_weight] * len(values)
    assert [square_zero(2, 3, e) for e in range(1, 5)] == [22, 1184, 22016, 950272]
    print("Normalized parity polynomials and leading coefficients through dimension eight.")


def direct_ring_count(n, order, add, multiply):
    """Enumerate matrices over a ring with elements encoded by 0,...,order-1."""
    sums = [[add(a, b) for b in range(order)] for a in range(order)]
    products = [[multiply(a, b) for b in range(order)] for a in range(order)]
    def is_square_zero(entries):
        for i in range(n):
            for j in range(n):
                entry = 0
                for k in range(n):
                    entry = sums[entry][products[entries[i * n + k]][entries[k * n + j]]]
                if entry:
                    return False
        return True
    return sum(is_square_zero(a) for a in product(range(order), repeat=n*n))


def polynomial_product(a, b, polynomial):
    """Multiply in F2[t]/polynomial, using coefficient bits."""
    result = 0
    degree = polynomial.bit_length() - 1
    while b:
        if b & 1:
            result ^= a
        b >>= 1
        a <<= 1
        if a >> degree:
            a ^= polynomial
    return result


def check_direct():
    for n, order, factors in (
        (2, 8, [(2, 3)]), (2, 9, [(3, 2)]), (2, 12, [(2, 2), (3, 1)]),
        (3, 3, [(3, 1)]), (3, 4, [(2, 2)]),
    ):
        actual = direct_ring_count(n, order, lambda a,b: (a+b) % order,
                                   lambda a,b: (a*b) % order)
        assert actual == prod(square_zero(p, n, e) for p, e in factors)
    # F2[t]/t^2, F2[t]/t^3, and the field F4 = F2[t]/(t^2+t+1).
    for n, polynomial, q, length in ((3, 0b100, 2, 2), (2, 0b1000, 2, 3),
                                      (3, 0b111, 4, 1)):
        order = q**length
        actual = direct_ring_count(n, order, lambda a,b: a ^ b,
                                   lambda a,b: polynomial_product(a, b, polynomial))
        assert actual == square_zero(q, n, length)
    print("Direct entrywise checks over Z/3, Z/4, Z/8, Z/9, Z/12, F4 and two truncated polynomial rings.")


def check_exhaustive(stream):
    dimensions = []
    for row in csv.reader(stream):
        n, inspected, mod_four, *indices = map(int, row)
        dimensions.append(n)
        assert inspected == 2**(n*n)
        expected = jordan_counts(2, n)
        assert indices == [expected[k] for k in range(1, n+1)]
        assert mod_four == square_zero(2, n, 2)
        print(f"d={n}: {inspected:,} binary matrices; indices {indices}; {mod_four:,} square-zero lifts mod 4.")
    assert dimensions == [1, 2, 3, 4, 5]


if __name__ == "__main__":
    if sys.argv[1:] == ["--exhaustive"]:
        check_exhaustive(sys.stdin)
    elif sys.argv[1:]:
        raise SystemExit("Usage: python3 check.py [--exhaustive < exhaustive-output.csv]")
    check_fields()
    check_polynomial()
    check_direct()
