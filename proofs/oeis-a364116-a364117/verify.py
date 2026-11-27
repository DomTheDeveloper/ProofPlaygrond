"""Check the written congruences by two evaluations of Bala's Legendre array.

Run with Python 3.9 or newer. Only the standard library is used.
"""

from collections import Counter
from functools import lru_cache
from math import comb, isqrt


@lru_cache(maxsize=None)
def legendre_numerator(n):
    """Coefficients of (1-x)^n P_n((1+x)/(1-x)), by Bonnet's recurrence."""
    if n == 0:
        return (1,)
    if n == 1:
        return (1, 1)
    previous = (0,) + legendre_numerator(n - 1) + (0,)
    older = (0, 0) + legendre_numerator(n - 2) + (0, 0)
    result = []
    for j in range(n + 1):
        first = (2 * n - 1) * (previous[j + 1] + previous[j])
        second = (n - 1) * (older[j + 2] - 2 * older[j + 1] + older[j])
        value, remainder = divmod(first - second, n)
        assert remainder == 0
        result.append(value)
    return tuple(result)


def modular_product(a, b, degree, modulus):
    """Multiply truncated residue polynomials using a carry-free integer encoding."""
    width = ((min(len(a), len(b)) * (modulus - 1) ** 2).bit_length() + 7) // 8

    def encode(poly):
        return int.from_bytes(b''.join(c.to_bytes(width, 'little') for c in poly), 'little')

    count = min(degree + 1, len(a) + len(b) - 1)
    bits = 8 * width * count
    low = ((encode(a) * encode(b)) % (1 << bits)).to_bytes(width * count, 'little')
    return [int.from_bytes(low[start:start + width], 'little') % modulus
            for start in range(0, len(low), width)]


def via_recurrence(row, n, modulus):
    base = [c % modulus for c in legendre_numerator(n)]
    power = row
    product = [1]
    while power:
        if power % 2:
            product = modular_product(product, base, n, modulus)
        power //= 2
        if power:
            base = modular_product(base, base, n, modulus)

    weight = 1
    value = 0
    for h in range(n + 1):
        if n - h < len(product):
            value += weight * product[n - h]
        weight = weight * (n * row + h + 1) // (h + 1)
    return value % modulus


@lru_cache(maxsize=500)
def via_exact_coefficients(row, n):
    """Exact coefficient extraction in the independent variable y=x/(1-x)."""
    f = [comb(n, j) * comb(n + j, j) for j in range(n + 1)]
    b = [1]
    # If B=F^row then F B' = row F' B. Coefficient comparison gives k b_k.
    for k in range(1, n + 1):
        numerator = sum(((row + 1) * j - k) * f[j] * b[k - j]
                        for j in range(1, k + 1))
        coefficient, remainder = divmod(numerator, k)
        assert remainder == 0
        b.append(coefficient)
    return sum(comb(n, j) * c for j, c in enumerate(b))


def valuation(number, prime):
    result = 0
    while number % prime == 0:
        result += 1
        number //= prime
    return result


def verify():
    counts = Counter()

    def checked(row, n, modulus):
        first = via_recurrence(row, n, modulus)
        second = via_exact_coefficients(row, n) % modulus
        assert first == second, (row, n, modulus, first, second)
        return first

    def expect(label, row, n, modulus, expected):
        value = checked(row, n, modulus)
        assert value == expected % modulus, (label, row, n, modulus, value, expected)
        counts[label] += 1

    # OEIS initial terms serve as external checks on the two row conventions.
    for offset, terms in enumerate((
            (1, 3, 73, 5623, 908001, 251831261, 106898093065, 64439674636863),
            (1, 5, 163, 14409, 2511251, 730485013, 320259339415, 197591579213969))):
        for n, term in enumerate(terms):
            assert via_exact_coefficients(n + offset, n) == term
            expect('OEIS initial values', n + offset, n, term + 2, term)

    primes = [p for p in range(3, 48, 2) if all(p % d for d in range(2, isqrt(p) + 1))]
    for p in primes:
        k, size = 1, p
        while size <= 343:
            if p >= 5:
                if k == 1:
                    expect('A364117 prime', p + 1, p, p ** 3, 2 * p + 3)
                expect('A364116 prime powers', size, size, p ** (k + 3), 2 * size + 1)
                n = size - size // p
                expect('A364116 Euler phi indices', n, n, p ** (k + 2), 1)
            expect('A364117 shifted prime powers', size, size - 1, p ** (k + 3), 1)
            for row in (1, 2, p, 2 * p, p ** 2):
                modulus = p ** (3 + valuation(row, p))
                residue = 19 if p == 3 and row % 3 else 1
                expect('shifted row theorem', row, size - 1, modulus, residue)
            k += 1
            size *= p

    for p in (5, 7, 11, 13, 17, 19):
        for m in (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12):
            for row in (1, 2, 3, 4, 5, p, 2 * p, p ** 2):
                modulus = p ** (3 + valuation(row, p))
                lower = checked(row, m, modulus)
                expect('row dilations', row, p * m, modulus, lower)

    assert via_exact_coefficients(3, 3) == 5623
    expect('A364116 counterexample', 3, 3, 81, 34)
    assert 34 != 7
    for label, count in sorted(counts.items()):
        print(f'{label}: {count}')
    print(f'All {sum(counts.values())} checks passed with both coefficient evaluations.')


if __name__ == '__main__':
    verify()
