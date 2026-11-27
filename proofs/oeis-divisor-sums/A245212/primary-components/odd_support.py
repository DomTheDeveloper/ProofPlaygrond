"""Find the smallest product of p/(p-1) above 2 on at most four odd primes."""
from fractions import Fraction
from math import isqrt, prod


def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def crossings(prefix=(), ratio=Fraction(1), remaining=4):
    if ratio > 2:
        yield ratio, prefix
        return
    if not remaining:
        return
    assert ratio < 2  # The numerator of every product on odd primes is odd.
    p = prefix[-1] + 2 if prefix else 3
    while ratio * Fraction(p, p - 1) ** remaining > 2:
        if prime(p):
            yield from crossings(prefix + (p,), ratio * Fraction(p, p - 1), remaining - 1)
        p += 2


if __name__ == "__main__":
    rows = list(crossings())
    best = min(ratio for ratio, _ in rows)
    supports = [s for value, s in rows if value == best]
    assert (best, supports) == (Fraction(12801, 6400), [(3, 5, 17, 251)])
    assert prod(Fraction(p, p - 1) for p in supports[0]) == best
    assert 1 - 2 / best == Fraction(1, 12801)
    print(len(rows), "first-crossing supports;", best, supports)
