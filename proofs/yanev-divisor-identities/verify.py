"""Independent finite checks of the OEIS formulas and Jordan-totient extension."""
from math import gcd, isqrt
from pathlib import Path
import sys


def factor(n):
    factors = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            factors[p] = factors.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        factors[n] = 1
    return factors


def divisors(n):
    small = [d for d in range(1, isqrt(n) + 1) if n % d == 0]
    return small + [n // d for d in reversed(small) if d * d != n]


def unitary(n):
    return sum(p for p, e in factor(n).items() if e == 1)


def jordan(n, r):
    value = n**r
    for p in factor(n):
        value -= value // (p**r)
    return value


def square_checks(n):
    squares = [d for d in divisors(n) if isqrt(d)**2 == d]
    large_divisors = divisors(max(squares))
    for r in (1, 2, 3):
        lhs = sum(jordan(d, r) for d in squares)
        assert lhs * sum(d**r for d in large_divisors) == sum(d**(2*r) for d in large_divisors)
    return sum(jordan(d, 1) for d in squares)


def check_table(path, evaluator):
    pairs = [row.split() for row in path.read_text().splitlines()
             if row.strip() and not row.lstrip().startswith("#")]
    assert all(evaluator(int(i)) == int(a) for i, a in pairs)
    return len(pairs)


if __name__ == "__main__":
    for n in range(1, 301):
        assert unitary(n) == sum(p for p in divisors(n) if p > 1 and len(divisors(p)) == 2
                                 and gcd(p, n//p) == 1)
    for m in range(1, 151):
        for n in range(1, 151):
            assert unitary(m*n) + unitary(gcd(m*m, n)) + unitary(gcd(m, n*n)) == unitary(m) + unitary(n)
    for n in range(1, 16385):
        square_checks(n)
    print("22,500 ordered pairs and 16,384 inputs at three Jordan orders passed.")
    if len(sys.argv) == 3:
        print("A063956 table:", check_table(Path(sys.argv[1]), unitary))
        print("A055210 table:", check_table(Path(sys.argv[2]), square_checks))
