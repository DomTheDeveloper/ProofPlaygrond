"""Independent interval/inversion certificate for the exponent-three and -four layers.

The final index is isolated by rigorous bounds on two exponential remainders.
This checker does not use the prime-power divisibility filter in check_layers.py.
"""
from fractions import Fraction as F
from itertools import permutations
from math import lcm, prod


def z(p, index):
    power = p**index
    return F(power-1, index*power)


def cutoff(B, C, remaining, start, target):
    """Return a height H above which the entire ordered tail is excluded."""
    H = start
    while True:
        if B*prod(1-F(1, (p-1)*H) for p in remaining) > target:
            return H
        if B + C/H**len(remaining) < target:
            return H
        if B == target and C*(min(remaining)-1) < B*H**(len(remaining)-1):
            return H
        H *= 2


def direct(B, C, target, q, j, r):
    y = z(q, j)
    const = B*(1-y/(q-1))
    slope = C*y-const/(r-1)
    if slope == 0:
        assert const != target, "equality ray"
        return None
    need = (target-const)/slope
    if need <= 0:
        return None
    k = need.denominator//need.numerator
    # If need = (r^k-1)/(k*r^k), its reduced denominator is at least r^k.
    if j <= k < need.denominator.bit_length() and z(r, k) == need:
        return k
    # r >= 5 throughout, so k >= the bit length cannot be a solution.
    return None


def remaining_indices(B, C, target, q, r, first, stop):
    """Outward bounds for k=(1-r^-k)*D/N, enclosing every k >= j."""
    coeffs = (target-B, B/(q-1), -B/(r-1), C+B/((q-1)*(r-1)))
    common = lcm(*(c.denominator for c in coeffs))
    a, b, c, d = (int(common*x) for x in coeffs)
    Q, R = q**12, r**12
    for j in range(first, stop):
        if j < 12:
            yield j
            continue
        n0, d0 = a*j+b, c*j+d
        n1, d1 = n0*Q-b, d0*Q-d
        if n0*n1 <= 0:
            yield j
            continue
        if n0 < 0:
            n0, d0, n1, d1 = -n0, -d0, -n1, -d1
        if d0*n1 > d1*n0:
            n0, d0, n1, d1 = n1, d1, n0, d0
        # d0/n0 <= (c*j+d*(1-eps))/(a*j+b*(1-eps)) <= d1/n1.
        high = d1//n1
        if high >= j and high*n0*R >= (R-1)*d0:
            yield j


def verify(h, primes):
    t3 = sum((e+1)*3**e for e in range(h+1))
    s3 = sum(3**e for e in range(h+1))
    target = F(2*3**h*(h+1), t3)*prod(F(p-1,p) for p in primes)
    weight = F(s3, t3)
    maximum = cutoff(F(1), weight, primes, 2, target)
    rows = tests = 0
    hits = set()
    for p, q, r in permutations(primes):
        for i in range(2, maximum):
            x = z(p, i)
            B, C = 1-x/(p-1), weight*x
            stop = cutoff(B, C, (q,r), i, target)
            rows += stop-i
            for j in remaining_indices(B, C, target, q, r, i, stop):
                tests += 1
                k = direct(B,C,target,q,j,r)
                if k is not None:
                    hits.add(tuple(sorted(((3,h), (p,i-1), (q,j-1), (r,k-1)))))
    return rows, tests, sorted(hits)


if __name__ == "__main__":
    # The written monotone bounds give these lists independently of the other checker.
    large = (11,13,17,19,23,29,31,37,41,43,47,53,59,61)
    for h, supports in [(3, [(5,7,r) for r in large[:5]]),
                        (4, [(5,7,r) for r in large]+[(5,11,13)])]:
        pairs = leaves = 0
        for S in supports:
            rows, tests, hits = verify(h, S)
            assert hits == [], (h, S, hits)
            pairs += rows
            leaves += tests
            print(h, S, rows, tests, hits, flush=True)
        print("total", h, pairs, leaves, flush=True)
