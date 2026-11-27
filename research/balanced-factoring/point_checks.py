"""Exact finite checks of the projective count and quaternion collision formulas."""

from collections import Counter, defaultdict
from itertools import product
from math import gcd, isqrt


def affine_count(n):
    roots = Counter(y * y % n for y in range(n))
    return sum(roots[(x**3 - x) % n] for x in range(n))


def quaternion_mul(left, right):
    a, b, c, d = left
    e, f, g, h = right
    return (a*e - b*f - c*g - d*h, a*f + b*e + c*h - d*g,
            a*g - b*h + c*e + d*f, a*h + b*g - c*f + d*e)


def conjugate(quat):
    a, b, c, d = quat
    return a, -b, -c, -d


def representations(n):
    pairs = defaultdict(list)
    coordinates = range(-isqrt(n), isqrt(n) + 1)
    for a, b in product(coordinates, repeat=2):
        total = a*a + b*b
        if total <= n:
            pairs[total].append((a, b))
    return [left + right for s in range(n + 1)
            for left in pairs[s] for right in pairs[n-s]]


def check_collisions(p, q):
    n = p*q
    reps = representations(n)
    units = representations(1)
    orbits = {min(quaternion_mul(u, a) for u in units) for a in reps}
    size = (p+1)*(q+1)
    assert len(reps) == 8*size and len(orbits) == size
    histogram = Counter(gcd(n, *quaternion_mul(b, conjugate(a)))
                        for a in orbits for b in orbits)
    assert histogram == {1: size*p*q, p: size*q, q: size*p, n: size}
    return size, histogram[p] + histogram[q]


if __name__ == "__main__":
    for p, q in [(3, 7), (7, 11), (7, 19), (11, 23)]:
        n = p*q
        affine = affine_count(n)
        projective = (affine_count(p)+1)*(affine_count(q)+1)
        assert affine == n and projective == affine+1+p+q
        print(f"{n}: {affine} affine points, {projective} projective points")
    for p, q in [(3, 5), (3, 7), (5, 7), (7, 11), (11, 13)]:
        orbits, successes = check_collisions(p, q)
        print(f"{p*q}: {successes} proper gcds in {orbits**2} ordered orbit pairs")
