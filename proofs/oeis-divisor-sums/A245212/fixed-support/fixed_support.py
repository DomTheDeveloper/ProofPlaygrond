"""Exactly classify all positive-exponent solutions of OEIS A245212 on a fixed prime support.

Usage: python3 fixed_support.py 3 5 7 11
A ray (p, factors) represents all m*p**e, e >= 1, with m given by factors.
"""
from argparse import ArgumentParser
from fractions import Fraction
from functools import lru_cache
from itertools import permutations
from math import isqrt, prod


def check_support(primes):
    if len(set(primes)) != len(primes):
        raise ValueError('The support contains a repeated prime.')
    if any(p < 2 or any(p % d == 0 for d in range(2, isqrt(p) + 1)) for p in primes):
        raise ValueError('The support must consist of primes.')


def integer_root_bound(rational, degree):
    """Largest nonnegative integer whose degree-th power is at most rational."""
    numerator = rational.numerator // rational.denominator
    low, high = 0, 1
    while high ** degree <= numerator:
        high *= 2
    while high - low > 1:
        middle = (low + high) // 2
        if middle ** degree <= numerator:
            low = middle
        else:
            high = middle
    return low


def valuation(number, prime):
    count = 0
    while number % prime == 0:
        count += 1
        number //= prime
    return count


@lru_cache(maxsize=32768)
def normalized_sum(p, index):
    power = p ** index
    return Fraction(power - 1, index * power)


def classify(primes):
    primes = tuple(primes)
    check_support(primes)
    if not primes:
        return [()], [], []
    alpha = {p: Fraction(1, p - 1) for p in primes}
    target = 2 * prod(Fraction(p - 1, p) for p in primes)
    points, rays = set(), set()
    visits = [0] * (len(primes) + 1)

    def recurse(remaining, fixed, moment, divsum, minimum):
        count = len(remaining)
        visits[count] += 1
        p = remaining[0]
        if count == 1:
            coefficient = divsum - moment * alpha[p]
            if not coefficient:
                if moment == target:
                    rays.add((p, tuple(sorted(fixed))))
                return
            required = (target - moment) / coefficient
            if required <= 0:
                return
            index = required.denominator // required.numerator
            if index < minimum or index > valuation(required.denominator, p):
                return
            if normalized_sum(p, index) == required:
                points.add(tuple(sorted(fixed + ((p, index - 1),))))
            return
        if moment > target:
            ceiling = moment * sum(alpha[q] for q in remaining) / (moment - target)
            bound = ceiling.numerator // ceiling.denominator
        else:
            ceiling = divsum / (moment * max(alpha[q] for q in remaining))
            bound = integer_root_bound(ceiling, count - 1)
        for index in range(minimum, bound + 1):
            scale = normalized_sum(p, index)
            recurse(remaining[1:], fixed + ((p, index - 1),),
                    moment * (1 - alpha[p] * scale), divsum * scale, index)

    for order in permutations(primes):
        recurse(order, (), Fraction(1), Fraction(1), 2)
    return sorted(points), sorted(rays), visits[1:]


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('primes', nargs='*', type=int)
    args = parser.parse_args()
    points, rays, visits = classify(args.primes)
    print('Support:', tuple(sorted(args.primes)))
    print('Solutions returned as individual exponent tuples:', points)
    print('Unrestricted prime-power rays:', rays)
    print('Visited nodes, ordered by number of remaining exponents:', visits)
