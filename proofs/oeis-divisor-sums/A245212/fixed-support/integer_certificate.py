"""Independent interval and divisibility certificate for a prescribed prime support."""
from argparse import ArgumentParser
from fractions import Fraction
from functools import lru_cache
from itertools import permutations
from math import isqrt, prod


@lru_cache(maxsize=32768)
def moments(p, exponent):
    power = p ** exponent
    sigma = (p * power - 1) // (p - 1)
    weighted = ((exponent + 1) * p * p * power - (exponent + 2) * p * power + 1) // (p - 1) ** 2
    return power * (exponent + 1), weighted, sigma


def tail_excluded(fixed, remaining, minimum):
    scale, moment, divsum = fixed
    limit_factor = prod(Fraction(p, p - 1) for p in remaining)
    limit = Fraction(moment, scale) * limit_factor
    if limit == 2 and len(remaining) >= 2:
        coefficient = Fraction(divsum, scale) * limit_factor
        if coefficient * (min(remaining) - 1) < 2 * (minimum + 1) ** (len(remaining) - 1):
            return True
    lower, upper_divsum = Fraction(moment, scale), Fraction(divsum, scale)
    for p in remaining:
        d, w, s = moments(p, minimum)
        lower *= Fraction(w, d)
        upper_divsum *= Fraction(s, d)
    return lower > 2 or limit + upper_divsum < 2


def exhaustive(support):
    if len(set(support)) != len(support) or any(
            p < 2 or any(p % d == 0 for d in range(2, isqrt(p) + 1)) for p in support):
        raise ValueError('A support must consist of distinct primes.')
    if not support:
        return [()], [], [], 0
    found, rays = set(), set()
    visits = [0] * (len(support) + 1)
    tests = 0

    def recurse(remaining, fixed, factors, first):
        nonlocal tests
        visits[len(remaining)] += 1
        p = remaining[0]
        scale, moment, divsum = fixed
        if len(remaining) == 1:
            difference = moment - (p - 1) * divsum
            if not difference:
                if 2 * scale == p * divsum:
                    rays.add((p, tuple(sorted(factors))))
                return
            last = 0
            while difference % p == 0:
                difference //= p
                last += 1
            for exponent in range(first, last + 1):
                tests += 1
                d, w, s = moments(p, exponent)
                if moment * w + divsum * s == 2 * scale * d:
                    found.add(tuple(sorted(factors + ((p, exponent),))))
            return
        cutoff = first
        while not tail_excluded(fixed, remaining, cutoff):
            cutoff *= 2
        for exponent in range(first, cutoff):
            local = moments(p, exponent)
            recurse(remaining[1:], tuple(u * v for u, v in zip(fixed, local)),
                    factors + ((p, exponent),), exponent)

    for order in permutations(support):
        recurse(order, (1, 1, 1), (), 1)
    return sorted(found), sorted(rays), visits[1:], tests


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('primes', nargs='*', type=int)
    args = parser.parse_args()
    points, rays, visits, tests = exhaustive(tuple(args.primes))
    print('Support:', tuple(sorted(args.primes)))
    print('Solutions returned as individual exponent tuples:', points)
    print('Unrestricted prime-power rays:', rays)
    print('Visited nodes, ordered by number of remaining exponents:', visits)
    print('Direct tests after valuation bound:', tests)
