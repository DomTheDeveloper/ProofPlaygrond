"""Exact local certificates for the divisor-sum bits of a balanced odd semiprime.

Usage: python local_bits.py N [--primes 2 3 5]
The promised factors are distinct odd primes p < q <= 2*p.
Python 3.10 or later, no third-party dependencies.
"""

import argparse
from dataclasses import dataclass
from math import gcd, isqrt


@dataclass(frozen=True)
class Progression:
    first: int
    step: int
    count: int


def midpoint_interval(n):
    root = isqrt(n)
    low = root + int(root * root < n)
    return low, isqrt(9 * n // 8)


def roots_mod_prime_power(value, prime, exponent):
    roots, modulus = [0], 1
    for _ in range(exponent):
        next_modulus = modulus * prime
        roots = [
            r + k * modulus
            for r in roots for k in range(prime)
            if ((r + k * modulus)**2 - value) % next_modulus == 0
        ]
        modulus = next_modulus
    return roots, modulus


def local_classes(n, max_gap_squared, prime):
    """Disjoint classes for positive m^2-n having a square root at this prime."""
    unit_digits = 3 if prime == 2 else 1
    units = [1] if prime == 2 else sorted({k * k % prime for k in range(1, prime)})
    power, valuation = 1, 0
    while power <= max_gap_squared:
        for unit in units:
            roots, modulus = roots_mod_prime_power(
                n + power * unit, prime, valuation + unit_digits
            )
            for root in roots:
                yield root, modulus
        power *= prime * prime
        valuation += 2


def midpoint_progressions(n, primes=(2,)):
    """Exact candidates satisfying the real balance bound and all requested local tests."""
    if n < 3 or n % 2 == 0 or isqrt(n)**2 == n:
        raise ValueError("Expected an odd nonsquare N >= 3.")
    low, high = midpoint_interval(n)
    if high < low:
        return []
    current = [Progression(low, 1, high - low + 1)]
    for prime in sorted(set(primes)):
        if prime < 2 or any(prime % d == 0 for d in range(2, isqrt(prime) + 1)):
            raise ValueError(f"{prime} is not prime.")
        if gcd(prime, n) > 1:
            raise ValueError(f"{prime} divides N; the complementary divisor is {n // prime}.")
        new = []
        for residue, modulus in local_classes(n, high * high - n, prime):
            for row in current:
                index = (residue - row.first) * pow(row.step, -1, modulus) % modulus
                if index < row.count:
                    new.append(Progression(
                        row.first + row.step * index,
                        row.step * modulus,
                        1 + (row.count - 1 - index) // modulus,
                    ))
        current = new
    return current


def floor_sum(count, modulus, slope, intercept):
    """Sum floor((slope*i + intercept)/modulus), 0 <= i < count, for nonnegative inputs."""
    total = 0
    while True:
        quotient, slope = divmod(slope, modulus)
        total += quotient * (count * (count - 1) // 2)
        quotient, intercept = divmod(intercept, modulus)
        total += quotient * count
        height = slope * count + intercept
        if height < modulus:
            return total
        count, intercept = divmod(height, modulus)
        modulus, slope = slope, modulus


def candidate_bit(n, midpoint, i):
    shift = 3 * n.bit_length() + i + 1
    return ((((1 + 2 * midpoint) << shift) - 1) // n) % 2


def bit_counts(n, rows, indices=None):
    counts = []
    if indices is None:
        indices = range(n.bit_length())
    for i in indices:
        scale = 1 << (3 * n.bit_length() + i + 1)
        ones = 0
        for row in rows:
            slope = 2 * row.step * scale
            intercept = (1 + 2 * row.first) * scale - 1
            ones += floor_sum(row.count, n, slope, intercept)
            ones -= 2 * floor_sum(row.count, 2 * n, slope, intercept)
        counts.append(ones)
    return counts


def split_small_list(n, rows, budget):
    size = sum(row.count for row in rows)
    if size > budget:
        return None
    for row in rows:
        for i in range(row.count):
            mid = row.first + row.step * i
            diff2 = mid * mid - n
            d = isqrt(diff2)
            if d * d == diff2 and mid - d > 1:
                return mid - d, mid + d
    return None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("n", type=int)
    parser.add_argument("--primes", nargs="+", type=int, default=[2])
    args = parser.parse_args()
    n = args.n
    if n >= 4 and isqrt(n)**2 == n:
        print(f"Square factorization: {isqrt(n)} * {isqrt(n)}")
        return
    if n > 2 and n % 2 == 0:
        print(f"Even factorization: 2 * {n // 2}")
        return
    try:
        rows = midpoint_progressions(n, args.primes)
    except ValueError as error:
        parser.exit(2, f"{error}\n")
    size = sum(row.count for row in rows)
    print(f"Input length: {n.bit_length()} bits")
    print(f"Candidate midpoints: {size} in {len(rows)} disjoint progressions")
    if size == 0:
        print("The balanced semiprime promise is incompatible with these tests.")
        return
    counts = bit_counts(n, rows)
    profile = "".join("0" if x == 0 else "1" if x == size else "?" for x in counts)
    print(f"Provable replies in order: {profile}")
    print(f"Ambiguous replies: {profile.count('?')} of {len(profile)}")
    budget = n.bit_length()**2
    if size <= budget:
        factors = split_small_list(n, rows, budget)
        if factors:
            print(f"Verified factorization: {factors[0]} * {factors[1]}")
        else:
            print("Square tests exhausted the candidate list without a proper factor pair.")
    else:
        print(f"The candidate count exceeds the {budget}-square-test budget.")


if __name__ == "__main__":
    main()
