"""Check the finite part of the four divisor-sum classifications using exact arithmetic."""
from fractions import Fraction
from json import loads
from math import isqrt, prod
from pathlib import Path


def first_primes(count: int) -> list[int]:
    primes = []
    n = 2
    while len(primes) < count:
        if all(n % d for d in range(2, isqrt(n) + 1)):
            primes.append(n)
        n += 1
    return primes


def cutoff(power: int) -> tuple[int, int]:
    # Necessity: n < (n/phi(n))**(power + 2). The proof is in README.md.
    if power < 1:
        raise ValueError('The power must be a positive integer')
    exponent = power + 2
    excluded_rank = 2 * exponent - 1
    primorial = 1
    ratio = Fraction(1)
    for rank, p in enumerate(first_primes(excluded_rank), start=1):
        previous_ratio = ratio
        primorial *= p
        factor = Fraction(p, p - 1)
        ratio *= factor
        if rank == excluded_rank or (primorial >= ratio**exponent and p >= factor**exponent):
            # The factorial bound guarantees the last rank. The prime test can stop earlier.
            limit = previous_ratio**exponent
            return rank, (limit.numerator - 1) // limit.denominator
    raise ArithmeticError('No cutoff established')


def divisor_sieve(limit: int, power: int) -> tuple[list[int], list[int]]:
    phi = list(range(limit + 1))
    sigma = [0] * (limit + 1)
    for d in range(1, limit + 1):
        term = d**power
        for multiple in range(d, limit + 1, d):
            sigma[multiple] += term
        if d >= 2 and phi[d] == d:
            for multiple in range(d, limit + 1, d):
                phi[multiple] -= phi[multiple] // d
    return phi, sigma


def by_factorization(n: int, power: int) -> tuple[int, int]:
    remaining = n
    phi, sigma = 1, 1
    p = 2
    while p * p <= remaining:
        if remaining % p == 0:
            exponent = 0
            while remaining % p == 0:
                remaining //= p
                exponent += 1
            phi *= (p - 1) * p**(exponent - 1)
            sigma *= sum(p**(power * j) for j in range(exponent + 1))
        p += 1
    if remaining > 1:
        phi *= remaining - 1
        sigma *= 1 + remaining**power
    return phi, sigma


def main() -> None:
    expected = loads(Path(__file__).with_name('oeis-lists.json').read_text())
    for r in range(1, 5):
        name = f'A{64373 + r:06}'
        rank, bound = cutoff(r)
        phi, sigma = divisor_sieve(bound, r)
        answers = []
        for n in range(1, bound + 1):
            if (phi[n], sigma[n]) != by_factorization(n, r):
                raise ArithmeticError(f'Independent methods disagree at ({r}, {n})')
            if sigma[n] > phi[n]**(r + 1):
                answers.append(n)
        if answers != expected[name]:
            raise ArithmeticError(f'{name} differs from the OEIS list: {answers}')
        print(f'{name}: excluded rank {rank} and above; n <= {bound}; '
              f'{len(answers)} terms; maximum {answers[-1]}')


if __name__ == '__main__':
    main()
