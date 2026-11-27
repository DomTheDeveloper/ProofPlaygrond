"""Exact checks for the universal prime-level Legendre-row defect."""

from collections import Counter
from math import comb, isqrt


def primes(limit):
    return [p for p in range(2, limit + 1)
            if all(p % d for d in range(2, isqrt(p) + 1))]


def multiply(a, b, degree, modulus):
    result = [0] * (min(degree, len(a) + len(b) - 2) + 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b[:degree - i + 1]):
            result[i + j] = (result[i + j] + x * y) % modulus
    return result


def polynomial_power(base, exponent, degree, modulus):
    result = [1]
    while exponent:
        if exponent & 1:
            result = multiply(result, base, degree, modulus)
        exponent //= 2
        if exponent:
            base = multiply(base, base, degree, modulus)
    return result


def row_via_y(row, n, modulus):
    """Use P_n(1+2y) and the functional F_n(y^j)=binom(n,j)."""
    legendre = [comb(n, j) * comb(n + j, j) % modulus for j in range(n + 1)]
    power = polynomial_power(legendre, row, n, modulus)
    return sum(comb(n, j) * power[j] for j in range(len(power))) % modulus


def row_via_x(row, n, modulus):
    """Use (1-x)^n P_n((1+x)/(1-x))=sum binom(n,j)^2 x^j."""
    numerator = [comb(n, j) ** 2 % modulus for j in range(n + 1)]
    power = polynomial_power(numerator, row, n, modulus)
    return sum(power[j] * comb(row * n + n - j, n - j)
               for j in range(len(power))) % modulus


def moments(n, prime):
    modulus = prime ** 5
    x = [comb(n, j) * comb(n + j, j) % modulus for j in range(n + 1)]
    x[0] = 0
    power = [1]
    answer = []
    for _ in range(1, 8):
        power = multiply(power, x, n, modulus)
        answer.append(sum(comb(n, j) * power[j] for j in range(len(power))) % modulus)
    return answer


def main():
    counts = Counter()
    initial_row_3 = [1, 7, 163, 5623, 235251, 11009257, 554159719]
    initial_row_4 = [1, 9, 289, 14409, 908001, 65898009, 5246665201]
    for row, terms in ((3, initial_row_3), (4, initial_row_4)):
        for n, expected in enumerate(terms):
            modulus = expected + 1
            assert row_via_y(row, n, modulus) == expected % modulus
            assert row_via_x(row, n, modulus) == expected % modulus
            counts['OEIS initial values'] += 1

    for p in primes(131):
        if p < 7:
            continue
        modulus = p ** 5
        harmonic = sum(pow(k, -1, modulus) for k in range(1, p)) % modulus
        correction = p * harmonic % modulus

        plus = moments(p, p)
        minus = moments(p - 1, p)
        assert plus == [(2 + 5 * correction) % modulus,
                        4 * correction % modulus,
                        6 * correction % modulus, 0, 0, 0, 0]
        assert minus == [(-5 * correction) % modulus,
                         8 * correction % modulus, 0, 0, 0, 0, 0]
        counts['finite moment tables'] += 14

        rows = range(0, 2 * p + 3) if p <= 31 else range(0, 21)
        for row in rows:
            expected_plus = (2 * row + 1 + row * (row * row - row + 5) * correction) % modulus
            expected_minus = (1 + row * (4 * row - 9) * correction) % modulus
            for evaluator in (row_via_y, row_via_x):
                assert evaluator(row, p, modulus) == expected_plus
                assert evaluator(row, p - 1, modulus) == expected_minus
            counts['universal row formulas'] += 2

        u3p, u3m = row_via_y(3, p, modulus), row_via_y(3, p - 1, modulus)
        u4p, u4m = row_via_y(4, p, modulus), row_via_y(4, p - 1, modulus)
        assert (3 * u3p - 11 * u3m - 10) % modulus == 0
        assert (pow(u3p, 21, modulus) - pow(7, 21, modulus) * pow(u3m, 11, modulus)) % modulus == 0
        assert (7 * u4p - 17 * u4m - 46) % modulus == 0
        assert (pow(u4p, 63, modulus) - pow(9, 63, modulus) * pow(u4m, 17, modulus)) % modulus == 0
        counts['Bala prime-level assertions'] += 4

    for name, count in sorted(counts.items()):
        print(f'{name}: {count}')
    print(f'All {sum(counts.values())} exact checks passed with two row evaluators.')


if __name__ == '__main__':
    main()
