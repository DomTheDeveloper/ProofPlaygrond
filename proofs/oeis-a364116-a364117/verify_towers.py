"""Independent tests of both A364113 towers and the summand decomposition."""

from collections import Counter
from math import comb

from verify import via_exact_coefficients, via_recurrence


def decomposition(row, n, prime, shifted):
    """Sum (1) exactly, partitioned by the number of indices prime to p."""
    limit = n - int(shifted)
    if shifted:
        c = [comb(n + u - 1, u) ** 2 for u in range(limit + 1)]
        weights = [(-1) ** (m - 1) * comb(row * n - 1, m - 1) if m else 0
                   for m in range(n + 1)]
    else:
        c = [comb(n, u) ** 2 for u in range(limit + 1)]
        weights = [comb(row * n + m, m) for m in range(n + 1)]

    # Dynamic programming separates zero, one and at least two unit indices.
    by_units = [[0] * (limit + 1) for _ in range(3)]
    by_units[0][0] = 1
    for _ in range(row):
        next_counts = [[0] * (limit + 1) for _ in range(3)]
        for units, counts in enumerate(by_units):
            for total, count in enumerate(counts):
                if count:
                    for u in range(limit - total + 1):
                        group = min(2, units + int(u % prime != 0))
                        next_counts[group][total + u] += count * c[u]
        by_units = next_counts
    return [sum(x * weights[n - total] for total, x in enumerate(counts))
            for counts in by_units]


def main():
    counts = Counter()
    max_degree = 0
    for p in (5, 7, 11, 13, 17, 19):
        for m in (1, 2, 3, 5, 7):
            for r in (1, 2, 3):
                n = m * p ** r
                if n > 350:
                    continue
                modulus = p ** (3 * r)
                for row in (0, 1, 2, 3, 4, 5, 7, 10):
                    for shifted in (False, True):
                        hi, lo = n - int(shifted), n // p - int(shifted)
                        residue = via_recurrence(row, hi, modulus)
                        exact = via_exact_coefficients(row, hi)
                        lower = via_exact_coefficients(row, lo)
                        assert residue == exact % modulus == lower % modulus, (row, m, p, r, shifted)
                        assert residue == via_recurrence(row, lo, modulus)
                        counts['shifted tower' if shifted else 'unshifted tower'] += 1
                        max_degree = max(max_degree, hi)
                        if 1 <= row <= 5 and n <= 130 and (r >= 2 or m <= 3):
                            grid, one, several = decomposition(row, n, p, shifted)
                            assert grid + one + several == exact
                            assert (grid - lower) % modulus == 0
                            assert one % modulus == 0 and several % p ** (4 * r) == 0
                            counts['exact summand partitions'] += 1
    for name, count in sorted(counts.items()):
        print(f'{name}: {count}')
    print(f'All checks passed. Largest degree: {max_degree}.')


if __name__ == '__main__':
    main()
