"""Exhaust the ordered four-square representations for Sun's coefficient triple (18, 38, 18)."""
from collections import defaultdict
from math import isqrt


def check(n):
    pairs = defaultdict(list)
    for x in range(isqrt(n) + 1):
        for y in range(isqrt(n - x*x) + 1):
            pairs[x*x + y*y].append((x, y))
    count = hits = 0
    for s, first in pairs.items():
        second = pairs.get(n - s, ())
        for x, y in first:
            for z, w in second:
                count += 1
                k = x * y * (18*x*x + 38*y*y + 18*z*z)
                hits += isqrt(k)**2 == k
    return count, hits


if __name__ == "__main__":
    outcome = check(822335)
    print("Ordered representations and square hits at 822335:", outcome)
    assert outcome == (496920, 0)

