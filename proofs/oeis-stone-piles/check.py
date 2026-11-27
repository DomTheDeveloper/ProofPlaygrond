"""Independent checks for the stone-pile reachability and counting theorems (Python 3.9+)."""
from collections import Counter, deque
from itertools import combinations
from math import gcd, prod


def odd_part(n):
    return n // (n & -n)


def partitions(n, least=1):
    if n == 0:
        yield ()
    for k in range(least, n + 1):
        for rest in partitions(n - k, k):
            yield (k,) + rest


def forward_states(n):
    initial = (1,) * n
    reached = {initial}
    queue = deque([initial])
    while queue:
        current = queue.popleft()
        for a, multiplicity in Counter(current).items():
            if multiplicity < 2:
                continue
            others = list(current)
            others.remove(a)
            others.remove(a)
            for amount in range(1, a + 1):
                changed = [a + amount]
                if amount < a:
                    changed.append(a - amount)
                state = tuple(sorted(others + changed))
                if state not in reached:
                    reached.add(state)
                    queue.append(state)
    return reached


def pair_obstructions(parts):
    m = odd_part(sum(parts))
    return [gcd(m, *(x for k, x in enumerate(parts) if k != i and k != j))
            for i, j in combinations(range(len(parts)), 2)]


def reachable(parts):
    if odd_part(gcd(*parts)) != 1:
        return False
    if len(set(parts)) < len(parts) or any(x % 2 == 0 for x in parts):
        return True
    return parts == (1,) or 1 in pair_obstructions(parts)


def partition_table(n, distinct=False):
    result = [1] + [0] * n
    for k in range(1, n + 1):
        indices = range(n, k - 1, -1) if distinct else range(k, n + 1)
        for j in indices:
            result[j] += result[j - k]
    return result


def odd_prime_factors(n):
    remainder = odd_part(n)
    primes = []
    d = 3
    while d * d <= remainder:
        if remainder % d == 0:
            primes.append(d)
            while remainder % d == 0:
                remainder //= d
        d += 2
    if remainder > 1:
        primes.append(remainder)
    return primes


def basic_count(n, table):
    """Common odd divisor, plus coprime odd pairs for even n with odd part > 1."""
    primes = odd_prime_factors(n)
    total = sum((-1)**(k + 1) * table[n // prod(s)]
                for k in range(1, len(primes) + 1) for s in combinations(primes, k))
    if n % 2 == 0 and primes:
        phi = n // 2
        for p in primes:
            phi = phi // p * (p - 1)
        total += phi // 2
    return total


def check():
    ordinary = partition_table(105)
    distinct = partition_table(105, distinct=True)
    checked = 0
    for n in range(1, 43):
        reached = forward_states(n)
        total = missing = missing_terminal = 0
        for parts in partitions(n):
            assert reachable(parts) == (parts in reached), (n, parts)
            total += 1
            if parts not in reached:
                missing += 1
                missing_terminal += len(set(parts)) == len(parts)
        assert total == ordinary[n]
        assert missing == basic_count(n, ordinary)
        assert missing_terminal == basic_count(n, distinct)
        checked += total
    print(f"All {checked:,} partitions for 1 <= n <= 42 matched forward search.")

    for p in (3, 5, 7, 11, 13):
        assert basic_count(4*p, ordinary) == p + 4
        assert basic_count(8*p, ordinary) == 2*p + 20

    triples = []
    for a in range(1, 36, 2):
        for b in range(a + 2, (105 - a + 1) // 2, 2):
            triangle = (a, b, 105 - a - b)
            if gcd(*triangle) == 1 and min(pair_obstructions(triangle)) > 1:
                triples.append(triangle)
    assert len(triples) == 6 and (3, 25, 77) in triples
    print("Exceptional triples at 105:", triples)
    counts = [basic_count(105, table) + len(triples) for table in (ordinary, distinct)]
    assert counts == [15833, 685]
    print("Unreachable positions and unreachable terminal positions at 105:", counts)

    first_even = (2431, 2975, 17199, 487905)
    assert sum(first_even) == 510510 and gcd(*first_even) == 1
    blockers = pair_obstructions(first_even)
    assert blockers == [3, 5, 7, 11, 13, 17]
    print("The six pair obstructions at 510510:", blockers)


if __name__ == "__main__":
    check()
