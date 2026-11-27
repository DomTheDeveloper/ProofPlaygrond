"""Check the preperiod of the divisor-power sums in OEIS A328919."""
from math import lcm


def factors(n):
    result = []
    p = 2
    while p * p <= n:
        e = 0
        while n % p == 0:
            e += 1
            n //= p
        if e:
            result.append((p, e))
        p += 1 if p == 2 else 2
    if n > 1:
        result.append((n, 1))
    return result


def modular_preperiod(n):
    """Compare the transient with a periodic tail using local prime powers."""
    fs = factors(n)
    height = max((e for _, e in fs), default=0)
    period = lcm(*((p - 1) * p ** (e - 1) for p, e in fs))
    shift = ((height + period - 1) // period) * period

    def term(k):
        value = 1
        for p, e in fs:
            value *= sum(pow(p, j * k, n) for j in range(e + 1))
            value %= n
        return value % n

    for k in reversed(range(height)):
        if term(k) != term(k + shift):
            return k + 1
    return 0


def state_preperiod(n):
    """Detect the vector cycle directly, then minimize the scalar preperiod."""
    divisors = [d for d in range(1, n + 1) if n % d == 0]
    state = tuple(1 % n for _ in divisors)
    seen, residues = {}, []
    while state not in seen:
        seen[state] = len(residues)
        residues.append(sum(state) % n)
        state = tuple(x * d % n for x, d in zip(state, divisors))
    start = seen[state]
    period = len(residues) - start
    while start and residues[start - 1] == residues[start - 1 + period]:
        start -= 1
    return start


def main():
    limit = 100_000
    first = {}
    pure = []
    for n in range(1, limit + 1):
        value = modular_preperiod(n)
        assert 2 ** value <= n
        first.setdefault(value, n)
        if value == 0:
            pure.append(n)
        if n <= 500:
            assert value == state_preperiod(n)
    assert pure == [1, 12]
    assert first == {e: 2 ** e for e in range(limit.bit_length())}
    print("Models agree for 1 through 500.")
    print(f"Purely periodic inputs through {limit}: {pure}.")
    print(f"First occurrences verified for e = 0 through {max(first)}.")


if __name__ == "__main__":
    main()
