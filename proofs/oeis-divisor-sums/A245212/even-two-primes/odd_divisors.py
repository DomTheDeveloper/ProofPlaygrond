"""Classify A245212 by the divisor count of its odd part, uniformly in v_2."""
from argparse import ArgumentParser
from functools import lru_cache
from math import isqrt, prod


def v2(x):
    return (x & -x).bit_length() - 1


def patterns(n):
    if n == 1:
        yield ()
    for d in range(2, n + 1):
        if n % d == 0:
            for tail in patterns(n // d):
                yield (d,) + tail


def max_x(d):
    x = 2 * d
    while 2**x < 2 * d*d * (2 * x * d*d)**(d-1):
        x += 1
    return x - 1


@lru_cache(maxsize=16000)
def prime(p):
    return p >= 2 and (p == 2 or (p % 2 == 1 and
                       all(p % v for v in range(3, isqrt(p) + 1, 2))))


@lru_cache(maxsize=20000)
def local(p, i):
    v = p**(i-1)
    s = (p*v-1)//(p-1)
    return i*v, (i*p*v-s)//(p-1), s


def run(d):
    total = nodes = 0
    hits = []
    largest = max_x(d)

    def visit(rest, smallest, size, T, S, chosen, k):
        nonlocal nodes
        nodes += 1
        h = prod(rest)
        low = T*h+S
        top = 2*size*h
        gap = top - low
        if gap <= 0:
            return
        i = rest[0]
        if len(rest) == 1:
            first = (i-1)*T+S
            p = (first + gap-1)//gap
            if p < smallest or p % 2 == 0 or (T+S) % p:
                return
            if (T - (p-1)*S) % p**(i-1):
                return
            v, t, s = local(p, i)
            if T*t+S*s == 2*size*v and prime(p):
                hits.append((k, chosen + ((p, i-1),)))
            return
        length = len(rest)
        def possible(p):
            return low*p**length >= top*(p-1)**length
        if not possible(smallest):
            return
        hi = 2*smallest
        while possible(hi):
            hi *= 2
        lo = smallest
        while hi-lo > 1:
            mid = (lo+hi)//2
            if possible(mid):
                lo = mid
            else:
                hi = mid
        bound = 2*(k+1)*d*d
        b = prod(p**e for p,e in chosen)
        enlarged = b*lo**(i-1)
        if 2**(k+1)*bound >= 2*d*d*(bound*enlarged)**prod(rest[1:]):
            return
        for p in range(smallest, lo+1, 2):
            if prime(p):
                v, t, s = local(p, i)
                visit(rest[1:], p+2, size*v, T*t, S*s, chosen+((p, i-1),), k)

    for indices in patterns(d):
        total += 1
        # A pure odd prime power times a power of two was already excluded.
        if len(indices) == 1:
            continue
        if sum(v2(i+1) for i in indices) < len(indices):
            continue
        if all(i % 2 for i in indices) and any(i % 4 == 3 for i in indices):
            continue
        for x in range(1, largest+1):
            k = x-1
            v, t, s = local(2, x)
            visit(indices, 3, v, t, s, (), k)
    return largest, total, nodes, hits


if __name__ == "__main__":
    cli = ArgumentParser(description=__doc__)
    cli.add_argument("cutoff", type=int)
    cutoff = cli.parse_args().cutoff
    assert cutoff >= 2
    for d in range(2, cutoff+1):
        x, patterns_seen, nodes, hits = run(d)
        print(d, x, patterns_seen, nodes, hits, flush=True)
        assert not hits
