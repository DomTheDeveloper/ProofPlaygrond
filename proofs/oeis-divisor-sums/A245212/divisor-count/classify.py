"""Exactly classify A245212 equality for a given upper bound on tau(n)."""
from argparse import ArgumentParser
from bisect import bisect_left, bisect_right
from functools import lru_cache
from math import isqrt, prod


@lru_cache(maxsize=16384)
def prime(p):
    return p >= 2 and (p == 2 or (p % 2 and all(p % j for j in range(3,isqrt(p)+1,2))))


@lru_cache(maxsize=4)
def sieved(log_bound):
    n = 1 << log_bound
    sieve = bytearray([1])*(n+1)
    sieve[0:2] = bytes(2)
    for p in range(2, isqrt(n)+1):
        if sieve[p]:
            sieve[p*p::p] = bytes((n-p*p)//p+1)
    return [p for p in range(2,n+1) if sieve[p]]


def primes_between(lo, hi):
    if hi < lo:
        return
    if hi <= 8_388_608:
        table = sieved((hi-1).bit_length())
        for j in range(bisect_left(table,lo), bisect_right(table,hi)):
            yield table[j]
    else:
        # Memory remains bounded even if a higher requested cutoff has a long row.
        for p in range(lo, hi+1):
            if prime(p):
                yield p


def v2(n):
    return (n & -n).bit_length()-1


@lru_cache(maxsize=8192)
def atom(p, i):
    n = p**(i-1)
    s = (p*n-1)//(p-1)
    t = (1+(i*(p-1)-1)*p*n)//(p-1)**2
    return n*i, t, s


def patterns(limit, prefix=()):
    for i in range(2,limit+1):
        yield prefix+(i,)
        yield from patterns(limit//i, prefix+(i,))


def classify(limit):
    found = {1}
    total = nodes = last = maxprime = 0

    def admissible_odd_indices(indices):
        return sum(v2(i+1) for i in indices) >= len(indices)

    def visit(rest, floor, n, size, t, s):
        nonlocal nodes, last, maxprime
        nodes += 1
        H = prod(rest)
        P = H*t+s
        Q = 2*H*size
        gap = Q-P
        if gap <= 0:
            return
        if floor > 2:
            odd_moment = prod(i*(i+1)//2 for i in rest)
            if (t*odd_moment+s*H) % 2:
                return
            vt, vr = v2(t*odd_moment), 1+v2(size*H)
            vs = v2(s*H)  # lower bound; exact when every remaining exponent is even
            if vt != vr:
                required = min(vt,vr)
                if vs > required or (H%2 and vs != required):
                    return
            elif H%2 and vs <= vr:
                return
        i = rest[0]
        if len(rest) == 1:
            # The positive leading reciprocal coefficient pins p to a unit interval.
            first = (i-1)*t+s
            p = (first+gap-1)//gap
            if p < floor:
                return
            last += 1
            d, moment, sigma = atom(p,i)
            if t*moment+s*sigma == 2*size*d and prime(p):
                found.add(n*p**(i-1))
            return
        k = len(rest)
        def possible(x):
            return P*x**k >= Q*(x-1)**k
        if not possible(floor):
            return
        hi = 2*floor
        while possible(hi):
            hi *= 2
        lo = floor
        while hi-lo > 1:
            mid = (hi+lo)//2
            if possible(mid):
                lo = mid
            else:
                hi = mid
        maxprime = max(maxprime, lo)
        for p in primes_between(floor, lo):
            if floor == 2 and not (can_even if p == 2 else can_odd):
                continue
            d, moment, sigma = atom(p, i)
            visit(rest[1:], p+1, n*p**(i-1), size*d, t*moment, s*sigma)

    for v in patterns(limit):
        total += 1
        can_even, can_odd = admissible_odd_indices(v[1:]), admissible_odd_indices(v)
        if not can_even and not can_odd:
            continue
        visit(v, 2, 1, 1, 1, 1)
    assert found == {2**e for e in range(limit)}, found
    return total, nodes, last, maxprime, len(found)


if __name__ == "__main__":
    parser = ArgumentParser()
    parser.add_argument("cutoff", type=int)
    args = parser.parse_args()
    if args.cutoff < 1:
        parser.error("positive divisor cutoff required")
    print("cutoff patterns nodes last-base-tests largest-loop-bound equalities")
    print(args.cutoff, *classify(args.cutoff))
