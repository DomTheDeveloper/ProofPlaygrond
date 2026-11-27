"""Replay the odd-part divisor cutoff using finite residue sets and integer bisection."""
from bisect import bisect_left, bisect_right
from functools import lru_cache
from itertools import permutations
from math import isqrt, prod
import sys


def partitions(n, start=2):
    if n >= start:
        yield (n,)
    for a in range(start, isqrt(n)+1):
        if n % a == 0:
            for rest in partitions(n//a, a):
                yield (a,)+rest


@lru_cache(maxsize=8192)
def term(p, j):
    n = p**(j-1)
    t = (1 + ((p-1)*j-1)*p*n)//(p-1)**2
    return j*n, t, (p*n-1)//(p-1)


@lru_cache(maxsize=3000)
def residues(indices):
    if not indices:
        return ((1, 1, 1),)
    mod = 32
    j, rest = indices[0], indices[1:]
    local = set()
    for t in range(1, mod, 2):
        d = sum(pow(t, k, mod) for k in range(j))
        h = sum((k+1)*pow(t, k, mod) for k in range(j))
        local.add((j*pow(t, j-1, mod) % mod, h % mod, d % mod))
    return tuple({(a*d % mod, b*h % mod, c*s % mod) for a,b,c in local
                  for d,h,s in residues(rest)})


@lru_cache(maxsize=100000)
def reachable(indices, t, s, twice):
    return any((t*h+s*y-twice*v) % 32 == 0 for v,h,y in residues(indices))


@lru_cache(maxsize=3)
def prime_table(bits):
    limit = 1 << bits
    mark = bytearray(limit+1)
    for f in range(2, isqrt(limit)+1):
        if mark[f] == 0:
            mark[f*f::f] = bytes([1])*((limit-f*f)//f+1)
    return tuple(x for x in range(3, limit+1, 2) if not mark[x])


def primes(lo, hi):
    if hi <= 4194304:
        table = prime_table(hi.bit_length())
        yield from table[bisect_left(table, lo):bisect_right(table,hi)]
    else:
        for p in range(lo, hi+1, 2):
            if all(p%d for d in range(3, isqrt(p)+1, 2)):
                yield p


def check(d):
    count = leaves = 0
    found = []
    upper = 2*d*(1+3*(d-1).bit_length())

    def visit(rest, floor, scale, T, S, chosen, k):
        nonlocal count, leaves
        count += 1
        multiplicity = prod(rest)
        if (2*scale-T)*multiplicity <= S:
            return
        if not reachable(tuple(sorted(rest)), T % 32, S % 32, 2*scale % 32):
            return
        C = 2*(k+1)*d*d
        odd_prefix = prod(p**e for p,e in chosen)
        if 2**(k+1) * C >= 2*d*d * (C*odd_prefix)**multiplicity:
            return
        def score(trial):
            a,b,c = scale,T,S
            for j in rest:
                n,h,s = term(trial,j)
                a,b,c = a*n,b*h,c*s
            return b+c-2*a
        if score(floor) < 0:
            return
        lo, hi = floor, 2*floor
        while score(hi) >= 0:
            lo, hi = hi, hi*2
        while hi-lo > 1:
            mid = (lo+hi)//2
            if score(mid) >= 0:
                lo = mid
            else:
                hi = mid
        if len(rest) == 1:
            leaves += 1
            if score(lo) == 0 and lo%2 and all(lo%f for f in range(3,isqrt(lo)+1,2)):
                found.append((k, chosen+((lo,rest[0]-1),)))
            return
        # Tighten the same prefix bound using the actual upper limit just found.
        enlarged = odd_prefix * lo**(rest[0]-1)
        if 2**(k+1) * C >= 2*d*d * (C*enlarged)**prod(rest[1:]):
            return
        for p in primes(floor,lo):
            n,h,s = term(p,rest[0])
            visit(rest[1:], p+2, scale*n, T*h, S*s, chosen+((p,rest[0]-1),), k)

    for part in partitions(d):
        for indices in sorted(set(permutations(part))):
            for k in range(upper):
                v,t,s = term(2,k+1)
                # B > kU, B < m*tau(m), U >= m*tau(m)/(2*p) at each odd p.
                floor = max(3,k//2+1)
                visit(indices,floor if floor%2 else floor+1,v,t,s,(),k)
    return upper, count, leaves, found


if __name__ == "__main__":
    limit = int(sys.argv[1])
    assert limit >= 2
    for d in range(2, limit+1):
        upper, nodes, ends, found = check(d)
        print(d, upper, nodes, ends, found, flush=True)
        assert not found
