"""Cross-check by multiplicative partitions, modular reachability and monotone bisection.

The only residue assumption here is that primes after the first one are odd.
This checker does not use a formula for any 2-adic valuation.
"""
from argparse import ArgumentParser
from functools import lru_cache
from itertools import permutations
from math import isqrt, prod

MOD = 32


def partitions(d, smallest=2):
    if d >= smallest:
        yield (d,)
    for f in range(smallest, isqrt(d)+1):
        if d % f == 0:
            for tail in partitions(d//f, f):
                yield (f,)+tail


@lru_cache(maxsize=2048)
def odd_products(indices):
    if not indices:
        return ((1,1,1),)
    i = indices[0]
    atoms = set()
    for residue in range(1, MOD, 2):
        pw, w, s = 1, 0, 0
        for h in range(i):
            w = (w+(h+1)*pw) % MOD
            s = (s+pw) % MOD
            if h != i-1:
                pw = pw*residue % MOD
        atoms.add((i*pw % MOD,w,s))
    return tuple({(a*d % MOD,b*t % MOD,c*s % MOD)
                  for a,b,c in atoms for d,t,s in odd_products(indices[1:])})


@lru_cache(maxsize=16384)
def local(base,i):
    n = base**(i-1)
    s = (base*n-1)//(base-1)
    return n*i, (i*base*n-s)//(base-1), s


@lru_cache(maxsize=30000)
def is_prime(x):
    if x < 2 or x % 2 == 0:
        return x == 2
    return all(x % d for d in range(3,isqrt(x)+1,2))


@lru_cache(maxsize=4)
def table(bits):
    stop = 2**bits
    mark = bytearray(stop+1)
    for f in range(2,isqrt(stop)+1):
        if not mark[f]:
            mark[f*f::f] = bytes([1])*((stop-f*f)//f+1)
    return tuple(x for x in range(2,stop+1) if not mark[x])


def primes_in(lo,hi):
    if hi < lo:
        return
    if hi <= 8_388_608:
        from bisect import bisect_left, bisect_right
        pool = table((hi-1).bit_length())
        for idx in range(bisect_left(pool,lo), bisect_right(pool,hi)):
            yield pool[idx]
    else:
        for x in range(lo,hi+1):
            if is_prime(x):
                yield x


def run(limit):
    solutions = {1}
    patterns = rows = terminal = 0

    def visit(indices, smallest, number, den, moment, sigma):
        nonlocal rows, terminal
        rows += 1
        d = prod(indices)
        if moment*d + sigma >= 2*den*d:
            return
        odd = odd_products(tuple(sorted(indices)))
        if smallest > 2 and not any((moment*w + sigma*s - 2*den*v) % MOD == 0
                                    for v,w,s in odd):
            return

        def score(x):
            d, w, s = den, moment, sigma
            for index in indices:
                v, t, u = local(x,index)
                d, w, s = d*v, w*t, s*u
            return w+s-2*d

        if score(smallest) < 0:
            return
        lo = smallest
        hi = lo*2
        while score(hi) >= 0:
            lo, hi = hi, hi*2
        while hi-lo > 1:
            mid = (lo+hi)//2
            if score(mid) >= 0:
                lo = mid
            else:
                hi = mid
        if len(indices) == 1:
            terminal += 1
            if score(lo)==0 and is_prime(lo):
                solutions.add(number*lo**(indices[0]-1))
            return
        for p in primes_in(smallest,lo):
            v,t,s = local(p,indices[0])
            visit(indices[1:],p+1,number*p**(indices[0]-1),den*v,moment*t,sigma*s)

    for d in range(2,limit+1):
        for family in partitions(d):
            for indices in sorted(set(permutations(family))):
                patterns += 1
                visit(indices,2,1,1,1,1)
    assert solutions == {1<<k for k in range(limit)}
    print("cutoff ordered-patterns visited-prefixes terminal-crossings solutions")
    print(limit, patterns, rows, terminal, len(solutions))


if __name__ == "__main__":
    parser = ArgumentParser()
    parser.add_argument("cutoff",type=int)
    args = parser.parse_args()
    if args.cutoff < 1:
        parser.error("positive divisor cutoff required")
    run(args.cutoff)
