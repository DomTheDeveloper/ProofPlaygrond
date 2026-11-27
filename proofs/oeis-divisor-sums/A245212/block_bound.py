"""Independently bound the Euler product using prime counts in short intervals.

This program never enumerates the primes up to the cutoff. It uses the
combinatorial prime-count recurrence on the distinct quotients floor(n/i).
"""
from math import isqrt

CUTOFF = 125_000_000
UNIT = 1_000_000
ROUND = 1_000_000_000

def prime_count(n):
    if n < 2:
        return 0
    r = isqrt(n)
    small_max = n // r - 1
    values = [n // i for i in range(1, r+1)] + list(range(small_max, 0, -1))
    count = {v: v-1 for v in values}
    for p in range(2, r+1):
        before = count[p-1]
        if count[p] == before:
            continue
        square = p*p
        for v in values:
            if v < square:
                break
            count[v] -= count[v//p] - before
    return count[n]

def fourth_root(n):
    low, high = 0, 1 << ((n.bit_length()+3)//4)
    while low+1 < high:
        middle = (low+high)//2
        if middle**4 <= n:
            low = middle
        else:
            high = middle
    return low

def main():
    left = 2
    total = blocks = counted = 0
    while left <= CUTOFF:
        right = min(CUTOFF, left + left//16)
        through_right = prime_count(right)
        how_many = through_right - counted
        lower = fourth_root(UNIT**4 * left**3)
        total += (how_many*ROUND*UNIT + lower-UNIT-1)//(lower-UNIT)
        counted = through_right
        blocks += 1
        left = right+1
    # log 2 > 56/81 by the first two terms of 2*atanh(1/3).
    power = (81*total+56*ROUND-1)//(56*ROUND)
    print('cutoff, prime count, blocks:', CUTOFF, counted, blocks)
    print('log upper numerator, denominator:',total,ROUND)
    print('Euler product bounded by 2^',power,sep='')
    assert 120_000_000*((2**power)*CUTOFF+10**25)<CUTOFF*10**25
    print('fraction below 1 / 120000000 for every X >= 10^100')

if __name__ == '__main__':
    main()
