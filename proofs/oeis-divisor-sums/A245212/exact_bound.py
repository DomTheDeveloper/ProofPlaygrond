"""Certify an explicit Rankin bound. All operations that decide a bound are integers."""
from math import isqrt

LIMIT = 125_000_000
SCALE = 1 << 16
DEN = 1 << 32

def primes_to(limit):
    sieve = bytearray(b'\x01') * ((limit + 1) // 2)
    sieve[0] = 0
    for i in range(1, (isqrt(limit) + 1) // 2):
        if sieve[i]:
            p = 2*i + 1
            start = (p*p) // 2
            sieve[start::p] = b'\x00' * ((len(sieve) - start + p - 1) // p)
    yield 2
    for i in range(1, len(sieve)):
        if sieve[i]:
            yield 2*i + 1

def main():
    # Upper bound log product (1-p^(-3/4))^-1 by sum 1/(p^(3/4)-1).
    total = count = 0
    for p in primes_to(LIMIT):
        lower = isqrt(isqrt((p**3) << 64))  # floor(2^16 * p^(3/4))
        divisor = lower - SCALE
        total += (DEN*SCALE + divisor-1) // divisor
        count += 1
    # log 2 > 2/3, obtained by integrating 2/(1-t^2) from 0 to 1/3.
    power = (3*total + 2*DEN-1) // (2*DEN)
    print('prime cutoff:', LIMIT)
    print('number of primes:', count)
    print('log Euler-product upper numerator, denominator:', total, DEN)
    print('Euler product bounded by 2^',power,sep='')
    print('smooth fraction at 10^100 is at most',2**power,'/ 10^25')
    print('large-prime fraction is at most 1 /',LIMIT)
    for reciprocal in (100_000_000, 110_000_000, 120_000_000):
        holds=reciprocal*((2**power)*LIMIT + 10**25) < 10**25*LIMIT
        print('fraction below 1 /',reciprocal,holds)
    assert count == 7_110_142
    assert 120_000_000*((2**power)*LIMIT + 10**25)<10**25*LIMIT

if __name__ == '__main__':
    main()
