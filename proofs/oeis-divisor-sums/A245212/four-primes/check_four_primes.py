"""Independent exact checks of the sharp four-prime gap for OEIS A245212."""
from fractions import Fraction
from functools import cache
from itertools import combinations, product

@cache
def local(p, e):
    ps = [p**j for j in range(e+1)]
    return ps[-1], e+1, sum(ps), sum((j+1)*x for j,x in enumerate(ps))

def value(ps, es):
    n, tau, sigma, moment = 3, 2, 4, 7
    for p, e in zip(ps, es):
        power, count, total, weighted = local(p, e)
        n *= power
        tau *= count
        sigma *= total
        moment *= weighted
    return n, tau, sigma, 2*n*tau - moment

def direct(limit):
    tau = [0]*(limit+1)
    sigma = [0]*(limit+1)
    weighted = [0]*(limit+1)
    for d in range(1,limit+1):
        for n in range(d,limit+1,d):
            tau[n] += 1
            sigma[n] += d
        for n in range(d,limit+1,d):
            weighted[n] += d*tau[d]
    return tau, sigma, weighted

def main():
    cutoff = 300000
    counts, sums, moments = direct(cutoff)
    tested = small = 0
    minimum = Fraction(2)
    primes = (5,7,11,13,17,19,23,29,31,37,41,43,47)
    for ps in combinations(primes,3):
        for es in product(range(1,9),repeat=3):
            n,t,s,a = value(ps,es)
            assert 288*(a-s) >= 37*n*t
            minimum = min(minimum,Fraction(a-s,n*t))
            tested += 1
            if n<=cutoff:
                assert (t,s,a) == (counts[n],sums[n],2*n*counts[n]-moments[n])
                small += 1
    print(f'{tested} exact prime/exponent tuples; {small} checked separately by divisor sieve.')
    print(f'Minimum normalized gap on the finite grid: {minimum}.')
    last = None
    target = Fraction(37,288)
    for h in (1,2,4,8,16,32,64,128,256,512):
        n,t,s,a = value((5,7,11),(h,h,h))
        ratio = Fraction(a-s,n*t)
        assert ratio > target and (last is None or ratio < last)
        last = ratio
    assert last-target < Fraction(1,500)
    print('The sharpness sequence at exponent 512 is within 1/500 of 37/288.')

if __name__ == '__main__':
    main()
