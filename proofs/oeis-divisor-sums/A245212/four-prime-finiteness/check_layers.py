"""Classify A245212 on odd four-prime inputs with v_3(n) = 3 or 4.

The prime bounds and index bounds are derived in README.md.  No numerical
precision parameters or externally supplied upper bounds enter the proof.
"""
from fractions import Fraction as Q
from itertools import permutations
from math import isqrt, prod


def terms(p, e):
    """Return scale n*tau(n), moment T(n), and divisor sum for n=p**e."""
    n = p**e
    return (n*(e+1),
            (1 + ((e+1)*(p-1)-1)*p*n)//(p-1)**2,
            (p*n-1)//(p-1))


def eligible(h):
    scale, moment, divsum = terms(3, h)
    for support in [(7, 11, 13), (5, 13, 17)]:
        L = prod(Q(p, p-1) for p in support)
        assert Q(divsum, moment)/4 < Q(1, support[0]-1)
        assert Q(moment, scale)*L < 2
    assert Q(divsum, moment)/4 < Q(1, 4)
    for q in (7, 11):
        base = Q(moment, scale)*Q(5, 4)*Q(q, q-1)
        assert base < 2
        r = q+1
        while base*r > 2*(r-1):
            if all(r % d for d in range(2, isqrt(r)+1)):
                yield (5, q, r)
            r += 1


def modular_prefixes(p, first, last, final_prime, weight, divsum):
    """Necessary congruence for the final prime, using geometric-sum recurrences."""
    if last < first:
        return
    modulus = final_prime**8
    power = pow(p, first, modulus)
    # Compute both sums at exponent first-1 without dividing in Z/modulus.
    lifted = pow(p, first, modulus*(p-1)**2)
    s = ((lifted-1)//(p-1)) % modulus
    t = ((1 + (first*(p-1)-1)*lifted)//(p-1)**2) % modulus
    for j in range(first, last+1):
        required = modulus if j >= 9 else final_prime**(j-1)
        if (weight*t - (final_prime-1)*divsum*s) % required == 0:
            yield j
        s = (s+power) % modulus
        t = (t+(j+1)*power) % modulus
        power = power*p % modulus


def classify(h, primes):
    scale, moment, sigma = terms(3, h)
    target = Q(2*scale, moment)*prod(Q(p-1, p) for p in primes)
    weight = Q(sigma, moment)
    first_cap = int(sum(Q(1, p-1) for p in primes)/(1-target))
    pairs = passes = tests = 0
    solutions = set()
    for p, q, r in permutations(primes):
        aq, ar = Q(1, q-1), Q(1, r-1)
        for i in range(2, first_cap+1):
            zp = Q(p**i-1, i*p**i)
            B = 1-zp/(p-1)
            if B > target:
                cap = int(B*(aq+ar)/(B-target))
            else:
                cap = int((B*aq*ar+weight*zp)/(B*(aq+ar)))
            pairs += max(0, cap-i+1)
            ds, ts, ss = terms(p, i-1)
            for j in modular_prefixes(q, i, cap, r, moment*ts, sigma*ss):
                passes += 1
                dq, tq, sq = terms(q, j-1)
                mT, mS, mD = moment*ts*tq, sigma*ss*sq, scale*ds*dq
                diff = mT-(r-1)*mS
                if diff == 0:
                    if 2*mD == r*mS:
                        raise AssertionError(("ray", h, primes, i, j))
                    continue
                v = 0
                while diff % r == 0:
                    v += 1
                    diff //= r
                for e in range(j-1, v+1):
                    tests += 1
                    dr, tr, sr = terms(r, e)
                    if mT*tr+mS*sr == 2*mD*dr:
                        solutions.add(tuple(sorted(((3,h), (p,i-1), (q,j-1), (r,e)))))
    return pairs, passes, tests, sorted(solutions)


if __name__ == "__main__":
    for h in (3, 4):
        totals = [0, 0, 0]
        for support in eligible(h):
            pairs, passes, tests, solutions = classify(h, support)
            print(h, support, pairs, passes, tests, solutions, flush=True)
            assert not solutions
            totals = [x+y for x, y in zip(totals, (pairs, passes, tests))]
        print("total", h, *totals, flush=True)
