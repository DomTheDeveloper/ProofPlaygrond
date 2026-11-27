"""Classify A245212 equalities on the three remaining odd three-prime supports.
The variables j are exponents plus one. All operations deciding a branch are exact.
"""
from fractions import Fraction as Q
from functools import cache
from itertools import permutations
from math import prod

SUPPORTS = ((3, 5, 7), (3, 5, 11), (3, 5, 13))

@cache
def z(p, j):
    power = p**j
    return Q(power - 1, j * power)

def valuation(n, p):
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v

def verify(primes):
    t = 2 * prod(Q(p-1, p) for p in primes)
    root_limit = int(sum(Q(1,p-1) for p in primes) / (1-t))
    pairs = largest_cap = 0
    answers = set()
    for p, q, r in permutations(primes):
        aq, ar = Q(1,q-1), Q(1,r-1)
        for i in range(2, root_limit+1):
            c = z(p,i)
            b = 1 - c/(p-1)
            if b>t:
                cap = int(b*(aq+ar)/(b-t))
            else:
                cap = int((b*aq*ar+c)/(b*(aq+ar)))
            largest_cap = max(largest_cap,cap)
            for j in range(i, cap+1):
                pairs += 1
                second = z(q,j)
                d = b*(1-aq*second)
                coeff = c*second-d*ar
                if not coeff:
                    if d==t:
                        raise ArithmeticError(('family of equalities',p,i,q,j,r))
                    continue
                need = (t-d)/coeff
                if need<=0:
                    continue
                k = need.denominator // need.numerator
                if k<j or k>valuation(need.denominator,r):
                    continue
                if z(r,k)==need:
                    answers.add(tuple(sorted(((p,i-1),(q,j-1),(r,k-1)))))
    return root_limit,largest_cap,pairs,sorted(answers)

if __name__=='__main__':
    print('support | largest first index | largest second cap | ordered prefixes | equalities')
    for support in SUPPORTS:
        print(support, *verify(support), sep=' | ', flush=True)
