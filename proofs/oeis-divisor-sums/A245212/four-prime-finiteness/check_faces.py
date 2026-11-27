"""Certify separation of every limiting base moment with at least one infinite index.

Two searches are supplied. The first exhausts bounded index pairs. The second
locates each monotone row's crossing by bisection and tests only its neighbors.
"""
from fractions import Fraction as F
from itertools import permutations
from math import prod

GAP = F(1, 20_000_000)


def moment(p, i):
    return 1-F(p**i-1, (p-1)*i*p**i)


def exhaustive(P, t):
    lo, hi = t-GAP, t+GAP
    assert 1 > hi
    checked = 0
    for p in P:
        for i in range(2, 1+int(F(1, p-1)/(1-hi))):
            assert not lo <= moment(p, i) <= hi
            checked += 1
    for p, q in permutations(P, 2):
        lim = int((F(1, p-1)+F(1, q-1))/(1-hi))
        for i in range(2, lim+1):
            b = moment(p,i)
            if b < lo:
                continue
            assert b > hi
            last = int(b/((q-1)*(b-hi)))
            for j in range(i, last+1):
                assert not lo <= b*moment(q,j) <= hi
                checked += 1
    return checked


def monotone_check(P, t):
    # Use unnormalised moment H/(p^e*(e+1)), computed by a different formula.
    def w(p, i):
        n = p**(i-1)
        return F((i*(p-1)-1)*p*n+1, (p-1)**2*i*n)

    caps = {p:F(p,p-1) for p in P}
    scale = prod(caps.values())
    target, gap = 2, GAP*scale
    assert abs(scale-target) > gap
    critical = 0
    for p, q, s in permutations(P):
        i = 2
        while True:
            lower = w(p,i)*w(q,i)*caps[s]
            if lower > target+gap:
                break
            limit = w(p,i)*caps[q]*caps[s]
            assert abs(limit-target) > gap
            critical += 1
            if limit < target-gap:
                i += 1
                continue
            left = i
            if lower <= target:
                right = 2*i
                while w(p,i)*w(q,right)*caps[s] <= target:
                    right *= 2
                while right-left > 1:
                    mid = (left+right)//2
                    if w(p,i)*w(q,mid)*caps[s] <= target:
                        left = mid
                    else:
                        right = mid
                for j in (left, right):
                    assert abs(w(p,i)*w(q,j)*caps[s]-target) > gap
                    critical += 1
            else:
                assert lower > target+gap
            i += 1
        # The one-finite-index limit is above the same threshold for all i that follow.
    return critical


if __name__ == "__main__":
    for q in (7, 11, 13):
        P = (3,5,q)
        target = 2*prod(F(p-1,p) for p in P)
        assert target < 1
        print(P, target, "exhaustive", exhaustive(P,target),
              "monotone", monotone_check(P,target), "gap >", GAP)
