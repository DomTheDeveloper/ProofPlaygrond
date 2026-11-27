"""Independent, exact cross-check using a rational inequality for each next prime."""
from fractions import Fraction
from functools import cache
from itertools import product
from math import gcd, isqrt, prod
import sys

def is_prime(n):
    return n > 1 and all(n % d for d in range(2, isqrt(n)+1))

def weight(p, e):
    return sum(Fraction(j+1, p**(e-j)) for j in range(e+1))

def vectors(budget):
    yield ()
    for f in range(2,budget+1):
        for rest in vectors(budget//f):
            yield (f-1,)+rest

@cache
def residues(es,m):
    if not es:
        return {1}
    e=es[0]
    values=set()
    for a in range(1,m):
        if gcd(a,m)==1:
            z=pow(a,-1,m)
            values.add(sum((e+1-j)*pow(z,j,m) for j in range(e+1))%m)
    return {v*w%m for v,w in product(values,residues(es[1:],m))}

def descendants(prev,es,c,goal,limits=()):
    # The still-missing factors must multiply to goal/c.
    req=Fraction(goal,c)
    bottom=prod(e+1 for e in es)
    if req<=bottom:
        return
    mods=[m for m in (3,5,7,11,13,17,19,23,29,31,37,41,43,47) if m<=prev]+[4,8]
    for m in mods:
        if not any((req.denominator*z-req.numerator)%m==0 for z in residues(es,m)):
            return
    t=len(es)
    # (1-1/x)^t >= 1-t/x. Thus x <= t * req/(req-bottom).
    cap=int(t*req/(req-bottom))
    lo=prev+1
    if limits:
        low,high=limits[0]
        lo=max(lo,low)
        if high is not None:
            cap=min(cap,high)
    if lo>cap:
        return
    if t==1:
        # Test the only possible root by monotonicity, without factoring c.
        hi=cap+1
        while lo<hi:
            m=(lo+hi)//2
            if weight(m,es[0])<=req:
                hi=m
            else:
                lo=m+1
        if lo<=cap and weight(lo,es[0])==req and is_prime(lo):
            yield (lo,)
        return
    for x in range(lo,cap+1):
        if is_prime(x):
            for tail in descendants(x,es[1:],c*weight(x,es[0]),goal,limits[1:]):
                yield (x,)+tail

@cache
def split_small_moment(t):
    # Decompose exactly only in this range. Other inputs use the original search.
    if t>10**12:
        return ()
    factors=[]
    d=2
    while d*d<=t:
        if t%d==0:
            factors.append(d)
            while t%d==0:
                t//=d
        d=3 if d==2 else d+2
    if t>1:
        factors.append(t)
    return tuple(factors)

@cache
def small_primes(p):
    return tuple(q for q in range(2,p) if is_prime(q))

@cache
def forbidden_small_part(p,a):
    # Prime divisors strictly below the least prime cannot divide n.
    # Their full powers in T_a(p) must therefore divide tau(n)+1.
    value=sum((j+1)*p**j for j in range(a+1))
    rest=value
    for q in range(2,p):
        while rest%q==0:
            rest//=q
    return value//rest

@cache
def known_prime_divisors(t):
    # Only return divisors proved prime. A large unfactored remainder
    # weakens this shortcut and still goes through the exhaustive bounds.
    if t<=10**12:
        return split_small_moment(t)
    factors=[]
    for q in small_primes(50_001):
        if t%q:
            continue
        factors.append(q)
        while t%q==0:
            t//=q
    return tuple(factors)+split_small_moment(t)

def place_forced(p,a,tail,d):
    # The assigned indices record the positions in the increasing tail.
    # Reduced numerator factors in excess of the target must be canceled
    # by a still-missing denominator, hence by exactly one future prime.
    goal=d+1
    def visit(value,placed,seeds):
        empty=[i for i in range(len(tail)) if i not in placed]
        if not empty:
            if value==goal:
                yield p**a*prod(placed[i]**tail[i] for i in placed)
            return
        if value*prod(tail[i]+1 for i in empty)>=goal:
            return
        need=value.numerator//gcd(value.numerator,goal)
        unavailable=(p,)+tuple(placed.values())+small_primes(p)
        if any(need%q==0 for q in unavailable):
            return
        required=[q for q in seeds if need%q==0]
        if len(required)>len(empty):
            return
        def limits(i):
            lower=max([p]+[q for j,q in placed.items() if j<i])+1
            upper=min([q-1 for j,q in placed.items() if j>i],default=None)
            return lower,upper
        if required:
            r=min(required)
            for i in empty:
                low,high=limits(i)
                if r<low or (high is not None and high<r):
                    continue
                w=weight(r,tail[i])
                fresh=set(known_prime_divisors(w.numerator))
                yield from visit(value*w,dict(placed)|{i:r},seeds|fresh)
            return
        es=tuple(tail[i] for i in empty)
        caps=tuple(limits(i) for i in empty)
        fixed=p**a*prod(q**tail[i] for i,q in placed.items())
        for qs in descendants(p,es,value,goal,caps):
            yield fixed*prod(q**e for q,e in zip(qs,es))
    initial=weight(p,a)
    yield from visit(initial,{},set(known_prime_divisors(initial.numerator)))

def verify(p):
    answers=[]
    patterns=0
    for a in range(1,p):
        for tail in vectors((p-1)//a):
            if not tail:
                continue
            patterns+=1
            es=(a,)+tail
            d=prod(e+1 for e in es)
            # For odd nonsquares the target is odd. Every normalized
            # local triangular number must be odd.
            if p>2 and d%2==0 and any(e%4 in (2,3) for e in es):
                continue
            if (d+1)%forbidden_small_part(p,a):
                continue
            # If p exactly divides n, 2p+1 is prime and divides n.
            # The two normalized factors imply 3*d <= 4*p.
            if a==1 and (not is_prime(2*p+1) or 3*d>4*p):
                continue
            answers.extend(place_forced(p,a,tail,d))
    return patterns,sorted(answers)

if __name__=='__main__':
    limit=int(sys.argv[1]) if len(sys.argv)>1 else 37
    for p in range(2,limit+1):
        if is_prime(p):
            print(p,*verify(p),flush=True)
