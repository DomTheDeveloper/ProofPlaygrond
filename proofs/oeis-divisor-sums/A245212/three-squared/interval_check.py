"""Independent certificate for n = 9*5^a*7^b*11^c in OEIS A245212.
Bounds search boxes with monotone normalized divisor sums. Eliminates the last
exponent using divisibility, and checks any surviving triple against the integer equation.
"""
from fractions import Fraction
from functools import cache
from itertools import permutations
from math import prod

@cache
def local(p, e):
    """Return n*tau(n), sum(d*tau(d)), and sigma(n) for n=p**e."""
    n=p**e
    s=(p*n-1)//(p-1)
    moment=((e+1)*n*p*p-(e+2)*n*p+1)//((p-1)**2)
    return n*(e+1), moment, s

def outside(fixed, remaining, height):
    """Exclude 2 from the interval applying to all remaining exponents >= height."""
    scale, weight, divsum = fixed
    lower = Fraction(weight,scale)
    upper_moment = lower
    upper_divsum = Fraction(divsum,scale)
    for p in remaining:
        d,w,s = local(p,height)
        lower *= Fraction(w,d)
        upper_moment *= Fraction(p,p-1)
        upper_divsum *= Fraction(s,d)
    return lower>2 or upper_moment + upper_divsum<2

def tail_cutoff(fixed,remaining,first):
    height=max(1,first)
    while not outside(fixed,remaining,height):
        height*=2
        if height>16384:
            raise ArithmeticError('Uncertified tail: interval includes 2')
    return height

def exhaustive(support):
    empty=local(3,2)
    first_limit=tail_cutoff(empty,support,1)
    max_second=prefixes=final_tests=0
    solutions=set()
    for p,q,r in permutations(support):
        for a in range(1,first_limit):
            one=tuple(u*v for u,v in zip(empty,local(p,a)))
            limit=tail_cutoff(one,(q,r),a)
            max_second=max(max_second,limit)
            for b in range(a,limit):
                prefixes+=1
                scaled,t,s=(u*v for u,v in zip(one,local(q,b)))
                value=t-(r-1)*s
                if value==0:
                    if 2*scaled==r*s:
                        raise ArithmeticError(('all final exponents work', p,a,q,b,r))
                    continue
                c_max=0
                while value%r==0:
                    value//=r
                    c_max+=1
                for c in range(b,c_max+1):
                    final_tests+=1
                    d,w,z=local(r,c)
                    if t*w+s*z==2*scaled*d:
                        solutions.add(tuple(sorted(((p,a),(q,b),(r,c)))))
    return first_limit,max_second,prefixes,final_tests,sorted(solutions)

if __name__=='__main__':
    print('support | first tail excluded from | maximum second tail cutoff | ordered prefixes | final direct tests | equalities')
    for primes in ((5,7,11),):
        print(primes,*exhaustive(primes),sep=' | ',flush=True)
