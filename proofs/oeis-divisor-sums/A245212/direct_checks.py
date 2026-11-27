"""Check the structural identities against the defining divisor sums at small arguments."""
from math import isqrt

def v2(n):
    assert n > 0
    return (n & -n).bit_length()-1

def independent_sieve(bound):
    tau = [0]*(bound+1)
    sigma = [0]*(bound+1)
    for d in range(1,bound+1):
        for n in range(d,bound+1,d):
            tau[n] += 1
            sigma[n] += d
    moment = [0]*(bound+1)
    for d in range(1,bound+1):
        item=d*tau[d]
        for n in range(d,bound+1,d):
            moment[n]+=item
    return tau,sigma,moment

def verify(bound):
    tau,sigma,T = independent_sieve(bound)
    small = list(range(bound+1))
    for p in range(2,isqrt(bound)+1):
        if small[p]!=p:
            continue
        for j in range(p*p,bound+1,p):
            if small[j]==j:
                small[j]=p
    hits=[]
    pass_budget=pass_triangle=0
    cofactor_tests=0
    for n in range(1,bound+1):
        rest=n
        factors={}
        while rest>1:
            p=small[rest]
            exp=0
            while rest%p==0:
                rest//=p
                exp+=1
            factors[p]=exp
        k=factors.get(2,0)
        odd={p:e for p,e in factors.items() if p!=2}
        A=sum(v2(e+1) for e in odd.values())
        B=sum(v2(e+2)-1 for e in odd.values())
        C=sum(v2(p+1)-1 for p,e in odd.items() if e%2)
        K=k+1+v2(k+1)
        assert v2(T[n])==A+B
        assert v2(sigma[n])==A+C
        assert v2(2*n*tau[n])==A+K
        orders=(B,C,K)
        tri=orders.count(min(orders))==2
        pass_budget+=int(B>=0)
        pass_triangle+=int(tri)
        equal=(2*n*tau[n]-T[n]==sigma[n])
        if equal:
            assert B>=0 and tri
            hits.append(n)
        for p,e in factors.items():
            if e!=1:
                continue
            b=n//p
            numerator=T[b]+sigma[b]
            denominator=4*b*tau[b]-2*T[b]-sigma[b]
            criterion=denominator>0 and numerator==p*denominator
            assert criterion==equal
            cofactor_tests+=1
    assert hits==[1<<k for k in range(bound.bit_length())]
    print('positive integers checked:',bound)
    print('inputs passing exponent budget:',pass_budget)
    print('inputs passing exact valuation test:',pass_triangle)
    print('cofactor quotient comparisons:',cofactor_tests)
    print('equalities:',*hits)

if __name__=='__main__':
    verify(500_000)
