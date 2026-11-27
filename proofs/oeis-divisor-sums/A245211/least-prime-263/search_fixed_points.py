"""Exhaust all A245211 fixed points with a bounded least prime factor.

Uses integer arithmetic and deterministic trial division. No bound on n or
on its largest prime factor is supplied. Run with a smallest-prime cutoff.
"""
from functools import cache, lru_cache
from math import gcd, isqrt, prod
import argparse

@lru_cache(maxsize=8000)
def prime(x):
    return x >= 2 and (x == 2 or x % 2 == 1 and
                       all(x % d for d in range(3, isqrt(x) + 1, 2)))

def exponent_tails(budget):
    yield ()
    for e in range(1, budget):
        for tail in exponent_tails(budget // (e + 1)):
            yield (e,) + tail

@lru_cache(maxsize=8000)
def term(e, x):
    # T_e(x)/x**e equals (e+1) + e/x + ... + 1/x**e.
    t = e + 1
    for j in range(e, 0, -1):
        t = t * x + j
    return t, x ** e

@cache
def allowed(modulus, exponents):
    """Possible residues of the normalized remaining product at units mod m."""
    if not exponents:
        return frozenset({1})
    e, tail = exponents[0], exponents[1:]
    values = set()
    for x in range(1, modulus):
        if gcd(x, modulus) == 1:
            a, b = term(e, x)
            values.add(a * pow(b, -1, modulus) % modulus)
    return frozenset(a*b % modulus for a in values for b in allowed(modulus, tail))

@cache
def certified_large_prime():
    # Lucas's criterion. A unit of order q-1 forces q to be prime.
    q = 59737124597292648185414913209393
    factors = (2, 227, 15308633, 4576002647, 234787945631)
    assert 2**4 * prod(factors[1:]) == q-1
    assert all(prime(r) for r in factors)
    for witness in range(2, 101):
        if pow(witness, q-1, q) == 1 and all(
            pow(witness, (q-1)//r, q) != 1 for r in factors
        ):
            return q
    raise ArithmeticError("Lucas certificate failed")

@cache
def certified_263_primes():
    # Complete Lucas certificates for the two prime factors of T_13(263).
    certificates = (
        (214805549993, (2, 2, 2, 11, 293, 8330963), 3),
        (3094619080181, (2, 2, 5, 23, 79, 139, 612643), 7),
        (3812570706782993, (2, 2, 2, 2, 7, 11, 3094619080181), 5),
        (1883836937069958237217,
         (2, 2, 2, 2, 2, 3, 5147, 3812570706782993), 15),
    )
    proved = set()
    for q, factors, witness in certificates:
        assert prod(factors) == q - 1
        assert all(r in proved or prime(r) for r in set(factors))
        assert pow(witness, q - 1, q) == 1
        assert all(pow(witness, (q - 1)//r, q) != 1 for r in set(factors))
        proved.add(q)
    return certificates[0][0], certificates[-1][0]

@cache
def small_factors(x):
    """Return proven prime divisors, stopping trial division at 2000."""
    # This additional trial divisor occurs in T_9(227). Recheck both
    # divisibility and primality before using it in the forcing argument.
    ans=[q for q in (96893,) if x % q == 0 and prime(q)]
    large = certified_large_prime()
    if x % large == 0:
        ans.append(large)
    for q in certified_263_primes():
        if x % q == 0:
            ans.append(q)
    q=2
    while q*q<=x and q<=2000:
        if x%q==0:
            ans.append(q)
            while x%q==0:
                x//=q
        q=3 if q==2 else q+2
    if x>1 and (q*q>x or (x<=10**11 and prime(x))):
        ans.append(x)
    return ans

def forced_possible(p, a, exps, d):
    # All factors T_e(q) already chosen divide the total moment. Any
    # unabsorbed prime in this product must occur in a remaining slot.
    def visit(u,v,known,available,divisors):
        lower=u*prod(e+1 for e in available)
        if not available:
            return lower==(d+1)*v
        if lower>=(d+1)*v:
            return False
        missing=u//gcd(u,(d+1)*v)
        forced=sorted(q for q in divisors if missing%q==0)
        if any(q<p or q in known for q in forced) or len(forced)>len(available):
            return False
        if not forced:
            return True
        q=forced[0]
        for e in set(available):
            others=list(available)
            others.remove(e)
            t,w=term(e,q)
            if visit(u*t,v*w,known|{q},others,divisors|set(small_factors(t))):
                return True
        return False
    t,w=term(a,p)
    return visit(t,w,{p},list(exps),set(small_factors(t)))

def examine(smallest, a_min=1, a_max=None, tail_min=0, tail_max=None):
    hits, patterns, nodes = [], 0, 0

    def extend(xs, exps, pending, u, v, target):
        nonlocal nodes
        nodes += 1
        # Each remaining factor is strictly above its limiting value.
        if u * prod(e + 1 for e in pending) >= target * v:
            return

        # All future primes exceed the last selected prime, so each is a
        # unit modulo every listed modulus whose largest prime factor is small enough.
        for m, largest in ((3,3),(8,2),(5,5),(7,7),(9,3),(11,11),(13,13),
                           (16,2),(25,5),(27,3),(17,17),(19,19),(23,23),
                           (29,29),(31,31),(37,37),(41,41),(43,43),(47,47)):
            if largest <= xs[-1] and not any((u*z-target*v) % m == 0
                                             for z in allowed(m,pending)):
                return
        if pending == (1,):
            den = target*v-2*u
            x, rem = divmod(u,den)
            if rem == 0 and x > xs[-1] and prime(x):
                primes = xs + (x,)
                hits.append((prod(t**e for t,e in zip(primes,exps)),primes,exps))
            return

        if pending == (1, 1) and all(e == 1 for e in exps):
            # The largest prime y divides some 2*z+1 with z<y.
            # Since 2*z+1 < 2*y, it equals y. Test z in the fixed
            # prefix, then z=x, the penultimate prime.
            def record(x,y):
                if prev < x < y and prime(x) and prime(y):
                    primes=xs+(x,y)
                    hits.append((prod(primes),primes,exps))
            prev=xs[-1]
            for z in xs:
                y=2*z+1
                divisor=target*v*y-2*u*(2*y+1)
                if divisor>0:
                    x,r=divmod(u*(2*y+1),divisor)
                    if not r:
                        record(x,y)
            x,r=divmod(3*u,target*v-4*u)
            if not r:
                record(x,2*x+1)
            return

        def sign_at(x):
            # Replace every remaining prime by x. This is an upper bound
            # when its actual values are all at least x.
            a, b = u, v
            for e in pending:
                t, w = term(e, x)
                a *= t
                b *= w
            return a - target * b

        lo = xs[-1] + 1
        if sign_at(lo) < 0:
            return
        # The upper bound is strictly decreasing and eventually negative.
        hi = lo
        while sign_at(hi) >= 0:
            hi *= 2
        low = lo
        while hi - low > 1:
            mid = (low + hi) // 2
            if sign_at(mid) < 0:
                hi = mid
            else:
                low = mid
        if len(pending) == 1:
            # At most one integer can be a zero of the last factor.
            if sign_at(low) == 0 and prime(low):
                primes = xs + (low,)
                hits.append((prod(x**e for x, e in zip(primes, exps)), primes, exps))
            return
        # If the last exponent dominates the others, its prime power
        # divides the product of the other T polynomials. This also bounds
        # every intermediate prime, sometimes much more sharply.
        excess = pending[-1] - sum(pending[:-1])
        if excess > 0:
            limit = u * prod((e+1)*(e+2)//2 for e in pending[:-1])
            if lo**excess > limit:
                return
            if low**excess > limit:
                l, h = lo, low
                while h-l > 1:
                    m = (l+h)//2
                    if m**excess <= limit:
                        l = m
                    else:
                        h = m
                low = l
        for x in range(lo, low + 1):
            if prime(x):
                t, w = term(pending[0], x)
                extend(xs + (x,), exps, pending[1:], u*t, v*w, target)

    stop = (smallest - 1) // 2 + 1 if a_max is None else a_max
    for a in range(a_min, stop):
        tail_index = -1
        for tail in exponent_tails((smallest - 1) // a):
            if not tail:
                continue
            tail_index += 1
            if tail_index < tail_min or (tail_max is not None and tail_index >= tail_max):
                continue
            es = (a,) + tail
            d = prod(e + 1 for e in es)
            patterns += 1
            u, v = term(a, smallest)
            # If r divides T_a(p) more often than it divides D+1, r must
            # divide n in T(n)=n(D+1). Use any small prime divisor found.
            # At a forced prime the normalized local moment is at least
            # 1 + 1/(2r). All other unknown normalized moments exceed one.
            missing = u // gcd(u, d+1)
            forced = [r for r in range(2, 2*smallest+2) if prime(r) and missing % r == 0]
            if any(r < smallest for r in forced) or len(forced) > len(tail):
                continue
            lower_numerator = u * prod(e+1 for e in tail) * prod(2*r+1 for r in forced)
            upper_numerator = (d+1) * v * prod(2*r for r in forced)
            if lower_numerator > upper_numerator:
                continue
            if not forced_possible(smallest,a,tail,d):
                continue
            extend((smallest,), es, tail, u, v, d + 1)
    return patterns, nodes, hits

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('cutoff', type=int, nargs='?', default=37)
    args = parser.parse_args()
    print('least_prime exponent_patterns search_nodes fixed_points')
    for p in range(2, args.cutoff + 1):
        if prime(p):
            patterns, nodes, hits = examine(p)
            print(p, patterns, nodes, [n for n, _, _ in hits], flush=True)

