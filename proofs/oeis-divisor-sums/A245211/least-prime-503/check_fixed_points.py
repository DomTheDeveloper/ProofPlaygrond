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
def pocklington_factor():
    # For each prime divisor l of q, both specified primes divide l-1.
    # Their product exceeds sqrt(q), ruling out a composite q.
    q = sum((j+1)*227**j for j in range(14))
    f, g = 4576002647, 234787945631
    assert is_prime(f) and is_prime(g) and f != g
    assert (q-1) % (f*g) == 0 and (f*g)**2 > q
    for r in (f, g):
        assert pow(2, q-1, q) == 1
        assert gcd(pow(2, (q-1)//r, q)-1, q) == 1
    return q

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
        assert all(r in proved or is_prime(r) for r in set(factors))
        assert pow(witness, q - 1, q) == 1
        assert all(pow(witness, (q - 1)//r, q) != 1 for r in set(factors))
        proved.add(q)
    return certificates[0][0], certificates[-1][0]

@cache
def certified_269_prime():
    # Complete Lucas certificates for T_13(269) and its large q-1 factor.
    certificates = (
        (14635092528104565487, (2, 3, 138561641, 17603588341), 3),
        (542512058959614745217387126772353,
         (2, 2, 2, 2, 2, 2, 2, 29, 257, 269, 144451,
          14635092528104565487), 3),
    )
    proved = set()
    for q, factors, witness in certificates:
        assert prod(factors) == q - 1
        assert all(r in proved or is_prime(r) for r in set(factors))
        assert pow(witness, q - 1, q) == 1
        assert all(pow(witness, (q - 1)//r, q) != 1 for r in set(factors))
        proved.add(q)
    return certificates[-1][0]

@cache
def certified_269_successor_primes():
    certificates = (
        (13974006881147, (2, 13, 71, 22571, 335381), 2),
        (1596161396191, (2, 3, 5, 47, 89, 127, 100153), 12),
        (1647238560869113, (2, 2, 2, 3, 43, 1596161396191), 5),
    )
    proved = set()
    for q, factors, witness in certificates:
        assert prod(factors) == q - 1
        assert all(r in proved or is_prime(r) for r in set(factors))
        assert pow(witness, q - 1, q) == 1
        assert all(pow(witness, (q - 1)//r, q) != 1 for r in set(factors))
        proved.add(q)
    small = 47137
    assert is_prime(small)
    q1, _, q2 = (q for q, _, _ in certificates)
    assert small * q1 * q2 == 2 * certified_269_prime() + 1
    return small, q1, q2

@cache
def certified_283_primes():
    certificates = (
        (33311847537949, (2, 2, 3, 7, 193147, 2053201), 2),
        (3498950330708810221,
         (2, 2, 3, 3, 5, 23, 97, 173, 50363928533), 6),
    )
    proved = set()
    for q, factors, witness in certificates:
        assert prod(factors) == q - 1
        assert all(r in proved or is_prime(r) for r in set(factors))
        assert pow(witness, q - 1, q) == 1
        assert all(pow(witness, (q - 1)//r, q) != 1 for r in set(factors))
        proved.add(q)
    moment = sum((j + 1) * 283**j for j in range(14))
    assert 9 * certificates[0][0] * certificates[1][0] == moment
    return certificates[0][0], certificates[1][0]

@cache
def certified_307_primes():
    factors = (57427, 96823, 424967, 102818321)
    assert all(is_prime(q) for q in factors)
    moment = sum((j + 1) * 307**j for j in range(10))
    assert prod(factors) == moment
    return factors

@cache
def certified_313_prime():
    # Complete Lucas certificates for the large factor of T_13(313).
    certificates = (
        (51284105359262441,
         (2, 2, 2, 5, 7, 23, 1032841, 7710161), 3),
        (1295309273607968370700398258494227,
         (2, 3, 685093, 6144547567, 51284105359262441), 2),
    )
    proved = set()
    for q, factors, witness in certificates:
        assert prod(factors) == q - 1
        assert all(r in proved or is_prime(r) for r in set(factors))
        assert pow(witness, q - 1, q) == 1
        assert all(pow(witness, (q - 1)//r, q) != 1 for r in set(factors))
        proved.add(q)
    moment = sum((j + 1) * 313**j for j in range(14))
    assert 3 * certificates[-1][0] == moment
    return certificates[-1][0]

@cache
def certified_401_primes():
    """Complete factorization of T_25(401), with Lucas certificates."""
    small = (2777, 2498137)
    assert all(is_prime(q) for q in small)
    certificates = (
        (44854364709863143,
         (2, 3, 7, 19, 21379, 34549, 76099), 3),
        (30486691755424187,
         (2, 19, 67, 593, 15073, 1339669), 2),
        (5525347040369568803507,
         (2, 90619, 30486691755424187), 2),
        (10037566653262838460593813688652541806393,
         (2, 2, 2, 3, 61, 113, 1439, 7631124997,
          5525347040369568803507), 5),
    )
    proved = set()
    for q, factors, witness in certificates:
        assert prod(factors) == q - 1
        assert all(r in proved or is_prime(r) for r in set(factors))
        assert pow(witness, q - 1, q) == 1
        assert all(pow(witness, (q - 1)//r, q) != 1
                   for r in set(factors))
        proved.add(q)
    moment = sum((j + 1) * 401**j for j in range(26))
    answer = small + (certificates[0][0], certificates[-1][0])
    assert prod(answer) == moment
    return answer

@cache
def certified_409_prime():
    """Complete Lucas certificate for T_12(409)."""
    certificates = (
        (319593384716803, (2, 3, 7, 188017, 40471693), 7),
        (3826786260314991211367,
         (2, 5986961, 319593384716803), 5),
        (285498811742277931917137438827867,
         (2, 3, 409, 30401537, 3826786260314991211367), 2),
    )
    proved = set()
    for q, factors, witness in certificates:
        assert prod(factors) == q - 1
        assert all(r in proved or is_prime(r) for r in set(factors))
        assert pow(witness, q - 1, q) == 1
        assert all(pow(witness, (q - 1)//r, q) != 1
                   for r in set(factors))
        proved.add(q)
    moment = sum((j + 1) * 409**j for j in range(13))
    assert certificates[-1][0] == moment
    return certificates[-1][0]

@cache
def certified_419_chain_prime():
    """Lucas certificate for the large factor of T_4(839)."""
    q = 826629447841
    factors = (2, 2, 2, 2, 2, 3, 5, 7, 246020669)
    witness = 13
    assert prod(factors) == q - 1
    assert all(is_prime(r) for r in set(factors))
    assert pow(witness, q - 1, q) == 1
    assert all(pow(witness, (q - 1)//r, q) != 1 for r in set(factors))
    moment = sum((j + 1) * 839**j for j in range(5))
    assert 3 * q == moment
    return q

@cache
def certified_431_primes():
    """Complete factorizations of T_21(431) and T_25(431)."""
    certificates = (
        (50901259, (2, 3, 683, 12421), 2),
        (2036050361, (2, 2, 2, 5, 50901259), 3),
        (182731447799029, (2, 2, 3, 3, 3, 3, 277, 2036050361), 10),
        (408716967719, (2, 29, 5351, 1316921), 7),
        (4636711, (2, 3, 3, 3, 5, 13, 1321), 6),
        (185468441, (2, 2, 2, 5, 4636711), 3),
        (80757992885189113465213993,
         (2, 2, 2, 3, 137, 1013, 133379, 980137, 185468441), 5),
        (2544456102028701855435052121524386993552097,
         (2, 2, 2, 2, 2, 3, 11, 73, 408716967719,
          80757992885189113465213993), 7),
        (3669599, (2, 1834799), 13),
        (66052783, (2, 3, 3, 3669599), 5),
        (61150311611, (2, 5, 43, 859, 165553), 2),
        (2523217, (2, 2, 2, 2, 3, 52567), 10),
        (7212319, (2, 3, 17, 70709), 11),
        (32008271723, (2, 7, 317, 7212319), 2),
        (12741733, (2, 2, 3, 3, 3, 117979), 5),
        (4844271667741331987201,
         (2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 13, 12373, 369319,
          12741733), 3),
        (6591642899211909277635103388839711484157169,
         (2, 2, 2, 2, 3, 3, 3, 3, 13, 2523217, 32008271723,
          4844271667741331987201), 19),
        (3617069, (2, 2, 7, 13, 19, 523), 10),
        (151916899, (2, 3, 7, 3617069), 2),
        (75879569, (2, 2, 2, 2, 17, 31, 8999), 3),
        (105679530977, (2, 2, 2, 2, 2, 41, 107, 752789), 3),
        (5547277, (2, 2, 3, 3, 7, 22013), 2),
        (155323757, (2, 2, 7, 5547277), 2),
        (2725310640323, (2, 31, 283, 155323757), 2),
        (1150081090216307, (2, 211, 2725310640323), 2),
        (89706325036871947, (2, 3, 13, 1150081090216307), 3),
        (8098937527, (2, 3, 53, 197, 129281), 5),
        (1719798921283, (2, 3, 13, 13, 3001, 565163), 3),
        (1387366555902446403685366447,
         (2, 3, 13, 1277, 8098937527, 1719798921283), 3),
        (67621321, (2, 2, 2, 3, 3, 5, 13, 14449), 7),
        (58695306629, (2, 2, 7, 31, 67621321), 2),
        (117390613259, (2, 58695306629), 2),
    )
    proved = set()
    for q, factors, witness in certificates:
        assert prod(factors) == q - 1
        assert all(r in proved or is_prime(r) for r in set(factors))
        assert pow(witness, q - 1, q) == 1
        assert all(pow(witness, (q - 1)//r, q) != 1 for r in set(factors))
        proved.add(q)
    t21 = sum((j + 1) * 431**j for j in range(22))
    t25 = sum((j + 1) * 431**j for j in range(26))
    f21 = (182731447799029,
           2544456102028701855435052121524386993552097)
    f25 = (712183, 66052783, 61150311611,
           6591642899211909277635103388839711484157169)
    chain4 = (3, 6091, 151916899)
    chain21 = (75879569, 105679530977, 89706325036871947,
               1387366555902446403685366447)
    chain433 = (58695306629, 117390613259)
    assert prod(f21) == t21 and prod(f25) == t25
    assert prod(chain4) == sum((j + 1) * 863**j for j in range(5))
    assert prod(chain21) == sum((j + 1) * 863**j for j in range(22))
    assert 3 * chain433[0] == sum((j + 1) * 433**j for j in range(5))
    assert 2 * chain433[0] + 1 == chain433[1]
    assert is_prime(f25[0])
    return f21 + f25 + chain4 + chain21 + chain433

@cache
def certified_439_factors():
    """Prove the prime divisors of the four indicated full local moments."""
    certificates = (
        (25326082891, (2, 3, 3, 3, 3, 5, 2441, 12809), 2),
        (4453357970557, (2, 2, 3, 3, 11, 389, 421, 68669), 2),
        (109672890951493, (2, 2, 3, 3, 11, 30757, 9004511), 6),
        (35264923, (2, 3, 7, 11, 37, 2063), 2),
        (994462289, (2, 2, 2, 2, 167, 372179), 3),
        (118537860234333817, (2, 2, 2, 3, 3, 19, 87133, 994462289), 5),
        (292615995962398080896076371, (2, 5, 7, 35264923, 118537860234333817), 2),
        (585231991924796161792152743, (2, 292615995962398080896076371), 5),
        (667469961894052368039509630751847, (2, 3, 433, 439, 585231991924796161792152743), 3),
    )
    proved = set()
    for q, factors, witness in certificates:
        assert prod(factors) == q-1
        assert all(r in proved or (r <= 10_000_000 and is_prime(r)) for r in set(factors))
        assert pow(witness, q-1, q) == 1
        assert all(gcd(pow(witness, (q-1)//r, q)-1, q) == 1 for r in set(factors))
        proved.add(q)
    factorizations = {
        4: (3, 117563, 527507),
        6: (2, 2, 495571, 25326082891),
        10: (2, 3, 4453357970557, 109672890951493),
        12: (667469961894052368039509630751847,),
    }
    for e, factors in factorizations.items():
        assert prod(factors) == sum((i+1)*439**i for i in range(e+1))
        assert all(r in proved or (r <= 10_000_000 and is_prime(r)) for r in set(factors))
    return tuple(sorted({r for factors in factorizations.values() for r in factors}))


@cache
def certified_443_factors():
    """Prime divisors needed for the least-prime-443 layer."""
    certificates = (
        (8986283, (2, 491, 9151), 2),
        (17972567, (2, 8986283), 5),
        (143780537, (2, 2, 2, 17972567), 3),
        (43629347, (2, 2003, 10891), 2),
        (8277708747617, (2, 2, 2, 2, 2, 7, 7, 11, 11, 43629347), 3),
        (46011457, (2, 2, 2, 2, 2, 2, 3, 3, 3, 26627), 5),
        (29508421, (2, 2, 3, 5, 151, 3257), 6),
        (145830616583, (2, 7, 353, 29508421), 5),
        (12619879, (2, 3, 653, 3221), 3),
        (1728737447, (2, 17, 83, 173, 3541), 5),
        (214367249, (2, 2, 2, 2, 101, 109, 1217), 3),
        (228793984129, (2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 67, 317, 1039), 11),
        (3398084859321368641,
         (2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 5, 191, 228793984129), 7),
        (6584407866379548231030163,
         (2, 3, 3, 3, 3, 3, 3, 3, 443, 3398084859321368641), 3),
        (40563181, (2, 2, 3, 3, 3, 3, 5, 7, 7, 7, 73), 6),
        (6350490490999, (2, 3, 97, 269, 40563181), 6),
        (534103050044875841,
         (2, 2, 2, 2, 2, 2, 5, 31183, 93739, 571001), 3),
        (55908839072597513284199,
         (2, 7, 7477, 534103050044875841), 7),
    )
    proved = set()
    for q, factors, witness in certificates:
        assert prod(factors) == q - 1
        assert all(r in proved or (r <= 10_000_000 and is_prime(r)) for r in set(factors))
        assert pow(witness, q - 1, q) == 1
        assert all(gcd(pow(witness, (q - 1) // r, q) - 1, q) == 1 for r in set(factors))
        proved.add(q)
    factorizations = {
        (443, 4): (3, 18803, 3419963),
        (443, 5): (3, 5, 5, 9511, 143780537),
        (443, 6): (2, 2, 1601, 8277708747617),
        (443, 7): (2, 2, 46011457, 145830616583),
        (443, 8): (613141, 12619879, 1728737447),
        (443, 9): (6584407866379548231030163,),
        (443, 13): (6350490490999, 55908839072597513284199),
        (887, 4): (3, 4817, 214367249),
    }
    for (p, e), factors in factorizations.items():
        assert prod(factors) == sum((j + 1) * p**j for j in range(e + 1))
        assert all(r in proved or (r <= 10_000_000 and is_prime(r)) for r in set(factors))
    return tuple(sorted({r for factors in factorizations.values() for r in factors}))


@cache
def certified_449_factors():
    """Prime divisors needed for the least-prime-449 layer."""
    certificates = (
        (32851801, (2, 2, 2, 3, 3, 5, 5, 18251), 14),
        (60478001, (2, 2, 2, 2, 5, 5, 5, 11, 2749), 6),
        (175265246899, (2, 3, 3, 7, 23, 60478001), 3),
        (1045614797939, (2, 67, 1171, 6663617), 2),
        (16134658021, (2, 2, 3, 3, 5, 13, 59, 116867), 6),
        (4808831238654555181,
         (2, 2, 3, 5, 577, 8609, 16134658021), 2),
        (7188856581307871918843714684616645809,
         (2, 2, 2, 2, 19, 4703, 1045614797939, 4808831238654555181), 3),
        (627033833, (2, 2, 2, 5503, 14243), 3),
        (78237883, (2, 3, 3, 29, 71, 2111), 2),
        (8293215599, (2, 53, 78237883), 7),
        (222468199, (2, 3, 37, 1002109), 6),
        (764402028329, (2, 2, 2, 29, 26731, 123259), 6),
        (38986695749796247573,
         (2, 2, 3, 7, 23, 26399, 764402028329), 5),
        (37870589, (2, 2, 7, 1352521), 2),
        (60971648291, (2, 5, 7, 23, 37870589), 7),
        (1790446499, (2, 419, 997, 2143), 2),
        (25066250987, (2, 7, 1790446499), 2),
        (418762595128002998021459,
         (2, 137, 60971648291, 25066250987), 2),
        (837525190256005996042919,
         (2, 418762595128002998021459), 11),
        (1263954656792831143909399093368946362119406610915119463,
         (2, 3, 29, 222468199, 38986695749796247573,
          837525190256005996042919), 3),
        (68253551466812881771107551041923103554447956989416451003,
         (2, 3, 3, 3,
          1263954656792831143909399093368946362119406610915119463), 3),
    )
    proved = set()
    for q, factors, witness in certificates:
        assert prod(factors) == q - 1
        assert all(r in proved or (r <= 10_000_000 and is_prime(r)) for r in set(factors))
        assert pow(witness, q - 1, q) == 1
        assert all(gcd(pow(witness, (q - 1) // r, q) - 1, q) == 1
                   for r in set(factors))
        proved.add(q)
    factorizations = {
        25: (1003019, 1270103, 32851801, 175265246899,
             7188856581307871918843714684616645809),
        28: (3, 5, 627033833, 8293215599,
             68253551466812881771107551041923103554447956989416451003),
    }
    for e, factors in factorizations.items():
        assert prod(factors) == sum((j + 1) * 449**j for j in range(e + 1))
        assert all(r in proved or (r <= 10_000_000 and is_prime(r)) for r in factors)
    return tuple(sorted({r for factors in factorizations.values() for r in factors}))


@cache
def certified_461_factors():
    """Prime divisors needed for the least-prime-461 layer."""
    certificates = (
        (477647899, (2, 3, 7, 13, 874813), 3),
        (9416347663, (2, 3, 241, 6511997), 3),
        (2406573637623563, (2, 11, 11617, 9416347663), 2),
        (11852263, (2, 3, 3, 43, 15313), 5),
        (514960543, (2, 3, 3, 73, 391903), 3),
        (367681827703, (2, 3, 7, 17, 514960543), 5),
        (104588681334159405337,
         (2, 2, 2, 3, 11852263, 367681827703), 5),
        (4054484820600023507294143,
         (2, 3, 7, 13, 71, 104588681334159405337), 12),
        (21983416697293327456548843347,
         (2, 2711, 4054484820600023507294143), 2),
        (188090113262041709718231903676933,
         (2, 2, 3, 23, 31, 21983416697293327456548843347), 2),
        (1238817912977785312717190787187383817901,
         (2, 2, 5, 5, 7, 97, 97,
          188090113262041709718231903676933), 2),
        (213449622406948886201024974616126238622162775909475855225749,
         (2, 2, 7, 2557, 2406573637623563,
          1238817912977785312717190787187383817901), 2),
        (70158841, (2, 2, 2, 3, 5, 73, 8009), 31),
        (101578151, (2, 5, 5, 2031563), 17),
        (9007375573716328043,
         (2, 13, 1627, 2096221, 101578151), 2),
        (45406477, (2, 2, 3, 3, 97, 13003), 2),
        (1362194311, (2, 3, 5, 45406477), 3),
        (119873099369, (2, 2, 2, 11, 1362194311), 3),
        (958984794953, (2, 2, 2, 119873099369), 3),
        (24933604668779, (2, 13, 958984794953), 2),
        (5086455352430917, (2, 2, 3, 17, 24933604668779), 6),
        (1628381983, (2, 3, 2207, 122971), 3),
        (4878455671, (2, 3, 3, 5, 11, 4927733), 6),
        (925760739339649797305849,
         (2, 2, 2, 7, 2081, 1628381983, 4878455671), 3),
        (379561903129256416895398091,
         (2, 5, 41, 925760739339649797305849), 2),
        (1175337272633976315693605334810791115007970821343,
         (2, 304393, 5086455352430917,
          379561903129256416895398091), 5),
    )
    proved = set()
    for q, factors, witness in certificates:
        assert prod(factors) == q - 1
        assert all(r in proved or (r <= 10_000_000 and is_prime(r))
                   for r in set(factors))
        assert pow(witness, q - 1, q) == 1
        assert all(gcd(pow(witness, (q - 1) // r, q) - 1, q) == 1
                   for r in set(factors))
        proved.add(q)
    factorizations = {
        25: (477647899,
             213449622406948886201024974616126238622162775909475855225749),
        28: (3, 5, 70158841, 9007375573716328043,
             1175337272633976315693605334810791115007970821343),
    }
    for e, factors in factorizations.items():
        assert prod(factors) == sum((j + 1) * 461**j for j in range(e + 1))
        assert all(r in proved or (r <= 10_000_000 and is_prime(r))
                   for r in factors)
    return tuple(sorted({r for factors in factorizations.values() for r in factors}))


@cache
def certified_467_factors():
    """Prime divisors needed for the least-prime-467 layer."""
    certificates = (
        (78249433, (2, 2, 2, 3, 373, 8741), 5),
        (782494331, (2, 5, 78249433), 2),
        (41514787, (2, 3, 3, 709, 3253), 2),
        (1909680203, (2, 23, 41514787), 5),
        (76160799733, (2, 2, 3, 37061, 171251), 5),
    )
    proved = set()
    for q, factors, witness in certificates:
        assert prod(factors) == q - 1
        assert all(r in proved or (r <= 10_000_000 and is_prime(r))
                   for r in set(factors))
        assert pow(witness, q - 1, q) == 1
        assert all(gcd(pow(witness, (q - 1) // r, q) - 1, q) == 1
                   for r in set(factors))
        proved.add(q)
    t9 = (7083499, 782494331, 1909680203)
    assert prod(t9) == sum((j + 1) * 467**j for j in range(10))
    assert all(r in proved or (r <= 10_000_000 and is_prime(r)) for r in t9)
    t57_factor = 76160799733
    assert sum((j + 1) * 467**j for j in range(58)) % t57_factor == 0
    return tuple(sorted(t9 + (t57_factor,)))


@cache
def certified_479_factors():
    """Prime divisors needed for the least-prime-479 layer."""
    certificates = (
        (37650031, (2, 3, 5, 11, 271, 421), 11),
        (79318556486132556604693560491,
         (2, 5, 19, 263, 5323, 1306139, 6063931, 37650031), 2),
        (3840380209, (2, 2, 2, 2, 3, 3, 3, 7, 401, 3167), 11),
        (2263228226288717, (2, 2, 147331, 3840380209), 2),
        (26608781, (2, 2, 5, 11, 79, 1531), 3),
        (42404471, (2, 5, 4240447), 7),
        (37655170249, (2, 2, 2, 3, 37, 42404471), 13),
        (25479149197, (2, 2, 3, 227, 9353579), 2),
        (302386542669997, (2, 2, 3, 23, 43, 25479149197), 2),
        (3407291562805526197,
         (2, 2, 3, 3, 313, 302386542669997), 5),
        (7260968101982946665652131488052126390641693,
         (2, 2, 3, 3, 3, 47, 419, 26608781, 37655170249,
          3407291562805526197), 5),
    )
    proved = set()
    for q, factors, witness in certificates:
        assert prod(factors) == q - 1
        assert all(r in proved or (r <= 10_000_000 and is_prime(r))
                   for r in set(factors))
        assert pow(witness, q - 1, q) == 1
        assert all(gcd(pow(witness, (q - 1) // r, q) - 1, q) == 1
                   for r in set(factors))
        proved.add(q)
    factorizations = {
        4: (3, 9439, 9310879),
        12: (23957, 79318556486132556604693560491),
        25: (68281, 236707, 2263228226288717,
             7260968101982946665652131488052126390641693),
    }
    for e, factors in factorizations.items():
        assert prod(factors) == sum((j + 1) * 479**j for j in range(e + 1))
        assert all(r in proved or (r <= 10_000_000 and is_prime(r))
                   for r in factors)
    return tuple(sorted({r for factors in factorizations.values() for r in factors}))


@cache
def certified_487_factors():
    """Prime divisors needed for the least-prime-487 layer."""
    certificates = (
        (10985291, (2, 5, 157, 6997), 6),
        (2278303, (2, 3, 13, 29209), 5),
    )
    proved = set()
    for q, factors, witness in certificates:
        assert prod(factors) == q - 1
        assert all(r in proved or (r <= 10_000_000 and is_prime(r))
                   for r in set(factors))
        assert pow(witness, q - 1, q) == 1
        assert all(gcd(pow(witness, (q - 1) // r, q) - 1, q) == 1
                   for r in set(factors))
        proved.add(q)
    q9, q60 = (10985291, 2278303)
    assert sum((j + 1) * 487**j for j in range(10)) % q9 == 0
    assert sum((j + 1) * 487**j for j in range(61)) % q60 == 0
    return tuple(sorted((q9, q60)))


@cache
def certified_491_factors():
    """Prime divisor needed for the least-prime-491 layer."""
    q = 74505131977
    factors = (2, 2, 2, 3, 11, 71, 593, 6703)
    witness = 5
    assert prod(factors) == q - 1
    assert all(r <= 10_000_000 and is_prime(r) for r in set(factors))
    assert pow(witness, q - 1, q) == 1
    assert all(gcd(pow(witness, (q - 1) // r, q) - 1, q) == 1
               for r in set(factors))
    assert sum((j + 1) * 983**j for j in range(13)) % q == 0
    return (q,)


@cache
def certified_503_factors():
    """Prime divisors of local moments needed for the least-prime-503 layer."""
    small = (8147, 10899209, 1216541551)
    assert all(is_prime(q) for q in small)
    certificates = (
        (26065693349, (2, 2, 29, 419, 536287), 2),
        (56771080114123, (2, 3, 3, 11, 11, 26065693349), 3),
        (1248963762510707, (2, 11, 56771080114123), 2),
        (140534590487, (2, 19, 7127, 518911), 5),
        (345553861247897, (2, 2, 2, 7, 7, 307, 1783, 1610423), 3),
        (238432164261048931, (2, 3, 5, 23, 345553861247897), 2),
        (690215519345889109,
         (2, 2, 3, 11, 13, 1319, 34513, 8835679), 2),
        (1896712247162503271533,
         (2, 2, 3, 229, 690215519345889109), 2),
        (62102152396594682116533487,
         (2, 3, 3, 17, 107, 1896712247162503271533), 29),
        (266528710821412022109611567232271539726943147,
         (2, 3, 3, 238432164261048931, 62102152396594682116533487), 2),
        (674217058109673310528911325697259879233596325351568766603,
         (2, 3, 3, 140534590487,
          266528710821412022109611567232271539726943147), 2),
        (42659401646883945868279443474872264567866037127544366454869197799153118141861,
         (2, 2, 5, 17, 149, 1248963762510707,
          674217058109673310528911325697259879233596325351568766603), 7),
        (60235013, (2, 2, 17, 47, 47, 401), 2),
        (636202207307, (2, 5281, 60235013), 2),
        (1043371619983481, (2, 2, 2, 5, 41, 636202207307), 6),
        (15191381593, (2, 2, 2, 3, 3, 43, 1447, 3391), 5),
        (2055442091367457571, (2, 5, 197, 1043371619983481), 2),
        (36287411933, (2, 2, 32173, 281971), 2),
        (3701316017167, (2, 3, 17, 36287411933), 21),
        (320066105936828222533,
         (2, 2, 3, 11, 655103, 3701316017167), 14),
        (35248337, (2, 2, 2, 2, 619, 3559), 3),
        (16843662874275183209,
         (2, 2, 2, 23, 11701, 221951, 35248337), 3),
        (235811280239852564927, (2, 7, 16843662874275183209), 5),
    )
    proved = set()
    for q, factors, witness in certificates:
        assert prod(factors) == q - 1
        assert all(r in proved or (r <= 10_000_000 and is_prime(r))
                   for r in set(factors))
        assert pow(witness, q - 1, q) == 1
        assert all(gcd(pow(witness, (q - 1) // r, q) - 1, q) == 1
                   for r in set(factors))
        proved.add(q)
    q28 = 42659401646883945868279443474872264567866037127544366454869197799153118141861
    successor = (31, 1167821, 15191381593, 2055442091367457571,
                 320066105936828222533, 235811280239852564927)
    assert all(is_prime(q) for q in successor[:2])
    assert prod(successor) == 2 * q28 + 1
    assert sum((j + 1) * 503**j for j in range(25)) % 8147 == 0
    assert sum((j + 1) * 503**j for j in range(22)) % 10899209 == 0
    assert sum((j + 1) * 503**j for j in range(25)) % 1216541551 == 0
    assert sum((j + 1) * 503**j for j in range(29)) == 3 * q28
    return tuple(sorted(small + (q28,) + successor))


@cache
def known_prime_divisors(t):
    # Only return divisors proved prime. A large unfactored remainder
    # weakens this shortcut and still goes through the exhaustive bounds.
    if t<=10**12:
        return split_small_moment(t)
    large = pocklington_factor()
    factors = [large] if t % large == 0 else []
    factors.extend(q for q in certified_439_factors() if t % q == 0)
    factors.extend(q for q in certified_443_factors() if t % q == 0)
    factors.extend(q for q in certified_449_factors() if t % q == 0)
    factors.extend(q for q in certified_461_factors() if t % q == 0)
    factors.extend(q for q in certified_467_factors() if t % q == 0)
    factors.extend(q for q in certified_479_factors() if t % q == 0)
    factors.extend(q for q in certified_487_factors() if t % q == 0)
    factors.extend(q for q in certified_491_factors() if t % q == 0)
    factors.extend(q for q in certified_503_factors() if t % q == 0)
    factors.extend(q for q in certified_263_primes() if t % q == 0)
    large_269 = certified_269_prime()
    if t % large_269 == 0:
        factors.append(large_269)
    factors.extend(q for q in certified_269_successor_primes() if t % q == 0)
    factors.extend(q for q in certified_283_primes() if t % q == 0)
    factors.extend(q for q in certified_307_primes() if t % q == 0)
    large_313 = certified_313_prime()
    if t % large_313 == 0:
        factors.append(large_313)
    factors.extend(q for q in certified_401_primes() if t % q == 0)
    q409 = certified_409_prime()
    if t % q409 == 0:
        factors.append(q409)
    q419 = certified_419_chain_prime()
    if t % q419 == 0:
        factors.append(q419)
    factors.extend(q for q in certified_431_primes() if t % q == 0)
    for q in small_primes(100_001):
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

def verify(p, a_min=1, a_max=None, tail_min=0, tail_max=None):
    answers=[]
    patterns=0
    stop = p if a_max is None else a_max
    for a in range(a_min, stop):
        tail_index = -1
        for tail in vectors((p-1)//a):
            if not tail:
                continue
            tail_index += 1
            if tail_index < tail_min or (tail_max is not None and tail_index >= tail_max):
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



