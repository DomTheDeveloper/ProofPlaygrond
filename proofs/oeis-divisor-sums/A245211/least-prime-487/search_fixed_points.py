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
        assert all(r in proved or prime(r) for r in set(factors))
        assert pow(witness, q - 1, q) == 1
        assert all(pow(witness, (q - 1)//r, q) != 1 for r in set(factors))
        proved.add(q)
    return certificates[-1][0]

@cache
def certified_269_successor_primes():
    # The three prime factors of 2*T_13(269)+1.  The middle certificate
    # supplies a factor required by the last Lucas certificate.
    certificates = (
        (13974006881147, (2, 13, 71, 22571, 335381), 2),
        (1596161396191, (2, 3, 5, 47, 89, 127, 100153), 12),
        (1647238560869113, (2, 2, 2, 3, 43, 1596161396191), 5),
    )
    proved = set()
    for q, factors, witness in certificates:
        assert prod(factors) == q - 1
        assert all(r in proved or prime(r) for r in set(factors))
        assert pow(witness, q - 1, q) == 1
        assert all(pow(witness, (q - 1)//r, q) != 1 for r in set(factors))
        proved.add(q)
    small = 47137
    assert prime(small)
    q1, _, q2 = (q for q, _, _ in certificates)
    assert small * q1 * q2 == 2 * certified_269_prime() + 1
    return small, q1, q2

@cache
def certified_283_primes():
    # Complete Lucas certificates for the two large factors of T_13(283).
    certificates = (
        (33311847537949, (2, 2, 3, 7, 193147, 2053201), 2),
        (3498950330708810221,
         (2, 2, 3, 3, 5, 23, 97, 173, 50363928533), 6),
    )
    proved = set()
    for q, factors, witness in certificates:
        assert prod(factors) == q - 1
        assert all(r in proved or prime(r) for r in set(factors))
        assert pow(witness, q - 1, q) == 1
        assert all(pow(witness, (q - 1)//r, q) != 1 for r in set(factors))
        proved.add(q)
    moment, _ = term(13, 283)
    assert 9 * certificates[0][0] * certificates[1][0] == moment
    return certificates[0][0], certificates[1][0]

@cache
def certified_307_primes():
    # Complete deterministic factorization of T_9(307).
    factors = (57427, 96823, 424967, 102818321)
    assert all(prime(q) for q in factors)
    moment, _ = term(9, 307)
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
        assert all(r in proved or prime(r) for r in set(factors))
        assert pow(witness, q - 1, q) == 1
        assert all(pow(witness, (q - 1)//r, q) != 1 for r in set(factors))
        proved.add(q)
    moment, _ = term(13, 313)
    assert 3 * certificates[-1][0] == moment
    return certificates[-1][0]

@cache
def certified_401_primes():
    """Complete factorization of T_25(401), with Lucas certificates."""
    small = (2777, 2498137)
    assert all(prime(q) for q in small)
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
        assert all(r in proved or prime(r) for r in set(factors))
        assert pow(witness, q - 1, q) == 1
        assert all(pow(witness, (q - 1)//r, q) != 1
                   for r in set(factors))
        proved.add(q)
    moment, _ = term(25, 401)
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
        assert all(r in proved or prime(r) for r in set(factors))
        assert pow(witness, q - 1, q) == 1
        assert all(pow(witness, (q - 1)//r, q) != 1
                   for r in set(factors))
        proved.add(q)
    moment, _ = term(12, 409)
    assert certificates[-1][0] == moment
    return certificates[-1][0]

@cache
def certified_419_chain_prime():
    """Lucas certificate for the large factor of T_4(839)."""
    q = 826629447841
    factors = (2, 2, 2, 2, 2, 3, 5, 7, 246020669)
    witness = 13
    assert prod(factors) == q - 1
    assert all(prime(r) for r in set(factors))
    assert pow(witness, q - 1, q) == 1
    assert all(pow(witness, (q - 1)//r, q) != 1 for r in set(factors))
    moment, _ = term(4, 839)
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
        assert all(r in proved or prime(r) for r in set(factors))
        assert pow(witness, q - 1, q) == 1
        assert all(pow(witness, (q - 1)//r, q) != 1 for r in set(factors))
        proved.add(q)
    t21, _ = term(21, 431)
    t25, _ = term(25, 431)
    f21 = (182731447799029,
           2544456102028701855435052121524386993552097)
    f25 = (712183, 66052783, 61150311611,
           6591642899211909277635103388839711484157169)
    chain4 = (3, 6091, 151916899)
    chain21 = (75879569, 105679530977, 89706325036871947,
               1387366555902446403685366447)
    chain433 = (58695306629, 117390613259)
    assert prod(f21) == t21 and prod(f25) == t25
    assert prod(chain4) == term(4, 863)[0]
    assert prod(chain21) == term(21, 863)[0]
    assert 3 * chain433[0] == term(4, 433)[0]
    assert 2 * chain433[0] + 1 == chain433[1]
    assert prime(f25[0])
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
        assert all(r in proved or (r <= 10_000_000 and prime(r)) for r in set(factors))
        assert pow(witness, q-1, q) == 1
        assert all(pow(witness, (q-1)//r, q) != 1 for r in set(factors))
        proved.add(q)
    factorizations = {
        4: (3, 117563, 527507),
        6: (2, 2, 495571, 25326082891),
        10: (2, 3, 4453357970557, 109672890951493),
        12: (667469961894052368039509630751847,),
    }
    for e, factors in factorizations.items():
        assert prod(factors) == term(e,439)[0]
        assert all(r in proved or (r <= 10_000_000 and prime(r)) for r in set(factors))
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
        assert all(r in proved or (r <= 10_000_000 and prime(r)) for r in set(factors))
        assert pow(witness, q - 1, q) == 1
        assert all(pow(witness, (q - 1) // r, q) != 1 for r in set(factors))
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
        assert prod(factors) == term(e, p)[0]
        assert all(r in proved or (r <= 10_000_000 and prime(r)) for r in set(factors))
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
        assert all(r in proved or (r <= 10_000_000 and prime(r)) for r in set(factors))
        assert pow(witness, q - 1, q) == 1
        assert all(pow(witness, (q - 1) // r, q) != 1 for r in set(factors))
        proved.add(q)
    factorizations = {
        25: (1003019, 1270103, 32851801, 175265246899,
             7188856581307871918843714684616645809),
        28: (3, 5, 627033833, 8293215599,
             68253551466812881771107551041923103554447956989416451003),
    }
    for e, factors in factorizations.items():
        assert prod(factors) == term(e, 449)[0]
        assert all(r in proved or (r <= 10_000_000 and prime(r)) for r in factors)
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
        assert all(r in proved or (r <= 10_000_000 and prime(r))
                   for r in set(factors))
        assert pow(witness, q - 1, q) == 1
        assert all(pow(witness, (q - 1) // r, q) != 1
                   for r in set(factors))
        proved.add(q)
    factorizations = {
        25: (477647899,
             213449622406948886201024974616126238622162775909475855225749),
        28: (3, 5, 70158841, 9007375573716328043,
             1175337272633976315693605334810791115007970821343),
    }
    for e, factors in factorizations.items():
        assert prod(factors) == term(e, 461)[0]
        assert all(r in proved or (r <= 10_000_000 and prime(r))
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
        assert all(r in proved or (r <= 10_000_000 and prime(r))
                   for r in set(factors))
        assert pow(witness, q - 1, q) == 1
        assert all(pow(witness, (q - 1) // r, q) != 1
                   for r in set(factors))
        proved.add(q)
    t9 = (7083499, 782494331, 1909680203)
    assert prod(t9) == term(9, 467)[0]
    assert all(r in proved or (r <= 10_000_000 and prime(r)) for r in t9)
    t57_factor = 76160799733
    assert term(57, 467)[0] % t57_factor == 0
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
        assert all(r in proved or (r <= 10_000_000 and prime(r))
                   for r in set(factors))
        assert pow(witness, q - 1, q) == 1
        assert all(pow(witness, (q - 1) // r, q) != 1
                   for r in set(factors))
        proved.add(q)
    factorizations = {
        4: (3, 9439, 9310879),
        12: (23957, 79318556486132556604693560491),
        25: (68281, 236707, 2263228226288717,
             7260968101982946665652131488052126390641693),
    }
    for e, factors in factorizations.items():
        assert prod(factors) == term(e, 479)[0]
        assert all(r in proved or (r <= 10_000_000 and prime(r))
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
        assert all(r in proved or (r <= 10_000_000 and prime(r))
                   for r in set(factors))
        assert pow(witness, q - 1, q) == 1
        assert all(pow(witness, (q - 1) // r, q) != 1
                   for r in set(factors))
        proved.add(q)
    q9, q60 = (10985291, 2278303)
    assert term(9, 487)[0] % q9 == 0
    assert term(60, 487)[0] % q60 == 0
    return tuple(sorted((q9, q60)))


@cache
def small_factors(x):
    """Return proven prime divisors, stopping trial division at 2000."""
    # This additional trial divisor occurs in T_9(227). Recheck both
    # divisibility and primality before using it in the forcing argument.
    ans=[q for q in (96893,) if x % q == 0 and prime(q)]
    ans.extend(q for q in certified_439_factors() if x % q == 0)
    ans.extend(q for q in certified_443_factors() if x % q == 0)
    ans.extend(q for q in certified_449_factors() if x % q == 0)
    ans.extend(q for q in certified_461_factors() if x % q == 0)
    ans.extend(q for q in certified_467_factors() if x % q == 0)
    ans.extend(q for q in certified_479_factors() if x % q == 0)
    ans.extend(q for q in certified_487_factors() if x % q == 0)
    large = certified_large_prime()
    if x % large == 0:
        ans.append(large)
    for q in certified_263_primes():
        if x % q == 0:
            ans.append(q)
    large_269 = certified_269_prime()
    if x % large_269 == 0:
        ans.append(large_269)
    for q in certified_269_successor_primes():
        if x % q == 0:
            ans.append(q)
    for q in certified_283_primes():
        if x % q == 0:
            ans.append(q)
    for q in certified_307_primes():
        if x % q == 0:
            ans.append(q)
    large_313 = certified_313_prime()
    if x % large_313 == 0:
        ans.append(large_313)
    for q in certified_401_primes():
        if x % q == 0:
            ans.append(q)
    q409 = certified_409_prime()
    if x % q409 == 0:
        ans.append(q409)
    q419 = certified_419_chain_prime()
    if x % q419 == 0:
        ans.append(q419)
    for q in certified_431_primes():
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



