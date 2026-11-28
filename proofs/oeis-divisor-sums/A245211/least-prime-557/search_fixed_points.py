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
def certified_491_factors():
    """Prime divisor needed for the least-prime-491 layer."""
    q = 74505131977
    factors = (2, 2, 2, 3, 11, 71, 593, 6703)
    witness = 5
    assert prod(factors) == q - 1
    assert all(r <= 10_000_000 and prime(r) for r in set(factors))
    assert pow(witness, q - 1, q) == 1
    assert all(pow(witness, (q - 1) // r, q) != 1
               for r in set(factors))
    assert term(12, 983)[0] % q == 0
    return (q,)


@cache
def certified_503_factors():
    """Prime divisors of local moments needed for the least-prime-503 layer."""
    small = (8147, 10899209, 1216541551)
    assert all(prime(q) for q in small)
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
        assert all(r in proved or (r <= 10_000_000 and prime(r))
                   for r in set(factors))
        assert pow(witness, q - 1, q) == 1
        assert all(pow(witness, (q - 1) // r, q) != 1
                   for r in set(factors))
        proved.add(q)
    q28 = 42659401646883945868279443474872264567866037127544366454869197799153118141861
    successor = (31, 1167821, 15191381593, 2055442091367457571,
                 320066105936828222533, 235811280239852564927)
    assert all(prime(q) for q in successor[:2])
    assert prod(successor) == 2 * q28 + 1
    assert term(24, 503)[0] % 8147 == 0
    assert term(21, 503)[0] % 10899209 == 0
    assert term(24, 503)[0] % 1216541551 == 0
    assert term(28, 503)[0] == 3 * q28
    return tuple(sorted(small + (q28,) + successor))


@cache
def certified_509_factors():
    """Prime divisors needed for the least-prime-509 forced chains."""
    certificates = (
        (10836929, (2, 2, 2, 2, 2, 2, 169327), 3),
        (21673859, (2, 10836929), 2),
        (2760707698398197, (2, 2, 6011, 71039, 1616281), 2),
        (93444854619392980475433187993,
         (2, 2, 2, 3, 65071, 21673859, 2760707698398197), 5),
        (47656875855890420042470925876431,
         (2, 3, 5, 17, 93444854619392980475433187993), 15),
        (408396682273, (2, 2, 2, 2, 2, 3, 173, 3121, 7879), 5),
        (224497381922542986239249612899949,
         (2, 2, 11927, 12637, 2430469, 375149, 408396682273), 2),
        (185564932806599, (2, 281, 743, 1879, 236507), 11),
        (29922992681, (2, 2, 2, 5, 7, 7, 17, 367, 2447), 3),
        (19239037, (2, 2, 3, 17, 94309), 23),
        (76956149, (2, 2, 19239037), 2),
        (869142746807, (2, 5647, 76956149), 5),
        (49889887541663900558719332444584615929,
         (2, 2, 2, 3, 3, 5591, 65699, 72533, 29922992681,
          869142746807), 13),
        (32423297, (2, 2, 2, 2, 2, 2, 2, 253307), 3),
        (453926159, (2, 7, 32423297), 7),
        (4915000331, (2, 5, 29, 127, 133451), 10),
        (720137059, (2, 3, 109, 1101127), 2),
        (6237612169, (2, 2, 2, 3, 449, 578843), 7),
        (30104952944559148047643,
         (2, 3, 1117, 720137059, 6237612169), 2),
        (63721451, (2, 5, 5, 13, 13, 7541), 10),
        (197752903, (2, 3, 239, 239, 577), 5),
        (30033128884417,
         (2, 2, 2, 2, 2, 2, 3, 7, 113, 197752903), 10),
        (11297109169, (2, 2, 2, 2, 3, 3, 41, 1913467), 7),
        (120344677, (2, 2, 3, 41, 244603), 5),
        (43963789187, (2, 43, 67, 1201, 6353), 2),
        (2637827351221, (2, 2, 3, 5, 43963789187), 2),
        (1904690883386740803703,
         (2, 3, 120344677, 2637827351221), 3),
        (56620216386372062357735651567,
         (2, 41, 362521, 1904690883386740803703), 5),
        (13432640863, (2, 3, 19, 53, 2223211), 3),
        (253154431, (2, 3, 3, 3, 5, 103, 9103), 3),
        (3616564201267, (2, 3, 2381, 253154431), 2),
        (61613411555644724077933,
         (2, 2, 3, 7, 163, 1244263, 3616564201267), 5),
        (357536518461153958590548414946509329,
         (2, 2, 2, 2, 3, 3, 3, 13432640863,
          61613411555644724077933), 7),
        (988383107, (2, 31, 757, 21059), 2),
        (10347037367, (2, 19, 2851, 95507), 5),
        (111870677, (2, 2, 17, 1645157), 2),
        (671224063, (2, 3, 111870677), 3),
        (149011741987, (2, 3, 37, 671224063), 3),
        (138395989, (2, 2, 3, 3, 3844333), 6),
        (3603001177627, (2, 3, 4339, 138395989), 5),
        (175396211, (2, 5, 11, 389, 4099), 6),
        (6665056019, (2, 19, 175396211), 2),
        (8677902936739, (2, 3, 7, 31, 6665056019), 2),
        (22101577431521824321,
         (2, 2, 2, 2, 2, 2, 3, 5, 7, 379, 8677902936739), 13),
        (24494257, (2, 2, 2, 2, 3, 3, 170099), 5),
        (130353144994489,
         (2, 2, 2, 3, 13, 37, 461, 24494257), 11),
        (93857557, (2, 2, 3, 13, 601651), 5),
        (392019731, (2, 5, 173, 226601), 2),
        (784039463, (2, 392019731), 5),
        (25089262817, (2, 2, 2, 2, 2, 784039463), 3),
        (3010711538041, (2, 2, 2, 3, 5, 25089262817), 38),
        (366195451, (2, 3, 5, 5, 691, 3533), 2),
        (87367747323221,
         (2, 2, 5, 7, 13, 29, 41, 101, 399739), 3),
        (57580356307, (2, 3, 11, 41131, 21211), 2),
        (525016991, (2, 5, 3583, 14653), 7),
        (400601614574767, (2, 3, 11, 11, 1051, 525016991), 3),
        (18427674270439283, (2, 23, 400601614574767), 2),
        (109850683, (2, 3, 127, 144161), 2),
        (112047696661, (2, 2, 3, 5, 17, 109850683), 2),
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
        (509, 4): (3, 112047696661),
        (1019, 4): (3, 2207, 2341, 348083),
        (1019, 12): (23, 14879, 47656875855890420042470925876431),
        (1019, 13): (6701, 11897, 224497381922542986239249612899949),
        (1019, 21): (446603, 7907833, 185564932806599,
                     49889887541663900558719332444584615929),
        (2039, 4): (3, 53, 1733, 4153, 75553),
        (2039, 12): (453926159, 4915000331, 30104952944559148047643),
        (2039, 13): (53, 1579, 1709, 16091, 43189, 775367,
                     63721451, 30033128884417),
        (4079, 4): (3, 40849, 11297109169),
        (4079, 12): (401, 1031, 28817, 408943,
                     56620216386372062357735651567),
        (4079, 13): (19, 601, 14009, 21187,
                     357536518461153958590548414946509329),
        (8159, 4): (3, 11, 11, 13, 4751, 988383107),
        (8159, 12): (109, 3603001177627, 22101577431521824321,
                     130353144994489),
        (16319, 4): (3, 19, 61, 9857, 10347037367),
        (32639, 4): (3, 43, 295201, 149011741987),
    }
    partial_4079_28 = (3, 5, 5653, 14153, 36061, 93857557,
                       3010711538041)
    partial_1019_28 = (3, 5, 239, 3943, 346607, 366195451,
                       57580356307)
    partial_2039_28 = (3, 5, 87367747323221, 18427674270439283)
    for (q, e), factors in factorizations.items():
        assert prod(factors) == term(e, q)[0]
        assert all(r in proved or prime(r) for r in set(factors))
    assert term(28, 4079)[0] % prod(partial_4079_28) == 0
    assert all(r in proved or prime(r) for r in set(partial_4079_28))
    assert term(28, 1019)[0] % prod(partial_1019_28) == 0
    assert all(r in proved or prime(r) for r in set(partial_1019_28))
    assert term(28, 2039)[0] % prod(partial_2039_28) == 0
    assert all(r in proved or prime(r) for r in set(partial_2039_28))
    return tuple(sorted({r for fs in factorizations.values() for r in fs} |
                        set(partial_4079_28) | set(partial_1019_28) |
                        set(partial_2039_28)))


@cache
def certified_523_factors():
    """Prime divisors needed for the least-prime-523 forced chain."""
    certificates = (
        (34342883, (2, 7, 37, 167, 397), 2),
        (507000397, (2, 2, 3, 7, 6035719), 2),
        (2028001589, (2, 2, 507000397), 2),
        (23264769079, (2, 3, 3, 3, 503, 856519), 3),
        (232647690791, (2, 5, 23264769079), 17),
        (103918988891, (2, 5, 29, 547, 655103), 2),
        (2689444028197928641384331,
         (2, 5, 41, 821, 34342883, 232647690791), 6),
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
    large = (2028001589, 2689444028197928641384331)
    successor_one = (593, 6839803)
    successor_two = (31, 37, 7349, 6140531, 103918988891)
    assert term(12, 523)[0] == prod(large)
    assert 2 * large[0] + 1 == prod(successor_one)
    assert 2 * large[1] + 1 == prod(successor_two)
    assert all(q in proved or prime(q)
               for q in set(large + successor_one + successor_two))
    return tuple(sorted(set(large + successor_one + successor_two)))


@cache
def certified_547_factors():
    """Prime divisors needed for the least-prime-547 forced chains."""
    certificates = (
        (23978780431, (2, 3, 5, 11, 1747, 41593), 11),
        (5370245393, (2, 2, 2, 2, 263, 307, 4157), 3),
        (107727122583581, (2, 2, 5, 17, 59, 5370245393), 2),
        (1393354351, (2, 3, 3, 5, 5, 1453, 2131), 3),
        (38541389, (2, 2, 53, 137, 1327), 2),
        (652659881327, (2, 8467, 38541389), 5),
        (1729809749469080801,
         (2, 2, 2, 2, 2, 5, 5, 3313, 652659881327), 3),
        (15985853621, (2, 2, 5, 11, 1747, 41593), 2),
        (6552346121, (2, 2, 2, 5, 41, 97, 41189), 6),
        (13104692243, (2, 6552346121), 2),
        (928902901, (2, 2, 3, 5, 5, 1453, 2131), 2),
        (6224595469, (2, 2, 3, 7, 13, 5700179), 2),
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
    t9 = (17, 23978780431, 107727122583581)
    t13 = (3, 7, 23, 4728181, 1393354351, 1729809749469080801)
    successors = (3, 7, 11, 31, 41, 223, 401, 523, 7309,
                  15985853621, 13104692243, 928902901, 6224595469)
    assert term(9, 547)[0] == prod(t9)
    assert term(13, 547)[0] == prod(t13)
    assert 2 * 23978780431 + 1 == 3 * 15985853621
    assert 2 * 107727122583581 + 1 == 41 * 401 * 13104692243
    assert 2 * 4728181 + 1 == 3 * 3 * 7 * 7 * 41 * 523
    assert 2 * 1393354351 + 1 == 3 * 928902901
    assert (2 * 1729809749469080801 + 1 ==
            11 * 31 * 223 * 7309 * 6224595469)
    assert all(q in proved or prime(q)
               for q in set(t9 + t13 + successors))
    return tuple(sorted(set(t9 + t13 + successors)))


def _jacobi(a, n):
    """Jacobi symbol (a/n), for the Lucas n+1 certificate below."""
    a %= n
    ans = 1
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5):
                ans = -ans
        a, n = n, a
        if a % 4 == n % 4 == 3:
            ans = -ans
        a %= n
    return ans if n == 1 else 0


def _matmul2(a, b, modulus):
    return ((a[0]*b[0] + a[1]*b[2]) % modulus,
            (a[0]*b[1] + a[1]*b[3]) % modulus,
            (a[2]*b[0] + a[3]*b[2]) % modulus,
            (a[2]*b[1] + a[3]*b[3]) % modulus)


def _lucas_u(index, p, q, modulus):
    """U_index(P,Q) modulo modulus by binary matrix powering."""
    if index == 0:
        return 0
    result = (1, 0, 0, 1)
    base = (p % modulus, (-q) % modulus, 1, 0)
    exponent = index - 1
    while exponent:
        if exponent & 1:
            result = _matmul2(result, base, modulus)
        base = _matmul2(base, base, modulus)
        exponent //= 2
    return result[0]


@cache
def certified_557_factors():
    """Prime divisors needed for the least-prime-557 forced chains."""
    certificates = (
        (10794083, (2, 13, 17, 24421), 2),
        (239723414648741, (2, 2, 5, 11, 29, 59, 59, 10794083), 2),
        (26629171, (2, 3, 5, 23, 38593), 3),
        (5260752506077, (2, 2, 3, 101, 163, 26629171), 2),
        (999542976154631, (2, 5, 19, 5260752506077), 29),
        (146595611, (2, 5, 7, 157, 13339), 2),
        (21942579359, (2, 7, 7, 83, 2697637), 7),
        (37665699571, (2, 3, 3, 3, 5, 149, 936259), 10),
        (10713596782868836397,
         (2, 2, 29, 167, 14683, 37665699571), 2),
        (1516340097310772305818210989387586236333,
         (2, 2, 11, 146595611, 21942579359,
          10713596782868836397), 2),
        (143955907, (2, 3, 101, 139, 1709), 2),
        (160654792213, (2, 2, 3, 3, 31, 143955907), 5),
        (380907011, (2, 5, 11, 3462791), 6),
        (132555639829, (2, 2, 3, 29, 380907011), 2),
        (1219246775147143, (2, 3, 3, 7, 73, 132555639829), 3),
        (42394295929, (2, 2, 2, 3, 53, 1093, 30493), 11),
        (18766987, (2, 3, 7, 73, 6121), 2),
        (15645941, (2, 2, 5, 782297), 3),
        (51951569, (2, 2, 2, 2, 43, 75511), 3),
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

    # Lucas's n+1 criterion for the 73-digit factor of T_28(557).
    huge = 9312304158704552410728341941717457119840870664004687487146354658536155089
    plus_factors = (2, 5, 11, 233, 239723414648741,
                    999542976154631,
                    1516340097310772305818210989387586236333)
    assert prod(plus_factors) == huge + 1
    assert all(r in proved or (r <= 10_000_000 and prime(r))
               for r in set(plus_factors))
    assert _jacobi(-43, huge) == -1
    assert _lucas_u(huge + 1, 1, 11, huge) == 0
    assert all(gcd(_lucas_u((huge + 1) // r, 1, 11, huge), huge) == 1
               for r in set(plus_factors))

    t4 = (3, 160654792213)
    t9 = (42394295929, 1219246775147143)
    t28 = (3, 79601, huge)
    successors = (3, 13, 17, 439, 3622051, 15645941,
                  18766987, 51951569)
    assert term(4, 557)[0] == prod(t4)
    assert term(9, 557)[0] == prod(t9)
    assert term(28, 557)[0] == prod(t28)
    assert 2 * 160654792213 + 1 == 3 * 13 * 439 * 18766987
    assert 2 * 42394295929 + 1 == 3**4 * 17**2 * 3622051
    assert 2 * 1219246775147143 + 1 == 3 * 15645941 * 51951569
    assert all(q in proved or q == huge or prime(q)
               for q in set(t4 + t9 + t28 + successors))
    return tuple(sorted(set(t4 + t9 + t28 + successors)))


@cache
def certified_557_exceptional_shapes():
    """Exclude the two expensive orderings of (4,33,1,1) exactly."""
    p = 557
    q = 160654792213
    c_num = term(4, p)[0] * term(33, q)[0]
    c_den = term(4, p)[1] * term(33, q)[1]
    delta = 681 * c_den - 4 * c_num
    # If both exponent-one primes exceed q, positivity already fails.
    assert 2 * c_num < delta * q
    # In the remaining ordering p < r < q < s.  Since s > r,
    # 2c/delta < r < 4c/delta.  The displayed formula is the unique s.
    lower = 2 * c_num // delta
    upper = 4 * c_num // delta + 1
    assert lower < upper < q
    for r in range(max(p + 1, lower), upper + 1):
        if not prime(r):
            continue
        denominator = delta * r - 2 * c_num
        s, remainder = divmod(c_num * (2 * r + 1), denominator)
        assert remainder or s <= q or not prime(s)
    return True


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
    ans.extend(q for q in certified_491_factors() if x % q == 0)
    ans.extend(q for q in certified_503_factors() if x % q == 0)
    ans.extend(q for q in certified_509_factors() if x % q == 0)
    ans.extend(q for q in certified_523_factors() if x % q == 0)
    ans.extend(q for q in certified_547_factors() if x % q == 0)
    ans.extend(q for q in certified_557_factors() if x % q == 0)
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
            if smallest == 557 and es in ((4, 1, 33, 1), (4, 33, 1, 1)):
                assert certified_557_exceptional_shapes()
                continue
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



