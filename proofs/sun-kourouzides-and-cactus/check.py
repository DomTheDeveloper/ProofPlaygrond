from collections import Counter

from functools import lru_cache

from itertools import combinations, combinations_with_replacement, product

from math import gcd, isqrt

from pathlib import Path

import json

def prime_counts(limit):
    flags = bytearray([1]) * (limit + 1)
    flags[:2] = b'\x00\x00'
    for p in range(2, isqrt(limit) + 1):
        if flags[p]:
            for multiple in range(p * p, limit + 1, p):
                flags[multiple] = 0
    result = []
    running = 0
    for flag in flags:
        running += flag
        result.append(running)
    return result

def prime_checks():
    pi = prime_counts(124 ** 2)
    block = {(n, k): pi[k*n]**(k+1) - pi[(k+1)*n]**k
             for n in range(5, 17) for k in range(1, 16//n+1)}
    square = {n: pi[n*n]**(n+1) - pi[(n+1)**2]**n for n in range(3, 124)}
    assert len(block) == 17 and min(block.values()) == 4
    assert len(square) == 121 and min(square.values()) == 40
    return {'block_cases': len(block), 'block_min_gap': min(block.values()),
            'square_cases': len(square), 'square_min_gap': min(square.values())}

def divide_monic(numerator, divisor):
    work = list(numerator)
    degree = len(divisor) - 1
    quotient = [0] * max(0, len(work) - degree)
    for high in range(len(work)-1, degree-1, -1):
        coefficient = work[high]
        shift = high - degree
        quotient[shift] = coefficient
        for j, value in enumerate(divisor):
            work[shift+j] -= coefficient * value
    return tuple(quotient), tuple(work[:degree])

@lru_cache(None)
def cyclotomic(order):
    # X^m-1 is the product of Phi_d for d dividing m.
    p = (-1,) + (0,) * (order-1) + (1,)
    for d in range(1, order):
        if order % d == 0:
            p, remainder = divide_monic(p, cyclotomic(d))
            assert not any(remainder)
    return p

def power_residues(order):
    modulus = cyclotomic(order)
    basis = (1,) + (0,) * (len(modulus)-2)
    powers = []
    for _ in range(order):
        powers.append(basis)
        leading = basis[-1]
        basis = tuple(c - leading*d for c,d in zip((0,)+basis[:-1], modulus[:-1]))
    assert basis == powers[0]
    return powers

def triangle_grid():
    powers = power_residues(60)
    sine = {n: tuple(a-b for a,b in zip(powers[n%60], powers[-n%60]))
            for n in range(-14, 15)}
    ordinary = set()
    exceptional = set()
    admissible = 0
    for a,b,c in product(range(-14, 15), repeat=3):
        if max(abs(a+b), abs(a+c), abs(b+c)) >= 10:
            continue
        admissible += 1
        if any(x+y+z for x,y,z in zip(sine[a],sine[b],sine[c])):
            continue
        key = tuple(sorted((a,b,c)))
        if key[1] == 0 and key[0] == -key[2]:
            ordinary.add((a,b,c))
        else:
            exceptional.add((a,b,c))
    orbits = sorted({tuple(sorted(t)) for t in exceptional})
    assert len(ordinary) == 55 and len(exceptional) == 12
    assert orbits == [(-9,3,5),(-5,-3,9)]
    return {'grid_examined': 29**3, 'inside_pair_bounds': admissible,
            'ordinary': len(ordinary), 'exceptional': len(exceptional),
            'exceptional_sorted': orbits}

def direct_ceva(division_count):
    # Direct, exact product-of-sines comparison. The common (2i)^3 cancels.
    order = 6 * division_count
    powers = power_residues(order)
    def terms(triple):
        cache = Counter()
        for signs in product((-1,1), repeat=3):
            exponent = sum(v*s for v,s in zip(triple, signs)) % order
            cache[exponent] += signs[0]*signs[1]*signs[2]
        return cache
    total = 0
    for triple in combinations_with_replacement(range(1,division_count),3):
        delta = terms(triple)
        delta.subtract(terms(tuple(division_count-x for x in triple)))
        pairs = [(powers[e],c) for e,c in delta.items() if c]
        if any(sum(c*v[j] for v,c in pairs) for j in range(len(powers[0]))):
            continue
        total += {1:1, 2:3, 3:6}[len(set(triple))]
    return total

def four_squares(limit=100_000):
    # A witness for each 8b+7 up to the cutoff. Only residues 1+1+1+4
    # modulo 8 are possible. Other classes follow by the paper argument.
    witnesses = {}
    for x in range(1, isqrt(limit)+1):
        if x % 4 == 0:
            continue
        x2 = x*x
        for y in range(1, isqrt(limit-x2)+1):
            if y%4==0 or (x%2==0 and y%2==0):
                continue
            m = 1680*y**3
            remainder = limit-x2-y*y
            for z in range(1, isqrt(remainder)+1):
                residue = (x2+y*y+z*z) % 8
                if residue not in (3,6):
                    continue
                val = x2*x2 + m*z
                if isqrt(val)**2 != val:
                    continue
                w_start, stride = (2,4) if residue==3 else (1,2)
                base = x2+y*y+z*z
                for w in range(w_start,isqrt(limit-base)+1,stride):
                    n = base+w*w
                    if n not in witnesses:
                        witnesses[n] = (x,y,z,w)
    assert len(witnesses) == (limit+1)//8
    for n in range(7,limit+1,8):
        x,y,z,w = witnesses[n]
        assert x*x+y*y+z*z+w*w==n
        assert isqrt(x**4+1680*y**3*z)**2 == x**4+1680*y**3*z
    return {'limit':limit, 'odd_core_witnesses':len(witnesses)}

if __name__ == '__main__':
    checks = {'prime_counts':prime_checks(), 'triangle_grid':triangle_grid()}
    counts = {h:direct_ceva(h) for h in range(2, 31)}
    for h, actual in counts.items():
        expected = 0 if h%2 else 3*h-5+12*(h%10==0)
        assert actual == expected, (h, actual, expected)
    checks['direct_ceva'] = {'division_counts': [2,30], 'exact_counts':list(counts.values())}
    checks['sun_1680'] = four_squares()
    print(json.dumps(checks, indent=2))
