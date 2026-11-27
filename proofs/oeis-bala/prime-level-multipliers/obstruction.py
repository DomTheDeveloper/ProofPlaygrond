"""Check both prime-level Bala obstruction sums in the field of p elements."""
from math import isqrt
from argparse import ArgumentParser


def primes_up_to(limit):
    return [p for p in range(7, limit + 1)
            if all(p % j for j in range(2, isqrt(p) + 1))]


def obstruction(p):
    inv = [0, 1] + [0] * (p - 2)
    for s in range(2, p):
        inv[s] = -(p // s) * inv[p % s] % p
    apery = [1, 3]
    for s in range(2, p):
        numerator = (11*s*(s-1)+3)*apery[-1] + (s-1)**2*apery[-2]
        apery.append(numerator * inv[s]**2 % p)
    answers = []
    for first, previous in ((1, 2), (2, -1)):
        seed = [0] + [(first*apery[s] + previous*apery[s-1])*inv[5] % p
                      for s in range(1, p)]
        answers.append(sum(seed[s]*seed[p-s]*inv[s]**2 for s in range(1,p)) % p)
    return tuple(answers)


if __name__ == "__main__":
    args = ArgumentParser(description=__doc__)
    args.add_argument("cutoff", type=int)
    upper = args.parse_args().cutoff
    assert upper >= 7
    primes = primes_up_to(upper)
    bad = [(p, pair) for p in primes if (pair := obstruction(p)) != (0, 0)]
    print("tested", len(primes), "primes, from", primes[0], "to", primes[-1])
    print("nonzero obstruction pairs:", bad)
    assert not bad
