"""Exact A245212 search with two odd prime factors and prescribed v_2(n)."""
from argparse import ArgumentParser
from fractions import Fraction as F
from functools import lru_cache
from math import isqrt


def prime(x):
    return x >= 2 and all(x % d for d in range(2, isqrt(x) + 1))


@lru_cache(maxsize=12000)
def local(p, i):
    power = p ** (i - 1)
    sigma = (p * power - 1) // (p - 1)
    moment = (i * p * power - sigma) // (p - 1)
    return power, moment, sigma


def z(p, i):
    return F(p**i - 1, i * p**i)


def classify(k):
    h = 2 ** (k + 1)
    u, v = k * h + 1, h - 1
    weight = F(v, u)
    target = 1 + weight
    hits = set()
    small_anchors = candidate_tests = supports = prefix_tests = 0

    def fixed_index(p, i):
        nonlocal small_anchors, candidate_tests
        small_anchors += 1
        power, tm, sm = local(p, i)
        T, S = u * tm, v * sm
        b = h * (k + 1) * power * i - T
        if b <= 0:
            return
        # q^(j-2) <= T+S, q >= p+2.
        jmax, step = 2, 1
        while step * (p + 2) <= T + S:
            step *= p + 2
            jmax += 1
        for j in range(max(2, S // b + 1), jmax + 1):
            g = j * b - S
            first = (j - 1) * T + S
            q = (first + g - 1) // g
            candidate_tests += 1
            if q <= p or q % 2 == 0 or (T + S) % q:
                continue
            qpower, tq, sq = local(q, j)
            if T * tq + S * sq == h * (k + 1) * power * i * qpower * j and prime(q):
                hits.add((p, i - 1, q, j - 1))

    def fixed_support(p, q):
        nonlocal prefix_tests, supports
        supports += 1
        d = 1 - target * F((p - 1) * (q - 1), p * q)
        for first, last in ((p, q), (q, p)):
            alpha, beta = F(1, first - 1), F(1, last - 1)
            cap = (alpha + beta) / d if d > 0 else (alpha * beta + weight) / (alpha + beta)
            for i in range(2, int(cap) + 1):
                prefix_tests += 1
                x = z(first, i)
                den = beta - (alpha * beta + weight) * x
                num = d - alpha * x
                if not den:
                    assert num != 0, "unrestricted equality ray"
                    continue
                need = num / den
                if need <= 0:
                    continue
                j = need.denominator // need.numerator
                if j < i or j > need.denominator.bit_length():
                    continue
                if z(last, j) == need:
                    factors = sorted(((first, i - 1), (last, j - 1)))
                    hits.add((*factors[0], *factors[1]))

    p = 3
    while F(p, p - 1)**2 * (1 + weight / 4) > target:
        if prime(p):
            cap_p = F(p, p - 1)
            assert cap_p != target
            if cap_p > target:
                i = 2
                while True:
                    power, tm, _ = local(p, i)
                    if F(tm, power * i) >= target:
                        break
                    fixed_index(p, i)
                    i += 1
            else:
                # Leave a positive margin for the last prime even at infinite index.
                cutoff = max(2, 1 + int(weight * cap_p / (target - cap_p)))
                for i in range(2, cutoff):
                    fixed_index(p, i)
                upper = cap_p * (1 + weight / (2 * cutoff))
                last = int(target / (target - upper))
                for q in range(p + 2, last + 1, 2):
                    if prime(q):
                        fixed_support(p, q)
        p += 2
    return (small_anchors, candidate_tests, supports, prefix_tests), sorted(hits)


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("first", type=int)
    parser.add_argument("last", type=int)
    opts = parser.parse_args()
    if not 1 <= opts.first <= opts.last:
        parser.error("use a positive, increasing range")
    for k in range(opts.first, opts.last + 1):
        counts, hits = classify(k)
        print(k, *counts, hits, flush=True)
        assert not hits, (k, hits)
