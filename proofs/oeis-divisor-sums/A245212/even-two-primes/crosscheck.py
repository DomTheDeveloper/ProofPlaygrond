"""Independent exact interval and bisection certificate for v_2(n) layers."""
import sys
from fractions import Fraction as F
from functools import lru_cache
from math import isqrt


def primes(a, b):
    for p in range(a, b + 1):
        if p >= 2 and all(p % f for f in range(2, isqrt(p) + 1)):
            yield p


@lru_cache(maxsize=24000)
def pieces(p, i):
    power = p ** (i - 1)
    sigma = (p * power - 1) // (p - 1)
    moment = (1 + ((p - 1) * i - 1) * p * power) // (p - 1)**2
    return power * i, moment, sigma


def check(k):
    scale, T0, S0 = pieces(2, k + 1)
    w, t = F(S0, T0), F(2 * scale, T0)
    assert t == 1 + w
    solutions = set()
    rows = large_prime_rows = 0

    def support(p, q):
        nonlocal rows
        P = F(p, p - 1) * F(q, q - 1)
        alpha, beta = F(1, p - 1), F(1, q - 1)
        limit = 2
        while not (P * (1 - alpha / limit) * (1 - beta / limit) > t or
                   P * (1 + w / limit**2) < t or
                   (P == t and limit * (alpha + beta) > w + alpha * beta)):
            limit *= 2
        for s, u in ((p, q), (q, p)):
            for i in range(2, limit):
                rows += 1
                den, moment, sigma = pieces(s, i)
                c, h, d = 2 * scale * den, T0 * moment, S0 * sigma
                difference = abs(h - (u - 1) * d)
                if difference == 0:
                    assert c != u * d, "unrestricted equality ray"
                    continue
                # u^(j-1) divides this fixed integer.
                jmax = 1
                while difference % u == 0:
                    difference //= u
                    jmax += 1
                if jmax < i:
                    continue
                # Evaluate each remaining index outright by integer arithmetic.
                for j in range(i, jmax + 1):
                    dn, mt, sg = pieces(u, j)
                    if c * dn == h * mt + d * sg:
                        solutions.add(tuple(sorted(((s, i - 1), (u, j - 1)))))

    def large_q(p, i, Q):
        nonlocal large_prime_rows
        den, mt, sg = pieces(p, i)
        c, h, d = 2 * scale * den, T0 * mt, S0 * sg
        # If q >= Q then Q^(j-2) <= T(2^k p^(i-1)) + sigma(2^k p^(i-1)).
        j = 2
        low_power = 1
        while low_power <= h + d:
            gap = (c - h) * j - d
            lead = (j - 1) * h + d
            if gap > 0 and gap * (Q - 1) < lead:
                large_prime_rows += 1

                def sign(base):
                    # Bounds from the first term and from summing a geometric series.
                    # Only between these bounds does a full polynomial need evaluation.
                    if lead > base * gap:
                        return 1
                    if lead <= (base - 1) * gap:
                        return -1
                    dn, mtq, sgq = pieces(base, j)
                    return h * mtq + d * sgq - c * dn

                if sign(Q) >= 0:
                    low, high = Q, 2 * Q
                    while sign(high) >= 0:
                        low, high = high, 2 * high
                    while high - low > 1:
                        mid = (high + low) // 2
                        if sign(mid) >= 0:
                            low = mid
                        else:
                            high = mid
                    if sign(low) == 0 and any(primes(low, low)):
                        solutions.add(((p, i - 1), (low, j - 1)))
            low_power *= Q
            j += 1

    # Bound the smaller odd prime using a doubling search.
    P = 4
    while F(P, P - 1)**2 * (1 + w / 4) > t:
        P *= 2
    for p in primes(3, P - 1):
        cap = F(p, p - 1)
        L = 2
        while True:
            Q = max(L, p + 1)
            den, mt, _ = pieces(p, L)
            if F(mt, den) >= t or cap * F(Q, Q - 1) * (1 + w / (2 * L)) <= t:
                break
            L *= 2
        for q in primes(p + 1, Q - 1):
            support(p, q)
        # For q >= Q and i >= L the two bounds just tested exclude equality.
        for i in range(2, L):
            large_q(p, i, Q)
    return rows, large_prime_rows, sorted(solutions)


if __name__ == "__main__":
    first, last = map(int, sys.argv[1:])
    assert 1 <= first <= last
    for layer in range(first, last + 1):
        a, b, hits = check(layer)
        print(layer, a, b, hits, flush=True)
        assert not hits, (layer, hits)
