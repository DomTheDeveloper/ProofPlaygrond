"""Verify the fixture certificates. Pass --replay to run all six bounded searches."""

from argparse import ArgumentParser
from json import loads
from math import gcd, isqrt, prod
from pathlib import Path

from compress_bits import decode, query_arguments, separating_window
from curves import multiply, prime_powers
from point_checks import affine_count, check_collisions
from recover import recover


def verify_primes():
    """Lucas certificates prove the large primes. Small leaves use trial division."""
    proven = set()
    rows = loads(Path(__file__).with_name("prime-witnesses.json").read_text())
    for row in rows:
        n, a, factors = row["n"], row["a"], row["factors"]
        assert prod(factors) == n-1 and pow(a, n-1, n) == 1
        for r in set(factors):
            if r not in proven:
                assert 2 <= r < 150000
                assert all(r % d != 0 for d in range(2, isqrt(r)+1))
                proven.add(r)
            assert gcd(pow(a, (n-1)//r, n)-1, n) == 1
        proven.add(n)
    return proven


def verify_word(n, pair, expected):
    p, q = pair
    window = separating_window(n, n.bit_length() ** 2)
    assert (window.start, window.width) == (expected["start"], expected["width"])
    digits = []
    for z in query_arguments(n, window):
        sigma = (2*(z//n)-1)*(p+1)*(q+1)
        digits.append(str(((sigma << (z.bit_length()//2))//z) % 2))
    word = "".join(digits)
    assert word == expected["word"]
    assert decode(n, window, word) == tuple(pair)


def verify_certificate(n, expected):
    c = expected["certificate"]
    g = gcd(c["residue"], n)
    assert 1 < g < n and g == c["divisor"] and n % g == 0
    if "multiplier" in c:
        k, a, y = c["multiplier"], c["a"], c["y"]
        assert a*a - 4*k*n == y*y
        assert a == isqrt(4*k*n-1) + 1 + c["offset"]
        assert (a-y)//2 == c["residue"]
        return
    seed = c["seed"]
    u, v = seed*seed-5, 4*seed
    point = (pow(u, 3, n), pow(v, 3, n))
    a24 = (v-u)**3*(3*u+v)*pow(16*u**3*v, -1, n) % n
    for _, power in prime_powers(n.bit_length() ** 2):
        point = multiply(point, power, a24, n)
    d = 2 * max(1, isqrt(n.bit_length() ** 3)//2)
    ell = c["last_prime"]
    j = (ell+d//2)//d
    r = abs(ell-j*d)
    x1, z1 = multiply(point, j*d, a24, n)
    x2, z2 = multiply(point, r, a24, n)
    assert (x1*z2-x2*z1) % n == c["residue"]
    assert gcd(multiply(point, ell, a24, n)[1], n) == g
    assert gcd(multiply(point, 2*j*d-ell, a24, n)[1], n) == 1


def main():
    cli = ArgumentParser(description=__doc__)
    cli.add_argument("--replay", action="store_true")
    args = cli.parse_args()
    fixtures = loads(Path(__file__).with_name("fixtures.json").read_text())
    primes = verify_primes()
    for f in fixtures:
        n, pair = f["n"], f["factors"]
        p, q = pair
        assert p in primes and q in primes
        assert p*q == n and p < q < 2*p and p % 4 == q % 4 == 3
        for method in ("multipliers", "curves"):
            expected = f[method]
            if expected is not None:
                verify_certificate(n, expected)
                verify_word(n, pair, expected)
            if args.replay:
                actual = recover(n, method)
                assert actual == expected
                print(n.bit_length(), method, "split" if actual else "exhausted", flush=True)
    for p, q in [(3,7), (7,11), (7,19), (11,23)]:
        assert affine_count(p*q) == p*q
        assert (affine_count(p)+1)*(affine_count(q)+1) == p*q+p+q+1
    for pair in [(3,5), (3,7), (5,7), (7,11), (11,13)]:
        check_collisions(*pair)
    print("Verified six primes, gcds, both divisor-sum words and decodings, and finite point counts.")


if __name__ == "__main__":
    main()
