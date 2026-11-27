"""A bounded, deterministic two-stage elliptic-curve search for a proper gcd."""

from dataclasses import dataclass
from math import gcd, isqrt


def prime_powers(bound):
    """Largest power of each prime at most bound, in increasing prime order."""
    sieve = bytearray([1]) * (bound + 1)
    sieve[:2] = b"\x00\x00"
    for p in range(2, isqrt(bound)+1):
        if sieve[p]:
            sieve[p*p::p] = bytes(1 + (bound - p*p)//p)
    for p in range(2, bound+1):
        if sieve[p]:
            power = p
            while power <= bound//p:
                power *= p
            yield p, power


def double(point, a24, n):
    x, z = point
    plus = (x+z)**2 % n
    minus = (x-z)**2 % n
    diff = (plus-minus) % n
    return plus*minus % n, diff*(minus+a24*diff) % n


def add_diff(left, right, diff, n):
    x, z = left
    y, w = right
    u, v = diff
    a = (x-z)*(y+w) % n
    b = (x+z)*(y-w) % n
    return v*(a+b)**2 % n, u*(a-b)**2 % n


def multiply(point, scalar, a24, n):
    """Montgomery ladder on x/z, including the zero scalar."""
    if scalar == 0:
        return (1, 0)
    left, right = point, double(point, a24, n)
    for digit in bin(scalar)[3:]:
        cross = add_diff(left, right, point, n)
        if digit == "0":
            left, right = double(left, a24, n), cross
        else:
            left, right = cross, double(right, a24, n)
    return left


def large_prime_step(n, seed, point, a24, primes, stride):
    """Compare x([k*stride]Q) and x([r]Q) when k*stride +/- r is prime."""
    babies, giants = {}, {}
    block = []
    product = 1
    for prime in primes:
        k = (prime+stride//2)//stride
        r = abs(prime-k*stride)
        if r not in babies:
            babies[r] = multiply(point,r,a24,n)
        if k not in giants:
            giants[k] = multiply(point,k*stride,a24,n)
        x,z = giants[k]
        u,v = babies[r]
        residue = (x*v-u*z) % n
        product = product*residue % n
        block.append((prime,residue))
        if len(block) == 128 or prime == primes[-1]:
            if gcd(product,n) != 1:
                for candidate, value in block:
                    g = gcd(value,n)
                    if 1 < g < n:
                        return Split(n,seed,"large prime",candidate,value,g)
            block.clear()
            product = 1
    return None


@dataclass(frozen=True)
class Split:
    n: int
    seed: int
    stage: str
    last_prime: int
    residue: int
    divisor: int


def split(n):
    """Return a verified proper divisor when the bounded schedule finds one."""
    if n < 3:
        return None
    if n % 2 == 0:
        return Split(n, 0, "even", 0, 2, 2)
    root = isqrt(n)
    if root*root == n:
        return Split(n, 0, "square", 0, root, root)
    b = n.bit_length()
    powers = list(prime_powers(b*b))
    second = [p for p,_ in prime_powers(b**3) if p > b*b]
    stride = 2*max(1,isqrt(b**3)//2)
    for seed in range(6, 6+b):
        u = (seed*seed-5) % n
        v = 4*seed % n
        x, z = pow(u,3,n), pow(v,3,n)
        den = 16*x*v % n
        g = gcd(den,n)
        if 1 < g < n:
            return Split(n,seed,"denominator",0,den,g)
        if g != 1:
            continue
        a24 = pow(v-u,3,n)*(3*u+v)*pow(den,-1,n) % n
        disc = a24*(a24-1) % n
        g = gcd(disc,n)
        if 1 < g < n:
            return Split(n,seed,"discriminant",0,disc,g)
        if g != 1:
            continue
        point = (x,z)
        for p,power in powers:
            point = multiply(point,power,a24,n)
            g = gcd(point[1],n)
            if 1 < g < n:
                return Split(n,seed,"point",p,point[1],g)
            if g == n:
                break
        else:
            result = large_prime_step(n,seed,point,a24,second,stride)
            if result is not None:
                return result
    return None


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("n",type=int)
    args = parser.parse_args()
    certificate = split(args.n)
    print(certificate if certificate is not None else "No split in this schedule.")
