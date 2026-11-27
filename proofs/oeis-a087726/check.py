"""Compare the A087726 formula with direct matrix multiplication (Python 3)."""
from itertools import product


def predicted(n):
    remaining = n
    count = 1
    p = 2
    while p * p <= remaining:
        exponent = 0
        while remaining % p == 0:
            remaining //= p
            exponent += 1
        if exponent:
            count *= p**(2*exponent) + (exponent//2)*(p*p - 1)*p**(2*exponent - 2)
        p += 1
    if remaining > 1:
        count *= remaining**2
    return count


def direct(n):
    return sum(1 for a, b, c, d in product(range(n), repeat=4)
               if (a*a + b*c) % n == 0 and (a*b + b*d) % n == 0
               and (c*a + d*c) % n == 0 and (c*b + d*d) % n == 0)


if __name__ == "__main__":
    moduli = [*range(1, 33), 49, 64]
    for n in moduli:
        actual = direct(n)
        assert predicted(n) == actual, (n, actual, predicted(n))
    print(f"All {sum(n**4 for n in moduli):,} matrices across {len(moduli)} moduli matched.")
    for n in (4, 9, 12, 27, 30, 49, 64):
        print(f"N({n}) = {predicted(n)}")
