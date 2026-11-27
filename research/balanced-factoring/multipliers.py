"""Search a polynomial budget of weighted difference-of-squares identities."""

from argparse import ArgumentParser
from dataclasses import dataclass
from math import gcd, isqrt


@dataclass(frozen=True)
class SquareSplit:
    n: int
    multiplier: int
    offset: int
    a: int
    y: int
    residue: int
    divisor: int


def split(n):
    if n < 3 or n % 2 == 0:
        raise ValueError("Expected an odd integer at least 3.")
    budget = n.bit_length() ** 2
    for k in range(1, budget + 1):
        target = 4*k*n
        lower = 1 + isqrt(target - 1)
        for offset in range(budget // k + 1):
            a = lower + offset
            difference = a*a - target
            y = isqrt(difference)
            if y*y == difference:
                residue = (a-y)//2
                g = gcd(residue, n)
                if 1 < g < n:
                    return SquareSplit(n, k, offset, a, y, residue, g)
    return None


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("n", type=int)
    result = split(parser.parse_args().n)
    print("No split in this schedule." if result is None else result)
