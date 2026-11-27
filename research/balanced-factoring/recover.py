"""Recover a divisor-sum word from an odd balanced semiprime on a successful curve."""

from argparse import ArgumentParser
from dataclasses import asdict
from json import dumps
from math import gcd

from compress_bits import decode, query_arguments, separating_window
from curves import split as curve_split
from multipliers import split as multiplier_split


def recover(n, method="both"):
    """The input promise is n=p*q with distinct odd primes p<q<=2*p."""
    if n < 3 or n % 2 == 0:
        raise ValueError("Expected a positive odd balanced semiprime.")
    window = separating_window(n, n.bit_length() ** 2)
    if method not in ("both", "curves", "multipliers"):
        raise ValueError("Unknown search method.")
    certificate = multiplier_split(n) if method != "curves" else None
    if certificate is None and method != "multipliers":
        certificate = curve_split(n)
    if certificate is None:
        return None
    g = gcd(certificate.residue, n)
    if g != certificate.divisor or not 1 < g < n:
        raise ArithmeticError("Invalid gcd certificate.")
    p, q = sorted((g, n // g))
    if p == q or q > 2 * p:
        raise ValueError("The recovered factors violate the balanced-semiprime promise.")
    divisor_sum = (p + 1) * (q + 1)
    digits = []
    for z in query_arguments(n, window):
        divisor_sum_z = (2 * (z // n) - 1) * divisor_sum
        scaled_sum = divisor_sum_z << (z.bit_length() // 2)
        digits.append(str((scaled_sum // z) % 2))
    word = "".join(digits)
    if decode(n, window, word) != (p, q):
        raise ArithmeticError("The independent midpoint decoder disagreed.")
    return dict(n=n, factors=[p, q], sigma=divisor_sum, start=window.start,
                width=window.width, word=word, certificate=asdict(certificate))


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("n", type=int)
    parser.add_argument("--method", choices=["both", "curves", "multipliers"], default="both")
    args = parser.parse_args()
    result = recover(args.n, args.method)
    print("No split in this schedule." if result is None else dumps(result, indent=2))
