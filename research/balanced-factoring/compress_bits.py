"""Select a short block of divisor-sum queries, then decode the supplied bits.

  python compress_bits.py N
  python compress_bits.py N --budget 100 --replies 0101

The input promise is N=p*q with distinct odd primes p<q<=2*p.
The selector and decoder use only integer arithmetic. Answers to the selected
queries are a separate input. A singleton midpoint interval needs no answers.
"""

import argparse
from dataclasses import dataclass
from math import isqrt
from local_bits import floor_sum, midpoint_interval


@dataclass(frozen=True)
class Window:
    low: int
    high: int
    start: int
    width: int
    span_per_block: int


def count_at_least(length, n, slope, threshold):
    """Count d in [1,length] with (slope*d mod n) >= threshold."""
    return (floor_sum(length, n, slope, slope + n - threshold)
            - floor_sum(length, n, slope, slope))


def separating_window(n, budget=1):
    if n < 3 or n % 2 == 0 or isqrt(n)**2 == n:
        raise ValueError("Expected an odd nonsquare N >= 3.")
    low, high = midpoint_interval(n)
    if budget < 1:
        raise ValueError("The candidate budget must be positive.")
    if high < low:
        raise ValueError("The balanced midpoint interval is empty.")
    span = (high - low) // budget
    if span == 0:
        return Window(low, high, 0, 0, span)
    width = (3 * span).bit_length()
    radius = (n - 1) >> width
    slope = pow(2, 3 * n.bit_length() + 1, n)
    for start in range((span * radius).bit_length() + 1):
        near_zero = span - count_at_least(span, n, slope, radius + 1)
        near_n = count_at_least(span, n, slope, n - radius)
        if near_zero + near_n == 0:
            return Window(low, high, start, width, span)
        slope = 2 * slope % n
    raise ArithmeticError("No separating window within the proved bound.")


def query_arguments(n, window):
    return [n << (5*n.bit_length() + 2*i)
            for i in range(window.start, window.start + window.width)]


def count_word(n, first, count, window, word):
    """Count midpoints matching one binary word without scanning the interval."""
    cells = 1 << window.width
    scale = 1 << (3*n.bit_length() + window.start + window.width)
    intercept = scale * (1 + 2*first) - 1
    slope = 2 * scale
    modulus = cells * n
    return (floor_sum(count, modulus, slope, intercept + (cells-word)*n)
            - floor_sum(count, modulus, slope, intercept + (cells-word-1)*n))


def decode(n, window, replies):
    if len(replies) != window.width or any(c not in "01" for c in replies):
        raise ValueError(f"Expected {window.width} binary digits.")
    word = int(replies or "0", 2)
    block_length = window.span_per_block + 1
    for first in range(window.low, window.high+1, block_length):
        lo, hi = first, min(window.high, first + block_length - 1)
        if count_word(n, lo, hi-lo+1, window, word) == 0:
            continue
        while lo < hi:
            mid = (lo+hi)//2
            if count_word(n, lo, mid-lo+1, window, word):
                hi = mid
            else:
                lo = mid+1
        gap_squared = lo*lo-n
        gap = isqrt(gap_squared)
        if gap*gap == gap_squared and lo-gap > 1:
            return lo-gap, lo+gap
    return None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("n", type=int)
    parser.add_argument("--replies")
    parser.add_argument("--budget", type=int, default=1, help="maximum candidate intervals")
    parser.add_argument("--list-queries", action="store_true")
    args = parser.parse_args()
    try:
        window = separating_window(args.n, args.budget)
        print(f"Binary input length: {args.n.bit_length()}")
        print(f"Midpoint interval: [{window.low}, {window.high}]")
        print(f"First query index: {window.start} (zero based)")
        print(f"Consecutive queries: {window.width}")
        if args.list_queries:
            for z in query_arguments(args.n, window):
                print(z)
        if args.replies is not None or window.width == 0:
            factors = decode(args.n, window, args.replies or "")
            if factors:
                print(f"Verified factorization: {factors[0]} * {factors[1]}")
            else:
                print("These replies yield no proper factor pair.")
    except ValueError as error:
        parser.exit(2, f"{error}\n")


if __name__ == "__main__":
    main()
