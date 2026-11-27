"""Independently recheck the A245211 least-prime layer at 283."""

from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

from check_fixed_points import certified_283_primes, verify
from search_fixed_points import examine, term

least_prime = 283
factor_one, factor_two = certified_283_primes()
moment, _ = term(13, least_prime)

assert factor_one == 33311847537949
assert factor_two == 3498950330708810221
assert moment == 9 * factor_one * factor_two

integer_patterns, integer_nodes, integer_hits = examine(least_prime)
rational_patterns, rational_hits = verify(least_prime)

assert integer_patterns == rational_patterns == 10_483
assert integer_nodes == 401_419
assert integer_hits == rational_hits == []

print(
    least_prime,
    integer_patterns,
    integer_nodes,
    integer_hits,
    rational_patterns,
    rational_hits,
)
print("219,184 exponent patterns through least prime 283; sole fixed point 21.")
