"""Independently recheck the A245211 least-prime layer at 307."""

from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

from check_fixed_points import certified_307_primes, verify
from search_fixed_points import examine, term

least_prime = 307
factors = certified_307_primes()
moment, _ = term(9, least_prime)

assert factors == (57427, 96823, 424967, 102818321)
assert moment == factors[0] * factors[1] * factors[2] * factors[3]

integer_patterns, integer_nodes, integer_hits = examine(least_prime)
rational_patterns, rational_hits = verify(least_prime)

assert integer_patterns == rational_patterns == 12_423
assert integer_nodes == 59
assert integer_hits == rational_hits == []

print(
    least_prime,
    integer_patterns,
    integer_nodes,
    integer_hits,
    rational_patterns,
    rational_hits,
)
print("243,296 exponent patterns through least prime 307; sole fixed point 21.")
