"""Independently recheck the A245211 least-prime layer at 409."""

from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

from check_fixed_points import verify
from search_fixed_points import examine

least_prime = 409
integer_patterns, integer_nodes, integer_hits = examine(least_prime)
rational_patterns, rational_hits = verify(least_prime)

assert integer_patterns == rational_patterns == 20_499
assert integer_nodes == 121
assert integer_hits == rational_hits == []

print(
    least_prime,
    integer_patterns,
    integer_nodes,
    integer_hits,
    rational_patterns,
    rational_hits,
)
print("521,121 exponent patterns through least prime 409; sole fixed point 21.")
