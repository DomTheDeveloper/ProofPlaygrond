"""Independently recheck the A245211 least-prime layer at 313."""

from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

from check_fixed_points import verify
from search_fixed_points import examine

least_prime = 313
integer_patterns, integer_nodes, integer_hits = examine(least_prime)
rational_patterns, rational_hits = verify(least_prime)

assert integer_patterns == rational_patterns == 12_805
assert integer_nodes == 28
assert integer_hits == rational_hits == []

print(
    least_prime,
    integer_patterns,
    integer_nodes,
    integer_hits,
    rational_patterns,
    rational_hits,
)
print("268,642 exponent patterns through least prime 313; sole fixed point 21.")
