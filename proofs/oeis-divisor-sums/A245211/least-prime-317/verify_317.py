"""Independently recheck the A245211 least-prime layer at 317."""

from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

from check_fixed_points import verify
from search_fixed_points import examine

least_prime = 317
integer_patterns, integer_nodes, integer_hits = examine(least_prime)
rational_patterns, rational_hits = verify(least_prime)

assert integer_patterns == rational_patterns == 12_913
assert integer_nodes == 699_457
assert integer_hits == rational_hits == []

print(
    least_prime,
    integer_patterns,
    integer_nodes,
    integer_hits,
    rational_patterns,
    rational_hits,
)
print("281,555 exponent patterns through least prime 317; sole fixed point 21.")
