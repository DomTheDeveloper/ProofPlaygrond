"""Independently recheck the A245211 least-prime layer at 257."""

from pathlib import Path
import sys

EXTENSION = Path(__file__).resolve().parent.parent / "extension"
sys.path.insert(0, str(EXTENSION))

from search_fixed_points import examine
from check_fixed_points import verify

least_prime = 257
integer_patterns, integer_nodes, integer_hits = examine(least_prime)
rational_patterns, rational_hits = verify(least_prime)

assert integer_patterns == rational_patterns == 9_229
assert integer_nodes == 376_878
assert integer_hits == rational_hits == []

print(
    least_prime,
    integer_patterns,
    integer_nodes,
    integer_hits,
    rational_patterns,
    rational_hits,
)
print("159,078 exponent patterns through least prime 257; sole fixed point 21.")
