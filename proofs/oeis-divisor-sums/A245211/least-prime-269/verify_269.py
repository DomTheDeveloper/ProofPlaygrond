"""Independently recheck the A245211 least-prime layer at 269."""

from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

from check_fixed_points import (
    certified_269_prime,
    certified_269_successor_primes,
    verify,
)
from search_fixed_points import examine, term

least_prime = 269
moment = certified_269_prime()
successors = certified_269_successor_primes()
computed_moment, _ = term(13, least_prime)

assert moment == 542512058959614745217387126772353
assert computed_moment == moment
assert successors == (47137, 13974006881147, 1647238560869113)
assert 2 * moment + 1 == successors[0] * successors[1] * successors[2]

integer_patterns, integer_nodes, integer_hits = examine(least_prime)
rational_patterns, rational_hits = verify(least_prime)

assert integer_patterns == rational_patterns == 9_681
assert integer_nodes == 370_664
assert integer_hits == rational_hits == []

print(
    least_prime,
    integer_patterns,
    integer_nodes,
    integer_hits,
    rational_patterns,
    rational_hits,
)
print("178,126 exponent patterns through least prime 269; sole fixed point 21.")
