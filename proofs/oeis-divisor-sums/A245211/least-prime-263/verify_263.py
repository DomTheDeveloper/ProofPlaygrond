"""Independently recheck the A245211 least-prime layer at 263."""

from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

from check_fixed_points import verify
from search_fixed_points import certified_263_primes, examine, term

least_prime = 263
factor_one, factor_two = certified_263_primes()
moment, _ = term(13, least_prime)

assert factor_one == 214805549993
assert factor_two == 1883836937069958237217
assert moment == factor_one * factor_two

integer_patterns, integer_nodes, integer_hits = examine(least_prime)
rational_patterns, rational_hits = verify(least_prime)

assert integer_patterns == rational_patterns == 9_367
assert integer_nodes == 93_727
assert integer_hits == rational_hits == []

print(
    least_prime,
    integer_patterns,
    integer_nodes,
    integer_hits,
    rational_patterns,
    rational_hits,
)
print("168,445 exponent patterns through least prime 263; sole fixed point 21.")
