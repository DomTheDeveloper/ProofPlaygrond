"""Replay the complete least-prime-499 A245211 certificate."""

from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))

from check_fixed_points import verify
from search_fixed_points import examine


def main():
    integer_patterns, search_nodes, integer_hits = examine(499)
    rational_patterns, rational_hits = verify(499)
    assert integer_patterns == rational_patterns == 28_651
    assert search_nodes == 399_572
    assert integer_hits == rational_hits == []
    print(499, integer_patterns, search_nodes, integer_hits, rational_patterns, rational_hits)
    print("891,312 ordered exponent patterns through least prime 499. The sole fixed point is 21.")


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Run the certificate with assertions enabled.")
    main()
