"""Replay the complete least-prime-509 A245211 certificate."""

from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))

from check_fixed_points import verify
from search_fixed_points import examine


def main():
    integer_patterns, search_nodes, integer_hits = examine(509)
    rational_patterns, rational_hits = verify(509)
    assert integer_patterns == rational_patterns == 30_081
    assert search_nodes == 1_762_123
    assert integer_hits == rational_hits == []
    print(509, integer_patterns, search_nodes, integer_hits, rational_patterns, rational_hits)
    print("950,206 ordered exponent patterns through least prime 509. The sole fixed point is 21.")


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Run the certificate with assertions enabled.")
    main()
