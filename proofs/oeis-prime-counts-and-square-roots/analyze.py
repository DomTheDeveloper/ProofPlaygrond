"""Summarize ordered rows n, phi(n), pi(n) emitted by either C++ verifier."""
import hashlib
import json
import sys
from fractions import Fraction
from pathlib import Path


def analyze(path):
    data = path.read_bytes()
    rows = [tuple(map(int, line.split())) for line in data.splitlines()]
    if any(n < 2 or not 0 < phi <= 3 * pi for n, phi, pi in rows):
        raise ValueError("An input row is outside the claimed comparison.")
    if any(x[0] >= y[0] for x, y in zip(rows, rows[1:])):
        raise ValueError("Input rows must be in strictly increasing order.")

    summaries = {}
    for c in (1, 2, 3):
        less = [row for row in rows if row[1] < c * row[2]]
        equal = [n for n, phi, pi in rows if phi == c * pi]
        summaries[c] = {
            "number_strictly_below": len(less),
            "last_strictly_below_n_phi_pi": less[-1],
            "equality_cases": equal,
            "last_at_or_below": max(less[-1][0], equal[-1]),
        }

    best = None
    records = []
    for n, phi, pi in reversed(rows):
        value = Fraction(phi, pi)
        if best is None or value < best:
            records.append(n)
            best = value
    return {
        "inclusive_sieve_bound": 5 * 2**26,
        "rows_at_or_below_3": len(rows),
        "raw_rows_sha256": hashlib.sha256(data).hexdigest(),
        "comparisons": summaries,
        "A080289_prefix": list(reversed(records)),
    }


if __name__ == "__main__":
    print(json.dumps(analyze(Path(sys.argv[1])), indent=2))
