#!/usr/bin/env python3
"""Exact small-board cross-check for the Chomp solver executable."""
from __future__ import annotations

import argparse
import ast
import re
import subprocess
from pathlib import Path


def positions(rows: int, width: int):
    x = [0] * rows

    def rec(pos: int, bound: int):
        if pos == rows:
            yield tuple(x)
            return
        lo = 1 if pos == 0 else 0
        for value in range(lo, bound + 1):
            x[pos] = value
            yield from rec(pos + 1, value)

    yield from rec(0, width)


def options(x: tuple[int, ...]):
    for row in range(len(x)):
        for target in range(x[row]):
            if row == 0 and target == 0:
                continue
            yield x[:row] + tuple(min(v, target) for v in x[row:])


def brute(rows: int, width: int):
    is_n: dict[tuple[int, ...], bool] = {}
    p_positions: list[tuple[int, ...]] = []
    for x in positions(rows, width):
        n_value = any(not is_n[y] for y in options(x))
        is_n[x] = n_value
        if not n_value:
            p_positions.append(x)

    openings: dict[int, list[tuple[int, ...]]] = {w: [] for w in range(1, width + 1)}
    for x in p_positions:
        w = x[0]
        for r in range(1, rows):
            t = x[r]
            if (
                t < w
                and all(x[i] == w for i in range(r))
                and all(x[i] == t for i in range(r, rows))
            ):
                openings[w].append(x)
                break
    return p_positions, {w: v for w, v in openings.items() if len(v) >= 2}


def run_solver(binary: Path, rows: int, width: int):
    cp = subprocess.run(
        [str(binary), str(rows), str(width)],
        text=True,
        capture_output=True,
        check=True,
    )
    match = re.search(r"P=(\d+)", cp.stdout)
    if match is None:
        raise RuntimeError("solver output did not contain a P-position count")
    p_count = int(match.group(1))
    sections: dict[int, list[tuple[int, ...]]] = {}
    current = None
    for line in cp.stdout.splitlines():
        m = re.match(rf"{rows}x(\d+) openings=(\d+)", line)
        if m:
            current = int(m.group(1))
            sections[current] = []
        elif line.startswith("  (") and current is not None:
            sections[current].append(ast.literal_eval(line.strip()))
    return p_count, sections


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("binary", type=Path)
    args = parser.parse_args()
    binary = args.binary.resolve()
    cases = [(2, 8), (3, 8), (4, 8), (5, 8), (6, 7)]
    for rows, width in cases:
        p_positions, expected = brute(rows, width)
        got_count, got_openings = run_solver(binary, rows, width)
        assert got_count == len(p_positions), (rows, width, got_count, len(p_positions))
        assert got_openings == expected, (rows, width, got_openings, expected)
        print(f"{rows}x{width}: passed ({got_count} P-positions)")
    print("ALL SMALL EXACT CROSS-CHECKS PASSED")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
