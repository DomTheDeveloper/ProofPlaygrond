#!/usr/bin/env python3
"""Independent finite sanity checks for the four-direction theorem.

Checks point-line incidence pair-codegree exactly and solves small binary
four-direction packing instances with SciPy/HiGHS.  These computations are
corroboration only; the asymptotic proof uses Kahn's theorem.
"""
from __future__ import annotations

import csv
from pathlib import Path
from typing import Iterable

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import lil_matrix

ROOT = Path(__file__).resolve().parent


def points(n: int, eps: int) -> list[tuple[int, int]]:
    return [(x, y) for x in range(n) for y in range(n) if (x + y) % 2 == eps]


def line_key_families(p: tuple[int, int]) -> tuple[tuple[str, int], ...]:
    x, y = p
    return (("row", y), ("col", x), ("diag+", x - y), ("diag-", x + y))


def verify_linearity(n: int, eps: int) -> None:
    seen: dict[tuple[tuple[str, int], tuple[str, int]], tuple[int, int]] = {}
    for p in points(n, eps):
        keys = line_key_families(p)
        for i in range(len(keys)):
            for j in range(i + 1, len(keys)):
                pair = tuple(sorted((keys[i], keys[j])))
                if pair in seen and seen[pair] != p:
                    raise AssertionError((n, eps, pair, seen[pair], p))
                seen[pair] = p


def solve_integral(n: int, eps: int) -> int:
    pts = points(n, eps)
    index = {p: i for i, p in enumerate(pts)}
    groups: dict[tuple[str, int], list[int]] = {}
    for p in pts:
        for key in line_key_families(p):
            groups.setdefault(key, []).append(index[p])
    A = lil_matrix((len(groups), len(pts)), dtype=float)
    for row, ids in enumerate(groups.values()):
        A[row, ids] = 1.0
    result = milp(
        c=-np.ones(len(pts)),
        integrality=np.ones(len(pts)),
        bounds=Bounds(0, 1),
        constraints=LinearConstraint(A.tocsr(), -np.inf, 2),
        options={"time_limit": 30},
    )
    if result.fun is None:
        raise RuntimeError(f"HiGHS failed for n={n}, eps={eps}: {result.message}")
    return int(round(-result.fun))


def main() -> None:
    for n in range(2, 101):
        for eps in (0, 1):
            verify_linearity(n, eps)
    print("incidence pair-codegree check passed for n <= 100")

    rows: list[tuple[int, int, int]] = []
    for n in range(5, 25):
        vals = [solve_integral(n, eps) for eps in (0, 1)]
        rows.append((n, vals[0], vals[1]))
        print(f"n={n:2d}: I4(eps=0)={vals[0]:2d}, I4(eps=1)={vals[1]:2d}")

    out = ROOT / "small_integral_values.csv"
    with out.open("w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(["n", "I4_eps0", "I4_eps1"])
        writer.writerows(rows)
    print(f"wrote {out}")


if __name__ == "__main__":
    main()
