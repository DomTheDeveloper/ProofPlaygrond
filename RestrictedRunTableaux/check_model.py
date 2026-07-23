#!/usr/bin/env python3
"""Exact checker for the restricted-run tableaux Markov-additive reduction.

All calculations use fractions and polynomial coefficient dictionaries. The
script checks the six-state transition model, the martingale corrector,
stationarity/covariance, two exact phase-harmonic polynomial families, exit
signs, and the initial values of G(n).
"""

from __future__ import annotations

from collections import defaultdict
from fractions import Fraction as F
from functools import lru_cache
from math import comb
from typing import Dict, Tuple

State = str
Vec = Tuple[int, int]
Poly = Dict[Tuple[int, int], F]

STATES: tuple[State, ...] = ("A1", "B1", "A2", "B2", "A3", "B3")

# (target state, probability, corrected increment)
TRANSITIONS: dict[State, tuple[tuple[State, F, Vec], ...]] = {
    "A1": (("B1", F(1), (0, 0)),),
    "A2": (("B2", F(1), (0, 0)),),
    "A3": (("B3", F(1), (0, 0)),),
    "B1": (
        ("B1", F(1, 2), (1, 0)),
        ("A2", F(1, 4), (-2, 2)),
        ("A3", F(1, 4), (0, -2)),
    ),
    "B2": (
        ("B2", F(1, 2), (-1, 1)),
        ("A1", F(1, 4), (2, 0)),
        ("A3", F(1, 4), (0, -2)),
    ),
    "B3": (
        ("B3", F(1, 2), (0, -1)),
        ("A1", F(1, 4), (2, 0)),
        ("A2", F(1, 4), (-2, 2)),
    ),
}

STATIONARY: dict[State, F] = {
    "A1": F(1, 9), "B1": F(2, 9),
    "A2": F(1, 9), "B2": F(2, 9),
    "A3": F(1, 9), "B3": F(2, 9),
}

SIGMA = ((F(10, 9), F(-5, 9)), (F(-5, 9), F(10, 9)))


def clean(p: Poly) -> Poly:
    return {m: c for m, c in p.items() if c}


def add(*ps: Poly) -> Poly:
    out: defaultdict[Tuple[int, int], F] = defaultdict(F)
    for p in ps:
        for m, c in p.items():
            out[m] += c
    return clean(dict(out))


def scale(a: F, p: Poly) -> Poly:
    return clean({m: a * c for m, c in p.items()})


def shift(p: Poly, dx: int, dy: int) -> Poly:
    """Return p(x+dx,y+dy)."""
    out: defaultdict[Tuple[int, int], F] = defaultdict(F)
    for (i, j), c in p.items():
        for a in range(i + 1):
            for b in range(j + 1):
                out[(a, b)] += (
                    c * comb(i, a) * F(dx) ** (i - a)
                    * comb(j, b) * F(dy) ** (j - b)
                )
    return clean(dict(out))


def evaluate(p: Poly, x: int, y: int) -> F:
    return sum((c * F(x) ** i * F(y) ** j for (i, j), c in p.items()), F(0))


# H^- has leading term u=x*y*(x+y), is positive in the live cone, and is
# non-positive at every reachable killed overshoot.
H_MINUS: dict[int, Poly] = {
    1: {(2, 1): F(1), (1, 2): F(1), (1, 0): F(2, 3), (0, 1): F(-4, 3)},
    2: {(2, 1): F(1), (1, 2): F(1), (1, 0): F(4, 3)},
    3: {(2, 1): F(1), (1, 2): F(1), (0, 1): F(-2, 3)},
}

# Q=H^+-H^- is a non-negative phase-harmonic quadratic. H^+ controls the
# square of the tangential coordinate at every boundary/overshoot location.
Q: dict[int, Poly] = {
    1: {
        (2, 0): F(2), (1, 1): F(7), (1, 0): F(6),
        (0, 2): F(3, 2), (0, 1): F(6), (0, 0): F(7, 2),
    },
    2: {
        (2, 0): F(2), (1, 1): F(7), (1, 0): F(6),
        (0, 2): F(3, 2), (0, 1): F(6), (0, 0): F(43, 6),
    },
    3: {
        (2, 0): F(2), (1, 1): F(7), (1, 0): F(6),
        (0, 2): F(3, 2), (0, 1): F(6), (0, 0): F(23, 6),
    },
}
H_PLUS = {i: add(H_MINUS[i], Q[i]) for i in (1, 2, 3)}


def phase(state: State) -> int:
    return int(state[1])


def check_stochastic_and_martingale() -> None:
    for s in STATES:
        assert sum((p for _, p, _ in TRANSITIONS[s]), F(0)) == 1
        mean_x = sum((p * dx for _, p, (dx, _) in TRANSITIONS[s]), F(0))
        mean_y = sum((p * dy for _, p, (_, dy) in TRANSITIONS[s]), F(0))
        assert (mean_x, mean_y) == (0, 0), (s, mean_x, mean_y)


def check_stationary_and_covariance() -> None:
    incoming = {s: F(0) for s in STATES}
    for s in STATES:
        for t, p, _ in TRANSITIONS[s]:
            incoming[t] += STATIONARY[s] * p
    assert incoming == STATIONARY

    cov = [[F(0), F(0)], [F(0), F(0)]]
    for s in STATES:
        for _, p, (dx, dy) in TRANSITIONS[s]:
            v = (F(dx), F(dy))
            for i in range(2):
                for j in range(2):
                    cov[i][j] += STATIONARY[s] * p * v[i] * v[j]
    assert tuple(tuple(row) for row in cov) == SIGMA


def check_harmonic_family(family: dict[int, Poly]) -> None:
    for s in STATES:
        lhs = family[phase(s)]
        rhs: Poly = {}
        for t, p, (dx, dy) in TRANSITIONS[s]:
            rhs = add(rhs, scale(p, shift(family[phase(t)], dx, dy)))
        assert clean(lhs) == clean(rhs), (s, add(lhs, scale(F(-1), rhs)))


def check_cone_and_exit_signs() -> None:
    # The explicit formulas in Proof.md prove these inequalities globally.
    for i in (1, 2, 3):
        for x in range(1, 81):
            for y in range(1, 81):
                assert evaluate(H_MINUS[i], x, y) > 0
                assert evaluate(Q[i], x, y) > 0
                assert evaluate(H_PLUS[i], x, y) > 0

    for z in range(0, 100):
        assert evaluate(H_MINUS[2], 0, z) == 0
        assert evaluate(H_MINUS[3], z, 0) == 0
        assert evaluate(H_MINUS[2], -1, z) < 0
    for z in range(2, 100):
        assert evaluate(H_MINUS[3], z, -1) <= 0

    # H^+ controls squared tangential displacement on all four exit faces.
    for z in range(0, 100):
        assert evaluate(H_PLUS[2], 0, z) >= F(3, 2) * z * z
        assert evaluate(H_PLUS[2], -1, z) >= F(1, 2) * z * z
        assert evaluate(H_PLUS[3], z, 0) >= 2 * z * z
        assert evaluate(H_PLUS[3], z, -1) == z * z


def check_quadratic_poisson_corrector() -> None:
    # A_ij solves (I-P)A_ij=C_ij-Sigma_ij. Therefore
    # X_i X_j - n Sigma_ij + A_ij(J_n) is a martingale.
    A = {
        (0, 0): dict(zip(STATES, (
            F(-26, 27), F(4, 27), F(-26, 27), F(4, 27), F(-8, 27), F(22, 27)))),
        (0, 1): dict(zip(STATES, (
            F(4, 27), F(-11, 27), F(22, 27), F(7, 27), F(4, 27), F(-11, 27)))),
        (1, 1): dict(zip(STATES, (
            F(-8, 27), F(22, 27), F(-26, 27), F(4, 27), F(-26, 27), F(4, 27)))),
    }
    for (i, j), values in A.items():
        for s in STATES:
            cond_cov = sum(
                (p * F(d[i]) * F(d[j]) for _, p, d in TRANSITIONS[s]), F(0)
            )
            next_a = sum((p * values[t] for t, p, _ in TRANSITIONS[s]), F(0))
            assert values[s] - next_a == cond_cov - SIGMA[i][j]


def count_g(n: int) -> int:
    @lru_cache(maxsize=None)
    def rec(a: int, b: int, c: int, last: int, run: int) -> int:
        if (a, b, c) == (n, n, n):
            return int(run != 1)
        total = 0
        counts = [a, b, c]
        for letter in range(3):
            if counts[letter] == n:
                continue
            if last < 3 and letter != last and run == 1:
                continue
            nxt = counts.copy()
            nxt[letter] += 1
            if not (nxt[0] >= nxt[1] >= nxt[2]):
                continue
            total += rec(*nxt, letter, 2 if letter == last else 1)
        return total
    return rec(0, 0, 0, 3, 0)


def check_initial_values() -> None:
    expected = (0, 1, 1, 5, 15, 69, 304, 1518, 7807, 42314)
    actual = tuple(count_g(n) for n in range(1, 11))
    assert actual == expected, actual


def check_common_path_weight() -> None:
    # (1/3)*(1/2)^(3n-2m)*(1/4)^(m-1)=4/(3*8^n).
    for n in range(2, 30):
        for m in range(1, 3 * n // 2 + 1):
            if 2 * m <= 3 * n:
                weight = F(1, 3) * F(1, 2) ** (3 * n - 2 * m) * F(1, 4) ** (m - 1)
                assert weight == F(4, 3 * 8**n)


def main() -> None:
    check_stochastic_and_martingale()
    check_stationary_and_covariance()
    check_harmonic_family(H_MINUS)
    check_harmonic_family(Q)
    check_harmonic_family(H_PLUS)
    check_cone_and_exit_signs()
    check_quadratic_poisson_corrector()
    check_common_path_weight()
    check_initial_values()
    print("PASS: exact restricted-run Markov-additive checks")


if __name__ == "__main__":
    main()
