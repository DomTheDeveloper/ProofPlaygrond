#!/usr/bin/env python3
"""Generate and independently verify the exact W(3,20) SAT instance.

Variable x_i is true when i has color 1.
A satisfying assignment is a coloring of [N] with:
  * no color-0 3-term arithmetic progression; and
  * no color-1 20-term arithmetic progression.
Thus N=389 is UNSAT exactly when W(3,20) <= 389.
"""

from __future__ import annotations

import argparse
import hashlib
import re
from pathlib import Path


def clauses_for(n: int):
    # Every 3-AP contains color 1: x_a OR x_(a+d) OR x_(a+2d).
    for a in range(1, n + 1):
        for d in range(1, (n - a) // 2 + 1):
            yield (a, a + d, a + 2 * d)

    # Every 20-AP contains color 0: not all twenty x variables are true.
    for a in range(1, n + 1):
        for d in range(1, (n - a) // 19 + 1):
            yield tuple(-(a + i * d) for i in range(20))


def generate(n: int, output: Path) -> None:
    clauses = list(clauses_for(n))
    with output.open("w", encoding="ascii") as f:
        f.write(f"p cnf {n} {len(clauses)}\n")
        for clause in clauses:
            f.write(" ".join(map(str, clause)) + " 0\n")

    data = output.read_bytes()
    c3 = sum((n - a) // 2 for a in range(1, n + 1))
    c20 = sum((n - a) // 19 for a in range(1, n + 1))
    print(f"N={n}")
    print(f"3-AP clauses={c3}")
    print(f"20-AP clauses={c20}")
    print(f"total clauses={len(clauses)}")
    print(f"CNF sha256={hashlib.sha256(data).hexdigest()}")


def parse_model(log: Path, n: int) -> list[bool]:
    text = log.read_text(encoding="utf-8", errors="replace")
    if "s SATISFIABLE" not in text:
        raise ValueError("solver log does not report SATISFIABLE")
    assignment: dict[int, bool] = {}
    for line in text.splitlines():
        if not line.startswith("v "):
            continue
        for token in re.findall(r"-?\d+", line[2:]):
            lit = int(token)
            if lit == 0:
                continue
            assignment[abs(lit)] = lit > 0
    missing = [i for i in range(1, n + 1) if i not in assignment]
    if missing:
        raise ValueError(f"model is missing {len(missing)} variables, first={missing[:10]}")
    return [False] + [assignment[i] for i in range(1, n + 1)]


def verify_model(n: int, log: Path, output: Path | None) -> None:
    x = parse_model(log, n)

    checked3 = 0
    for a in range(1, n + 1):
        for d in range(1, (n - a) // 2 + 1):
            checked3 += 1
            if not (x[a] or x[a + d] or x[a + 2 * d]):
                raise AssertionError(f"color-0 3-AP at a={a}, d={d}")

    checked20 = 0
    for a in range(1, n + 1):
        for d in range(1, (n - a) // 19 + 1):
            checked20 += 1
            if all(x[a + i * d] for i in range(20)):
                raise AssertionError(f"color-1 20-AP at a={a}, d={d}")

    bits = "".join("1" if x[i] else "0" for i in range(1, n + 1))
    print(f"verified SAT model for N={n}")
    print(f"checked 3-APs={checked3}")
    print(f"checked 20-APs={checked20}")
    print(f"model sha256={hashlib.sha256(bits.encode()).hexdigest()}")
    if output is not None:
        output.write_text(bits + "\n", encoding="ascii")


def main() -> None:
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="command", required=True)

    gen = sub.add_parser("generate")
    gen.add_argument("--n", type=int, required=True)
    gen.add_argument("--output", type=Path, required=True)

    ver = sub.add_parser("verify-model")
    ver.add_argument("--n", type=int, required=True)
    ver.add_argument("--log", type=Path, required=True)
    ver.add_argument("--output", type=Path)

    args = parser.parse_args()
    if args.command == "generate":
        generate(args.n, args.output)
    else:
        verify_model(args.n, args.log, args.output)


if __name__ == "__main__":
    main()
