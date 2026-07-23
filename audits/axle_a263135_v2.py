#!/usr/bin/env python3
"""AXLE A263135 wrapper for the live repaired DTD proof branch."""

from __future__ import annotations

from pathlib import Path

import axle_a263135 as base


def canonical_prefix(repo: Path) -> str:
    path = repo / "FormalConjectures/OEIS/263135.lean"
    source = path.read_text(encoding="utf-8")
    marker = next(
        (
            candidate
            for candidate in (
                "@[category research open, AMS 5]",
                "@[category research open, AMS 05]",
            )
            if candidate in source
        ),
        None,
    )
    if marker is None:
        raise RuntimeError(f"canonical theorem marker not found in {path}")
    prefix = source.split(marker, 1)[0]
    doc_start = prefix.rfind("/--")
    if doc_start == -1 or not prefix[doc_start:].strip().endswith("-/"):
        raise RuntimeError("could not isolate the canonical theorem docstring")
    prefix = prefix[:doc_start] + "end OeisA263135\n"
    return base.strip_project_attributes(base.strip_imports(prefix))


base.canonical_prefix = canonical_prefix
base.PROOF_SHA = "agent/solve-oeis-a263135"

if __name__ == "__main__":
    raise SystemExit(base.main())
