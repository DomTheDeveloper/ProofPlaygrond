#!/usr/bin/env python3
"""AXLE A263135 wrapper using explicit Finset.sum syntax in the canonical prelude."""

from __future__ import annotations

import axle_a263135 as base

_OLD_CONTACTS = """def contacts (S : Finset Vertex) : ℕ :=
  ∑ v in S, if v.side = true then 0 else
    ∑ d : Direction, if neighbor v d ∈ S then 1 else 0
"""

_NEW_CONTACTS = """def contacts (S : Finset Vertex) : ℕ :=
  Finset.sum S (fun v =>
    if v.side = true then 0 else
      Finset.sum Finset.univ (fun d : Direction =>
        if neighbor v d ∈ S then 1 else 0))
"""

_original_canonical_prefix = base.canonical_prefix


def canonical_prefix(repo):
    prefix = _original_canonical_prefix(repo)
    if _OLD_CONTACTS not in prefix:
        raise RuntimeError("canonical contacts definition did not match expected source")
    return prefix.replace(_OLD_CONTACTS, _NEW_CONTACTS)


base.canonical_prefix = canonical_prefix

if __name__ == "__main__":
    raise SystemExit(base.main())
