# Consolidated tracker targeted audits

This audit lane compiles three active research modules independently under each source repository's pinned Lean toolchain:

- Erdős Problem 545 literal counterexample proof;
- Zhi-Wei Sun Conjecture 2.6 finite and analytic proof modules;
- OEIS A280831 parametric-family lemmas.

Current iterative source heads:

- Erdős 545: `d1521d52329c1ce891642d50be1bdb654ad43433`;
- Sun 2.6: `4541e7704610f4e16bb1ef4d637a5867ac2c78db`;
- A280831 families: `c39efc8f29479a6111a627fb388a846147a40556`.

Each job records the exact checked source commit, rejects placeholders and compiler-trust shortcuts, compiles only the relevant module, inspects the printed axiom transcript, and uploads its log.

This is an iterative verification surface. A final immutable audit will pin exact source SHAs after each branch is repaired and green.
