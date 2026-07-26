# Consolidated tracker targeted audits

This audit lane compiles three active research modules independently under each source repository's pinned Lean toolchain:

- Erdős Problem 545 literal counterexample proof;
- Zhi-Wei Sun Conjecture 2.6 finite and analytic proof modules;
- OEIS A280831 parametric-family lemmas.

Current iterative source heads:

- Erdős 545: `e48690cec64e5b2a719f344b2ffd2bf012a0b487`;
- Sun 2.6: `fc3595a02b559ee08fae89f5f0eeeabfeeda5b83`;
- A280831 families: `58797393438be078942dc8c7bc2d456d01779fee`.

Each job records the exact checked source commit, rejects placeholders and compiler-trust shortcuts, compiles only the relevant module, inspects the printed axiom transcript, and uploads its log.

This is an iterative verification surface. A final immutable audit will pin exact source SHAs after each branch is repaired and green.
