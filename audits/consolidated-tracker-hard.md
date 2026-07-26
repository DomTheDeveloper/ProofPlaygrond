# Consolidated tracker targeted audits

This audit lane compiles three active research modules independently under each source repository's pinned Lean toolchain:

- Erdős Problem 545 literal counterexample proof;
- Zhi-Wei Sun Conjecture 2.6 finite and analytic proof modules;
- OEIS A280831 parametric-family lemmas.

Current iterative source heads:

- Erdős 545: `0e3a4ac0fc7ee93cec184bf27bb8f4a79f3dcfca`;
- Sun 2.6: `70b0ac2147bdcaed3390e4866571b1d2d925f5ac`;
- A280831 families: `c39efc8f29479a6111a627fb388a846147a40556`.

Each job records the exact checked source commit, rejects placeholders and compiler-trust shortcuts, compiles only the relevant module, inspects the printed axiom transcript, and uploads its log.

This is an iterative verification surface. A final immutable audit will pin exact source SHAs after each branch is repaired and green.
