# OEIS A263135 native final audit

The promoted canonical honeycomb-contact proof is pinned to immutable Formal Conjectures commit `cb8de9921fc62810991a0384ee412cfed0ad8e7c`.

The audit checks the exact catalog declaration `OeisA263135.conjecture`, not merely the auxiliary theorem used during development. It:

- rejects placeholders and trust shortcuts across the complete `Scratch/A263135*.lean` chain and both canonical A263135 files;
- builds the complete `A263135ScratchAudit` module chain;
- executes `Scratch/A263135Audit.lean`;
- prints the axiom dependencies of `OeisA263135.conjecture`;
- rejects `sorryAx`, `Lean.trustCompiler`, `Lean.ofReduce`, and `Lean.ofReduceBool`.

The underlying proof chain previously passed all gates in run `29987594607`, with dependencies `[propext, Classical.choice, Quot.sound]`. The promoted catalog theorem preserves the original statement and delegates to that verified theorem. The finite two-vertex base case uses kernel reduction with `decide`, not `native_decide` or compiler trust.
