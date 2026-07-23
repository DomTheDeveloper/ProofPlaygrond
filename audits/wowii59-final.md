# WOWII Conjecture 59 final audit

This is the sole active verification lane for the proposed explicit 18-vertex counterexample.

The workflow checks the current `agent/solve-wowii-59` source branch and records the resolved immutable SHA. The repaired source now uses:

- module-level unlimited heartbeats and recursion depth;
- an unlimited process stack during compilation;
- kernel-checked `bv_decide` for the concrete residue and cycle-cover certificates;
- the corrected hub disequality direction;
- direct specialization of the universal conjecture statement.

The gate rejects proof holes, unsafe declarations, custom axioms, `native_decide`, and compiler-trust shortcuts; builds the exact counterexample; prints the terminal theorem axioms; and rejects `sorryAx` or compiler-trust dependencies.