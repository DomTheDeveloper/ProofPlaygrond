# Graffiti.pc 169 verification

The saved file Graffiti169.lean proves the leaf bound for every finite connected simple graph with at least two vertices. Its exact theorem shows that the one-vertex graph is the unique exception among finite connected simple graphs. A leaf has degree one. On the one-vertex graph the sole tree has zero leaves and the proposed lower bound equals one.

For a vertex r of the input graph G, let E(r) count all vertices of G at even distance from r. The existence theorem supplies a tree T on all vertices of G, using only edges of G, with at least 1 + max E − min E leaves. Audit169.lean derives the equivalent statement that the same tree satisfies 1 + E(r) ≤ leaves(T) + E(s) for every ordered pair r, s. This second statement defines a leaf by having exactly one neighbor and expresses evenness by divisibility by two. It also checks the singleton counterexample directly.

## Rebuild from the two source files

Use Linux with Lean 4.33.1 and Mathlib v4.33.1 at commit `0df444a360eaa60ab8c11dca51a86af692955474`. From a checkout of that Mathlib revision with its compiled dependencies installed, run the following command. Replace the path with the directory where you extracted this archive.

```sh
lake env bash /path/to/extracted/verify.sh
```

The script copies the two source files into a fresh temporary directory, verifies the saved proof's SHA-256, builds each file with warnings treated as errors, runs leanchecker on each module, and checks all five transitive axiom lists. It requires Bash and the standard Linux utilities sha256sum and grep. The complete output is in logs/reproduction.log. The original module's rebuilt .olean was byte-identical to the original proof object.

## Check the exported proofs independently

proof.ndjson contains the five named theorems with their proof terms and transitive dependencies in lean4export format 3.1.0. Use the con-leche binary from the Lean 4.36.0 distribution. From the extracted directory, run the following commands.

```sh
sha256sum -c SHA256SUMS
con-leche --verified --jobs=2 --progress=10000 proof.ndjson
```

The independent checker accepted 8,685 declarations and exited with status zero. Its complete output is in logs/external-kernel.log. export-summary.json identifies all five theorem bodies and the three explicit axioms in the stream. They are propext, Classical.choice and Quot.sound. The original theorem and both audit statements are unconditional with respect to the Riemann hypothesis.

The five exported targets were Graffiti169.graffiti169, Graffiti169.graffiti169_exact, Graffiti169.exists_spanning_tree, Graffiti169Audit.spanning_tree_for_all_roots and Graffiti169Audit.singleton_fails. To regenerate an equivalent export with those fresh modules on LEAN_PATH, use the following command.

```sh
lean4export Audit169 -- Graffiti169.graffiti169 Graffiti169.graffiti169_exact \
  Graffiti169.exists_spanning_tree Graffiti169Audit.spanning_tree_for_all_roots \
  Graffiti169Audit.singleton_fails > proof.ndjson
```

The original problems and definitions appear in the University of Houston–Downtown catalogue, entry 169. The catalogue lists the conjecture as open in its November 5, 2026 update. Historical priority remains unverified.

https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/wowiiaii.pdf#page=97
