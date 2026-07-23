# Chomp 10x42 kernel-proof plan

The existing exact C++ computation is discovery evidence, not a Lean proof.  The final
Formal Conjectures theorem must not use `sorry`, `native_decide`, `Lean.ofReduce`, or a
trusted external result.

## Correct game semantics

The old `IsPSet` definition quantified over one global P-set for every Ferrers position of
arbitrary size.  The computation did not establish that global statement.  The replacement
uses the ordinary finite normal-play semantics below a position:

* a **losing proof** contains a winning proof for every legal child;
* a **winning proof** contains one legal child with a losing proof.

These are finite inductive proof objects.  Because every Chomp move removes at least one
square, their dependency graph is acyclic.

## Certificate shape

The untrusted exporter may propose a DAG with records

```
state, label, optional losing reply
```

where `label` is losing or winning.  The Lean proof generator/checker must establish:

1. every child of every losing node is present and labelled winning;
2. every winning node's recorded reply is a legal move and is labelled losing;
3. the three target children are labelled losing;
4. the three rectangle openings are legal and pairwise distinct.

A generic Lean theorem then converts a valid finite DAG into the inductive game-outcome
proofs.  The C++ solver is not trusted: only the generated Lean proof terms count.

## Feasibility gate

The current retrograde search visits 3,042,311,754 prefixes and 107,342,138 losing
positions, so replaying the search in the kernel is not acceptable.  The next tool exports
only the strategy DAG reachable from the three target losing positions and reports:

* unique losing nodes;
* unique winning nodes;
* proof edges;
* serialized and compressed size;
* maximum theorem fan-out.

If the raw DAG is still too large, response selection will be optimized for maximal
subproof reuse and the observed states will be mined for a parametrized strategy invariant.
