# Exact MDD compression of the Chomp 10×42 P-set

The target-stopping exact solver enumerates all P-positions in rank order through the third
claimed child.  Its database contains **107,342,138** exact P-position ranks and ends at

```text
[42,42,42,42,42,42,42,25,25,25]
```

with combinatorial rank `15,820,013,305`.

`chomp_p_mdd.cpp` unranks that sorted stream and constructs the exact reduced layered
multi-valued decision diagram over the ten row lengths.  Hashes only select candidate buckets;
a node is merged only after exact transition-by-transition comparison.

A complete run produced:

```text
words=107342138
depth=0 nodes=1 transitions=42
depth=1 nodes=42 transitions=797
depth=2 nodes=756 transitions=10166
depth=3 nodes=9364 transitions=102147
depth=4 nodes=90493 transitions=825905
depth=5 nodes=678267 transitions=5403664
depth=6 nodes=3667697 transitions=25241311
depth=7 nodes=9994761 transitions=54615011
depth=8 nodes=2465000 transitions=10555794
depth=9 nodes=40 transitions=40
total_nodes=16906422 total_transitions=96754877
```

The construction took about 29 seconds and under 1 GiB RSS in the current sandbox.  This is a
substantial compression relative to 107 million explicit P states and the multi-billion-state
retrograde scan, but it is still too large for a naive theorem-per-node Lean development.

## Formal-proof consequence

The viable route is symbolic model checking over the reduced MDD:

1. represent the exact P predicate by a layered decision diagram;
2. verify, inside Lean, sound MDD operations for intersection, union, complement within the
   bounded Ferrers domain, and preimages under each bite map;
3. certify that no P-position has a P child;
4. certify that every valid non-P position below the target rank has a move to P;
5. invoke the progressively bounded game theorem to obtain kernel proofs that the three target
   children are losing.

The MDD builder remains untrusted.  The final Lean checker must verify node well-formedness and
every symbolic-operation certificate, and the final theorem must contain no `sorry`, `admit`,
`native_decide`, custom axiom, `Lean.ofReduce`, `Lean.ofReduceBool`, or compiler-trust escape.
