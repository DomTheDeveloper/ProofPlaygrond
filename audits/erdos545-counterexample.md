# Erdős Problem 545 literal-counterexample audit

This gate checks commit `30c256a6e19a7fe32976f675ffe6fbb9c743af0f` in
`DomTheDeveloper/formal-conjectures`.

The checked Lean file proves the specialized formula

`R(K₂ ⊔ rK₁) = r + 2`

for ordinary non-induced monochromatic graph copies, and derives the two
isolated-vertex counterexamples to the statement in Formal Conjectures issue
#782.

The workflow rejects `sorry`, `admit`, `native_decide`, `unsafe`, custom axioms,
and compiler-trust shortcuts, then runs `#print axioms` on the final theorems.
