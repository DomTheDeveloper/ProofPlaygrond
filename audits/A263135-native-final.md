# OEIS A263135 native final audit

Verify `DomTheDeveloper/formal-conjectures@6ad03f2a0fa5de81c0ed08fd0fc38a42f12513b7` by compiling every `Scratch.A263135*` module in topological import order, then building `Scratch.A263135Audit` with the repository-pinned Lean toolchain and enforcing a `#print axioms OeisA263135.conjecture_solved` result without `sorryAx` or compiler-trust axioms.
