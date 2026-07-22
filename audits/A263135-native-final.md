# OEIS A263135 native final audit

Verify `DomTheDeveloper/formal-conjectures@6ad03f2a0fa5de81c0ed08fd0fc38a42f12513b7` by compiling every `Scratch.A263135*` module in topological import order directly with the repository-pinned Lean executable, writing each `.olean` into the project Lean path, then compiling `Scratch.A263135Audit` and enforcing a `#print axioms OeisA263135.conjecture_solved` result without `sorryAx` or compiler-trust axioms.
