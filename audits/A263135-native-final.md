# OEIS A263135 native final audit

Verify frozen commit `DomTheDeveloper/formal-conjectures@9b08804ddd17dff14660f6b0cd5d01a9636a4b23` on `ubuntu-latest`, avoiding the slim runner's 15-minute cancellation ceiling. The canonical theorem imports only `Mathlib` and `FormalConjectures.Util.Attributes.Basic`; the complete 27-module proof stack is registered in `A263135ScratchAudit`. Build that library, execute `Scratch/A263135Audit.lean`, and enforce a `#print axioms OeisA263135.conjecture_solved` result without `sorryAx` or compiler-trust axioms.
