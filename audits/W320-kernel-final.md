# W(3,20) kernel final audit

Audit the exact DTD proof commit `c81b931c9bc70203dc1a687a1381957d6c3e167e` from pull request `DomTheDeveloper/formal-conjectures#173`.

Required checks:

- exact five-file proof scope;
- build `FormalConjectures.GreensOpenProblems.Green14FastKernel20`;
- print axioms for `Green14.FastKernel.valid_20` and `Green14.FastKernel.W_3_20_lower_fast`;
- reject `sorryAx`, `Lean.ofReduceBool`, and `Lean.trustCompiler`.
