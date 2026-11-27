import FormalConjectures.OEIS.«86766»
import FiroozbakhtCounterexample
import Lean.Elab.Term

/-!
# Check the A086766 counterexample against DeepMind's declaration

The term elaborator retrieves a declaration's type. The counterexample supplies
a proof of its negation using only the imported certificate.
-/

open Lean Elab Term in
elab "decl_type% " n:ident : term => do
  let c ← getConstInfo (← resolveGlobalConstNoOverload n)
  pure c.type

namespace A086766Audit

theorem same_sequence : OeisA86766.a = A086766Certificate.a := rfl

theorem upstream_value : OeisA86766.a 109890 = 0 :=
  A086766Certificate.a_109890

theorem negates_declared_type : ¬ (decl_type% OeisA86766.conjecture2) :=
  A086766Certificate.refutes_conjecture2

#print axioms same_sequence
#print axioms upstream_value
#print axioms negates_declared_type
end A086766Audit
