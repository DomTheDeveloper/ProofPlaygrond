module

import all FreePoles
import all PowerFreeCounting
import all PowerFreeGlobal
import all DeclaredTargets
public meta import Lean.Elab.Command

/-! Read the authentic upstream RH declaration. For each application, check the
function against that premise in Lean's kernel and compare the instantiated
conclusion to its separately stated target. -/

open Lean Elab Command

#print axioms PowerFree.quotient_order
#print axioms PowerFree.main_pole
#print axioms PowerFree.poles_of_RH
#print axioms PowerFree.multiplicity_of_RH
#print axioms PowerFree.first_pole_on_chain
#print axioms PowerFree.RH_iff_poleLine
#print axioms PowerFree.squarefree_pole_line_of_RH
#print axioms PowerFree.kFree_two_iff
#print axioms PowerFree.kFreeSeries_eq_quotient
#print axioms PowerFree.mellin_kFreeCount
#print axioms PowerFree.residue_at_one
#print axioms PowerFree.analytic_order_at_zero
#print axioms PowerFree.leading_coefficient_of_RH
#print axioms PowerFree.residue_at_scaled_zero_of_RH
#print axioms PowerFree.perron_residue_of_RH
#print axioms PowerFree.negative_zero_deriv
#print axioms PowerFree.left_order_of_RH
#print axioms PowerFree.global_poles_of_RH
#print axioms PowerFree.trivial_on_grid_iff
#print axioms PowerFree.negative_grid_order_of_RH
#print axioms PowerFree.simple_ratio_residue
#print axioms PowerFree.negative_residue_of_RH
#print axioms PowerFree.cancelled_trivial_limit
#print axioms PowerFree.pole_locations_of_RH

run_cmd do
  let some path ← IO.getEnv "POWERFREE_RH_OLEAN"
    | throwError "Set POWERFREE_RH_OLEAN to the compact project's compiled Main.olean."
  let (data, _) ← readModuleData path
  let some (.thmInfo input) := data.constants.find? (fun c ↦ c.name == `riemannHypothesis)
    | throwError "Missing compiled RH theorem."
  unless input.levelParams.isEmpty && input.type == .const `RiemannHypothesis [] do
    throwError "Unexpected RH interface."
  let env ← getEnv
  let endpoint := mkApp (mkConst `New.zeta_zeros_on_line) (mkConst `New.grh)
  unless input.value.consumeMData == endpoint do throwError "Unexpected upstream proof term."
  for (fn, goal) in [(`PowerFree.poles_of_RH, `PowerFree.Target.poles),
      (`PowerFree.multiplicity_of_RH, `PowerFree.Target.scaled_zero_multiplicity),
      (`PowerFree.squarefree_pole_line_of_RH, `PowerFree.Target.squarefree_pole_line),
      (`PowerFree.analytic_order_at_zero, `PowerFree.Target.analytic_order_at_zero),
      (`PowerFree.leading_coefficient_of_RH, `PowerFree.Target.leading_coefficient),
      (`PowerFree.residue_at_scaled_zero_of_RH, `PowerFree.Target.simple_residue),
      (`PowerFree.perron_residue_of_RH, `PowerFree.Target.perron_residue),
      (`PowerFree.pole_locations_of_RH, `PowerFree.Target.all_pole_locations),
      (`PowerFree.negative_grid_order_of_RH, `PowerFree.Target.negative_grid_order),
      (`PowerFree.negative_residue_of_RH, `PowerFree.Target.negative_residue)] do
    let some (.thmInfo th) := env.find? fn | throwError "Missing theorem {fn}."
    let .forallE _ premise result _ := th.type | throwError "Expected a quantified proof."
    unless premise == input.type do throwError "Mismatched input for {fn}."
    let expected := mkConst goal
    let proof := Expr.lam `rh input.type (mkApp (mkConst fn) (.bvar 0)) .default
    let want := Expr.forallE `rh input.type expected .default
    let .ok inferred := Kernel.check env {} proof | throwError "Kernel rejected application {fn}."
    let .ok true := Kernel.isDefEq env {} inferred want | throwError "Mismatched abstraction {fn}."
    let conclusion := result.instantiate1 (mkConst input.name)
    unless !conclusion.hasLooseBVars do throwError "Open conclusion {goal}."
    let .ok true := Kernel.isDefEq env {} conclusion expected | throwError "Mismatched target {goal}."
    logInfo m!"PASS  {fn} {input.name}  :  {goal}"
