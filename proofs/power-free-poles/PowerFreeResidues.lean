import PowerFreeCounting
import PowerFreeGlobal
import Main

namespace PowerFree

theorem finite_order_at_zero : Target.analytic_order_at_zero :=
  @analytic_order_at_zero riemannHypothesis

theorem leading_coefficient : Target.leading_coefficient :=
  @leading_coefficient_of_RH riemannHypothesis

theorem simple_residue : Target.simple_residue :=
  @residue_at_scaled_zero_of_RH riemannHypothesis

theorem perron_residue : Target.perron_residue :=
  @perron_residue_of_RH riemannHypothesis

theorem all_pole_locations : Target.all_pole_locations :=
  @pole_locations_of_RH riemannHypothesis

theorem negative_grid_order : Target.negative_grid_order :=
  @negative_grid_order_of_RH riemannHypothesis

theorem negative_residue : Target.negative_residue :=
  @negative_residue_of_RH riemannHypothesis

end PowerFree
