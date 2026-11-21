import Statements
import Development.AutomorphicArithmetic.CharacterBoxes.ClaimStrip
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EveryCharacterOfLiteratureOfVWin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WindowBoundOfLiteratureLevel
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.RowSrc
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.RecTExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.GoodReduction.SerreTate

open UpperTheory.LiteratureTheorems GlobalTheory.Mem.LiteralAutomorphy

private theorem characterWindows (O : OpenLiteratureStatements) (g : UpperTheory.V.Z.Win.RowT) :
    UpperTheory.Top.VWin := by
  let L := literature_local O
  let A := literature_automorphy O
  exact UpperTheory.V.v_window_of_literal_automorphy_n
    ⟨⟨L.bz, L.bern, L.geo, L.zel, L.disj, L.mp, L.temp, L.seg, L.sq, L.gen,
      L.multi, L.exh, L.cos, L.conv, L.dzi, L.brauer, L.chev, L.green⟩,
     ⟨A.decay, A.hc, A.fin, A.js, A.cusp, UpperTheory.BaseChangeIdentities.baseChangeN,
      A.gk, g, A.pur, A.coh, A.art, A.ray, A.chA, A.chW, A.berger⟩,
     literature_cohomology O,
     ⟨grothendieck_deformation_of_literature O, PositivityTheory.DualRT.abelianDeRham,
      GlobalTheory.abelianDualCrystal_of_dual_of_smoothLift GlobalTheory.dualAbelianScheme
        GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations,
      GlobalTheory.PeriodFamily.periodComparison_holds, GlobalTheory.PeriodFamily.gaussManinPeriods_holds,
      UpperTheory.Lit.serreTateGoodReduction, PositivityTheory.Prw.ellipticMainTheoremCM_holds,
      GlobalTheory.Laid.hcfj_holds, siegel_klingen_deligne_ribet_of_literature O,
      PositivityTheory.Prw.partialZetaFunctionalEquation_holds, GlobalTheory.Top.heckeTateFE⟩⟩

theorem LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf := by
  let g := UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter
  let O : OpenLiteratureStatements := ⟨g, UpperTheory.Zero.LLC.recTExists, g⟩
  exact every_character_of_literature_of_vWin O (characterWindows O g)

theorem riemannHypothesis : RiemannHypothesis := Claim.zeta LFunction_ne_zero_of_half_lt_re
theorem riemannZeta_eq_zero_re : RiemannZetaZerosOnLine := riemannHypothesis
theorem LFunction_eq_zero_re : DirichletLZerosOnLine := Claim.strip LFunction_ne_zero_of_half_lt_re
theorem LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine := by
  intro N _ χ _
  exact LFunction_eq_zero_re N χ

private theorem checkedClaims : RiemannHypothesis ∧ RiemannZetaZerosOnLine ∧
    DirichletLNonvanishingRightOfHalf ∧ DirichletLZerosOnLine ∧ PrimitiveDirichletLZerosOnLine :=
  ⟨riemannHypothesis, riemannZeta_eq_zero_re, LFunction_ne_zero_of_half_lt_re,
    LFunction_eq_zero_re, LFunction_eq_zero_re_of_isPrimitive⟩

open Lean Elab Command in
run_cmd do
  let used ← collectAxioms ``checkedClaims
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  unless used.size == allowed.size && allowed.all used.contains do
    throwError "Unexpected axioms for the five original statements: {used}"
  logInfo m!"Axioms for all five original statements: {used}"
