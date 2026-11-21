/-
Copyright 2026 David Sanftenberg. SPDX-License-Identifier: Apache-2.0
The arithmetic inputs adapt the principal-character specialization at d7857c26.
The final comparison derives all five statements of Levent Alpöge’s release.
-/
import CompanionTheory.AutomorphicTheory.MirabolicRestriction.MirabolicInduction.CuspidalMirabolic
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.DsExhaust
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.FinalB
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Imports
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PrincipalPolarisationUniqueSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelOfPrincipalisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmCurveGoodOutsidePrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodChernWeil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicDiscreteSeriesHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweDualityRealHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTailTer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfinitesimalEquivalenceUnitaryGroupPQ
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JoinOutOfFive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegOfNadelVanishingPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KudlaSplittingSplitUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerOneHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetaplecticRepresentationHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdFactorsOfMonic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectionFormulaAndChernDegreeOfHeightProjectio
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianLieSeminegativeBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelKlingenDeligneRibetOfBoth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelToroidalIntegralHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalCompactificationHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolGeOfHilbertSamuel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlathFactorisationOfTensorProduct
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WindowBoundOfLiteratureLevel
import Development.AutomorphicArithmetic.CharacterBoxes.ClaimStrip
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.RowSrc
import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.GlnTemp
import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.RallisDM
import Development.AutomorphicArithmetic.ThetaCorrespondence.GoodReduction.SerreTate
import Development.AutomorphicArithmetic.ThetaCorrespondence.Linnik
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ModularityOfHyps
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SiegelEisensteinSecondTermHypotheses
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopCovolSlim2Use
import Development.AutomorphicArithmetic.ThetaCorrespondence.WeilRepresentation.WeilEx
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GreenbergWilesOfPoitouTate
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BlochKatoLocal
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HeckeTateFunctionalEquation
import Development.WeilBound.CoreStatements.AutomorphicKernels.DeligneRibet.NotDvdAbsNorm
import Development.WeilBound.CoreStatements.AutomorphicKernels.NadelVanishing.TopNSI
import Development.WeilBound.CoreStatements.HodgeTatePoints.ZarTop
import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.FinalB
import Development.WeilBound.CoreStatements.PublishedTheorems.ClozelPurity.Bridge
import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GlobalEulerCharOfLemmaX
import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalFiniteness.GlobalFiniteness
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PoitouTateNineTerm.PoitouTateNormalisedHolds
import Development.WeilBound.CoreStatements.ResolutionCharZero.PrincipalisationCharZeroClosed
import Development.WeilBound.CoreStatements.ResolutionCharZero.ResolutionCharZero
import Development.WeilBound.CoreStatements.StandardPublishedResults.StandardTheoremStatements.CuspDecaySobolev
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.CycleHeightFormulas.CycleHeightsDirect
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.NefDivisors.NefRR
import Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.CuspidalConstantTerms.FiniteOfCuspOfConstTerm
import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.FdTopB
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.EisensteinChartSplitting.SiegelEisensteinContinuation
import Statements

namespace RiemannGaussian.AlpogeWindow

theorem archive_local_theta_inputs : GlobalTheory.FunPr.ThetaLocalInputs := by
  have doubling := ResidueKilled.dm_of_two GlobalTheory.RapidDecay.cuspRapidDecay
    PositivityTheory.RgEis.Sp.Hd.siegelEisensteinContinuation trivial
  exact {
    greenSeriesSt := GlobalTheory.GreenSeries.green_series PositivityTheory.GreenCharacters.greenCuspidal
    linnik := UpperTheory.Lit.linnik
    complexMultiplicationJSt := GlobalTheory.CompanionTheory.Published.complexMultiplicationJ
    cuspidalMirabolic := CompanionTheory.Mirab.cuspidalMirabolic
    weylBranching := GlobalTheory.Published.weylBranching_holds
    bernsteinUnitaryProductIrreducible := PositivityTheory.RgUd.All.bernsteinUnitaryProductIrreducible
    zelevinskyPolynomialRing := PositivityTheory.Prw.zelevinskyPolynomialRing_of
      PositivityTheory.Prw.bernsteinZelevinskyFiniteness_holds PositivityTheory.RgGu.segmentRepresentation
      (PositivityTheory.Groth.grothendieckRingPolynomial_of_seg PositivityTheory.RgGu.segmentRepresentation)
    bernsteinZelevinskyFiniteness := PositivityTheory.Prw.bernsteinZelevinskyFiniteness_holds
    cuspTraceClass := PositivityTheory.Prw.cuspTraceClass_of PositivityTheory.Prw.dixmierMalliavinFactorisation_holds
    flathFactorisation := GlobalTheory.flathFactorisation_of_tensorProduct CompanionTheory.Rg.Fl.B.flathTensorProduct
      CompanionTheory.Rg.Fl.B.unitaryIrreducibleAdmissible
    weilSiegelFormulaUnitary := UpperTheory.Lit.Sw47.weilUnitary
    rallisInnerProductConvergent := UpperTheory.Lit.Rallis.RallisIPProof.rallis_of_dm doubling
      UpperTheory.Lit.Sw47.convergent UpperTheory.Lit.weilThetaConvergence
    doublingMethod := doubling
    unramifiedDoublingGL := GlobalTheory.UnramDoublingProof.unramifiedDoublingGL
    hermitianLocalGlobal := GlobalTheory.Published.hermitianLocalGlobal_holds
    quadraticClassFieldTheory := GlobalTheory.Published.quadraticClassFieldTheory_holds
    borelCasselman := GlobalTheory.Published.BorelCasselman_holds
    radfordShufflePolynomial := GlobalTheory.Published.radfordShufflePolynomial_holds
    dixmierMalliavinFactorisation := PositivityTheory.DM.dixmierMalliavinFactorisation_holds
    schurOrthogonalitySquareIntegrable := GlobalTheory.Published.schurOrthogonalitySquareIntegrable'
    heckeLPartialContinuation := GlobalTheory.Published.HeckeLPartialContinuation_holds
    logDerOne := GlobalTheory.LogDerOneProof.logDerOne_holds
    kFiniteVectorsUnitary := GlobalTheory.CompanionTheory.Published.kFiniteVectors_irreducibleUnitary_unitaryGroupPQ
    discreteSeriesLowestKType := PositivityTheory.Prw.discreteSeriesLowestKType_holds
    holomorphicDiscreteSeries := GlobalTheory.HolDS.holomorphicDiscreteSeries_holds
    gKGlobalisation := GlobalTheory.gkGlobalisation_holds
    cuspBounded := PositivityTheory.Stage1.PM.cuspBounded
    strongApproxSU := GlobalTheory.StrongApproxSUProof.strongApproxSU
    heckeLEntireAndNonzeroAtOne := GlobalTheory.Published.HeckeLEntireAndNonzeroAtOne_holds
    realMetaplecticRepresentation := CompanionTheory.ThKR.realMetaplecticRepresentation_holds
    cuspDecayBound := GlobalTheory.CuspGeo.cuspDecayBound
    gLHoweDuality := GlobalTheory.Published.glHoweDuality_holds
    kudlaSplittingSplitUnitary := GlobalTheory.kudlaSplittingSplitUnitary
    metaplecticRepresentation := GlobalTheory.metaplecticRepresentation_holds
    harishChandraModules := GlobalTheory.HcPort.print_harishChandraModules
    discreteSeriesCover := CompanionTheory.RgExh.discreteSeriesCover
    idealInvariantsOneOrbitSt := PositivityTheory.Prw.idealInvariantsOneOrbitSt_holds
    hermitianHassePrinciple := GlobalTheory.Published.hermitianHassePrinciple_holds
    stoneVonNeumann := GlobalTheory.Published.StoneVonNeumann_holds
    discreteSeriesUpqExists := CompanionTheory.RgDs.B.discreteSeriesUpqExists
    formalDegreeCompactDual := PositivityTheory.RgFd.B.formalDegreeCompactDual
    thetaRationalInvariance := GlobalTheory.Published.thetaRationalInvariance_holds
    discreteSeriesHermitianUnique := PositivityTheory.Prw.discreteSeriesHermitianUnique_holds
    discreteSeriesExists := CompanionTheory.RgDs.B.discreteSeriesExists
    harishChandraFinite := PositivityTheory.RgHf.harishChandraFinite
    cuspRapidDecay := GlobalTheory.RapidDecay.cuspRapidDecay
    weilRepresentationUnitaryPair := GlobalTheory.weilRepresentationUnitaryPair
    discreteSeriesCoverExists := CompanionTheory.RgDs.B.discreteSeriesCoverExists
    cuspDecaySobolev := PositivityTheory.Stage1.PM.cuspDecaySobolev
    casselmanWallach := PositivityTheory.CWB.casselmanWallach
    howeDualityReal := GlobalTheory.howeDualityReal_holds
    siegelSetUnitary := UpperTheory.Lit.siegelSetUnitary_of_core
    weilRepresentationExists := UpperTheory.Lit.weilRepresentationExists_pair }

end RiemannGaussian.AlpogeWindow

set_option synthInstance.maxHeartbeats 200000

namespace RiemannGaussian.AlpogeWindow.ArchivedInputs

theorem siegel_klingen_deligne_ribet_of_literature : GlobalTheory.Published.SiegelKlingenDeligneRibet :=
  GlobalTheory.siegelKlingenDeligneRibet_of_both PositivityTheory.Prw.siegelKlingen_holds PositivityTheory.PfDRL.deligneRibet

theorem join_out_of_literature : GlobalTheory.Mem.LiteralAutomorphy.JoinOut :=
  GlobalTheory.JoinFun.joinOut_of_five PositivityTheory.Prw.ellipticMainTheoremCM_holds GlobalTheory.Laid.hcfj_holds siegel_klingen_deligne_ribet_of_literature PositivityTheory.Prw.partialZetaFunctionalEquation_holds GlobalTheory.CompanionTheory.HeckeFE.heckeTateFunctionalEquation

theorem algebraic_character_wd_of_literature : GlobalTheory.Published.AlgebraicCharacterWD :=
  UpperTheory.Lit.CharWD.algebraicCharacterWD GlobalTheory.globalArtinReciprocity_holds UpperTheory.Lit.heckeLAdicCharacterDeRham GlobalTheory.deRham_potentiallySemistable

theorem ar_calc_of_literature : GlobalTheory.Published.ArCalc :=
  GlobalTheory.ArithmeticHeightTower.ArakelovDirectHeights.arCalc_direct PositivityTheory.Tls2.Pl.poincareLelong PositivityTheory.ResPlug.FromRes.resK

theorem ar_degree_of_literature : GlobalTheory.Published.ArDegree :=
  GlobalTheory.Published.arDegree_of_heightProjection (GlobalTheory.Published.CycleHeights.heightProjection (GlobalTheory.ArithmeticHeightTower.ArakelovDirectHeights.cycleHeights_direct PositivityTheory.Tls2.Pl.poincareLelong PositivityTheory.ResPlug.FromRes.resK)) GlobalTheory.ChernDegree.chernDegreeComplex

theorem arith_hilbert_samuel_of_literature : GlobalTheory.Published.ArithHilbertSamuel :=
  GlobalTheory.arithHilbertSamuel_of_principalisation PositivityTheory.ResPlug.WeightsCompactStabilizer.principalisation_closed

theorem ess_square_integrable_segments_of_literature : GlobalTheory.Published.EssSquareIntegrableSegments :=
  PositivityTheory.Exh.essSquareIntegrableSegments_of_seg (PositivityTheory.RgGu.segmentRepresentation)

theorem pair_u_of_literature : _root_.UpperTheory.GalS.PairUAlt :=
  _root_.UpperTheory.GalS.field_of_starFull_alt UpperTheory.Zero.LLC.recTExists DiscreteGroups.sglob.LConv.localConverseGL (PositivityTheory.Exh.langlandsExhaustionGL_of_seg (PositivityTheory.RgGu.segmentRepresentation)) UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter

theorem gelfand_kazhdan_dual_of_literature : GlobalTheory.Published.GelfandKazhdanDual :=
  PositivityTheory.JMult1.gelfandKazhdanDual_of_rigidity PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity RfCs.cuspidalSpectrumGL.2.2

theorem zelevinsky_polynomial_ring_of_literature : GlobalTheory.Published.ZelevinskyPolynomialRing :=
  PositivityTheory.Prw.zelevinskyPolynomialRing_of PositivityTheory.Prw.bernsteinZelevinskyFiniteness_holds PositivityTheory.RgGu.segmentRepresentation ((PositivityTheory.Groth.grothendieckRingPolynomial_of_seg (PositivityTheory.RgGu.segmentRepresentation)))

theorem depth_zero_induction_of_literature : GlobalTheory.Published.DepthZeroInduction :=
  (GlobalTheory.DepthZeroPass.depthZeroInduction GlobalTheory.CompanionTheory.GeoLink.geometricLemma PositivityTheory.Prw.bernsteinZelevinskyFiniteness_holds zelevinsky_polynomial_ring_of_literature)

theorem langlands_exhaustion_gl_of_literature : GlobalTheory.Published.LanglandsExhaustionGL :=
  PositivityTheory.Exh.langlandsExhaustionGL_of_seg (PositivityTheory.RgGu.segmentRepresentation)

theorem langlands_multisegments_of_literature : GlobalTheory.Published.LanglandsMultisegments :=
  PositivityTheory.Exh.langlandsMultisegments_of_seg (PositivityTheory.RgGu.segmentRepresentation)

theorem standard_cosocle_gl_of_literature : GlobalTheory.Published.StandardCosocleGL :=
  PositivityTheory.Exh.standardCosocleGL_of_seg (PositivityTheory.RgGu.segmentRepresentation)

theorem local_langlands_gl_recT_exists_of_literature : _root_.UpperTheory.Zero.LLC.RecTExists :=
  _root_.UpperTheory.One.M.New.llOf_alt UpperTheory.Zero.LLC.recTExists DiscreteGroups.sglob.LConv.localConverseGL depth_zero_induction_of_literature GlobalTheory.BrauerZero.brauerDegreeZero GlobalTheory.Published.chevalleyUnits' GlobalTheory.globalArtinReciprocity_holds langlands_exhaustion_gl_of_literature langlands_multisegments_of_literature standard_cosocle_gl_of_literature zelevinsky_polynomial_ring_of_literature GlobalTheory.CompanionTheory.GeoLink.geometricLemma PositivityTheory.Prw.bernsteinZelevinskyFiniteness_holds

theorem tempered_product_of_square_integrable_of_literature : GlobalTheory.Published.TemperedProductOfSquareIntegrable :=
  UpperTheory.Lit.Cas.temperedProduct GlobalTheory.CompanionTheory.GeoLink.geometricLemma PositivityTheory.Prw.bernsteinZelevinskyFiniteness_holds PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top PositivityTheory.Tls2.BZGL.standardFunctorsFiniteLength_top langlands_exhaustion_gl_of_literature standard_cosocle_gl_of_literature langlands_multisegments_of_literature ess_square_integrable_segments_of_literature

theorem cusp_trace_class_of_literature : GlobalTheory.Published.CuspTraceClass :=
  PositivityTheory.Prw.cuspTraceClass_of PositivityTheory.Prw.dixmierMalliavinFactorisation_holds

theorem cycle_heights_of_literature : GlobalTheory.Published.CycleHeights :=
  GlobalTheory.ArithmeticHeightTower.ArakelovDirectHeights.cycleHeights_direct PositivityTheory.Tls2.Pl.poincareLelong PositivityTheory.ResPlug.FromRes.resK

theorem doubling_method : GlobalTheory.Published.DoublingMethodLocalZetaIntegrals :=
  ResidueKilled.dm_of_two GlobalTheory.RapidDecay.cuspRapidDecay PositivityTheory.RgEis.Sp.Hd.siegelEisensteinContinuation trivial

theorem flath_factorisation_of_literature : GlobalTheory.Published.FlathFactorisation :=
  GlobalTheory.flathFactorisation_of_tensorProduct CompanionTheory.Rg.Fl.B.flathTensorProduct CompanionTheory.Rg.Fl.B.unitaryIrreducibleAdmissible

theorem cusp_u_of_literature : _root_.UpperTheory.GalS.CuspUAlt :=
  (_root_.UpperTheory.GalS.bridgeStar_alt gelfand_kazhdan_dual_of_literature).2 pair_u_of_literature

theorem grothendieck_deformation_of_literature : GlobalTheory.Published.GrothendieckDeformation :=
  GlobalTheory.Published.grothendieckDeformation_of_lifting GlobalTheory.abelianDeRham GlobalTheory.abelianScheme_hom_lifting_nilpotent_dividedPowers

theorem grothendieck_messing_of_literature : GlobalTheory.Published.GrothendieckMessing :=
  GlobalTheory.Published.GrothendieckDeformation.grothendieckMessing grothendieck_deformation_of_literature

theorem hecke_l_adic_character_crystalline_of_literature : GlobalTheory.Published.HeckeLAdicCharacterCrystalline :=
  _root_.GlobalTheory.Published.CharCrysModel.of_hypotheses_m_alt UpperTheory.Lit.heckeLAdicCharacterDeRham GlobalTheory.deRham_potentiallySemistable algebraic_character_wd_of_literature local_langlands_gl_recT_exists_of_literature

theorem hecke_l_adic_character_above_of_literature : GlobalTheory.Published.HeckeLAdicCharacterAbove :=
  GlobalTheory.HeckeAboveBridge.heckeLAdicCharacterAbove_of_potSemistable UpperTheory.Lit.heckeLAdicCharacterDeRham hecke_l_adic_character_crystalline_of_literature GlobalTheory.deRham_potentiallySemistable

theorem hecke_l_adic_parameter_above_of_literature : _root_.GlobalTheory.Published.HeckeLAdicParameterAboveAlt :=
  (_root_.GlobalTheory.heckeLAdicParameterAbove_of_algebraicCharacterWD_alt algebraic_character_wd_of_literature)

theorem kawamata_viehweg_of_literature : GlobalTheory.Published.KawamataViehweg :=
  GlobalTheory.KVFromPair.kawamataViehweg_of_nadelVanishingPair (GlobalTheory.nefNumerics_outright) (And.left (NadelVanishingSeparation.NSI.nadelVanishingAndNonKltDivisor))

theorem carU_local_global_of_literature : _root_.UpperTheory.GalS.CarUAlt :=
  (_root_.UpperTheory.GalS.ofDual_star_alt (PositivityTheory.PRW.GKD.gelfandKazhdanDual_of_multiplicityOne PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity PositivityTheory.jumpWindows.cuspidalMultiplicityOne GlobalTheory.CompanionTheory.CuspFinGL.cuspFormsBoundedGL) UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter)

theorem carU_above_l_of_literature : _root_.UpperTheory.GalS.CarUAlt :=
  (_root_.UpperTheory.GalS.carU_of_finite_gl_recT CuspFormAutomorphicBounds.automorphicFormsFiniteGL local_langlands_gl_recT_exists_of_literature carU_local_global_of_literature)

theorem square_integrable_segment_of_literature : GlobalTheory.Published.SquareIntegrableSegment :=
  PositivityTheory.Prw.squareIntegrableSegment_of ess_square_integrable_segments_of_literature

theorem totally_disjoint_product_irreducible_of_literature : GlobalTheory.Published.TotallyDisjointProductIrreducible :=
  PositivityTheory.SlGl.totallyDisjointProductIrreducible_of_parts (GlobalTheory.geometricLemma_of_filtration PositivityTheory.Prw.bernsteinZelevinskyFiniteness_holds PositivityTheory.Geo.geometricLemmaFiltration) (PositivityTheory.RgGu.segmentRepresentation) (PositivityTheory.Groth.grothendieckRingPolynomial_of_seg (PositivityTheory.RgGu.segmentRepresentation))

theorem unlinked_product_irreducible_of_literature : GlobalTheory.Published.UnlinkedProductIrreducible :=
  (GlobalTheory.TotDisjUnlinked.main totally_disjoint_product_irreducible_of_literature)

theorem vol_ge_of_literature : GlobalTheory.Published.VolGe :=
  GlobalTheory.VolBr.volGe_of_hilbertSamuel arith_hilbert_samuel_of_literature ar_calc_of_literature GlobalTheory.nefNumerics_outright

theorem vol_nef_of_literature : GlobalTheory.Published.VolNef :=
  GlobalTheory.Published.ArithHilbertSamuel.volNef arith_hilbert_samuel_of_literature

theorem greenberg_wiles_of_literature : ReciprocityTheory.Gal.GreenbergWiles :=
  GlobalTheory.CompanionTheory.GreenbergWiles.Assembly.greenbergWiles_of_poitouTate PositivityTheory.Lit1.PTN.poitouTateNormalised_holds PositivityTheory.Lit1.GEN.globalEulerChar_full GlobalTheory.CompanionTheory.Hypotheses₂.localTateDuality GlobalTheory.CompanionTheory.Hypotheses₂.LocalEuler.localEulerChar_holds GlobalTheory.CompanionTheory.Hypotheses₂.localFiniteness

theorem literature_local : _root_.GlobalTheory.Mem.LiteralAutomorphy.LocalRepresentationTheoryHypothesesAlt where
  bz := PositivityTheory.Prw.bernsteinZelevinskyFiniteness_holds
  bern := PositivityTheory.RgUd.All.bernsteinUnitaryProductIrreducible
  geo := GlobalTheory.CompanionTheory.GeoLink.geometricLemma
  zel := zelevinsky_polynomial_ring_of_literature
  disj := totally_disjoint_product_irreducible_of_literature
  mp := PositivityTheory.Prw.moyPrasadJacquetIso_holds
  temp := tempered_product_of_square_integrable_of_literature
  seg := ess_square_integrable_segments_of_literature
  sq := square_integrable_segment_of_literature
  gen := ((GlobalTheory.RgGu.genericUnlinkedGL_of_segRep2 (PositivityTheory.RgGu.segmentRepresentation)))
  multi := langlands_multisegments_of_literature
  exh := langlands_exhaustion_gl_of_literature
  cos := standard_cosocle_gl_of_literature
  llc := UpperTheory.Zero.LLC.recTExists
  conv := DiscreteGroups.sglob.LConv.localConverseGL
  dzi := depth_zero_induction_of_literature
  brauer := GlobalTheory.BrauerZero.brauerDegreeZero
  chev := GlobalTheory.Published.chevalleyUnits'
  green := PositivityTheory.Stage1.PM.greenRegularCharacters

theorem literature_automorphy : _root_.GlobalTheory.Mem.LiteralAutomorphy.GlobalAutomorphicGaloisHypotheses' where
  decay := GlobalTheory.RapidDecay.cuspRapidDecay
  hc := PositivityTheory.RgHf.harishChandraFinite
  fin := CuspFormAutomorphicBounds.automorphicFormsFiniteGL
  js := PositivityTheory.AdelicQuotientData.jacquetShalika
  cusp := RfCs.cuspidalSpectrumGL
  bc := UpperTheory.BaseChangeIdentities.baseChangeN
  gk := gelfand_kazhdan_dual_of_literature
  gal := pair_u_of_literature
  car := UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter
  pur := PositivityTheory.Lit1.ClozelPurity.clozelPurity
  coh := PositivityTheory.Rg.Cz.clozelCohomological
  art := GlobalTheory.globalArtinReciprocity_holds
  ray := PositivityTheory.Stage1.PM.rayClassFieldSt
  chA := hecke_l_adic_character_above_of_literature
  chW := algebraic_character_wd_of_literature
  berger := GlobalTheory.deRham_potentiallySemistable

theorem literature_cohomology : GlobalTheory.Mem.LiteralAutomorphy.LitCoh where
  pt := PositivityTheory.Lit1.PTN.poitouTateNormalised_holds
  lf := GlobalTheory.CompanionTheory.Hypotheses₂.localFiniteness
  lt := GlobalTheory.CompanionTheory.Hypotheses₂.localTateDuality
  le := GlobalTheory.CompanionTheory.Hypotheses₂.LocalEuler.localEulerChar_holds
  gf := PositivityTheory.Lit1.GF.globalFiniteness
  ge := PositivityTheory.Lit1.GEN.globalEulerChar_full
  uo := GlobalTheory.CompanionTheory.Hypotheses₂.unramifiedOrthogonality
  gw := greenberg_wiles_of_literature
  lfK := CompanionTheory.LocalTateOrthogonality.Gcoh.top_locfin
  ltK := CompanionTheory.LocalTateOrthogonality.Gcoh.top_tate
  leK := CompanionTheory.LocalTateOrthogonality.Gcoh.top_euler
  bk := GlobalTheory.CompanionTheory.Hypotheses₂.BK.blochKatoLocal

theorem literature_nonexistence : _root_.GlobalTheory.Mem.LiteralAutomorphy.NonEndoscopicHypothesesAlt where
  loc := literature_local
  aut := literature_automorphy
  coh := literature_cohomology
  join := join_out_of_literature
  fe := GlobalTheory.CompanionTheory.HeckeFE.heckeTateFunctionalEquation

theorem published_results_analytic : GlobalTheory.NRows.GeometricGaloisRepCompatibility where
  weil := GlobalTheory.weilRepresentationUnitaryPair
  ds := CompanionTheory.RgDs.B.discreteSeriesExists
  ana := GlobalTheory.CompanionTheory.Hypotheses₂.harishChandra_analyticity_density
  dsc := CompanionTheory.RgExh.discreteSeriesClassification
  trc := cusp_trace_class_of_literature
  dm := PositivityTheory.DM.dixmierMalliavinFactorisation_holds
  flath := flath_factorisation_of_literature
  sw := UpperTheory.Lit.Sw47.weilUnitary
  dbl := doubling_method
  udbl := GlobalTheory.UnramDoublingProof.unramifiedDoublingGL
  hl := GlobalTheory.Published.HeckeLPartialContinuation_holds
  ht := GlobalTheory.HtCardProof.htCard

theorem published_results_local : GlobalTheory.NLink.Hypotheses₂ where
  font := GlobalTheory.MemLoc.fontaineBcris
  artin := GlobalTheory.globalArtinReciprocity_holds
  bk := GlobalTheory.CompanionTheory.Hypotheses₂.BK.blochKatoLocal
  tate := CompanionTheory.LocalTateOrthogonality.Gcoh.top_tate
  euler := CompanionTheory.LocalTateOrthogonality.Gcoh.top_euler
  fin := CompanionTheory.LocalTateOrthogonality.Gcoh.top_locfin
  bs := GlobalTheory.BSP.bhattScholzeIntegral

theorem published_results_eigen : _root_.GlobalTheory.Fc.S0.UnitaryGroupThirdPlaceHypotheses where
  clozelCohomological := PositivityTheory.Rg.Cz.clozelCohomological
  greenCuspidal := PositivityTheory.GreenCharacters.greenCuspidal
  heckeLAdicCharacter := PositivityTheory.Stage1.PM.heckeLAdicCharacter
  chebotarevDegreeOne := GlobalTheory.Published.chebotarevDegreeOne'
  galoisRepOfPolarizedCuspidal := cusp_u_of_literature
  baseChangeDefiniteUnitary := ((UpperTheory.BaseChangeIdentities.definiteN_of UpperTheory.BaseChangeIdentities.baseChangeN))
  bhattScholzeCrystallineLattices := ((GlobalTheory.bhattScholze_coeff GlobalTheory.BSP.bhattScholzeIntegral))
  heckeLAdicCharacterAbove := hecke_l_adic_character_above_of_literature
  cuspRapidDecay := GlobalTheory.RapidDecay.cuspRapidDecay
  weilSiegelFormulaUnitary := UpperTheory.Lit.Sw47.weilUnitary
  siegelWeilUnitaryConvergent := UpperTheory.Lit.Sw47.convergent
  doublingMethod := doubling_method
  unramifiedDoublingGL := GlobalTheory.UnramDoublingProof.unramifiedDoublingGL
  bernsteinZelevinskyFiniteness := PositivityTheory.Prw.bernsteinZelevinskyFiniteness_holds
  formalDegreeCompactDual := PositivityTheory.RgFd.B.formalDegreeCompactDual
  bernsteinUnitaryProductIrreducible := PositivityTheory.RgUd.All.bernsteinUnitaryProductIrreducible
  geometricLemmaFiltration := GlobalTheory.geometricLemmaFiltration_holds
  unlinkedProductIrreducible := unlinked_product_irreducible_of_literature
  depthZeroJacquetInjective := GlobalTheory.DepthZeroJac.depthZeroJacquetInjective
  jacquetShalika := PositivityTheory.AdelicQuotientData.jacquetShalika
  automorphicFormsFiniteGL := CuspFormAutomorphicBounds.automorphicFormsFiniteGL
  localGlobalAboveL := carU_above_l_of_literature
  regularAlgebraicPurity := ((GlobalTheory.regularAlgebraicPurity_of_clozel PositivityTheory.Lit1.ClozelPurity.clozelPurity PositivityTheory.Rg.Cz.clozelCohomological))
  globalArtinReciprocity := GlobalTheory.globalArtinReciprocity_holds
  heckeLAdicParameterAbove := hecke_l_adic_parameter_above_of_literature
  deRhamPotSemistable := GlobalTheory.deRham_potentiallySemistable
  harishChandraFinite := PositivityTheory.RgHf.harishChandraFinite
  greenRegularCharacters := PositivityTheory.Stage1.PM.greenRegularCharacters
  zelevinskyPolynomialRing := zelevinsky_polynomial_ring_of_literature
  rayClassFieldSt := PositivityTheory.Stage1.PM.rayClassFieldSt
  rayCharacterArtin := ((GlobalTheory.Published.GlobalArtinReciprocity.rayCharacterArtin GlobalTheory.globalArtinReciprocity_holds))
  genericUnitaryDualGL := PositivityTheory.Gud.Fin.genericUnitaryDualGL_holds
  standardCosocleGL := standard_cosocle_gl_of_literature
  cheb := GlobalTheory.Published.cheb_holds
  discreteSeriesCover := CompanionTheory.RgExh.discreteSeriesCover
  harishChandraModules := GlobalTheory.HcPort.print_harishChandraModules
  casselmanWallach := PositivityTheory.CWB.casselmanWallach
  weilRepresentationUnitaryPair := GlobalTheory.weilRepresentationUnitaryPair
  discreteSeriesExists := CompanionTheory.RgDs.B.discreteSeriesExists
  discreteSeriesClassification := CompanionTheory.RgExh.discreteSeriesClassification
  strongApproxSU := GlobalTheory.StrongApproxSUProof.strongApproxSU
  siegelWeilUnitaryConvergent2 := GlobalTheory.CompanionTheory.SW.siegelWeilUnitaryConvergent
  harishChandraAnalyticity := GlobalTheory.CompanionTheory.Hypotheses₂.harishChandra_analyticity_density
  cuspTraceClass := cusp_trace_class_of_literature
  dixmierMalliavinFactorisation := PositivityTheory.DM.dixmierMalliavinFactorisation_holds
  flathFactorisation := flath_factorisation_of_literature
  cMCurveGoodOutsidePrimeSt := GlobalTheory.Published.cmCurveGoodOutsidePrime
  weberRayFieldSt := PositivityTheory.Prw.weberRayFieldSt_holds
  discreteSeriesCoverExists := CompanionTheory.RgDs.B.discreteSeriesCoverExists
  siegelWeilUnitarySchrodinger := PositivityTheory.SiegelWeilCoefficients.field
  siegelEisensteinContinuation := PositivityTheory.RgEis.Sp.Hd.siegelEisensteinContinuation
  siegelEisensteinSimplePole := trivial
  schurOrthogonalitySquareIntegrable := GlobalTheory.Published.schurOrthogonalitySquareIntegrable'
  litN := literature_nonexistence
  toHypothesesX := published_results_analytic
  nLink := published_results_local
  depthZeroSupport' := GlobalTheory.SmGL.depthZeroSupport
  localFiniteness := GlobalTheory.CompanionTheory.Hypotheses₂.localFiniteness
  localTateDuality := GlobalTheory.CompanionTheory.Hypotheses₂.localTateDuality
  localEulerChar := GlobalTheory.CompanionTheory.Hypotheses₂.LocalEuler.localEulerChar_holds

theorem published_results_arithmetic : GlobalTheory.CovTop.PublishedHodgeBundleTheorems where
  p1 := GlobalTheory.toroidalCompactification_holds
  p2 := vol_ge_of_literature
  p3 := vol_nef_of_literature
  p4 := ar_calc_of_literature
  p5 := GlobalTheory.abelianDeRham
  p8 := PositivityTheory.Stage1.PM.rayClassFieldSt
  p12 := GlobalTheory.SS.semistableReductionSt
  p13 := GlobalTheory.StrongApproxSUProof.strongApproxSU
  p14 := ((GlobalTheory.GreenSeries.green_series PositivityTheory.GreenCharacters.greenCuspidal))
  p16 := GlobalTheory.GoodMetric.goodChernWeil
  p19 := (((GlobalTheory.QNorm.landherr_and_landherrSt).2))
  p20 := GlobalTheory.QNorm.hasseNormSt
  p22 := GlobalTheory.semiAbelianHomExtension_holds
  p23 := GlobalTheory.Alc.inducedSimpleLowestAlcove
  p25 := GlobalTheory.AbLaw.principalPolarisation_unique_section
  p26 := GlobalTheory.abMulN_holds
  q1 := grothendieck_messing_of_literature
  q4 := UpperTheory.Lit.prismaticDieudonneHodge
  q6 := kawamata_viehweg_of_literature
  q7 := GlobalTheory.nefNumerics_outright
  q8 := GlobalTheory.l2ExtensionLogCanonical'
  q9 := arith_hilbert_samuel_of_literature
  q10 := GlobalTheory.Published.chowFormExists_holds
  q11 := cycle_heights_of_literature
  q13 := GlobalTheory.Published.serreHolomorphicSections_holds
  q15 := NadelVanishingSeparation.NSI.nadelVanishingAndNonKltDivisor
  q16 := PositivityTheory.ResPlug.WeightsCompactStabilizer.principalisation_closed
  q18 := GlobalTheory.formalAlgebraisation

theorem principal_archived_covolume : GlobalTheory.CovTop.CovolumeBoundOfX := by
  exact SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt
    PositivityTheory.Resplug.ResolutionBlowup.resolutionCharZero PositivityTheory.ResPlug.WeightsCompactStabilizer.principalisationCharZero_closed
    PositivityTheory.Tls2.Pl.poincareLelongInv PositivityTheory.Pf1.HilbertSamuelMoriwaki.hsUse_outright
    PositivityTheory.Pf1.HilbertSamuelMoriwaki.moriwakiBig_outright UpperTheory.Lit.farguesExact
    (PositivityTheory.HtPt.Narrow.zarhin GlobalTheory.dualAbelianScheme) PositivityTheory.Tls2.Nef.nefRR GlobalTheory.siegelToroidalIntegral_holds
    GlobalTheory.TorKSField.toroidalForFanKS GlobalTheory.Nef.semiAbelianLieSeminegative
    NadelVanishingSeparation.NSI.pointSeparationPair ar_degree_of_literature published_results_arithmetic
    grothendieck_deformation_of_literature

end RiemannGaussian.AlpogeWindow.ArchivedInputs

namespace RiemannGaussian.AlpogeWindow

open GlobalTheory.Mem.LiteralAutomorphy

private theorem characterWindows : UpperTheory.Top.VWin := by
  let loc : LitLocAlt := { ArchivedInputs.literature_local with }
  let aut : LiteratureAutomorphyHypothesis :=
    { ArchivedInputs.literature_automorphy with
      bc := UpperTheory.BaseChangeIdentities.baseChangeN
      gal := UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter }
  let cm : LiteratureCMHypothesis := {
    gm := ArchivedInputs.grothendieck_deformation_of_literature
    dr := GlobalTheory.abelianDeRham
    dual := GlobalTheory.abelianDualCrystal_of_dual_of_smoothLift GlobalTheory.dualAbelianScheme
      GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations
    per := GlobalTheory.PeriodFamily.periodComparison_holds
    gmp := GlobalTheory.PeriodFamily.gaussManinPeriods_holds
    st := UpperTheory.Lit.serreTateGoodReduction
    cm := PositivityTheory.Prw.ellipticMainTheoremCM_holds
    hj := GlobalTheory.Laid.hcfj_holds
    dri := ArchivedInputs.siegel_klingen_deligne_ribet_of_literature
    pz := PositivityTheory.Prw.partialZetaFunctionalEquation_holds
    fe := GlobalTheory.CompanionTheory.HeckeFE.heckeTateFunctionalEquation }
  exact UpperTheory.V.v_window_of_literal_automorphy_n
    ⟨loc, aut, ArchivedInputs.literature_cohomology, cm⟩

end RiemannGaussian.AlpogeWindow

open RiemannGaussian.AlpogeWindow in
theorem LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf := by
  let l := UpperTheory.Zero.LLC.recTExists
  obtain ⟨hA, hM⟩ := PositivityTheory.ThKR.theoremK_head2 PositivityTheory.RgEis.Hd.eisBL
    PositivityTheory.SiegelWeilFormula.Fin.siegelWeilStd
  exact UpperTheory.Lit.every_character_of_theta_integrals_local_matching
    ArchivedInputs.published_results_eigen archive_local_theta_inputs hA hM
    ArchivedInputs.principal_archived_covolume l characterWindows

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
