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

namespace RHReduction

set_option synthInstance.maxHeartbeats 200000

theorem localThetaInputs : GlobalTheory.FunPr.ThetaLocalInputs := by
  have doubling := ResidueKilled.dm_of_two GlobalTheory.RapidDecay.cuspRapidDecay
    PositivityTheory.RgEis.Sp.Hd.siegelEisensteinContinuation trivial
  exact {
    greenSeriesSt := GlobalTheory.GreenSeries.green_series PositivityTheory.GreenCharacters.greenCuspidal
    linnik := UpperTheory.Lit.linnik
    complexMultiplicationJSt := GlobalTheory.CompanionTheory.Published.complexMultiplicationJ
    cuspidalMirabolic := CompanionTheory.Mirab.cuspidalMirabolic
    weylBranching := GlobalTheory.Published.weylBranching_holds
    bernsteinUnitaryProductIrreducible := PositivityTheory.RgUd.All.bernsteinUnitaryProductIrreducible
    zelevinskyPolynomialRing := UpperTheory.Zero.LLC.Pr.zel
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

theorem siegelKlingenDeligneRibet : GlobalTheory.Published.SiegelKlingenDeligneRibet :=
  GlobalTheory.siegelKlingenDeligneRibet_of_both PositivityTheory.Prw.siegelKlingen_holds PositivityTheory.PfDRL.deligneRibet

theorem joinOut : GlobalTheory.Mem.LiteralAutomorphy.JoinOut :=
  GlobalTheory.JoinFun.joinOut_of_five PositivityTheory.Prw.ellipticMainTheoremCM_holds GlobalTheory.Laid.hcfj_holds siegelKlingenDeligneRibet
    PositivityTheory.Prw.partialZetaFunctionalEquation_holds GlobalTheory.CompanionTheory.HeckeFE.heckeTateFunctionalEquation

theorem arakelovCalculus : GlobalTheory.Published.ArCalc :=
  GlobalTheory.ArithmeticHeightTower.ArakelovDirectHeights.arCalc_direct PositivityTheory.Tls2.Pl.poincareLelong PositivityTheory.ResPlug.FromRes.resK

theorem cycleHeights : GlobalTheory.Published.CycleHeights :=
  GlobalTheory.ArithmeticHeightTower.ArakelovDirectHeights.cycleHeights_direct PositivityTheory.Tls2.Pl.poincareLelong PositivityTheory.ResPlug.FromRes.resK

theorem arakelovDegree : GlobalTheory.Published.ArDegree :=
  GlobalTheory.Published.arDegree_of_heightProjection (GlobalTheory.Published.CycleHeights.heightProjection cycleHeights)
    GlobalTheory.ChernDegree.chernDegreeComplex

theorem arithmeticHilbertSamuel : GlobalTheory.Published.ArithHilbertSamuel :=
  GlobalTheory.arithHilbertSamuel_of_principalisation PositivityTheory.ResPlug.WeightsCompactStabilizer.principalisation_closed

theorem squareIntegrableSegments : GlobalTheory.Published.EssSquareIntegrableSegments :=
  PositivityTheory.Exh.essSquareIntegrableSegments_of_seg PositivityTheory.RgGu.segmentRepresentation

theorem polarizedPair : _root_.UpperTheory.GalS.PairUAlt :=
  _root_.UpperTheory.GalS.field_of_starFull_alt UpperTheory.Zero.LLC.recTExists DiscreteGroups.sglob.LConv.localConverseGL
    UpperTheory.Zero.LLC.Pr.exh UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter

theorem depthZeroInduction : GlobalTheory.Published.DepthZeroInduction :=
  GlobalTheory.DepthZeroPass.depthZeroInduction GlobalTheory.CompanionTheory.GeoLink.geometricLemma
    PositivityTheory.Prw.bernsteinZelevinskyFiniteness_holds UpperTheory.Zero.LLC.Pr.zel

theorem temperedProduct : GlobalTheory.Published.TemperedProductOfSquareIntegrable :=
  UpperTheory.Lit.Cas.temperedProduct GlobalTheory.CompanionTheory.GeoLink.geometricLemma
    PositivityTheory.Prw.bernsteinZelevinskyFiniteness_holds PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
    PositivityTheory.Tls2.BZGL.standardFunctorsFiniteLength_top UpperTheory.Zero.LLC.Pr.exh UpperTheory.Zero.LLC.Pr.cos
    UpperTheory.Zero.LLC.Pr.multi squareIntegrableSegments

theorem kawamataViehweg : GlobalTheory.Published.KawamataViehweg :=
  GlobalTheory.KVFromPair.kawamataViehweg_of_nadelVanishingPair GlobalTheory.nefNumerics_outright (And.left
    NadelVanishingSeparation.NSI.nadelVanishingAndNonKltDivisor)

theorem localGlobalAbovePrime : _root_.UpperTheory.GalS.CarUAlt :=
  UpperTheory.GalS.ofDual_star_alt UpperTheory.Gal.AbelianGaloisNormality.gk_holds UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter

theorem disjointProductIrreducible : GlobalTheory.Published.TotallyDisjointProductIrreducible :=
  PositivityTheory.SlGl.totallyDisjointProductIrreducible_of_parts GlobalTheory.CompanionTheory.GeoLink.geometricLemma
    PositivityTheory.RgGu.segmentRepresentation PositivityTheory.Groth.grothendieckRingPolynomial_holds

theorem greenbergWiles : ReciprocityTheory.Gal.GreenbergWiles :=
  GlobalTheory.CompanionTheory.GreenbergWiles.Assembly.greenbergWiles_of_poitouTate PositivityTheory.Lit1.PTN.poitouTateNormalised_holds
    PositivityTheory.Lit1.GEN.globalEulerChar_full GlobalTheory.CompanionTheory.Hypotheses₂.localTateDuality
    GlobalTheory.CompanionTheory.Hypotheses₂.LocalEuler.localEulerChar_holds GlobalTheory.CompanionTheory.Hypotheses₂.localFiniteness

theorem localRepresentationTheory : _root_.GlobalTheory.Mem.LiteralAutomorphy.LocalRepresentationTheoryHypothesesAlt where
  bz := PositivityTheory.Prw.bernsteinZelevinskyFiniteness_holds
  bern := PositivityTheory.RgUd.All.bernsteinUnitaryProductIrreducible
  geo := GlobalTheory.CompanionTheory.GeoLink.geometricLemma
  zel := UpperTheory.Zero.LLC.Pr.zel
  disj := disjointProductIrreducible
  mp := PositivityTheory.Prw.moyPrasadJacquetIso_holds
  temp := temperedProduct
  seg := squareIntegrableSegments
  sq := PositivityTheory.Prw.squareIntegrableSegment_of squareIntegrableSegments
  gen := GlobalTheory.RgGu.genericUnlinkedGL_of_segRep2 PositivityTheory.RgGu.segmentRepresentation
  multi := UpperTheory.Zero.LLC.Pr.multi
  exh := UpperTheory.Zero.LLC.Pr.exh
  cos := UpperTheory.Zero.LLC.Pr.cos
  llc := UpperTheory.Zero.LLC.recTExists
  conv := DiscreteGroups.sglob.LConv.localConverseGL
  dzi := depthZeroInduction
  brauer := GlobalTheory.BrauerZero.brauerDegreeZero
  chev := GlobalTheory.Published.chevalleyUnits'
  green := PositivityTheory.Stage1.PM.greenRegularCharacters

theorem automorphicGalois : _root_.GlobalTheory.Mem.LiteralAutomorphy.GlobalAutomorphicGaloisHypotheses' where
  decay := GlobalTheory.RapidDecay.cuspRapidDecay
  hc := PositivityTheory.RgHf.harishChandraFinite
  fin := CuspFormAutomorphicBounds.automorphicFormsFiniteGL
  js := PositivityTheory.AdelicQuotientData.jacquetShalika
  cusp := RfCs.cuspidalSpectrumGL
  bc := UpperTheory.BaseChangeIdentities.baseChangeN
  gk := UpperTheory.Gal.AbelianGaloisNormality.gk_holds
  gal := polarizedPair
  car := UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter
  pur := PositivityTheory.Lit1.ClozelPurity.clozelPurity
  coh := PositivityTheory.Rg.Cz.clozelCohomological
  art := GlobalTheory.globalArtinReciprocity_holds
  ray := PositivityTheory.Stage1.PM.rayClassFieldSt
  chA := UpperTheory.Gal.Int.Inp.hk
  chW := UpperTheory.Gal.Int.Inp.alg
  berger := GlobalTheory.deRham_potentiallySemistable

theorem globalCohomology : GlobalTheory.Mem.LiteralAutomorphy.LitCoh where
  pt := PositivityTheory.Lit1.PTN.poitouTateNormalised_holds
  lf := GlobalTheory.CompanionTheory.Hypotheses₂.localFiniteness
  lt := GlobalTheory.CompanionTheory.Hypotheses₂.localTateDuality
  le := GlobalTheory.CompanionTheory.Hypotheses₂.LocalEuler.localEulerChar_holds
  gf := PositivityTheory.Lit1.GF.globalFiniteness
  ge := PositivityTheory.Lit1.GEN.globalEulerChar_full
  uo := GlobalTheory.CompanionTheory.Hypotheses₂.unramifiedOrthogonality
  gw := greenbergWiles
  lfK := CompanionTheory.LocalTateOrthogonality.Gcoh.top_locfin
  ltK := CompanionTheory.LocalTateOrthogonality.Gcoh.top_tate
  leK := CompanionTheory.LocalTateOrthogonality.Gcoh.top_euler
  bk := GlobalTheory.CompanionTheory.Hypotheses₂.BK.blochKatoLocal

theorem nonEndoscopicInputs : _root_.GlobalTheory.Mem.LiteralAutomorphy.NonEndoscopicHypothesesAlt where
  loc := localRepresentationTheory
  aut := automorphicGalois
  coh := globalCohomology
  join := joinOut
  fe := GlobalTheory.CompanionTheory.HeckeFE.heckeTateFunctionalEquation

theorem automorphicCompatibility : GlobalTheory.NRows.GeometricGaloisRepCompatibility where
  weil := GlobalTheory.weilRepresentationUnitaryPair
  ds := CompanionTheory.RgDs.B.discreteSeriesExists
  ana := GlobalTheory.CompanionTheory.Hypotheses₂.harishChandra_analyticity_density
  dsc := CompanionTheory.RgExh.discreteSeriesClassification
  trc := localThetaInputs.cuspTraceClass
  dm := PositivityTheory.DM.dixmierMalliavinFactorisation_holds
  flath := localThetaInputs.flathFactorisation
  sw := UpperTheory.Lit.Sw47.weilUnitary
  dbl := localThetaInputs.doublingMethod
  udbl := GlobalTheory.UnramDoublingProof.unramifiedDoublingGL
  hl := GlobalTheory.Published.HeckeLPartialContinuation_holds
  ht := GlobalTheory.HtCardProof.htCard

theorem localCohomology : GlobalTheory.NLink.Hypotheses₂ where
  font := GlobalTheory.MemLoc.fontaineBcris
  artin := GlobalTheory.globalArtinReciprocity_holds
  bk := GlobalTheory.CompanionTheory.Hypotheses₂.BK.blochKatoLocal
  tate := CompanionTheory.LocalTateOrthogonality.Gcoh.top_tate
  euler := CompanionTheory.LocalTateOrthogonality.Gcoh.top_euler
  fin := CompanionTheory.LocalTateOrthogonality.Gcoh.top_locfin
  bs := GlobalTheory.BSP.bhattScholzeIntegral

theorem unitaryGroupInputs : _root_.GlobalTheory.Fc.S0.UnitaryGroupThirdPlaceHypotheses :=
  { localThetaInputs with
    clozelCohomological := PositivityTheory.Rg.Cz.clozelCohomological
    greenCuspidal := PositivityTheory.GreenCharacters.greenCuspidal
    heckeLAdicCharacter := PositivityTheory.Stage1.PM.heckeLAdicCharacter
    chebotarevDegreeOne := GlobalTheory.Published.chebotarevDegreeOne'
    galoisRepOfPolarizedCuspidal := (_root_.UpperTheory.GalS.bridgeStar_alt UpperTheory.Gal.AbelianGaloisNormality.gk_holds).2 polarizedPair
    baseChangeDefiniteUnitary := (UpperTheory.BaseChangeIdentities.definiteN_of UpperTheory.BaseChangeIdentities.baseChangeN)
    bhattScholzeCrystallineLattices := (GlobalTheory.bhattScholze_coeff GlobalTheory.BSP.bhattScholzeIntegral)
    heckeLAdicCharacterAbove := UpperTheory.Gal.Int.Inp.hk
    siegelWeilUnitaryConvergent := UpperTheory.Lit.Sw47.convergent
    geometricLemmaFiltration := GlobalTheory.geometricLemmaFiltration_holds
    unlinkedProductIrreducible := GlobalTheory.TotDisjUnlinked.main disjointProductIrreducible
    depthZeroJacquetInjective := GlobalTheory.DepthZeroJac.depthZeroJacquetInjective
    jacquetShalika := PositivityTheory.AdelicQuotientData.jacquetShalika
    automorphicFormsFiniteGL := CuspFormAutomorphicBounds.automorphicFormsFiniteGL
    localGlobalAboveL := localGlobalAbovePrime
    regularAlgebraicPurity := (GlobalTheory.regularAlgebraicPurity_of_clozel PositivityTheory.Lit1.ClozelPurity.clozelPurity
      PositivityTheory.Rg.Cz.clozelCohomological)
    globalArtinReciprocity := GlobalTheory.globalArtinReciprocity_holds
    heckeLAdicParameterAbove := _root_.GlobalTheory.heckeLAdicParameterAbove_of_algebraicCharacterWD_alt UpperTheory.Gal.Int.Inp.alg
    deRhamPotSemistable := GlobalTheory.deRham_potentiallySemistable
    greenRegularCharacters := PositivityTheory.Stage1.PM.greenRegularCharacters
    rayClassFieldSt := PositivityTheory.Stage1.PM.rayClassFieldSt
    rayCharacterArtin := (GlobalTheory.Published.GlobalArtinReciprocity.rayCharacterArtin GlobalTheory.globalArtinReciprocity_holds)
    genericUnitaryDualGL := PositivityTheory.Gud.Fin.genericUnitaryDualGL_holds
    standardCosocleGL := UpperTheory.Zero.LLC.Pr.cos
    cheb := GlobalTheory.Published.cheb_holds
    discreteSeriesClassification := CompanionTheory.RgExh.discreteSeriesClassification
    siegelWeilUnitaryConvergent2 := GlobalTheory.CompanionTheory.SW.siegelWeilUnitaryConvergent
    harishChandraAnalyticity := GlobalTheory.CompanionTheory.Hypotheses₂.harishChandra_analyticity_density
    cMCurveGoodOutsidePrimeSt := GlobalTheory.Published.cmCurveGoodOutsidePrime
    weberRayFieldSt := PositivityTheory.Prw.weberRayFieldSt_holds
    siegelWeilUnitarySchrodinger := PositivityTheory.SiegelWeilCoefficients.field
    siegelEisensteinContinuation := PositivityTheory.RgEis.Sp.Hd.siegelEisensteinContinuation
    siegelEisensteinSimplePole := trivial
    litN := nonEndoscopicInputs
    toHypothesesX := automorphicCompatibility
    nLink := localCohomology
    depthZeroSupport' := GlobalTheory.SmGL.depthZeroSupport
    localFiniteness := GlobalTheory.CompanionTheory.Hypotheses₂.localFiniteness
    localTateDuality := GlobalTheory.CompanionTheory.Hypotheses₂.localTateDuality
    localEulerChar := GlobalTheory.CompanionTheory.Hypotheses₂.LocalEuler.localEulerChar_holds }

theorem hodgeBundleInputs : GlobalTheory.CovTop.PublishedHodgeBundleTheorems where
  p1 := GlobalTheory.toroidalCompactification_holds
  p2 := GlobalTheory.VolBr.volGe_of_hilbertSamuel arithmeticHilbertSamuel arakelovCalculus GlobalTheory.nefNumerics_outright
  p3 := GlobalTheory.Published.ArithHilbertSamuel.volNef arithmeticHilbertSamuel
  p4 := arakelovCalculus
  p5 := GlobalTheory.abelianDeRham
  p8 := PositivityTheory.Stage1.PM.rayClassFieldSt
  p12 := GlobalTheory.SS.semistableReductionSt
  p13 := GlobalTheory.StrongApproxSUProof.strongApproxSU
  p14 := (GlobalTheory.GreenSeries.green_series PositivityTheory.GreenCharacters.greenCuspidal)
  p16 := GlobalTheory.GoodMetric.goodChernWeil
  p19 := GlobalTheory.QNorm.landherr_and_landherrSt.2
  p20 := GlobalTheory.QNorm.hasseNormSt
  p22 := GlobalTheory.semiAbelianHomExtension_holds
  p23 := GlobalTheory.Alc.inducedSimpleLowestAlcove
  p25 := GlobalTheory.AbLaw.principalPolarisation_unique_section
  p26 := GlobalTheory.abMulN_holds
  q1 := GlobalTheory.Published.GrothendieckDeformation.grothendieckMessing GlobalTheory.HTFirstOrderIso.gd
  q4 := UpperTheory.Lit.prismaticDieudonneHodge
  q6 := kawamataViehweg
  q7 := GlobalTheory.nefNumerics_outright
  q8 := GlobalTheory.l2ExtensionLogCanonical'
  q9 := arithmeticHilbertSamuel
  q10 := GlobalTheory.Published.chowFormExists_holds
  q11 := cycleHeights
  q13 := GlobalTheory.Published.serreHolomorphicSections_holds
  q15 := NadelVanishingSeparation.NSI.nadelVanishingAndNonKltDivisor
  q16 := PositivityTheory.ResPlug.WeightsCompactStabilizer.principalisation_closed
  q18 := GlobalTheory.formalAlgebraisation

theorem covolumeBound : GlobalTheory.CovTop.CovolumeBoundOfX :=
  SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt
    PositivityTheory.Resplug.ResolutionBlowup.resolutionCharZero PositivityTheory.ResPlug.WeightsCompactStabilizer.principalisationCharZero_closed
    PositivityTheory.Tls2.Pl.poincareLelongInv PositivityTheory.Pf1.HilbertSamuelMoriwaki.hsUse_outright
    PositivityTheory.Pf1.HilbertSamuelMoriwaki.moriwakiBig_outright UpperTheory.Lit.farguesExact
    (PositivityTheory.HtPt.Narrow.zarhin GlobalTheory.dualAbelianScheme) PositivityTheory.Tls2.Nef.nefRR GlobalTheory.siegelToroidalIntegral_holds
    GlobalTheory.TorKSField.toroidalForFanKS GlobalTheory.Nef.semiAbelianLieSeminegative
    NadelVanishingSeparation.NSI.pointSeparationPair arakelovDegree hodgeBundleInputs
    GlobalTheory.HTFirstOrderIso.gd

open GlobalTheory.Mem.LiteralAutomorphy

private theorem characterWindows : UpperTheory.Top.VWin := by
  let loc : LitLocAlt := { localRepresentationTheory with }
  let aut : LiteratureAutomorphyHypothesis :=
    { automorphicGalois with
      bc := UpperTheory.BaseChangeIdentities.baseChangeN
      gal := UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter }
  let cm : LiteratureCMHypothesis := {
    gm := GlobalTheory.HTFirstOrderIso.gd
    dr := GlobalTheory.abelianDeRham
    dual := GlobalTheory.abelianDualCrystal_of_dual_of_smoothLift GlobalTheory.dualAbelianScheme
      GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations
    per := GlobalTheory.PeriodFamily.periodComparison_holds
    gmp := GlobalTheory.PeriodFamily.gaussManinPeriods_holds
    st := UpperTheory.Lit.serreTateGoodReduction
    cm := PositivityTheory.Prw.ellipticMainTheoremCM_holds
    hj := GlobalTheory.Laid.hcfj_holds
    dri := siegelKlingenDeligneRibet
    pz := PositivityTheory.Prw.partialZetaFunctionalEquation_holds
    fe := GlobalTheory.CompanionTheory.HeckeFE.heckeTateFunctionalEquation }
  exact UpperTheory.V.v_window_of_literal_automorphy_n
    ⟨loc, aut, globalCohomology, cm⟩

end RHReduction

open RHReduction in
theorem LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf := by
  obtain ⟨hA, hM⟩ := PositivityTheory.ThKR.theoremK_head2 PositivityTheory.RgEis.Hd.eisBL
    PositivityTheory.SiegelWeilFormula.Fin.siegelWeilStd
  exact UpperTheory.Lit.every_character_of_theta_integrals_local_matching
    unitaryGroupInputs localThetaInputs hA hM
    covolumeBound UpperTheory.Zero.LLC.recTExists characterWindows

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
