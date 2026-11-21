/-
Copyright 2026 David Sanftenberg. SPDX-License-Identifier: Apache-2.0
Adapted from the principal-character specialization at d7857c26. This edition
retains the declarations used by the ordinary-RH endpoint and replaces the
analytic deduction with PrincipalWindows. The arithmetic archive is by Levent Alpöge.
-/
import PrincipalWindows
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.LinearAlgebra.Prod
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.ZPow
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantIntegralVanishesIwahori
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JoinOutOfFive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegOfNadelVanishingPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KudlaSplittingSplitUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerOneHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetaplecticRepresentationHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParabolicBlockDecompositionEmbed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdFactorsOfMonic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectionFormulaAndChernDegreeOfHeightProjectio
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianLieSeminegativeBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelKlingenDeligneRibetOfBoth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelToroidalIntegralHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalCompactificationHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolGeOfHilbertSamuel
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowMainEqPOfSiegelWeil
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GenusMassAtTwo
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LitThin
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalEqUnitaryTwist
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsTerAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowRatWOfRowTest
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalComponentTempered
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarySegmentOfCentralUnit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlathFactorisationOfTensorProduct
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WindowBoundOfLiteratureLevel
import Development.AutomorphicArithmetic.CharacterBoxes.ClassSel
import Development.AutomorphicArithmetic.CharacterBoxes.SupplyChi
import Development.AutomorphicArithmetic.CharacterBoxes.ZeroFreeAllOfTopG
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.RowSrc
import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.GlnTemp
import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.RallisDM
import Development.AutomorphicArithmetic.ThetaCorrespondence.GoodReduction.SerreTate
import Development.AutomorphicArithmetic.ThetaCorrespondence.Linnik
import Development.AutomorphicArithmetic.ThetaCorrespondence.PrismaticDieudonne.PrismaticDieudonneHodge
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.EvaluationGridOfJoin
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FunctionalsSeparateOfHoweUnramOfSiegelWeil
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TestVectorAtDatumOfJoin
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AlLocalGlobalAboveLPstlocalGlobalAboveL
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CFinal
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ClosedFamilyAdmissibleTwistLink
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FourierCoefficientFitOfJoin
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Hyps
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkAltAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkBrest
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkIrr
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkROfIsLinked
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedBundlesL3OfOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemberBundlesLargeUnramifiedExponents
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ModularityOfHyps
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OpenAndLinkedOfStrongerExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OpenOrbitOfUnramifiedExponents
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowFunAtGridA
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowHTuCTmin
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SelectionClosedOfWuDecay
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SurjectiveAndLowWeightOfUnramifiedExponents
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopCovolSlim2Use
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WireSel
import Development.AutomorphicArithmetic.ThetaCorrespondence.WeilRepresentation.WeilEx
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GreenbergWilesOfPoitouTate
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BlochKatoLocal
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HeckeTateFunctionalEquation
import Development.AutomorphicSpectrum.PublishedTheorems.PublishedGlobalResults.InvLogIntervalIntegrable
import Development.WeilBound.CoreStatements.AutomorphicKernels.DeligneRibet.NotDvdAbsNorm
import Development.WeilBound.CoreStatements.AutomorphicKernels.DepthZeroCuspidal.IsArtinCond
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalLanglandsExistence.ContinuousOfIsSmoothChar
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalLanglandsExistence.ExistsPowEqOneOfValuationEqOne
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalLanglandsExistence.InstField
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalLanglandsExistence.IsTateMeasMulHighlyRamified
import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.MoriwakiBigTheorem.Outright
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
import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.CechDescentTests.SubquotientNontrivial
import Development.WeilBound.ThetaLifts.Reductions.FiniteClosure.TheoremKOfMod
import Formalism.LocalToGlobal.NormalizedHeckeFactors.BaseRowsEqRecordRows
import Formalism.LocalToGlobal.NormalizedHeckeFactors.EtaClosed
import GroundTheory.HeightsAndTheta.Theta.FiniteGL.Mirabolic

namespace RiemannGaussian.AlpogeWindow

open Formalism.BasicNotions Formalism.MainNotions UpperTheory.Top

def BoundedLiftRank {ε : ℝ} (Fm : FamP ε) : Prop :=
  ∃ k : ℕ, ∃ a : ℝ, ∀ x ≥ a, ∀ (i : Fm.Ix x) j, j ∈ SizeData₂.lifts (Fm.D x i) →
    (Fm.L x i).dZ0 j ≤ k * (Fm.D x i).what₂.D0

theorem boundedLiftRank_of_source {ε : ℝ} {Fm : FamP ε} (k : ℕ) (a : ℝ)
    (h : ∀ x ≥ a, ∀ (i : Fm.Ix x) j, j ∈ SizeData₂.lifts (Fm.D x i) →
      Module.finrank ℂ ((Fm.D x i).what₂.Mj j) ≤ k * (Fm.D x i).what₂.D0) :
    BoundedLiftRank Fm := by
  refine ⟨k, a, fun x hx i j hj => ?_⟩
  exact (LinearMap.finrank_range_le ((Fm.D x i).what₂.thetaT (Fm.D x i).what₂.mu0 j)).trans
    (h x hx i j hj)

private theorem divinN_at_of_rank_le {D : D7} (L : SizeData₂ D) (j k : ℕ) (C : ℝ)
    (hN : LinkN_at L j C) (hs : Summable (vvTerm D)) (hb : ∑' l, vvTerm D l ≤ L.sc.b)
    (hr : L.dZ0 j ≤ k * D.what₂.D0) (hlog : Real.log L.sc.x ^ 2 ≤ L.sc.x ^ L.sc.eps) :
    DIVinN_at L j (k * (|C| + 1)) := by
  let y := L.sc.x ^ L.sc.eps
  have hx : 0 < L.sc.x := one_pos.trans L.sc.one_lt_alt
  have hy : 1 ≤ y := Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le
  have hy0 : 0 ≤ y := zero_le_one.trans hy
  have hf : (1 : ℝ) ≤ D.R.f := by
    have : 0 < D.R.f := by unfold Ranks.f Ranks.n; positivity
    exact_mod_cast this
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (Nat.le_trans (by decide : 1 ≤ 2) D.R.two_le_m)
  have hb0 : 0 ≤ L.sc.b := (Real.exp_pos _).le
  have hNc : 0 ≤ L.Nc := by
    simp only [SizeData₂.Nc, budgetNc, rankBudget, bSize]
    positivity
  have hB : L.B0 = (D.R.f : ℝ) * D.R.m * L.sc.b * y := rfl
  have hbB : L.sc.b ≤ L.B0 := by
    rw [hB]
    have hfm := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hf hm) hy
    nlinarith only [mul_nonneg (sub_nonneg.mpr hfm) hb0]
  have hB0 : 0 ≤ L.B0 := hb0.trans hbB
  have hP : (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L ^ 2 = y * L.B0 := by
    change (D.R.f : ℝ) * D.R.m * L.sc.b * y ^ 2 = y * L.B0
    rw [hB]
    ring
  have hsum : y * L.B0 + Real.log L.sc.x ^ 2 * L.Nc ≤ y * (L.B0 + L.Nc) := by
    rw [mul_add]
    exact add_le_add_right (mul_le_mul_of_nonneg_right hlog hNc) _
  have hscaled := mul_le_mul (le_abs_self C) hsum (by positivity) (abs_nonneg C)
  have hrest : ∑' l, vvTerm D l ≤ y * (L.B0 + L.Nc) :=
    hb.trans (hbB.trans ((le_add_of_nonneg_right hNc).trans
      (le_mul_of_one_le_left (add_nonneg hB0 hNc) hy)))
  have hr' : (L.dZ0 j : ℝ) ≤ (k : ℝ) * D.what₂.D0 := by exact_mod_cast hr
  unfold DIVinN_at
  calc
    etaSum L j ≤ _ := hN hs
    _ ≤ (L.dZ0 j : ℝ) * ((|C| + 1) * y * (L.B0 + L.Nc)) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      rw [hP]
      linarith only [hscaled, hrest]
    _ ≤ ((k : ℝ) * D.what₂.D0) * ((|C| + 1) * y * (L.B0 + L.Nc)) :=
      mul_le_mul_of_nonneg_right hr' (by positivity)
    _ = _ := by dsimp [y]; ring

theorem divinN_of_bounded_rank {ε : ℝ} (Fm : FamP ε) (hε : 0 < ε)
    (hV : HypV Fm.toFamCore) (hN : LinkN Fm) (hR : BoundedLiftRank Fm) : DIVinN Fm := by
  obtain ⟨a, ha⟩ := hV
  obtain ⟨C, b, hb⟩ := hN
  obtain ⟨k, c, hc⟩ := hR
  obtain ⟨d, hd⟩ := log_sq_le_rpow hε
  refine ⟨k * (|C| + 1), max (max a (max b c)) (max d (Fm.x1 + 1)), fun x hx i j hj => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hx
  obtain ⟨⟨ga, gb, gc⟩, gd, gx⟩ := hx
  obtain ⟨hf, hs, hle⟩ := vvRecord _ _ (ha x ga i)
  have hb1 : 1 ≤ (Fm.L x i).sc.b :=
    Real.one_le_exp (Real.rpow_nonneg (by linarith [(Fm.L x i).sc.one_lt_alt]) _)
  refine divinN_at_of_rank_le _ j k C (hb x gb i hf j hj) hs
    (hle.trans (Real.sqrt_le_self_iff.2 (Or.inr hb1))) (hc x gc i j hj) ?_
  rw [Fm.L_x x i (by linarith), Fm.L_eps x i]
  exact hd x gd

end RiemannGaussian.AlpogeWindow

namespace RiemannGaussian.AlpogeLattice

theorem rational_outputs_fg {R K E V W : Type*} [CommRing R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [Field E] [AddCommGroup V] [Module R V] [Module K V]
    [IsScalarTower R K V] [AddCommGroup W] [Module E W] {σ : K →+* E}
    (emb : V →ₛₗ[σ] W) (hinj : Function.Injective emb) (op : W →ₗ[E] W)
    (A : Submodule R V) (hA : A.FG) :
    ∃ N : Submodule R V, N.FG ∧ ∀ x ∈ A, ∀ y, emb y = op (emb x) → y ∈ N := by
  let graph : Submodule R (V × V) :=
    { carrier := {p | p.1 ∈ A ∧ emb p.2 = op (emb p.1)}
      zero_mem' := ⟨A.zero_mem, by simp⟩
      add_mem' := fun hx hy => ⟨A.add_mem hx.1 hy.1, by
        simpa only [Prod.fst_add, Prod.snd_add, map_add] using congrArg₂ (· + ·) hx.2 hy.2⟩
      smul_mem' := fun r p hp => ⟨A.smul_mem r hp.1, by
        change emb (r • p.2) = op (emb (r • p.1))
        rw [← algebraMap_smul K r p.1, ← algebraMap_smul K r p.2,
          LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, map_smul, hp.2]⟩ }
  let first : graph →ₗ[R] A :=
    ((LinearMap.fst R V V).comp graph.subtype).codRestrict A fun p => p.property.1
  have hfirst : Function.Injective first := by
    intro p q hpq
    have h₁ : p.val.1 = q.val.1 := congrArg Subtype.val hpq
    apply Subtype.ext
    exact Prod.ext h₁ (hinj (p.property.2.trans ((congrArg (fun x => op (emb x)) h₁).trans q.property.2.symm)))
  have : Module.Finite R A := Module.Finite.iff_fg.2 hA
  have : IsNoetherian R graph := isNoetherian_of_injective first hfirst
  let second := (LinearMap.snd R V V).comp graph.subtype
  exact ⟨second.range, Submodule.fg_range second, fun x hx y hxy => ⟨⟨(x,y), hx, hxy⟩, rfl⟩⟩

end RiemannGaussian.AlpogeLattice

namespace RiemannGaussian.AlpogeWindow.Localization

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions

section

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V]

theorem mem_of_locally (M : Submodule (𝓞 K) V) (x : V)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), InLoc v M x) : x ∈ M := by
  let I := M.comap (LinearMap.toSpanSingleton (𝓞 K) V x)
  have htop : I = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal I hne
    obtain ⟨s, hs, hsx⟩ := h ⟨m, hm.isPrime,
      Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField K)⟩
    exact hs (hle (show s ∈ I from hsx))
  have h1 : (1 : 𝓞 K) ∈ I := htop ▸ Submodule.mem_top
  simpa only [one_smul] using (show (1 : 𝓞 K) • x ∈ M from h1)

omit [NumberField K] in

theorem exists_common_mul (M N : Submodule (𝓞 K) V) (hM : M.FG)
    (h : ∀ y ∈ M, ∃ s : 𝓞 K, s ≠ 0 ∧ s • y ∈ N) :
    ∃ c : 𝓞 K, c ≠ 0 ∧ ∀ y ∈ M, c • y ∈ N := by
  classical
  obtain ⟨S, hS⟩ := hM
  choose d hd hmem using fun y : S => h y.val (hS ▸ Submodule.subset_span y.property)
  let c := ∏ y : S, d y
  refine ⟨c, Finset.prod_ne_zero_iff.2 (fun y _ => hd y), ?_⟩
  change M ≤ N.comap (LinearMap.lsmul (𝓞 K) V c)
  rw [← hS, Submodule.span_le]
  intro y hy
  let i : S := ⟨y, hy⟩
  obtain ⟨b, hb⟩ := Finset.dvd_prod_of_mem d (Finset.mem_univ i)
  change c • y ∈ N
  rw [show c = d i * b from hb, mul_comm, mul_smul]
  exact N.smul_mem _ (hmem i)

theorem locLe_zero {w : HeightOneSpectrum (𝓞 K)} {A B : Submodule (𝓞 K) V}
    (h : DV.LocLe w 0 A B) (x : V) (hx : x ∈ A) : InLoc w B x := by
  obtain ⟨s, hs, hsx⟩ := h x hx
  exact ⟨s, hs, by simpa only [pow_zero, Ideal.one_eq_top, Submodule.top_smul] using hsx⟩

variable [Module K V] [IsScalarTower (𝓞 K) K V]

theorem mem_span_of_multiple (M : Submodule (𝓞 K) V) (y : V) (d : 𝓞 K)
    (hd : d ≠ 0) (hy : d • y ∈ M) : y ∈ Submodule.span K (M : Set V) := by
  have h := (Submodule.span K (M : Set V)).smul_mem (algebraMap (𝓞 K) K d)⁻¹
    (Submodule.subset_span hy)
  rwa [← algebraMap_smul K d y, smul_smul, inv_mul_cancel₀
    ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 hd), one_smul] at h

theorem fg_of_clearing {M N : Submodule (𝓞 K) V} (hN : N.FG) (d : 𝓞 K)
    (hd : d ≠ 0) (h : ∀ y ∈ M, d • y ∈ N) : M.FG := by
  let f := LinearMap.lsmul (𝓞 K) V d
  have hinj : Function.Injective f := by
    intro x y hxy
    have h' : (algebraMap (𝓞 K) K d) • x = (algebraMap (𝓞 K) K d) • y := by
      simpa only [algebraMap_smul] using (show d • x = d • y from hxy)
    exact smul_right_injective _ ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 hd) h'
  have hle : M.map f ≤ N := Submodule.map_le_iff_le_comap.mpr h
  have : Module.Finite (𝓞 K) N := Module.Finite.iff_fg.2 hN
  have hfg := (IsNoetherian.noetherian ((M.map f).comap N.subtype)).map N.subtype
  rw [Submodule.map_comap_subtype, inf_eq_right.2 hle] at hfg
  exact Submodule.fg_of_fg_map_injective f hinj hfg

end

theorem exists_ordinary_place (D : D7) (u : D.what₂.Word) :
    ∃ w : D.what₂.places.Pl, D.what₂.places.resChar w ≠ (D.mem u).A.T ∧
      ¬ DV.InertK D (D.what₂.places.resChar w) := by
  have hfree : ∃ p : ℕ, p.Prime ∧ p ≠ (D.mem u).A.T ∧ ¬ DV.InertK D p := by
    by_cases hT : (D.mem u).A.T = 2
    · refine ⟨D.host.q, D.host.hyp.1, by rw [hT]; have := D.host.hyp.2.2.1; omega, ?_⟩
      simp [DV.InertK, Host.cls, primeClass, D.host.q_notMem_small]
    · refine ⟨2, Nat.prime_two, Ne.symm hT, ?_⟩
      simp [DV.InertK, Host.cls, primeClass, D.host.two_mem_small]
  obtain ⟨p, hp, hT, hfree⟩ := hfree
  have := J.span_prime_isMaximal p hp
  obtain ⟨P, hP, hOver⟩ := (inferInstance : Nonempty (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 D.what₂.LL)))
  let v : HeightOneSpectrum (𝓞 D.what₂.LL) :=
    ⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot (by simp [hp.ne_zero] : Ideal.span {(p : ℤ)} ≠ ⊥) P⟩
  let w := D.plEq.symm v
  have hw : D.plEq w = v := D.plEq.apply_symm_apply v
  have hmem := J.resChar_mem D w
  rw [hw] at hmem
  have hcon : ((D.what₂.places.resChar w : ℕ) : ℤ) ∈ Ideal.span {(p : ℤ)} := by
    rw [hOver.over, Ideal.mem_comap]
    simpa using hmem
  have hdvd : p ∣ D.what₂.places.resChar w := by exact_mod_cast Ideal.mem_span_singleton.mp hcon
  have heq := ((Nat.dvd_prime (D.what₂.places.resChar_prime w)).mp hdvd).resolve_left hp.ne_one
  exact ⟨w, heq ▸ hT, heq ▸ hfree⟩

end RiemannGaussian.AlpogeWindow.Localization

namespace RiemannGaussian.AlpogeWindow

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions

open RiemannGaussian.AlpogeWindow.Localization

private theorem inLoc_smul {K V : Type} [Field K] [NumberField K] [AddCommGroup V]
    [Module (𝓞 K) V] {v : HeightOneSpectrum (𝓞 K)} {A : Submodule (𝓞 K) V}
    {y : V} (h : InLoc v A y) (c : 𝓞 K) : InLoc v A (c • y) := by
  obtain ⟨s, hs, hsy⟩ := h
  exact ⟨s, hs, by rw [smul_comm]; exact A.smul_mem c hsy⟩

private theorem level_image_denominator (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) :
    ∃ c : 𝓞 D.what₂.LL, c ≠ 0 ∧ ∀ y, D.nuIn u y ∈ LT.Nlam D u w →
      InLoc (D.plEq w) (DV.MramL D u) (c • y) := by
  let A := ((D.fm u).lat 0).L
  let op := ((((D.mem u).A.T : ℂ) ^ LT.expT D u w) • (LT.Uprod D u 0 w) ^ D.R.m)
  obtain ⟨N, hN, houtput⟩ := AlpogeLattice.rational_outputs_fg ((D.fm u).emb 0)
    ((D.fm u).emb_inj 0) op A ((D.fm u).lat_good 0).2.1
  have hspan : Submodule.span D.what₂.LL (A : Set ((D.fm u).lat 0).V) = ⊤ :=
    ((D.fm u).lat_good 0).2.2
  obtain ⟨c, hc, hclear⟩ := exists_common_mul N A hN fun z _ =>
    Formalism.HN.sizeIneq_exists_mul_mem A z (by rw [hspan]; trivial)
  refine ⟨c, hc, fun y hy => ?_⟩
  obtain ⟨z, hz, he⟩ := hy
  obtain ⟨s, hs, hsz⟩ := D.locSpan u w z hz.1
  have he' : (D.fm u).emb 0 (s • D.nuIn u y) = op ((D.fm u).emb 0 (s • z)) := by
    rw [← algebraMap_smul D.what₂.LL s (D.nuIn u y), ← algebraMap_smul D.what₂.LL s z, LinearMap.map_smulₛₗ,
      LinearMap.map_smulₛₗ, map_smul, he]
  refine ⟨s, hs, ?_⟩
  change (D.nuIn u).restrictScalars (𝓞 D.what₂.LL) (s • (c • y)) ∈ A
  rw [map_smul, map_smul, smul_comm s c]
  exact hclear _ (houtput _ hsz _ he')

private theorem nuLat_fg {D : D7} {L : SizeData₂ D} (hNu : DV.NuDef D L)
    (hT : NuAtTDef D L) (u : D.what₂.Word) : (L.NuLat u).FG := by
  classical
  let p := (D.mem u).A.T
  obtain ⟨S, hS⟩ := J.finite_places_over (K := D.what₂.LL) p (D.mem u).A.T_prime
  choose d hd hloc using level_image_denominator D u
  let c : 𝓞 D.what₂.LL := ∏ v ∈ S, d (D.plEq.symm v)
  have hc : c ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ => hd (D.plEq.symm v)
  apply Localization.fg_of_clearing (D.MramL_fg u) c hc
  intro y hy
  apply mem_of_locally
  intro v
  let w := D.plEq.symm v
  have hw : D.plEq w = v := D.plEq.apply_symm_apply v
  change InLoc v (DV.MramL D u) (c • y)
  rw [← hw]
  by_cases hp : D.what₂.places.resChar w = p
  · have hv : v ∈ S := (hS v).2 (by simpa only [← hp, ← hw] using J.resChar_mem D w)
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun v => d (D.plEq.symm v)) hv
    have hy' : D.nuIn u y ∈ LT.Nlam D u w :=
      (hT u w hp y).1 ⟨1, fun h => (D.plEq w).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h),
        by rwa [one_smul]⟩
    change c = d w * k at hk
    rw [hk, mul_comm, mul_smul]
    exact inLoc_smul (hloc w y hy') k
  · exact inLoc_smul (locLe_zero (hNu.1 u w hp) y hy) c

theorem principal_nu_commens {D : D7} {L : SizeData₂ D} (hNu : DV.NuDef D L)
    (hT : NuAtTDef D L) (u : D.what₂.Word) :
    (L.NuLat u).FG ∧ ∃ c : 𝓞 D.what₂.LL, c ≠ 0 ∧ ∀ y ∈ DV.MramL D u, c • y ∈ L.NuLat u := by
  obtain ⟨w, hw, hfree⟩ := Localization.exists_ordinary_place D u
  refine ⟨nuLat_fg hNu hT u, exists_common_mul _ _ (D.MramL_fg u) fun y hy => ?_⟩
  obtain ⟨s, hs, hsy⟩ := Localization.locLe_zero (hNu.2.1 u w hw (Or.inr hfree)).2 y hy
  exact ⟨s, fun hz => hs (hz ▸ Ideal.zero_mem _), hsy⟩

theorem principal_family_nuFull {ε : ℝ} (Fm : FamP ε) : NuFullF Fm := by
  refine ⟨Fm.x1 + 1, fun x hx i u => ?_⟩
  have hx' : Fm.x1 < x := by linarith
  let D := Fm.D x i
  let L := Fm.L x i
  have hNu := Fm.nuDef x hx' i
  have hdef := Fm.nprimeDef x hx' i u
  change (D.div.Nu u).L = Submodule.span (𝓞 D.what₂.LL) _ at hdef
  obtain ⟨hfg, s, hs, hclear⟩ := principal_nu_commens hNu (Fm.ex x hx' i).lat.atT u
  constructor
  · obtain ⟨d, hd, hI⟩ := (DV.Iu D L u).isFractional
    apply Localization.fg_of_clearing hfg d (nonZeroDivisors.ne_zero hd)
    change (D.div.Nu u).L ≤ (L.NuLat u).comap (LinearMap.lsmul (𝓞 D.what₂.LL) _ d)
    rw [hdef, Submodule.span_le]
    rintro _ ⟨a, ha, y, hy, rfl⟩
    obtain ⟨z, hz⟩ := hI a ha
    change d • (a • y) ∈ L.NuLat u
    rw [← smul_assoc, ← hz, algebraMap_smul]
    exact (L.NuLat u).smul_mem z hy
  · have hI : DV.Iu D L u ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ =>
      zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr (D.plEq v).ne_bot)
    obtain ⟨a, ha, haI⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger hI
    rw [eq_top_iff]
    intro y _
    let A := ((D.fm u).lat 0).L
    have hspan : Submodule.span D.what₂.LL (A : Set ((D.fm u).lat 0).V) = ⊤ :=
      ((D.fm u).lat_good 0).2.2
    obtain ⟨d, hd, hdy⟩ := Formalism.HN.sizeIneq_exists_mul_mem A (D.nuIn u y)
      (by rw [hspan]; trivial)
    have hin : d • y ∈ DV.MramL D u := by
      change (D.nuIn u).restrictScalars (𝓞 D.what₂.LL) (d • y) ∈ A
      rwa [map_smul]
    apply Localization.mem_span_of_multiple _ y (a * (s * d)) (mul_ne_zero ha (mul_ne_zero hs hd))
    rw [hdef, mul_smul, mul_smul, ← algebraMap_smul D.what₂.LL a]
    exact Submodule.subset_span ⟨_, haI, _, hclear _ hin, rfl⟩

noncomputable def levelNormRankSum (D : D7) (u : D.what₂.Word) : ℕ :=
  let A := (D.mem u).A
  ∑ v : A.vT, Module.finrank ℂ (LinearMap.range ((A.Nm v).domRestrict A.Mu0))

theorem ramified_dimension_bound (D : D7) (u : D.what₂.Word) :
    D.duS u ≤ levelNormRankSum D u + (D.mem u).A.du := by
  classical
  let A := (D.mem u).A
  have := A.Mu0_fd
  let f := fun v : A.vT => (A.Nm v).domRestrict A.Mu0
  let F := LinearMap.pi fun v : A.vT => (f v).rangeRestrict
  have : FiniteDimensional ℂ A.Mram := Submodule.finiteDimensional_of_le (show A.Mram ≤ A.Mu0 from inf_le_left)
  let kernelMap : LinearMap.ker F →ₗ[ℂ] A.Mram :=
    (A.Mu0.subtype.comp (LinearMap.ker F).subtype).codRestrict A.Mram fun z => by
      refine ⟨z.val.property, (Submodule.mem_iInf _).2 fun v => ?_⟩
      exact congrArg (fun t : (f v).range => t.val) (congrFun (LinearMap.mem_ker.1 z.property) v)
  have hker : Function.Injective kernelMap := fun _ _ h =>
    Subtype.ext (Subtype.ext (congrArg (fun t : A.Mram => t.val) h))
  have hk := LinearMap.finrank_le_finrank_of_injective hker
  have hr : Module.finrank ℂ (LinearMap.range F) ≤ levelNormRankSum D u := by
    apply (Submodule.finrank_le _).trans_eq
    exact Module.finrank_pi_fintype ℂ
  exact F.finrank_range_add_finrank_ker.symm.le.trans (Nat.add_le_add hr hk)

def LevelPrimeGrowth {ε : ℝ} (Fm : FamP ε) : Prop :=
  ∃ a : ℝ, ∀ x ≥ a, ∀ (i : Fm.Ix x) u, (Fm.L x i).sc.b ≤ (((Fm.D x i).mem u).A.T : ℝ)

theorem levelPrimeGrowth_of_tuGe {ε : ℝ} {Fm : FamP ε}
    (ht : ∃ a : ℝ, ∀ x ≥ a, ∀ i : Fm.Ix x, (Fm.L x i).TuGe) : LevelPrimeGrowth Fm := by
  obtain ⟨a, ha⟩ := ht
  refine ⟨a, fun x hx i u => ?_⟩
  let D := Fm.D x i
  let L := Fm.L x i
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  calc L.sc.b = L.sc.b ^ (1 : ℝ) := (Real.rpow_one _).symm
       _ ≤ L.sc.b ^ ((D.R.m : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le
         (Real.one_le_exp (Real.rpow_nonneg (zero_lt_one.trans L.sc.one_lt_alt).le _)) (by linarith)
       _ ≤ _ := ha x hx i u

private theorem places_to_level_ratio {ε : ℝ} (Fm : FamP ε) (hε : 0 < ε) (ht : LevelPrimeGrowth Fm) :
    ∃ a : ℝ, ∀ x ≥ a, ∀ (i : Fm.Ix x) u,
      (2 : ℝ) * (Fm.D x i).R.f ≤ ((Fm.D x i).mem u).A.T * Real.exp (-(x ^ (ε / 8))) ^ 2 := by
  obtain ⟨a, ha⟩ := ht
  have hg := (tendsto_exp_mul_div_rpow_atTop (3 / ε) (1/2) (by norm_num)).comp (tendsto_rpow_atTop hε)
  obtain ⟨b, hb⟩ := Filter.eventually_atTop.1 (hg.eventually_gt_atTop 4)
  obtain ⟨c, hc⟩ := Filter.eventually_atTop.1 ((tendsto_rpow_atTop (by positivity : 0 < 7*ε/8)).eventually_ge_atTop 4)
  refine ⟨max (max a b) (max c (Fm.x1 + 1)), fun x hx i u => ?_⟩
  let D := Fm.D x i
  let L := Fm.L x i
  have hlate : Fm.x1 < x := by linarith [le_of_max_le_right (le_of_max_le_right hx)]
  have hxL : L.sc.x = x := Fm.L_x x i hlate
  have hεL : L.sc.eps = ε := Fm.L_eps x i
  have hx1 : 1 ≤ x := hxL ▸ L.sc.one_lt_alt.le
  have hxp : 0 < x := zero_lt_one.trans_le hx1
  have hg' := hb x (le_of_max_le_right (le_of_max_le_left hx))
  change 4 < Real.exp (1/2 * x ^ ε) / ((x ^ ε) ^ (3 / ε)) at hg'
  rw [← Real.rpow_mul hxp.le, show ε * (3 / ε) = (3 : ℝ) by field_simp,
    show x ^ (3 : ℝ) = x ^ (3 : ℕ) by norm_cast] at hg'
  have hn : (D.R.n : ℝ) ≤ x ^ (3 : ℕ) := by
    have hn := ((Fm.sizes x hlate i).1).2.trans
      (Real.rpow_le_rpow_of_exponent_le L.sc.one_lt_alt.le (J.th_bounds L).2.2.2.1)
    change (D.R.n : ℝ) ≤ L.sc.x ^ (3 : ℝ) at hn
    rw [hxL] at hn
    exact_mod_cast hn
  have hbT := ha x (le_of_max_le_left (le_of_max_le_left hx)) i u
  change Real.exp (L.sc.x ^ L.sc.eps) ≤ _ at hbT
  rw [hxL, hεL] at hbT
  have h3 := (lt_div_iff₀ (pow_pos hxp 3)).mp hg'
  have hf : (D.R.f : ℝ) = 2 * D.R.n := by simp [Ranks.f]
  have htiny : 4 * x ^ (ε/8) ≤ x ^ ε := by
    have he : x ^ ε = x ^ (ε/8) * x ^ (7*ε/8) := by
      rw [← Real.rpow_add hxp]; congr 1; ring
    rw [he, mul_comm]
    exact mul_le_mul_of_nonneg_left (hc x (le_of_max_le_left (le_of_max_le_right hx)))
      (Real.rpow_nonneg hxp.le _)
  have hexp : Real.exp (1/2 * x ^ ε) ≤ Real.exp (x ^ ε) * Real.exp (-(x ^ (ε/8))) ^ 2 := by
    rw [sq, ← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith only [htiny])
  exact (show 2 * (D.R.f : ℝ) ≤ Real.exp (1/2 * x ^ ε) by linarith only [hf, hn, h3]).trans
    (hexp.trans (mul_le_mul_of_nonneg_right hbT (sq_nonneg _)))

def LocalNormRankBound (D : D7) (u : D.what₂.Word) : Prop :=
  let A := (D.mem u).A
  ∀ v : A.vT, (A.T - 1) * Module.finrank ℂ (LinearMap.range ((A.Nm v).domRestrict A.Mu0)) ≤ D.duS u

private theorem norm_rank_sum_le (D : D7) (u : D.what₂.Word) (h : LocalNormRankBound D u) :
    ((D.mem u).A.T - 1) * levelNormRankSum D u ≤ D.R.f * D.duS u := by
  unfold levelNormRankSum
  rw [Finset.mul_sum]
  exact (Finset.sum_le_sum fun v _ => h v).trans_eq (by simp [ColumnsAtT.card_vT])

theorem principal_ramified_share_of_level_growth {ε : ℝ} (Fm : FamP ε) (hε : 0 < ε)
    (hTu : LevelPrimeGrowth Fm) (h : ∃ a : ℝ, ∀ x ≥ a, ∀ (i : Fm.Ix x) u, LocalNormRankBound (Fm.D x i) u) :
    ∃ a : ℝ, ∀ x ≥ a, ∀ (i : Fm.Ix x) u,
      ((Fm.D x i).duS u : ℝ) - (((Fm.D x i).mem u).A.du : ℝ) ≤
        Real.exp (-(x ^ (ε / 8))) ^ 2 * ((Fm.D x i).duS u : ℝ) := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, hb⟩ := places_to_level_ratio Fm hε hTu
  refine ⟨max a b, fun x hx i u => ?_⟩
  let D := Fm.D x i
  let T := (D.mem u).A.T
  have hT : 2 ≤ T := (D.mem u).A.T_prime.two_le
  have hsum := norm_rank_sum_le D u (ha x (le_of_max_le_left hx) i u)
  have hsum' : T * levelNormRankSum D u ≤ 2 * (D.R.f * D.duS u) := by
    calc _ ≤ (2 * (T - 1)) * levelNormRankSum D u := Nat.mul_le_mul_right _ (by omega)
         _ = 2 * ((T - 1) * levelNormRankSum D u) := Nat.mul_assoc _ _ _
         _ ≤ _ := Nat.mul_le_mul_left _ hsum
  have hr : (T : ℝ) * levelNormRankSum D u ≤ 2 * ((D.R.f : ℝ) * D.duS u) := by exact_mod_cast hsum'
  have hdim : (D.duS u : ℝ) ≤ levelNormRankSum D u + ((D.mem u).A.du : ℝ) := by
    exact_mod_cast ramified_dimension_bound D u
  have hh := mul_le_mul_of_nonneg_right (hb x (le_of_max_le_right hx) i u) (Nat.cast_nonneg (D.duS u))
  have hcancel : (levelNormRankSum D u : ℝ) ≤ Real.exp (-(x ^ (ε/8))) ^ 2 * (D.duS u : ℝ) := by
    apply le_of_mul_le_mul_left _ (by exact_mod_cast (show 0 < T by omega) : (0 : ℝ) < T)
    linarith only [hr, hh]
  linarith only [hdim, hcancel]

end RiemannGaussian.AlpogeWindow

namespace RiemannGaussian.AlpogeWindow

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.FrobeniusOrbits Classical

noncomputable def roundingAt {D : D7} (L : SizeData₂ D) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) : ℝ :=
  2 * SizeData₂.lwP w * Int.fract (DV.ur D w (L.sg u w))

private theorem rounding_nonneg {D : D7} (L : SizeData₂ D) (u : D.what₂.Word) (w : D.what₂.places.Pl) :
    0 ≤ roundingAt L u w :=
  mul_nonneg (mul_nonneg (by norm_num) (J.logWeight_nonneg w)) (Int.fract_nonneg _)

theorem slope_error_eq_rounding {D : D7} (L : SizeData₂ D) (u : D.what₂.Word)
    (hd : DV.NprimeDef D L) (hfg : (D.div.Nu u).L.FG) (hr : 0 < (D.div.Nu u).rank) :
    |(D.div.Nu u).mu - (L.NuH u).mu - ∑ w ∈ L.supp, SizeData₂.sz w (L.sg u w)| =
      ∑ w ∈ L.supp, roundingAt L u w := by
  rw [J.mu_diff D L hd u (D.div_good.2 u) hfg (J.ne_bot_of_rank_pos _ hr), ← Finset.sum_sub_distrib]
  have h : (∑ w ∈ L.supp, (2 * SizeData₂.lwP w * (⌊DV.ur D w (L.sg u w)⌋ : ℝ) -
      SizeData₂.sz w (L.sg u w))) = -(∑ w ∈ L.supp, roundingAt L u w) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    unfold roundingAt Int.fract SizeData₂.sz DV.ur
    ring
  rw [h, abs_neg, abs_of_nonneg (Finset.sum_nonneg fun w _ => rounding_nonneg L u w)]

private theorem rounding_small_primes {D : D7} (L : SizeData₂ D) (u : D.what₂.Word) :
    ∑ w ∈ L.supp.filter (fun w => ¬ L.sc.X'' D.R.n < (D.what₂.places.resChar w : ℝ)), roundingAt L u w ≤
      (2 * Real.log 4) * L.sc.X'' D.R.n := by
  let X := L.sc.X'' D.R.n
  let N := ⌊X⌋₊
  let S := L.supp.filter (fun w => ¬ X < (D.what₂.places.resChar w : ℝ))
  let P := (Finset.range (N + 1)).filter Nat.Prime
  have hm : ∀ w ∈ S, D.what₂.places.resChar w ∈ P := by
    intro w hw
    have hle := le_of_not_gt (Finset.mem_filter.mp hw).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor hle)),
      D.what₂.places.resChar_prime w⟩
  have hX : 0 ≤ X := (one_pos.trans L.sc.one_lt_alt).le.trans (J.x_le_Xpp L.sc D.R)
  have hsum := (J.sum_lwP_le_primes D S P hm).trans (J.sum_log_primes_le N)
  change ∑ w ∈ S, roundingAt L u w ≤ (2 * Real.log 4) * X
  calc
    _ ≤ ∑ w ∈ S, 2 * SizeData₂.lwP w := Finset.sum_le_sum fun w _ =>
      mul_le_of_le_one_right (mul_nonneg (by norm_num) (J.logWeight_nonneg w)) (Int.fract_lt_one _).le
    _ = 2 * ∑ w ∈ S, SizeData₂.lwP w := (Finset.mul_sum ..).symm
    _ ≤ 2 * ((N : ℝ) * Real.log 4) := by linarith only [hsum]
    _ ≤ (2 * Real.log 4) * X := by
      have h := mul_le_mul_of_nonneg_right (Nat.floor_le hX) (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4))
      dsimp [N] at *
      linarith only [h]

private theorem level_correction_integral (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) :
    ∃ z : ℕ, (z : ℝ) = (D.R.m : ℝ) * EatT D u w := by
  unfold EatT
  split
  · obtain ⟨a, ha⟩ := D.R.m_even
    obtain ⟨b, hb⟩ := D.R.t_odd
    refine ⟨D.R.m * (2 * ∑ τ, Wtau D u τ + D.R.f * D.R.N D.R.m) +
      (topsOf D.host D.eTau).card * (b + 1) * a * (D.R.m + 1), ?_⟩
    have hm : (D.R.m : ℝ) = a + a := by exact_mod_cast ha
    have ht : (D.R.t : ℝ) = 2 * b + 1 := by exact_mod_cast hb
    push_cast
    unfold Nm
    rw [hm, ht]
    ring
  · exact ⟨0, by simp⟩

private theorem rounding_eq_zero_above {ε : ℝ} (Fm : FamP ε) {x : ℝ} (hx : Fm.x1 < x)
    (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word) (w : (Fm.D x i).what₂.places.Pl)
    (hX : (Fm.L x i).sc.X'' (Fm.D x i).R.n < ((Fm.D x i).what₂.places.resChar w : ℝ))
    (hg : (Fm.D x i).what₂.places.resChar w ∉ ({(Fm.D x i).host.g 0, (Fm.D x i).host.g 1} : Finset ℕ))
    (hd : (Fm.D x i).what₂.places.resChar w ≠ (Fm.D x i).host.d) : roundingAt (Fm.L x i) u w = 0 := by
  let D := Fm.D x i
  let L := Fm.L x i
  let p := D.what₂.places.resChar w
  let e := if p = (D.mem u).A.T then EatT D u w else (padicValNat p (D.mem u).C.DGam : ℝ)
  change p ∉ ({D.host.g 0, D.host.g 1} : Finset ℕ) at hg
  have hv (j : ℕ) (hj : j ∈ SizeData₂.lifts D) : L.E u j w = e := by
    have h0 : p ≠ D.host.g 0 := fun h => hg (by simp [h])
    have h1 : p ≠ D.host.g 1 := fun h => hg (by simp [h])
    have h2 : D.host.cls p ≠ PrimeClass.ramD := fun h => hd (cls_ramD h)
    have h3 : ¬ ((IsResidueClassZero D p ∨ IsSg D p) ∧ (p : ℝ) ≤ L.sc.X'' D.R.n) :=
      fun h => (not_le.mpr hX) h.2
    rw [(Fm.ex x hx i).err.edef u j hj w]
    dsimp only [p, D, L] at h0 h1 h2 h3
    simp only [Eval, e, p, D, if_neg h0, if_neg h1, if_neg h2, if_neg h3, add_zero]
  have hsg : L.sg u w = -(D.R.m : ℝ) * e := by
    unfold SizeData₂.sg
    calc
      _ = ∑ _j ∈ SizeData₂.lifts D, -e := by
        refine Finset.sum_congr rfl fun j hj => ?_
        have hgain : L.gain j w = 0 := by
          by_cases hs : w ∈ L.supp
          · by_cases hin : IsResidueClassZero D p ∨ IsSg D p
            · rw [((Fm.fills x hx i w).2.2.2.1 hs hin j hj)]
              unfold gainP
              rw [if_pos (Or.inr hX)]
            · exact (L.not_inert w (fun h => hin (Or.inr h)) (fun h => hin (Or.inl h))).1 j
          · exact L.gain_supp j w hs
        simp [SizeData₂.gainD, hgain, L.F_above j w hX hg hd, hv j hj]
      _ = _ := by simp [SizeData₂.lifts, nsmul_eq_mul]
  have he : ∃ z : ℕ, (z : ℝ) = (D.R.m : ℝ) * e := by
    dsimp only [e]
    split
    · exact level_correction_integral D u w
    · exact ⟨D.R.m * padicValNat p (D.mem u).C.DGam, by push_cast; rfl⟩
  obtain ⟨z, hz⟩ := he
  have hi : DV.ur D w (L.sg u w) = ((-((D.what₂.places.ramIdx w : ℤ) * z) : ℤ) : ℝ) := by
    unfold DV.ur
    push_cast
    rw [hsg, hz]
    ring
  change 2 * SizeData₂.lwP w * Int.fract (DV.ur D w (L.sg u w)) = 0
  rw [hi, Int.fract_intCast, mul_zero]

private theorem rounding_large_primes {ε : ℝ} (Fm : FamP ε) {x : ℝ} (hx : Fm.x1 < x)
    (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word) :
    let D := Fm.D x i
    let L := Fm.L x i
    ∑ w ∈ L.supp.filter (fun w => L.sc.X'' D.R.n < (D.what₂.places.resChar w : ℝ)), roundingAt L u w ≤
      6 * L.sc.X'' D.R.n := by
  let D := Fm.D x i
  let L := Fm.L x i
  let S := L.supp.filter (fun w => L.sc.X'' D.R.n < (D.what₂.places.resChar w : ℝ))
  let B := S.filter (fun w => roundingAt L u w ≠ 0)
  let P : Finset ℕ := {D.host.g 0} ∪ ({D.host.g 1} ∪ {D.host.d})
  have hm : ∀ w ∈ B, D.what₂.places.resChar w ∈ P := by
    intro w hw
    obtain ⟨hS, hn⟩ := Finset.mem_filter.mp hw
    by_contra h
    simp only [P, Finset.mem_union, Finset.mem_singleton, not_or] at h
    exact hn (rounding_eq_zero_above Fm hx i u w (Finset.mem_filter.mp hS).2 (by simpa using And.intro h.1 h.2.1) h.2.2)
  obtain ⟨_, _, _, _, _, _, hQD, _, _, _, _, _, _, _, _, _, _, _, _, _, hG, _⟩ := Fm.sizes x hx i
  have hsum : ∑ p ∈ P, Real.log (p : ℝ) ≤ 3 * L.sc.X'' D.R.n := by
    have h1 := J.sum_log_union_le {D.host.g 0} ({D.host.g 1} ∪ {D.host.d})
    have h2 := J.sum_log_union_le {D.host.g 1} {D.host.d}
    simp only [Finset.sum_singleton] at h1 h2
    change ∑ p ∈ ({D.host.g 0} ∪ ({D.host.g 1} ∪ {D.host.d}) : Finset ℕ), Real.log (p : ℝ) ≤ _
    linarith only [h1, h2, J.log_g_le (D := D) (L := L) hG 0, J.log_g_le (D := D) (L := L) hG 1,
      J.log_d_le (D := D) (L := L) hQD]
  have htotal := (J.sum_lwP_le_primes D B P hm).trans hsum
  change ∑ w ∈ S, roundingAt L u w ≤ _
  calc
    _ = ∑ w ∈ B, roundingAt L u w := (Finset.sum_filter_of_ne (fun w _ hn => hn)).symm
    _ ≤ ∑ w ∈ B, 2 * SizeData₂.lwP w := Finset.sum_le_sum fun w _ =>
      mul_le_of_le_one_right (mul_nonneg (by norm_num) (J.logWeight_nonneg w)) (Int.fract_lt_one _).le
    _ = 2 * ∑ w ∈ B, SizeData₂.lwP w := (Finset.mul_sum ..).symm
    _ ≤ _ := by linarith only [htotal]

theorem principal_family_linkMu {ε : ℝ} (Fm : FamP ε) (hr : J.MuRank Fm) : LinkMu Fm := by
  obtain ⟨a, ha⟩ := hr
  obtain ⟨b, hb⟩ := principal_family_nuFull Fm
  refine ⟨6 + 2 * Real.log 4, max (max a b) (Fm.x1 + 1), fun x hx i u => ?_⟩
  have hx' : Fm.x1 < x := by have := le_of_max_le_right hx; linarith
  let D := Fm.D x i
  let L := Fm.L x i
  rw [slope_error_eq_rounding L u (Fm.nprimeDef x hx' i) ((hb x (le_of_max_le_right (le_of_max_le_left hx)) i u).1)
    (ha x (le_of_max_le_left (le_of_max_le_left hx)) i u), add_mul]
  have hs := add_le_add (rounding_large_primes Fm hx' i u) (rounding_small_primes L u)
  exact (Finset.sum_filter_add_sum_filter_not L.supp
    (fun w => L.sc.X'' D.R.n < (D.what₂.places.resChar w : ℝ)) _).symm.le.trans hs

end RiemannGaussian.AlpogeWindow

namespace RiemannGaussian.AlpogeWindow

open Formalism.BasicNotions Formalism.MainNotions Formalism.HC GlobalTheory.EX UpperTheory.Top

structure PrincipalLocalComparisonData (ε : ℝ) where
  family : FamP ε
  principal : (GChi PChar.one).cls (3/2) family
  Cabs : ℝ
  CH : ℝ
  C0 : ℝ
  chosen : ChosenE family C0 CH
  linkN : LinkN family
  linkEta : LinkEta family
  irreducibility : LinkIRR family
  liftRank : BoundedLiftRank family
  division : LinkDIVt family Cabs CH
  linkG : LinkG family
  linkS : LinkS family C0

structure PrincipalComparisonData (ε eD eL : ℝ) extends PrincipalLocalComparisonData ε where
  global : LinkGLOBAL family Cabs CH C0 eD eL

structure PrincipalComparisonDesign (ε eD eL : ℝ) extends PrincipalComparisonData ε eD eL where
  muRank : J.MuRank family

theorem rh_of_principal_designs (h : ∀ δ : ℝ, 0 < δ → ∃ ε eD eL : ℝ,
    0 < ε ∧ (eD + eL + 7) * ε ≤ δ ∧ Nonempty (PrincipalComparisonDesign ε eD eL)) :
    RiemannHypothesis := by
  apply rh_of_principal_level_windows (la := 3/2) (by norm_num)
  intro θ hθ _
  obtain ⟨ε,eD,eL,hε,hloss,⟨D⟩⟩ := h (θ - 1/2) (sub_pos.mpr hθ)
  have hdiv := D.division D.linkEta (divinN_of_bounded_rank D.family hε
    (hypV_of_cls PChar.one (3/2) D.family D.principal) D.linkN D.liftRank)
  have hmu := principal_family_linkMu D.family D.muRank
  have htied := D.global D.chosen ⟨D.linkG,D.linkS,D.irreducibility,hdiv,hmu⟩
  obtain ⟨x₁,hx⟩ := UpperTheory.Comparison₂.level_gm_le_on_family_scales (Level.cyc PChar.one)
    eD eL ε hε D.family (eFamC_of_cls PChar.one (3/2) D.family D.principal) htied
  apply ((windows_iff D.family.toFamCore (3/2)).mp D.principal.1).mono (x0 := max 1 x₁)
  intro x hx₀ hwin
  exact (hx x (le_of_max_le_right hx₀) hwin).trans
    (Real.rpow_le_rpow_of_exponent_le (le_of_max_le_left hx₀) (by linarith only [hloss]))

end RiemannGaussian.AlpogeWindow

namespace RiemannGaussian.AlpogeWindow

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Classical

theorem single_mem_form_classes {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ}
    {bad : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))} (S : StepLevel F E σ J T f bad)
    {ι : Type} [Fintype ι] (emb : ι → E →+* ℂ) (lam : ι → DomWeight n)
    {C : Type} (yc : C → UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (hinj : Function.Injective fun c => (Quotient.mk'' (yc c) : Cls S))
    (c : C) {φ : C → Frames (gramC J emb) → ℂ} (hφ : φ ∈ FiC S emb lam yc) :
    Pi.single c (φ c) ∈ FiC S emb lam yc := by
  classical
  obtain ⟨g, hg, rfl⟩ := hφ
  let cl := fun x => (Quotient.mk'' x : Cls S)
  let cut := fun x => if cl x = cl (yc c) then g x else 0
  refine ⟨cut, ⟨?_, ?_⟩, ?_⟩
  · intro γ hγ x x' κ he y y' hy
    let k : UPts σ J (FiniteAdeleRing (𝓞 F) F) := ⟨κ.val, ((S.U_eq κ.val).1 κ.2).1⟩
    let a := x' * k⁻¹ * x⁻¹
    have ha : a.val = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ := by
      simp only [a, k, Subgroup.coe_inv, Subgroup.coe_mul, he]
      group
    have hcl : cl x = cl x' := by
      apply (DoubleCoset.eq _ _ x x').2
      exact ⟨a, Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨γ, hγ, ha.symm⟩),
        k, κ.2, by dsimp [a]; group⟩
    by_cases hx : cl x = cl (yc c)
    · simpa only [cut, ← hcl, if_pos hx] using hg.1 γ hγ x x' κ he y y' hy
    · simp only [cut, ← hcl, if_neg hx, Pi.zero_apply, mul_zero]
  · apply Submodule.mem_pi.2
    intro x _
    dsimp only [cut]
    split
    · exact Submodule.mem_pi.1 hg.2 x (Set.mem_univ x)
    · exact Submodule.zero_mem _
  · funext b
    change cut (yc b) = (Pi.single c (g (yc c)) : C → Frames (gramC J emb) → ℂ) b
    by_cases hb : b = c
    · subst b
      simp [cut]
    · simp [cut, show cl (yc b) ≠ cl (yc c) from fun h => hb (hinj h), Pi.single_eq_of_ne hb]

theorem single_mem_unramified_forms {D : D7} {u : D.what₂.Word}
    {eV : (D.mem u).A.vT ≃ PlT D u} {K : ClsTied u 0 (Nat.zero_le _)}
    (W : ValTied u eV 0 (Nat.zero_le _) K) (c : (D.mem u).C.cls 0) (φ : (D.mem u).A.Mu0) :
    Pi.single c (φ.val c) ∈ (D.mem u).A.Mu0 := by
  classical
  apply (Mu0_iff W _).2
  have h := single_mem_form_classes K.lev (embT D) ((D.fm u).lam 0) K.y K.y_bij.1 c
    ((Mu0_iff W _).1 φ.property)
  convert h using 1
  funext b z
  by_cases hb : b = c
  · subst b
    simp
  · simp [Pi.single_eq_of_ne hb]

end RiemannGaussian.AlpogeWindow

namespace RiemannGaussian.AlpogeWindow

open Formalism.BasicNotions Formalism.MainNotions Classical

noncomputable def levelUnitAction (D : D7) (u : D.what₂.Word) (v : (D.mem u).A.vT) :
    Representation ℂ ((D.mem u).A.Fv v)ˣ (D.mem u).A.Mu0 :=
  let A := (D.mem u).A
  Representation.subrepresentation (A.rhoT v) A.Mu0 fun g =>
    Submodule.map_le_iff_le_comap.mp (A.Mu0_stable v g)

theorem level_norm_rank_of_character (D : D7) (u : D.what₂.Word) (v : (D.mem u).A.vT)
    (h : ∀ g : ((D.mem u).A.Fv v)ˣ, g ≠ 1 → (levelUnitAction D u v).character g = 0) :
    let A := (D.mem u).A
    (A.T - 1) * Module.finrank ℂ (LinearMap.range ((A.Nm v).domRestrict A.Mu0)) ≤ D.duS u := by
  classical
  let A := (D.mem u).A
  let G := (A.Fv v)ˣ
  let ρ := levelUnitAction D u v
  have := A.Mu0_fd
  have hnorm : (A.Nm v).domRestrict A.Mu0 = A.Mu0.subtype.comp ρ.norm := by
    ext x : 1
    change (∑ g : G, A.rhoT v g) x.val = A.Mu0.subtype ((∑ g : G, ρ g) x)
    simp only [LinearMap.sum_apply, map_sum]
    rfl
  have hrange : LinearMap.range ρ.norm ≤ ρ.invariants := by
    rintro _ ⟨x, rfl⟩ g
    exact ρ.self_norm_apply g x
  have hr : Module.finrank ℂ (LinearMap.range ((A.Nm v).domRestrict A.Mu0)) ≤
      Module.finrank ℂ ρ.invariants := by
    rw [hnorm, LinearMap.range_comp]
    exact (Submodule.equivMapOfInjective A.Mu0.subtype A.Mu0.injective_subtype _).finrank_eq.symm.le.trans
      (Submodule.finrank_mono hrange)
  have hcard : Nat.card G = A.T - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, A.card_Fv]
  have hn : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  let := invertibleOfNonzero hn
  have hav := ρ.card_inv_mul_sum_char_eq_finrank
  have he : ∑ g : G, ρ.character g = ρ.character 1 :=
    Finset.sum_eq_single 1 (fun g _ hg => h g hg) (by simp)
  rw [he, Representation.char_one, ← div_eq_inv_mul] at hav
  have heq : (A.T - 1) * Module.finrank ℂ ρ.invariants = D.duS u := by
    rw [← hcard, Nat.mul_comm]
    exact_mod_cast ((div_eq_iff hn).mp hav).symm
  exact (Nat.mul_le_mul_left _ hr).trans_eq heq

theorem level_character_eq_zero_of_free_classes (D : D7) (u : D.what₂.Word)
    (v : (D.mem u).A.vT) (g : ((D.mem u).A.Fv v)ˣ)
    (hcut : ∀ c (φ : (D.mem u).A.Mu0), Pi.single c (φ.val c) ∈ (D.mem u).A.Mu0)
    (hfree : ∀ c, (D.fm u).dil 0 v g c ≠ c) : (levelUnitAction D u v).character g = 0 := by
  classical
  let A := (D.mem u).A
  let C := (D.mem u).C
  let U := levelUnitAction D u v g
  let P (c : C.cls 0) : Module.End ℂ A.Mu0 :=
    (((LinearMap.single ℂ (fun _ : C.cls 0 => C.Y 0 → ℂ) c).comp (LinearMap.proj c)).comp
      A.Mu0.subtype).codRestrict A.Mu0 (hcut c)
  have hPc (c : C.cls 0) (φ : A.Mu0) : (P c φ).val = Pi.single c (φ.val c) := rfl
  have htotal : ∑ c, P c = 1 := by
    ext φ : 1
    apply Subtype.ext
    rw [LinearMap.sum_apply]
    change A.Mu0.subtype (∑ c, P c φ) = φ.val
    simp only [map_sum, Submodule.subtype_apply, hPc, Finset.univ_sum_single]
  have hproj (c : C.cls 0) : P c * P c = P c := by
    ext φ : 1
    apply Subtype.ext
    change (P c (P c φ)).val = _
    simp only [hPc, Pi.single_eq_same]
  have hoff (c : C.cls 0) : P c * U * P c = 0 := by
    ext φ : 1
    apply Subtype.ext
    change (P c (U (P c φ))).val = 0
    rw [hPc]
    change (Pi.single c (A.rhoT v g (P c φ).val c) : C.cls 0 → C.Y 0 → ℂ) = 0
    rw [(D.fm u).rhoT_dil, hPc, Pi.single_eq_of_ne (hfree c), map_zero, Pi.single_zero]
  change LinearMap.trace ℂ A.Mu0 U = 0
  calc LinearMap.trace ℂ A.Mu0 U = LinearMap.trace ℂ A.Mu0 (U * ∑ c, P c) := by rw [htotal, mul_one]
       _ = ∑ c, LinearMap.trace ℂ A.Mu0 (U * P c) := by rw [Finset.mul_sum, map_sum]
       _ = 0 := Finset.sum_eq_zero fun c _ => by
         calc LinearMap.trace ℂ A.Mu0 (U * P c)
             = LinearMap.trace ℂ A.Mu0 (P c * U * P c) := by
               rw [LinearMap.trace_mul_cycle, hproj, LinearMap.trace_mul_comm]
           _ = 0 := by rw [hoff, map_zero]

def FreeLevelClasses (D : D7) (u : D.what₂.Word) : Prop :=
  (∀ c (φ : (D.mem u).A.Mu0), Pi.single c (φ.val c) ∈ (D.mem u).A.Mu0) ∧
    ∀ v (g : ((D.mem u).A.Fv v)ˣ), g ≠ 1 → ∀ c, (D.fm u).dil 0 v g c ≠ c

theorem localNormRankBound_of_free_classes (D : D7) (u : D.what₂.Word) (h : FreeLevelClasses D u) :
    LocalNormRankBound D u := fun v => level_norm_rank_of_character D u v fun g hg =>
      level_character_eq_zero_of_free_classes D u v g h.1 (h.2 v g hg)

end RiemannGaussian.AlpogeWindow

namespace RiemannGaussian.AlpogeWindow

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix

open Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0

open scoped TensorProduct

theorem stabilizers_trivial_of_two_level_primes {D : D7} {u : D.what₂.Word}
    (Tf : Forms0 D u) : product_first_zeroth_parts.admS D u := by
  intro c
  let K := Tf.cls0
  let y := (K.y c).val
  let incl := bc (inclE (E := D.host.E) (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (n := Fin (D.R.N 0))
  have htriv (s : (D.mem u).C.stab 0 c) : s = 1 := by
    let γ := (K.stabI c s).val
    obtain ⟨κ, hκ, he⟩ := (K.stabI_range c _).1 ⟨s, rfl⟩
    have hconj : incl γ = (MulAut.conj y) κ := he.symm
    have hpow (j : ℕ) : κ ^ j = y⁻¹ * incl (γ ^ j) * y := by
      rw [map_pow, hconj, ← map_pow, MulAut.conj_apply]
      group
    have hcop (i : Fin 2) (j N : ℕ) (hc : Nat.Coprime N (D.host.g i))
        (hj : (γ ^ j) ^ N = 1) : γ ^ j = 1 := by
      obtain ⟨w, hw⟩ := Formalism.L2.G.Triv.exists_place (F := D.host.F) (D.host.g i) (D.host.g_prime i)
      let pr := bc (prV (E := D.host.E) w) (n := Fin (D.R.N 0))
      have hloc : pr (κ ^ j) ∈ K.lev.Uloc w := ((K.lev.U_eq _).1 (K.lev.U.pow_mem hκ j)).2 w
      have h1 := torsion_reduction_trivial K.lev Tf.gl Tf.glev0 rank_zero_le_weight
        i (D.host.g_prime i) w hw _ hloc N hc (pow_image_eq_one pr incl κ y γ hpow j N hj)
      exact pow_eq_one_of_comp_eq_one incl pr (bc (Tf.gl.phi i w hw))
        (base_change_GL_comp_injective (m := D.R.N 0) _ _ _ (RingHom.injective _)) κ y γ hpow j h1
    have horder : γ ^ orderOf s = 1 := by
      change ((K.stabI c s).val) ^ orderOf s = 1
      rw [← Subgroup.coe_pow, ← map_pow, pow_orderOf_eq_one, map_one, Subgroup.coe_one]
    have hγ := eq_one_of_coprime_torsion_two_primes γ _ _ _ (D.host.g_prime 0) (D.host.g_prime 1)
      D.host.g_ne (orderOf_pos s) horder (hcop 0) (hcop 1)
    apply K.stabI_inj c
    rw [map_one]
    exact Subtype.ext hγ
  exact ⟨fun a b => (htriv a).trans (htriv b).symm⟩

theorem freeLevelClasses_of_forms {D : D7} {u : D.what₂.Word} (Tf : Forms0 D u) :
    FreeLevelClasses D u := by
  refine ⟨single_mem_unramified_forms Tf.val0, ?_⟩
  intro v g hg c hc
  obtain ⟨k, hk, δ, hδ⟩ := diamond_elements_exist_all Tf 0 (Nat.zero_le _) rfl v g
  exact hg (dilation_free_on_classes Tf (stabilizers_trivial_of_two_level_primes Tf) v g k hk δ hδ c hc)

theorem unramified_dimension_pos_of_forms {D : D7} {u : D.what₂.Word} (Tf : Forms0 D u) :
    0 < D.duS u := by
  classical
  let K := Tf.cls0
  let W := Tf.val0
  let F : Frames (gramC (gramN D 0 (Nat.zero_le _)) (embT D)) → ℂ :=
    Formalism.L2.Col.evV (embT D) (gramN D 0 (Nat.zero_le _)) ((D.fm u).lam 0)
    (RingHom.id ℂ) (Formalism.L2.Col.extV ℂ ((D.fm u).lam 0))
  have hF : F ≠ 0 := Formalism.L2.Col.evV_extV_ne_zero _ _ _ _ ⟨fun _ => 1, fun _ => by simp⟩
  let φ := fun (_ : (D.mem u).C.cls 0) (z : (D.mem u).C.Y 0) => F (W.eY z)
  have hφ : φ ∈ (D.mem u).A.Mu0 := by
    apply (Mu0_iff W _).2
    apply Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.adelic_function_ext K.lev (embT D)
      (embedding_conj_compat D) ((D.fm u).lam 0) K.y K.y_bij
    · intro c γ hγ hm
      obtain ⟨s, hs⟩ := ((K.stabI_range c ⟨γ, hγ⟩).2 hm)
      have := stabilizers_trivial_of_two_level_primes Tf c
      rw [Subsingleton.elim s 1, map_one] at hs
      exact (congrArg Subtype.val hs).symm
    · intro c
      change (fun z => F (W.eY (W.eY.symm z))) ∈ _
      simp only [Equiv.apply_symm_apply]
      exact Formalism.L2.Col.evV_mem_ValC (embT D) (gramN D 0 (Nat.zero_le _)) ((D.fm u).lam 0) (RingHom.id ℂ) _
  obtain ⟨c, _⟩ := K.y_bij.2 (Quotient.mk'' 1)
  have hn : (⟨φ, hφ⟩ : (D.mem u).A.Mu0) ≠ 0 := by
    intro hz
    apply hF
    funext z
    have hv := congrFun (congrFun (congrArg Subtype.val hz) c) (W.eY.symm z)
    change F (W.eY (W.eY.symm z)) = 0 at hv
    rw [W.eY.apply_symm_apply] at hv
    exact hv
  have : Nontrivial (D.mem u).A.Mu0 := ⟨⟨_, _, hn⟩⟩
  have := (D.mem u).A.Mu0_fd
  exact Module.finrank_pos

def HasLevelZeroForms {ε : ℝ} (Fm : FamP ε) : Prop :=
  ∃ a : ℝ, ∀ x ≥ a, ∀ (i : Fm.Ix x) u, Nonempty (Forms0 (Fm.D x i) u)

end RiemannGaussian.AlpogeWindow

namespace RiemannGaussian.AlpogeWindow

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms

open Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0

theorem ramified_dimension_pos_of_forms {D : D7} {u : D.what₂.Word} (Tf : Forms0 D u) :
    0 < (D.mem u).A.du := by
  let A := (D.mem u).A
  obtain ⟨M⟩ := free_rank_model_of_split Tf (stabilizers_trivial_of_two_level_primes Tf)
    (splitAtT_of_tied Tf.atT)
  have h := ramified_rank_mul A M
  have ht : 2 < A.T := lt_of_le_of_ne A.T_prime.two_le (D.T_ne_two u).symm
  have hpos : 0 < D.duS u * (A.T - 2) ^ D.R.f :=
    Nat.mul_pos (unramified_dimension_pos_of_forms Tf) (pow_pos (by omega) _)
  change A.du * (A.T - 1) ^ D.R.f = D.duS u * (A.T - 2) ^ D.R.f at h
  rw [← h] at hpos
  exact Nat.pos_of_mul_pos_right hpos

theorem principal_family_rank_of_forms {ε : ℝ} (Fm : FamP ε) (h : HasLevelZeroForms Fm) :
    J.MuRank Fm := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, hb⟩ := principal_family_nuFull Fm
  refine ⟨max a b, fun x hx i u => ?_⟩
  change 0 < (Fm.D x i).div.d u
  rw [(hb x (le_of_max_le_right hx) i).rank u]
  exact (ha x (le_of_max_le_left hx) i u).elim ramified_dimension_pos_of_forms

theorem rh_of_principal_adelic_designs (h : ∀ δ : ℝ, 0 < δ → ∃ ε eD eL : ℝ,
    0 < ε ∧ (eD + eL + 7) * ε ≤ δ ∧
      ∃ D : PrincipalComparisonData ε eD eL, HasLevelZeroForms D.family) : RiemannHypothesis := by
  apply rh_of_principal_designs
  intro δ hδ
  obtain ⟨ε, eD, eL, he, hloss, D, hD⟩ := h δ hδ
  exact ⟨ε, eD, eL, he, hloss, ⟨⟨D, principal_family_rank_of_forms _ hD⟩⟩⟩

end RiemannGaussian.AlpogeWindow

namespace RiemannGaussian.AlpogeWindow

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.L2

theorem principal_design_group_and_hecke :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ K : TransportedAlt,
      ∀ (Fm : FamP ε) (CH C0 : ℝ), Fm.Large K CH → ChosenE Fm C0 CH →
      Formalism.L2.G.GroupCompatibilityFamily Fm →
      (∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ i : Fm.Ix x, ∃ (M : MtFam (Fm.D x i))
        (_ : NormalizedLocalCompatibility (Fm.D x i) M), HeckeTied (Fm.D x i) M) →
      LinkEta Fm ∧ LinkG Fm := by
  let fam : FamClass := fun Fm => Formalism.L2.G.GroupCompatibilityFamily Fm ∧ ∃ C0 CH, ChosenE Fm C0 CH
  have hL := Formalism.L2.G.linkG_concrete5 fam (Closed.of_class fun _ _ h => h.1)
    (Closed.of_class fun Fm _ h => by
      obtain ⟨C0,CH,hchosen⟩ := h.2
      exact admissible_tops_mertens Fm (topsF_of_chosenE Fm hchosen))
  obtain ⟨ε₀, h₀, hL⟩ := hL
  refine ⟨ε₀, h₀, fun ε hε hsmall => ?_⟩
  obtain ⟨K, hK⟩ := hL ε hε hsmall
  exact ⟨K, fun Fm CH C0 hlarge hchosen hgroup hhecke =>
    ⟨linkEta_closed Fm hhecke, hK Fm CH ⟨hgroup,C0,CH,hchosen⟩ hlarge⟩⟩

end RiemannGaussian.AlpogeWindow

namespace RiemannGaussian.AlpogeWindow

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.L2

open GlobalTheory.Fc GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl

theorem principal_lift_rank_of_archived_bundles {ε : ℝ} {𝒜 : FamClass}
    {σ : RawSel BundleCondition 𝒜} {Q : V4.Slot}
    {hL : UpperTheory.Zero.LLC.RecTExists} {p : Parameters hL} {E : Par → BdP BundleCondition}
    (selected : IsSel Q (BundleLinkage p) E 𝒜 σ) (Fm : FamP ε) (hc : 𝒜 Fm) :
    BoundedLiftRank Fm := by
  obtain ⟨_, _, _, built⟩ := selected Fm hc
  apply boundedLiftRank_of_source 1 (Fm.x1 + 1)
  intro x hx i j hj
  have hx' : Fm.x1 < x := by linarith only [hx]
  let b := σ Fm hc x hx' i
  have rows : Rows.RowsHold0_3 b.P := by
    apply Built.ind (R := fun _ _ _ b => Rows.RowsHold0_3 b.P) ?_ (built x hx' i).1
    intro K β c b' _ _ linked
    obtain ⟨q, b'', ⟨w⟩, he⟩ := linked
    have equality := congrArg (fun s : Σ (D : D7) (O : GlobalTheory.EX.OB.Obj D),
      BundleCondition D O c => Rows.RowsHold0_3 s.2.2.P) he
    apply cast equality.symm
    have prim := GlobalTheory.Fc.RL.PrimAt.of_wit_alt w
    exact b''.B.Q.rowsHold0 b''.C.toS.ok1 prim.2 prim.1
  have hj' := Finset.mem_Icc.mp hj
  obtain ⟨k, rfl⟩ : ∃ k : Fin (Fm.D x i).R.m, j = k.val + 1 :=
    ⟨⟨j - 1, by omega⟩, by simp; omega⟩
  have hbase : (Fm.D x i).what₂.D0 = b.P.S0.D :=
    GlobalTheory.rowSide_card_eq_of_coord (Fm.ex x hx' i).p0.s (Fm.D x i).what₂.onb0 b.P.I.eRR0
  rw [one_mul, Formalism.L2.N.ExtNRows3.finrank_Mj_eq_dW b.P k,
    Formalism.L2.N.ExtNRows3.dW_eq_D b.P rows k, hbase]

theorem principal_links_of_archived_bundles :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ K : TransportedAlt,
    ∀ (𝒜 : FamClass), RawSel BundleCondition 𝒜 → ∀ (Fm : FamP ε) (CH C0 : ℝ), 𝒜 Fm →
      Fm.Large K CH → ChosenE Fm C0 CH → LinkEta Fm ∧ LinkG Fm := by
  obtain ⟨ε₀, h₀, getK⟩ := principal_design_group_and_hecke
  refine ⟨ε₀, h₀, fun ε hε hsmall => ?_⟩
  obtain ⟨K, hK⟩ := getK ε hε hsmall
  refine ⟨K, fun 𝒜 σ Fm CH C0 hc hlarge hchosen => hK Fm CH C0 hlarge hchosen ?_ ?_⟩
  · exact ⟨Fm.x1, fun x _ i hx => ⟨(σ Fm hc x hx i).R.T.g⟩⟩
  · refine ⟨Fm.x1 + 1, fun x hx i => ?_⟩
    let N := (σ Fm hc x (by linarith) i).R.T.n
    exact ⟨N.gal.mt, N.cover, N.gal.hecke⟩

end RiemannGaussian.AlpogeWindow

namespace RiemannGaussian.AlpogeWindow

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Lnk

theorem principal_ramified_share_of_forms {ε : ℝ} (Fm : FamP ε)
    (hTu : LevelPrimeGrowth Fm) (hforms : HasLevelZeroForms Fm) : RamShareF Fm := by
  obtain ⟨a, ha⟩ := hforms
  obtain ⟨b, hb⟩ := principal_ramified_share_of_level_growth Fm (fam_eps_pos Fm) hTu
    ⟨a, fun x hx i u => localNormRankBound_of_free_classes _ u
      ((ha x hx i u).elim freeLevelClasses_of_forms)⟩
  refine ⟨b, fun x hx i => ⟨_, sq_nonneg _, ?_, hb x hx i⟩⟩
  exact (Real.sqrt_sq (Real.exp_pos _).le).le

theorem principal_frame_of_forms {ε Cabs CH C0 : ℝ} (Fm : FamP ε)
    (hCH : 0 < CH) (hC0 : 1 ≤ C0) (hTu : LevelPrimeGrowth Fm) (hforms : HasLevelZeroForms Fm)
    (hp : ChosenProviso Fm C0) (hc : ChosenCode Fm C0 CH)
    (hS : LinkS Fm C0) (hI : LinkIRR Fm) (hD : LinkDIV Fm Cabs CH) :
    LatF Fm ∧ FrameF Fm CH := by
  have hC := zero_lt_one.trans_le hC0
  have hr := principal_family_rank_of_forms Fm hforms
  have hs := principal_ramified_share_of_forms Fm hTu hforms
  have hn := principal_family_nuFull Fm
  have hlat := latF Fm hD hn hr (rrRankF_of Fm Cabs CH C0 hC hS hp hI hD)
  have hreal := frameRealF_of' Fm Cabs CH C0 hCH.le hD hI hS hp hn hr
    (matKF_of Fm Cabs CH C0 hC hS hp hD) hs
  exact ⟨hlat, frameF_of Fm CH C0 hCH hC0 hreal hlat hp hc hn⟩

end RiemannGaussian.AlpogeWindow

namespace RiemannGaussian.AlpogeWindow

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Lnk

open Formalism.MainNotions.GlobalTheoryTheory

theorem principal_level_lower_of_count {ε : ℝ} (Fm : FamP ε) (hcount : CountF Fm) :
    ∃ a : ℝ, ∀ x ≥ a, ∀ i : Fm.Ix x, (Fm.L x i).TuGe := by
  obtain ⟨C, a, hC, ha⟩ := hcount
  obtain ⟨b, hb⟩ := m_large Fm (C + 1)
  obtain ⟨c, hc⟩ := ev_pow_le_exp 1 ε 1 one_pos (fam_eps_pos Fm)
  refine ⟨max (max a b) (max c (max 3 (Fm.x1 + 1))), fun x hx i u => ?_⟩
  have h₁ := le_of_max_le_left hx
  have h₂ := le_of_max_le_right hx
  have h₃ := le_of_max_le_right h₂
  have hx₁ : Fm.x1 < x := by linarith only [le_of_max_le_right h₃]
  have hx₃ : 3 ≤ x := le_of_max_le_left h₃
  let D := Fm.D x i
  let L := Fm.L x i
  have hL₁ : 1 ≤ L.sc.L := Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le
  have hLx : Real.log L.sc.x ≤ L.sc.L := by
    have hh := hc x (le_of_max_le_left h₂) (by linarith only [hx₃])
    rw [Real.rpow_one, one_mul] at hh
    change Real.log (Fm.L x i).sc.x ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps
    rw [Fm.L_x x i hx₁, Fm.L_eps x i]
    exact (Real.log_le_iff_le_exp (by linarith only [hx₃])).2 hh
  have hB := JDB.dataB_fam Fm x hx₃ hx₁ i
  have hv : 0 < D.host.v := Real.pi_pos.trans_le hB.1
  have hLa : L.La ≤ 4 * L.sc.L := by
    have hrd : D.host.rdE = 2 * D.host.v := by unfold Host.v; ring
    change Real.log (L.sc.x * Real.exp L.sc.L * D.host.rdE) ≤ _
    rw [hrd, Real.log_mul (mul_pos (zero_lt_one.trans L.sc.one_lt_alt) (Real.exp_pos _)).ne'
      (mul_pos (by norm_num) hv).ne', Real.log_mul (zero_lt_one.trans L.sc.one_lt_alt).ne' (Real.exp_pos _).ne',
      Real.log_exp, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hv.ne']
    linarith only [hLx, hB.2.1, hL₁, Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hmk : (D.R.m : ℝ) ^ 2 ≤ D.R.k := by
    have H : (D.R.m : ℝ) ^ 2 * L.sc.L ≤ D.R.k := hB.2.2.2.1
    exact (le_mul_of_one_le_right (sq_nonneg _) hL₁).trans H
  have hk : 0 < (D.R.k : ℝ) := by exact_mod_cast (show 0 < D.R.k by have := D.R.m_add_three_le_k; omega)
  have hterm : (D.R.m : ℝ) ^ 2 * L.La / D.R.k ≤ 4 * L.sc.L := by
    apply (div_le_iff₀ hk).2
    calc _ ≤ (D.R.m : ℝ) ^ 2 * (4 * L.sc.L) := mul_le_mul_of_nonneg_left hLa (sq_nonneg _)
         _ ≤ _ := by rw [mul_comm]; exact mul_le_mul_of_nonneg_left hmk (by linarith only [hL₁])
  have herror := mul_le_mul_of_nonneg_left (add_le_add hLa hterm) hC
  have hmain := lowB_ge D L.sc _ 0 _ _ hB
  simp only [max_self, zero_mul, sub_zero, StandardLattice.lowB, Fin.sum_univ_two] at hmain
  have hcuw := (ha x (le_of_max_le_left h₁) i u).1
  change (∑ j ∈ SizeData₂.lifts D, 1 / (D.R.f : ℝ) *
      ∑ τ, Real.log (wj D j τ * D.host.v / Real.pi)) + D.R.m * lgG D -
      C * (L.La + (D.R.m : ℝ) ^ 2 * L.La / D.R.k) ≤ Real.log ((D.mem u).A.T : ℝ) at hcuw
  have heq : SizeData₂.lifts D = Finset.Ico (0 + 1) (D.R.m + 1) := by ext j; simp [SizeData₂.lifts]
  rw [heq, ← Finset.sum_Ico_add' (fun j => 1 / (D.R.f : ℝ) *
    ∑ τ, Real.log (wj D j τ * D.host.v / Real.pi)) 0 D.R.m 1, ← Finset.range_eq_Ico,
    lgG, Real.log_mul (Nat.cast_ne_zero.mpr (D.host.g_prime 0).ne_zero)
      (Nat.cast_ne_zero.mpr (D.host.g_prime 1).ne_zero)] at hcuw
  have hm := mul_le_mul_of_nonneg_right (hb x (le_of_max_le_right h₁) hx₁ i) (show 0 ≤ L.sc.L by linarith)
  have hCL := mul_nonneg hC (show 0 ≤ L.sc.L by linarith)
  change Real.exp L.sc.L ^ ((D.R.m : ℝ) / 2) ≤ ((D.mem u).A.T : ℝ)
  rw [← Real.exp_mul]
  apply (Real.le_log_iff_exp_le (by exact_mod_cast (D.mem u).A.T_prime.pos)).1
  change (C + 1) * L.sc.L ≤ (D.R.m : ℝ) * L.sc.L at hm
  linarith only [hmain, hcuw, herror, hm, hCL, hL₁]

end RiemannGaussian.AlpogeWindow

namespace RiemannGaussian.AlpogeWindow

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Lnk

open Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0

def LevelLengthBoundAt {D : D7} (L : SizeData₂ D) (u : D.what₂.Word) (C : ℝ) : Prop :=
  ∀ w, D.what₂.places.resChar w = (D.mem u).A.T → (D.fm u).seenP w = true →
    DV.LocLe (D.plEq w) 0 (L.NuLat u) (DV.MramL D u) ∧
    (L.lenMN u w : ℝ) ≤ C * LocalQuadraticParts.nTT D * D.R.m * (L.sc.a / D.R.k + L.sc.b') * D.duS u

theorem level_unseen {D : D7} {L : SizeData₂ D} (hNu : DV.NuDef D L) (hT : NuAtTDef D L)
    (u : D.what₂.Word) (w : D.what₂.places.Pl) (hw : D.what₂.places.resChar w = (D.mem u).A.T)
    (hs : (D.fm u).seenP w = false) :
    DV.LocLe (D.plEq w) 0 (L.NuLat u) (DV.MramL D u) ∧ (L.lenMN u w : ℝ) = 0 := by
  have heq := Formalism.L2.GlobalTheoryTheory.Places.nlam_eq_sram D u w hs
  constructor
  · intro x hx
    have hloc : InLoc (D.plEq w) (L.NuLat u) x :=
      ⟨1, fun h => (D.plEq w).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by rwa [one_smul]⟩
    have hmem := (hT u w hw x).1 hloc
    rw [heq] at hmem
    obtain ⟨s, hsu, hsx⟩ := D.locSpan u w _ hmem.1
    refine ⟨s, hsu, ?_⟩
    rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
    change (D.nuIn u).restrictScalars (NumberField.RingOfIntegers D.what₂.LL) (s • x) ∈ ((D.fm u).lat 0).L
    rwa [map_smul]
  · have hz : DV.lenLoc (D.plEq w) (L.NuLat u) (DV.MramL D u) = 0 := by
      rw [D.lenLoc_atT hT u w hw, heq, Submodule.comap_subtype_self]
      exact Module.length_eq_zero_iff.2 (Submodule.Quotient.subsingleton_iff.2 rfl)
    have hh := hNu.2.2 u w 0 hz
    have he : (D.what₂.places.ramIdx w : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (D.what₂.places.ramIdx_pos w).ne'
    exact (mul_eq_zero.mp (by simpa using hh.symm)).resolve_right he

def LevelLatticeEstimates {ε : ℝ} (Fm : FamP ε) : Prop :=
  ∃ C a : ℝ, 0 ≤ C ∧ ∀ x ≥ a, ∀ (i : Fm.Ix x) u,
    RamifiedSlopeFormula (Fm.D x i) u ∧ LevelLengthBoundAt (Fm.L x i) u C

private theorem level_rank_and_max {D : D7} {u : D.what₂.Word} (Tf : Forms0 D u) :
    ((D.mem u).A.du : ℝ) = (1 - 1 / (((D.mem u).A.T : ℝ) - 1)) ^ D.R.f * (D.duS u : ℝ) ∧
    (LocalQuadraticParts.MuH D u).muMax ≤ ((D.fm u).lat 0).muMax := by
  obtain ⟨M⟩ := free_rank_model_of_split Tf (stabilizers_trivial_of_two_level_primes Tf) (splitAtT_of_tied Tf.atT)
  have hT : 3 ≤ (D.mem u).A.T :=
    lt_of_le_of_ne (D.mem u).A.T_prime.two_le (D.T_ne_two u).symm
  have hr : ((D.mem u).A.du : ℚ) = (D.duS u : ℚ) * (1 - 1 / (((D.mem u).A.T : ℚ) - 1)) ^ D.R.f :=
    ramified_rank_of_model _ M hT
  have hcast := congrArg (Rat.cast : ℚ → ℝ) hr
  push_cast at hcast
  refine ⟨hcast.trans (mul_comm _ _), ?_⟩
  rw [show (LocalQuadraticParts.MuH D u).muMax = (D.fm u).ramLat.muMax from (D.ram_slopes u).2.1]
  exact ramified_max_slope_le D u (ramified_lattice_ne_bot D u
    (ramified_forms_ne_bot D u M hT (unramified_dimension_pos_of_forms Tf)))

private theorem level_length_sum {D : D7} (L : SizeData₂ D) (u : D.what₂.Word) (B : ℝ) (hB : 0 ≤ B)
    (hr : 0 < (D.mem u).A.du) (hd : (D.duS u : ℝ) ≤ 2 * ((D.mem u).A.du : ℝ))
    (hlen : ∀ w, D.what₂.places.resChar w = (D.mem u).A.T → (L.lenMN u w : ℝ) ≤ B * D.duS u)
    (S : Finset D.what₂.places.Pl) (hS : ∀ w ∈ S, D.what₂.places.resChar w = (D.mem u).A.T) :
    (∑ w ∈ S, SizeData₂.sz w (L.lenMN u w)) / ((D.mem u).A.du : ℝ) ≤
      4 * B * Real.log ((D.mem u).A.T : ℝ) := by
  let r : ℝ := (D.mem u).A.du
  have hr' : 0 < r := Nat.cast_pos.mpr hr
  apply (div_le_iff₀ hr').2
  calc ∑ w ∈ S, SizeData₂.sz w (L.lenMN u w)
      ≤ ∑ w ∈ S, (4 * B * r) * lE w := by
        apply Finset.sum_le_sum
        intro w hw
        have hm := (hlen w (hS w hw)).trans (mul_le_mul_of_nonneg_left hd hB)
        have hw0 : 0 ≤ lE w := mul_nonneg (J.logWeight_nonneg w) (Nat.cast_nonneg _)
        rw [sz_eq]
        change _ ≤ 4 * B * (D.mem u).A.du * lE w
        linarith only [mul_le_mul_of_nonneg_left hm hw0]
    _ = (4 * B * r) * ∑ w ∈ S, lE w := (Finset.mul_sum ..).symm
    _ ≤ (4 * B * r) * Real.log ((D.mem u).A.T : ℝ) := mul_le_mul_of_nonneg_left
      (J.sum_lwP_e_le D _ (D.mem u).A.T_prime S hS) (by positivity)
    _ = _ := by ring

theorem principal_level_estimates_of_forms {ε : ℝ} (Fm : FamP ε) (hcount : CountF Fm)
    (hf : HasLevelZeroForms Fm) (hlocal : LevelLatticeEstimates Fm) : LocalQuadraticParts.LevelTFamily Fm := by
  obtain ⟨C, a, hC, ha⟩ := hlocal
  obtain ⟨b, hb⟩ := principal_ramified_share_of_forms Fm
    (levelPrimeGrowth_of_tuGe (principal_level_lower_of_count Fm hcount)) hf
  obtain ⟨c, hc⟩ := hf
  refine ⟨4 * C, max (max a b) (max c (Fm.x1 + 1)), fun x hx i u => ?_⟩
  let D := Fm.D x i
  let L := Fm.L x i
  obtain ⟨Tf⟩ := hc x (le_of_max_le_left (le_of_max_le_right hx)) i u
  obtain ⟨hs, hl⟩ := ha x (le_of_max_le_left (le_of_max_le_left hx)) i u
  obtain ⟨hRank, hMax⟩ := level_rank_and_max Tf
  have he := fam_eps_pos Fm
  have hlate : Fm.x1 < x := by linarith only [le_of_max_le_right (le_of_max_le_right hx)]
  have hx1 : 1 ≤ x := (Fm.one_lt_family_threshold.trans hlate).le
  have htwo : 2 ≤ Real.exp (x ^ (ε/8)) :=
    (by linarith [Real.exp_one_gt_d9] : (2 : ℝ) ≤ Real.exp 1).trans
      (Real.exp_le_exp.mpr (Real.one_le_rpow hx1 (by positivity)))
  obtain ⟨de, hd, hsq, hdim⟩ := hb x (le_of_max_le_right (le_of_max_le_left hx)) i
  rw [Real.exp_neg, ← one_div] at hsq
  have hhalf := hsq.trans (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) htwo)
  have hde : de ≤ 1/2 := by
    nlinarith only [Real.sq_sqrt hd, mul_self_le_mul_self (Real.sqrt_nonneg de) hhalf]
  have hdim' : (D.duS u : ℝ) ≤ 2 * ((D.mem u).A.du : ℝ) := by
    linarith only [(hdim u).trans (mul_le_mul_of_nonneg_right hde (Nat.cast_nonneg _))]
  let B := C * LocalQuadraticParts.nTT D * D.R.m * (L.sc.a / D.R.k + L.sc.b')
  have hB : 0 ≤ B := by
    have hsa : 0 < L.sc.a := mul_pos (zero_lt_one.trans L.sc.one_lt_alt) (Real.exp_pos _)
    have hsb : 0 < L.sc.b' := div_pos hsa (Real.exp_pos _)
    have hTT : 0 ≤ LocalQuadraticParts.nTT D := Nat.cast_nonneg _
    dsimp only [B]
    positivity
  have hall (w) (hw : D.what₂.places.resChar w = (D.mem u).A.T) :
      DV.LocLe (D.plEq w) 0 (L.NuLat u) (DV.MramL D u) ∧ (L.lenMN u w : ℝ) ≤ B * D.duS u := by
    cases hseen : (D.fm u).seenP w with
    | true => exact hl w hw hseen
    | false =>
      obtain ⟨hinc, hz⟩ := level_unseen (Fm.nuDef x hlate i) (Fm.ex x hlate i).lat.atT u w hw hseen
      exact ⟨hinc, hz.trans_le (mul_nonneg hB (Nat.cast_nonneg _))⟩
  refine ⟨hRank, (D.ram_slopes u).1.trans hs, hMax, fun w hw => (hall w hw).1, ?_⟩
  intro S hS
  have hsum := level_length_sum L u B hB (ramified_dimension_pos_of_forms Tf) hdim'
    (fun w hw => (hall w hw).2) S hS
  calc _ ≤ _ := hsum
       _ = _ := by dsimp only [B, D, L]; ring

theorem principal_level_size_of_count {ε : ℝ} (Fm : FamP ε) (hcount : CountF Fm) :
    ∃ C : ℝ, TuSize ({ Fm with CTu := C } : FamP ε) := by
  obtain ⟨t, ht⟩ := principal_level_lower_of_count Fm hcount
  obtain ⟨C, a, _, ha⟩ := hcount
  exact ⟨C, max t a, fun x hx i =>
    ⟨ht x (le_of_max_le_left hx) i, fun u => (ha x (le_of_max_le_right hx) i u).2.1⟩⟩

theorem principal_places_of_level_estimates {ε : ℝ} (Fm : FamP ε) (hcount : CountF Fm)
    (hf : HasLevelZeroForms Fm) (hg : LinkG Fm) (hlocal : LevelLatticeEstimates Fm) : PlacesF Fm := by
  have h26 := principal_level_estimates_of_forms Fm hcount hf hlocal
  obtain ⟨C, hTu⟩ := principal_level_size_of_count Fm hcount
  let F' : FamP ε := { Fm with CTu := C }
  have hcomm : NuCommensF F' := by
    refine ⟨Fm.x1 + 1, fun x hx i u => ?_⟩
    have hx' : Fm.x1 < x := by linarith
    exact principal_nu_commens (Fm.nuDef x hx' i) (Fm.ex x hx' i).lat.atT u
  have hr := principal_family_rank_of_forms Fm hf
  exact Formalism.L2.GlobalTheoryTheory.Places.placesF_min' F' h26 hcomm hTu hr hg (principal_family_linkMu Fm hr)

end RiemannGaussian.AlpogeWindow

namespace RiemannGaussian.AlpogeWindow

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Lnk Formalism.L2.Forms

open Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0

theorem finite_level_character_of_roots {D : D7} {u : D.what₂.Word} (T : Forms0 D u)
    (hroot : ∀ k, ∃ z : D.what₂.LL, IsPrimitiveRoot z (D.host.g k)) : ChiFin0 T := by
  obtain ⟨n, hn, hx⟩ := GlobalTheory.unipotent_type_character_finite_order
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ T.glev0 D.what₂.LL D.what₂.embLL D.host.g_prime hroot
  refine ⟨n, hn, fun i hi h x => ?_⟩
  subst i
  exact hx x

theorem principal_level_estimates_of_roots {ε : ℝ} (Fm : FamP ε) (hn : CountF Fm)
    (hf : HasLevelZeroForms Fm) (h : ∃ C a : ℝ, 0 ≤ C ∧ ∀ x ≥ a, ∀ i : Fm.Ix x,
      (∀ k, ∃ z : (Fm.D x i).what₂.LL, IsPrimitiveRoot z ((Fm.D x i).host.g k)) ∧
      ∀ u, LevelLengthBoundAt (Fm.L x i) u C) : LevelLatticeEstimates Fm := by
  obtain ⟨K, hK⟩ := principal_level_size_of_count Fm hn
  let F' : FamP ε := { Fm with CTu := K }
  obtain ⟨b, hb⟩ := Formalism.L2.GlobalTheoryTheory.Places.settingF_of F' hK
  obtain ⟨c, hc⟩ := hf
  obtain ⟨C, a, hC, ha⟩ := h
  refine ⟨C, max (max a b) (max c (Fm.x1 + 1)), hC, fun x hx i u => ?_⟩
  have hx₁ : Fm.x1 < x := by linarith only [le_of_max_le_right (le_of_max_le_right hx)]
  obtain ⟨hr, hlen⟩ := ha x (le_of_max_le_left (le_of_max_le_left hx)) i
  obtain ⟨T⟩ := hc x (le_of_max_le_left (le_of_max_le_right hx)) i u
  exact ⟨slope_formula_of_character_finite (hb x (le_of_max_le_right (le_of_max_le_left hx)) hx₁ i u)
    T (finite_level_character_of_roots T hr) (stabilizers_trivial_of_two_level_primes T), hlen u⟩

theorem principal_level_lengths_of_congruence {ε : ℝ} (Fm : FamP ε) (hn : CountF Fm)
    (h : ∃ a : ℝ, ∀ x ≥ a, ∀ (i : Fm.Ix x) u, CongruenceLatticeLengthBound (Fm.D x i) u) :
    ∃ b : ℝ, ∀ x ≥ b, ∀ (i : Fm.Ix x) u, LevelLengthBoundAt (Fm.L x i) u 9 := by
  obtain ⟨K, hK⟩ := principal_level_size_of_count Fm hn
  let F' : FamP ε := { Fm with CTu := K }
  obtain ⟨C, hW⟩ := J.numsL_wtsL_fam F' hK (Formalism.L2.GlobalTheoryTheory.Places.dlSize _ F')
  obtain ⟨b, hb⟩ := hW C le_rfl 3 le_rfl
  obtain ⟨a, ha⟩ := h
  refine ⟨max (max a b) (Fm.x1 + 1), fun x hx i u w hw _ => ?_⟩
  have hx' : Fm.x1 < x := by linarith only [le_of_max_le_right hx]
  let D := Fm.D x i
  let L := Fm.L x i
  have hc := ha x (le_of_max_le_left (le_of_max_le_left hx)) i
  have hT := (Fm.ex x hx' i).lat.atT
  have hNu := Fm.nuDef x hx' i
  have hW := hb x (le_of_max_le_right (le_of_max_le_left hx)) i
  have hsum := J.fifthLevelSizes_of_weights (by norm_num : (1 : ℝ) ≤ 3) hW.1 hW.2 u w hw
  obtain ⟨_, n, hlen, hbound⟩ := hc u w hw
  have hnorm := hNu.2.2 u w n ((J.lenAtT D L hT u w hw).trans hlen)
  refine ⟨nuAtT_of hT (fun v t ht => (hc v t ht).1) u w hw, ?_⟩
  have hram : 0 < (D.what₂.places.ramIdx w : ℝ) := Nat.cast_pos.mpr (D.what₂.places.ramIdx_pos w)
  have hupper : (n : ℝ) ≤ (D.what₂.places.ramIdx w : ℝ) *
      (D.R.m * D.duS u * (9 * LocalQuadraticParts.nTT D * (L.sc.a / D.R.k + L.sc.b'))) :=
    hbound.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hsum (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))) hram.le)
  apply (le_of_mul_le_mul_left (a := (D.what₂.places.ramIdx w : ℝ)) _ hram)
  calc (D.what₂.places.ramIdx w : ℝ) * (L.lenMN u w : ℝ) = n := (mul_comm _ _).trans hnorm.symm
       _ ≤ _ := hupper
       _ = _ := by ring

theorem principal_level_estimates_of_congruence {ε : ℝ} (Fm : FamP ε) (hn : CountF Fm)
    (hf : HasLevelZeroForms Fm) (h : ∃ a : ℝ, ∀ x ≥ a, ∀ i : Fm.Ix x,
      (∀ k, ∃ z : (Fm.D x i).what₂.LL, IsPrimitiveRoot z ((Fm.D x i).host.g k)) ∧
      ∀ u, CongruenceLatticeLengthBound (Fm.D x i) u) : LevelLatticeEstimates Fm := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, hb⟩ := principal_level_lengths_of_congruence Fm hn ⟨a, fun x hx i => (ha x hx i).2⟩
  exact principal_level_estimates_of_roots Fm hn hf ⟨9, max a b, by norm_num, fun x hx i =>
    ⟨(ha x (le_of_max_le_left hx) i).1, hb x (le_of_max_le_right hx) i⟩⟩

end RiemannGaussian.AlpogeWindow

namespace RiemannGaussian.AlpogeWindow

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Lnk

open Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

theorem principal_chosen_constant_one_le {ε C0 CH : ℝ} {Fm : FamP ε}
    (h : ChosenE Fm C0 CH) (hf : HasLevelZeroForms Fm) : 1 ≤ C0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, ⟨a, ha⟩, _⟩ := h
  obtain ⟨b, hb⟩ := hf
  obtain ⟨x, hx, _, _, ⟨i⟩⟩ := Fm.toFamCore.exists_pt (max a b)
  let D := Fm.D x i
  let L := Fm.L x i
  let u := D.u₀
  obtain ⟨Tf⟩ := hb x (le_of_max_le_right hx) i u
  obtain ⟨hlo, hhi⟩ := ha x (le_of_max_le_left hx) i u
  have hd : 0 < (D.duS u : ℝ) := Nat.cast_pos.mpr (unramified_dimension_pos_of_forms Tf)
  have hg : 0 < GamL L := Real.exp_pos _
  have hs : 0 < D.what₂.Dstar := (D.Dstar_eq u).symm.trans_gt (D.mem u).A.Dstar_pos
  have hpos : 0 < C0 := (div_pos (mul_pos hd (sq_pos_of_pos hg)) hs).trans_le hhi
  have hsq : 1 ≤ C0 * C0 := (div_le_iff₀ hpos).1 (by simpa only [one_div] using hlo.trans hhi)
  by_contra! hsmall
  nlinarith only [hsq, mul_pos (sub_pos.mpr hsmall) (by linarith : 0 < 1 + C0)]

theorem principal_base_slopes_of_columns {ε : ℝ} (Fm : FamP ε) (hn : CountF Fm)
    (hcol : ∃ a : ℝ, ∀ x ≥ a, ∀ (i : Fm.Ix x) u, Nonempty (flipTwoThree.ColVal (Fm.D x i) u)) :
    SlopesMF Fm := by
  have hmax := third_proposition_of_class (fun D =>
    slopeMaxClass_of_map D (class_map_of_archimedean D (class_map_archimedean D))) Fm
  exact flipTwoThree.slopesMF_of_count_fam Fm (slope_proposition_family Fm) hmax hn
    (Formalism.L2.GlobalTheoryTheory.Places.dlSize _ Fm) hcol

end RiemannGaussian.AlpogeWindow

namespace RiemannGaussian.AlpogeWindow

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Lnk Formalism.L2.Forms

open Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

def HasSymmetricColumnsAndRoots {ε : ℝ} (Fm : FamP ε) : Prop :=
  ∃ a : ℝ, ∀ x ≥ a, ∀ i : Fm.Ix x, Nonempty (ColsTiedSym (Fm.D x i)) ∧
    ∀ k, ∃ z : (Fm.D x i).what₂.LL, IsPrimitiveRoot z ((Fm.D x i).host.g k)

def SymmetricLevelInputs {D : D7} (F : ColsTiedSym D) (u : D.what₂.Word) : Prop :=
  (∃ n : ℕ, 0 < n ∧ ∀ x : ((F.forms u).cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.U,
    ((((F.forms u).cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.chi x : ℂˣ) : ℂ) ^ n = 1 ∧
    ∃ r : D.what₂.LL, D.what₂.embLL r = ((((F.forms u).cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.chi x : ℂˣ) : ℂ)) ∧
  product_first_zeroth_parts.admS D u

theorem symmetric_level_inputs_of_roots {D : D7} (F : ColsTiedSym D)
    (hr : ∀ k, ∃ z : D.what₂.LL, IsPrimitiveRoot z (D.host.g k)) (u : D.what₂.Word) :
    SymmetricLevelInputs F u := by
  obtain ⟨n, hn, hχ⟩ := finite_level_character_of_roots (F.forms u).to0 hr
  exact ⟨⟨n, hn, hχ 0 (Nat.zero_le _) rfl⟩, stabilizers_trivial_of_two_level_primes (F.forms u).to0⟩

theorem principal_column_estimates_of_symmetric {ε : ℝ} (Fm : FamP ε)
    (hcol : ∀ (D : D7), ColsTiedSym D → flipTwoThree.adm3 D → ∀ u, Nonempty (flipTwoThree.ColVal D u))
    (hhecke : ∀ (D : D7) (F : ColsTiedSym D) u, product_first_zeroth_parts.HidaSetting D u →
      SymmetricLevelInputs F u → SecondBranchInclusionLength D u ∧ HeckeIntegralLevelZero D u ∧ HeckeRamifiedLevelZero D u)
    (hn : CountF Fm) (hc : HasSymmetricColumnsAndRoots Fm) :
    HasLevelZeroForms Fm ∧ ∃ a : ℝ, ∀ x ≥ a, ∀ i : Fm.Ix x,
      (∀ k, ∃ z : (Fm.D x i).what₂.LL, IsPrimitiveRoot z ((Fm.D x i).host.g k)) ∧
      ∀ u, Nonempty (flipTwoThree.ColVal (Fm.D x i) u) ∧ CongruenceLatticeLengthBound (Fm.D x i) u := by
  obtain ⟨a, ha⟩ := hc
  obtain ⟨K, hK⟩ := principal_level_size_of_count Fm hn
  let F' : FamP ε := { Fm with CTu := K }
  obtain ⟨b, hb⟩ := Formalism.L2.GlobalTheoryTheory.Places.settingF_of F' hK
  refine ⟨⟨a, fun x hx i u => ?_⟩, max (max a b) (Fm.x1 + 1), fun x hx i => ?_⟩
  · obtain ⟨F⟩ := (ha x hx i).1
    exact ⟨(F.forms u).to0⟩
  · obtain ⟨⟨F⟩, hr⟩ := ha x (le_of_max_le_left (le_of_max_le_left hx)) i
    have hx' : Fm.x1 < x := by linarith only [le_of_max_le_right hx]
    have hadm : flipTwoThree.adm3 (Fm.D x i) :=
      fun u => stabilizers_trivial_of_two_level_primes (F.forms u).to0
    refine ⟨hr, fun u => ⟨hcol _ F hadm u, ?_⟩⟩
    have hs := hb x (le_of_max_le_right (le_of_max_le_left hx)) hx' i u
    obtain ⟨hB, hI, hR⟩ := hhecke _ F u hs (symmetric_level_inputs_of_roots F hr u)
    exact congruence_no_kernel_minimal hs hB hI hR

end RiemannGaussian.AlpogeWindow

namespace RiemannGaussian.AlpogeWindow

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Lnk Formalism.L2.Forms

open Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

theorem principal_hecke_of_symmetric_columns (D : D7) (F : ColsTiedSym D) (u : D.what₂.Word)
    (hs : product_first_zeroth_parts.HidaSetting D u) (h : SymmetricLevelInputs F u) :
    SecondBranchInclusionLength D u ∧ HeckeIntegralLevelZero D u ∧ HeckeRamifiedLevelZero D u := by
  have ht : RT.FormsTwistCompatibilityFamily D u := ⟨_, _, F.forms u, h.1⟩
  have hf : RT.ConcreteFormsLevelZero D u := ⟨ht, h.2⟩
  exact ⟨LemB.second_branch_all_members D u hs hf,
    PI.IntegralAtBasePointLattice.integral_at_t0_lattice D u ht h.2 hs,
    UnramifiedTrace.hecke_ramified_zero_all D u hs hf⟩

end RiemannGaussian.AlpogeWindow

namespace RiemannGaussian.AlpogeWindow

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Lnk

open Formalism.MainNotions.GlobalTheoryTheory Formalism.MainNotions.StandardLattice

open GlobalTheory.Core.Cls GlobalTheory.Mem GlobalTheory.Mem.Top

theorem volume_mass_of_dimension_formula {D : D7} (O : GlobalTheory.EX.OB.Obj D)
    (ht : D.what₂.Dstar = massI D D.R.r * idxSig D (D.host.g 0) (D.host.g 1) * ∏ τ, D.dsig τ) :
    BaseVolumeEqualsMass D := by
  have hv : D.what₂.Dstar = volY0 D * idxSig D (D.host.g 0) (D.host.g 1) * ∏ τ, D.dsig τ := O.ex.Dstar_def
  rw [mul_assoc] at hv ht
  have hp : 0 < D.what₂.Dstar := (D.Dstar_eq D.u₀).symm.trans_gt (D.mem D.u₀).A.Dstar_pos
  rw [ht] at hp
  exact mul_right_cancel₀ (right_ne_zero_of_mul hp.ne') (hv.symm.trans ht)

theorem sigma_degree_of_weyl_dimension {D : D7} (hd : ∀ ρ, D.dsig ρ = dimV (rowLam D ρ)) :
    SigmaDegreeTwoSidedBoundOfGap D := by
  intro e he _ ρ _
  let l := rowLam D ρ
  have hl : Formalism.QuantumDeterminants.IsHCParam l := by
    have hh := Vol.lamSH_isHCParam D.R (D.hc ρ)
    rw [param_vector_eq_line_param] at hh
    have transport {m n : ℕ} (eq : m = n) (l : Fin n → ℝ) :
        Formalism.QuantumDeterminants.IsHCParam (fun i => l (Fin.cast eq i)) →
        Formalism.QuantumDeterminants.IsHCParam l := by subst n; exact id
    exact transport _ _ hh
  have hdim := dim_weyl_pos_of_strictAnti l hl.1
  rw [hd]
  constructor
  · exact mul_le_of_le_one_left hdim.le (by linarith [(Real.exp_pos _).trans_le he])
  · have hle := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.fdegHC_le_dTau (rowSgn D) l hl
    rw [← dimV_eq_fdegHC _ hl.1, count_plus_line_sign, count_minus_line_sign] at hle
    have ht := (formalDegreeFactor_pos_of_strictAnti (rowSgn D) l hl.1).le
    have hp : (1 : ℝ) ≤ pY D := by exact_mod_cast (signature_counts_ge_one D).1
    have hq : (1 : ℝ) ≤ qY D := by exact_mod_cast (signature_counts_ge_one D).2
    have ha := abs_param_sup_nonneg l
    have hfac : 1 ≤ 3 * (pY D : ℝ) * qY D :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by norm_num) hp) hq
    have hb := le_mul_of_one_le_left ha hfac
    exact hle.trans (mul_le_mul (by linarith : dTau (rowSgn D) l ≤ 4 * dTau (rowSgn D) l)
      (pow_le_pow_left₀ ha hb _) (pow_nonneg ha _) (by linarith))

theorem principal_count_of_mass_and_degree {ε : ℝ} {Fm : FamP ε}
    (h : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, BaseVolumeEqualsMass (Fm.D x i) ∧
      SigmaDegreeTwoSidedBoundOfGap (Fm.D x i)) : CountF Fm := by
  apply countF_fam Fm
  apply family_part_five_of_explicit_constants
  apply division_level_prime_family
  · exact ⟨0, fun x _ _ i => massRatio_of_modelMassRatio (Fm.D x i) GlobalTheory.Mass.siegelMassRatio_holds⟩
  · exact ⟨0, fun x _ hx i => (h x hx i).1⟩
  · exact ⟨0, fun x _ hx i => (h x hx i).2⟩

theorem rh_of_principal_selected_geometry (h : ∀ δ : ℝ, 0 < δ → ∃ (ε : ℝ) (D : PrincipalLocalComparisonData ε),
    (D.Cabs + 7) * ε ≤ δ ∧ 0 ≤ D.Cabs ∧ 0 < D.CH ∧ ChosenWall D.family ∧
      CountF D.family ∧ HasSymmetricColumnsAndRoots D.family) :
    RiemannHypothesis := by
  apply rh_of_principal_adelic_designs
  intro δ hδ
  obtain ⟨ε, D, hloss, hC, hH, hw, hn, hs⟩ := h δ hδ
  let Fm := D.family
  obtain ⟨hf, a, ha⟩ := principal_column_estimates_of_symmetric Fm
    Formalism.L2.GlobalTheoryTheory.ColValS.colValOfTiedS_holds principal_hecke_of_symmetric_columns hn
    hs
  have hM := principal_base_slopes_of_columns Fm hn ⟨a, fun x hx i u => ((ha x hx i).2 u).1⟩
  have hN := principal_places_of_level_estimates Fm hn hf D.linkG
    (principal_level_estimates_of_congruence Fm hn hf ⟨a, fun x hx i =>
      ⟨(ha x hx i).1, fun u => ((ha x hx i).2 u).2⟩⟩)
  refine ⟨ε, D.Cabs, 0, fam_eps_pos Fm, by simpa using hloss, ⟨D, ?_⟩, hf⟩
  intro hchosen hin
  obtain ⟨C5, c6, _, h6, hT2, hTT, hBad, hW, hQD, hThin, hPr, hCode⟩ :=
    Formalism.L2.GlobalTheoryTheory.Loss7.loss_requirements_of_small_shares Fm D.C0 D.CH hchosen hw
  obtain ⟨hLat, hFrame⟩ := principal_frame_of_forms Fm hH (principal_chosen_constant_one_le hchosen hf)
    (levelPrimeGrowth_of_tuGe (principal_level_lower_of_count Fm hn)) hf hPr hCode hin.2.1 hin.2.2.1 hin.2.2.2.1
  have hSmall := Formalism.L2.GlobalTheoryTheory.Loss7.losses_of_small_share_weight Fm hTT hBad hin.1
  exact linkCore Fm D.Cabs D.CH 0 C5 c6 hC hH.le le_rfl h6 hn hM (slopesNF_of Fm hN)
    hLat (nodesF Fm) hFrame (lossF_of_7 Fm hSmall hW) (charF Fm) (size_windows_of_thick_density Fm hT2)
    hTT hQD hThin hin.2.2.1 hin.2.2.2.1

end RiemannGaussian.AlpogeWindow

namespace RiemannGaussian.AlpogeWindow

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Lnk Formalism.MainNotions.StandardLattice

open GlobalTheory.Fc GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Core.Cls

theorem principal_geometry_of_built_point {K : Ctx} (β : BPt K) :
    BaseVolumeEqualsMass β.D ∧ SigmaDegreeTwoSidedBoundOfGap β.D ∧ RootsG β.D := by
  refine ⟨volume_mass_of_dimension_formula β.O ?_, sigma_degree_of_weyl_dimension ?_,
    coeffField_rootsOfUnity_typePrimes_hermitianStages β.X⟩
  · have he : β.D.what₂.Dstar = β.X.B.Dstar :=
      (β.D.Dstar_eq β.D.u₀).symm.trans (β.X.C.A_Dstar _)
    rw [he, β.c.isOver.sizes.2]
    unfold DsPre
    congr 1
    exact Finset.prod_congr rfl fun τ _ => (β.c.dsig_eq τ).symm
  · exact fun ρ => (β.c.dsig_eq ρ).trans (DsLow.trueDsig_eq_dimV _ _)

end RiemannGaussian.AlpogeWindow

namespace RiemannGaussian.AlpogeWindow

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.MainNotions.Pk Formalism.HC Formalism.L2

open Formalism.MainNotions.Lnk

open GlobalTheory.EX GlobalTheory.Fc GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl

open GlobalTheory.Core.Cls UpperTheory.Top

private theorem thin_at_built_point {κ : Par} {K : Ctx} (hk : κ.Of K) (β : BPt K) :
    ChThin_at β.D β.O.L.sc.x β.O.L.sc.eps κ.c6 := by
  have hthin := hk.2.2.2.2.host.2.2.2.2.2.2.2.1
  change ThinOK β.p.L.sc κ.c6 β.X.B.host
  rw [β.sc]
  have transfer {B : Pre} (h : K.Over B) : ThinOK K.s κ.c6 B.host := by
    obtain ⟨_, _, _, _, _, _, rfl, _⟩ := h
    exact hthin
  exact transfer β.c.isOver

theorem principal_thin_of_archived_bundles {ε : ℝ} {𝒜 : FamClass} {σ : RawSel BundleCondition 𝒜}
    {Q : V4.Slot} {Lk : LkT BundleCondition} {E : Par → BdP BundleCondition}
    (hs : IsSel Q Lk E 𝒜 σ) (Fm : FamP ε) (hc : 𝒜 Fm) :
    ∃ c6 : ℝ, 0 < c6 ∧ ChosenThin Fm c6 := by
  obtain ⟨κ, hlink, _, hbuilt⟩ := hs Fm hc
  refine ⟨κ.c6, hlink.pos.2.1, Fm.x1 + 1, fun x hx i => ?_⟩
  have hx' : Fm.x1 < x := by linarith
  have h := Built.ind (R := fun D O _ _ => ChThin_at D O.L.sc.x O.L.sc.eps κ.c6)
    (fun _ β _ _ hk _ _ => thin_at_built_point hk β) (hbuilt x hx' i).1
  change ChThin_at (Fm.D x i) (Fm.L x i).sc.x (Fm.L x i).sc.eps κ.c6 at h
  rwa [Fm.L_x x i hx', Fm.L_eps x i] at h

theorem principal_proviso_of_archived_bundles {ε : ℝ} {𝒜 : FamClass} (σ : RawSel BundleCondition 𝒜)
    (Fm : FamP ε) (hc : 𝒜 Fm) : ChosenProviso Fm 3 := by
  apply StandardLattice.HarishChandraReduction.chosenProviso_min Fm 3 (Real.exp_one_lt_d9.le.trans (by norm_num))
    (fun _ _ _ => GlobalTheory.ColClassNumber.classNumber_all _ _)
  apply Ext.Lw.rank_conditions_of_lowest_space
  exact ⟨Fm.x1 + 1, fun x hx i u => Ext.Lw.mu0Tie_of_sym (σ Fm hc x (by linarith) i).R.T.cols u⟩

open Formalism.MainNotions.StandardLattice Formalism.MainNotions.StandardLattice.HarishChandraReduction

open Formalism.L2.Top3

theorem principal_tu_size_of_archived_bundles {ε : ℝ} {𝒜 : FamClass} {σ : RawSel BundleCondition 𝒜}
    {Q : V4.Slot} {Lk : LkT BundleCondition} {E : Par → BdP BundleCondition}
    (hs : IsSel Q Lk E 𝒜 σ) (Fm : FamP ε) (hc : 𝒜 Fm) (hTu : cTmin Fm.CYL ≤ Fm.CTu) :
    TuSize Fm := by
  obtain ⟨κ, _, _, hb⟩ := hs Fm hc
  have geom (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) :=
    Built.ind (R := fun D _ _ _ => BaseVolumeEqualsMass D ∧ SigmaDegreeTwoSidedBoundOfGap D)
      (fun _ β _ _ _ _ _ => ⟨(principal_geometry_of_built_point β).1, (principal_geometry_of_built_point β).2.1⟩)
      (hb x hx i).1
  have count := division_level_prime_family Fm
    ⟨0, fun x _ _ i => massRatio_of_modelMassRatio (Fm.D x i) GlobalTheory.Mass.siegelMassRatio_holds⟩
    ⟨0, fun x _ hx i => (geom x hx i).1⟩ ⟨0, fun x _ hx i => (geom x hx i).2⟩
  let C := max 5 (Fm.CYL + 1)
  obtain ⟨a, ha⟩ := count C C
  obtain ⟨b, hb⟩ := Formalism.MainNotions.GlobalTheoryTheory.rowsAF_fam Fm C
  apply Formalism.MainNotions.GlobalTheoryTheory.tuSize_fam Fm (cTmin Fm.CYL) (max a b) _ hTu
  intro x hx hx' i
  exact part_five_all_of_explicit _ _ _ _ _ (ha x (le_of_max_le_left hx) hx' i)
    (hb x (le_of_max_le_right hx) hx' i) (le_max_left _ _) (le_max_right _ _)

theorem principal_designs_of_archived_bundle_choices {𝒜 : FamClass} {σ : RawSel BundleCondition 𝒜}
    {Q : V4.Slot} {Lk : LkT BundleCondition} {E : Par → BdP BundleCondition}
    (hs : IsSel Q Lk E 𝒜 σ)
    (hd : DC.DesignChoices (DC.WithTw fun Fm => 𝒜 Fm ∧ (GChi PChar.one).cls (3/2) Fm) 3 (fun _ => cTmin)) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ K : TransportedAlt, ∃ (Fm : FamP ε) (CH : ℝ),
      D3 3 (fun Fm => 𝒜 Fm ∧ (GChi PChar.one).cls (3/2) Fm) Fm ∧
      0 < CH ∧ Fm.Large K CH ∧ ChosenE Fm 3 CH ∧ Fm.CF = CH := by
  obtain ⟨ε₀, h₀, chooseFam⟩ := hd
  refine ⟨ε₀, h₀, fun ε hε hsmall K => ?_⟩
  let oneMid : TransportedAlt := ⟨0, fun _ => 0, fun _ => 1, fun _ => 0⟩
  obtain ⟨Fm, CH, C5, Cb, ⟨⟨hc, hp⟩, htw⟩, _, hlarge, h5, hb, hthick, htt, hbad, hqd,
    hcode, hbox, hrows, hdvd, htu, htame, hCF, _, hCYL⟩ := chooseFam ε hε hsmall (K.sup oneMid)
  obtain ⟨hK, hM⟩ := (Fm.large_sup K oneMid CH).1 hlarge
  have hCH : (1 : ℝ) ≤ CH := hM.2.2.1 CH (by simp [FamP.cMid])
  obtain ⟨c6, h6, hthin⟩ := principal_thin_of_archived_bundles hs Fm hc
  have hchosen : ChosenE Fm 3 CH := ⟨C5, c6, Cb, h5, h6, hb, hthick, htt, hbad, hqd, hthin,
    principal_proviso_of_archived_bundles σ Fm hc, hcode⟩
  have hclass : WithChN (fun Fm => 𝒜 Fm ∧ (GChi PChar.one).cls (3/2) Fm) Fm :=
    ⟨⟨hc, hp⟩, hdvd, htame, hbox, hrows, hCYL⟩
  exact ⟨Fm, CH, ⟨⟨withSm_of_withChN Fm hclass, htw⟩, ⟨CH, hchosen⟩,
    principal_tu_size_of_archived_bundles hs Fm hc htu, dGamSize_of_dvd Fm hdvd⟩,
    one_pos.trans_le hCH, hK, hchosen, hCF⟩

theorem principal_geometry_of_archived_selection {ε : ℝ} (Fm : FamP ε) {Q : V4.Slot} {Lk : LkT BundleCondition}
    {E : Par → BdP BundleCondition} {𝒜 : FamClass} {σ : RawSel BundleCondition 𝒜} (hs : IsSel Q Lk E 𝒜 σ) (hc : 𝒜 Fm) :
    ChosenWall Fm ∧ CountF Fm ∧ HasSymmetricColumnsAndRoots Fm := by
  obtain ⟨κ, _, hclass, hbuilt⟩ := hs Fm hc
  have hduty := (GlobalTheory.EX.DQ.familyClass_sevenDuties_and_stableLattices _ Fm hclass).1
  have hw := (GlobalTheory.EX.DQ.duty_seven_library ε Fm hduty).2.2.2.2.1
  have hp : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x,
      BaseVolumeEqualsMass (Fm.D x i) ∧ SigmaDegreeTwoSidedBoundOfGap (Fm.D x i) ∧
      RootsG (Fm.D x i) ∧ Nonempty (Formalism.L2.Forms.ColsTiedSym (Fm.D x i)) := by
    intro x hx i
    obtain ⟨K, β, _, _, _, _, he⟩ := (hbuilt x hx i).1
    have e : Fm.D x i = β.D := congrArg Sigma.fst he
    have hg := e.symm ▸ principal_geometry_of_built_point β
    exact ⟨hg.1, hg.2.1, hg.2.2, ⟨(σ Fm hc x hx i).R.T.cols⟩⟩
  refine ⟨hw, principal_count_of_mass_and_degree (fun x hx i => ⟨(hp x hx i).1, (hp x hx i).2.1⟩),
    Fm.x1 + 1, fun x hx i => ?_⟩
  obtain ⟨_, _, hr, hcols⟩ := hp x (by linarith) i
  exact ⟨hcols, fun k => (hr k).1⟩

theorem rh_of_principal_archived_bundle_choices {𝒜 : FamClass} {σ : RawSel BundleCondition 𝒜} {Q : V4.Slot}
    {hL : UpperTheory.Zero.LLC.RecTExists} {p : Parameters hL} {E : Par → BdP BundleCondition}
    (hs : IsSel Q (BundleLinkage p) E 𝒜 σ)
    (hd : DC.DesignChoices (DC.WithTw fun Fm => 𝒜 Fm ∧ (GChi PChar.one).cls (3/2) Fm) 3 (fun _ => cTmin))
    (Cabs : ℝ) (habs : 0 ≤ Cabs)
    (hcmp : Closed (D3 3 fun Fm => 𝒜 Fm ∧ (GChi PChar.one).cls (3/2) Fm) fun Fm CH =>
      ChosenE Fm 3 CH → Fm.CF = CH → LinkN Fm ∧ LinkIRR Fm ∧ LinkDIVt Fm Cabs CH ∧ LinkS Fm 3) :
    RiemannHypothesis := by
  obtain ⟨d, hd0, chooseFam⟩ := principal_designs_of_archived_bundle_choices hs hd
  obtain ⟨a, ha, getThreshold⟩ := hcmp
  apply rh_of_principal_selected_geometry
  intro δ hδ
  obtain ⟨ε₀, h₀, links⟩ := principal_links_of_archived_bundles
  have hpos : 0 < Cabs + 7 := by linarith
  let ε := min (min ε₀ d) (min a (δ / (Cabs + 7)))
  have hε : 0 < ε := lt_min (lt_min h₀ hd0) (lt_min ha (div_pos hδ hpos))
  have hleft : ε ≤ min ε₀ d := min_le_left _ _
  have hright : ε ≤ min a (δ / (Cabs + 7)) := min_le_right _ _
  obtain ⟨K, hK⟩ := links ε hε (hleft.trans (min_le_left _ _))
  obtain ⟨K', hK'⟩ := getThreshold ε hε (hright.trans (min_le_left _ _))
  obtain ⟨Fm, CH, hclass, hCH, hlarge, hchosen, hCF⟩ :=
    chooseFam ε hε (hleft.trans (min_le_right _ _)) (K.sup K')
  obtain ⟨hlarge, hlarge'⟩ := (Fm.large_sup K K' CH).1 hlarge
  obtain ⟨hc, hp⟩ := d3_a hclass
  obtain ⟨hn, hirr, hdiv, hspectral⟩ := hK' Fm CH hclass hlarge' hchosen hCF
  obtain ⟨hEta, hG⟩ := hK 𝒜 σ Fm CH 3 hc hlarge hchosen
  have hrank := principal_lift_rank_of_archived_bundles hs Fm hc
  let design : PrincipalLocalComparisonData ε :=
    ⟨Fm, hp, Cabs, CH, 3, hchosen, hn, hEta, hirr, hrank, hdiv, hG, hspectral⟩
  have hloss := (le_div_iff₀ hpos).mp (hright.trans (min_le_right _ _))
  exact ⟨ε, design, (mul_comm ε _).symm ▸ hloss, habs, hCH,
    principal_geometry_of_archived_selection Fm hs hc⟩

end RiemannGaussian.AlpogeWindow

namespace RiemannGaussian.AlpogeWindow

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk

open Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT

open Formalism.HC Formalism.L2.Top3 Formalism.L2.Top4

open GlobalTheory.EX GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc

open Formalism.MainNotions.StandardLattice.HarishChandraReduction

open UpperTheory.Top

set_option maxHeartbeats 4000000 in

theorem rh_of_principal_archived_bundle_rows
    {Q : V4.Slot} {hL : UpperTheory.Zero.LLC.RecTExists} {p : Parameters hL}
    {E : Par → BdP BundleCondition}
    (h : HypsAlt (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) DefiniteSideCondition)
    (hs : IsSel Q (BundleLinkage p) E h.𝒜 h.σ)
    (hd : DC.DesignChoices (DC.WithTw fun Fm => h.𝒜 Fm ∧ (GChi PChar.one).cls (3/2) Fm) 3 (fun _ => cTmin))
    (green : GlobalTheory.GLq.Green) : RiemannHypothesis := by
  let sel : Formalism.L2.TwistSelection h.𝒜 := familySelection h.σ
  let selS : SelectionSpectralCondition h.𝒜 sel := spectralConditionOfRawSelection h.σ
  let selP : BaseLevelTiedChoiceAlt h.𝒜 sel := baseLevelChoiceOfRawSelection h.σ
  let selDH : SelectionDefiniteHeightCondition h.𝒜 sel := definiteHeightOfRawSelection h.σ
  let selC : ColumnChoiceCompatibleSelection h.𝒜 sel selP :=
    fun Fm hc x hx k i => (columnChoiceOfRawSelection h.σ Fm hc x hx k i).toS
  let selB : SelectionBundle h.𝒜 sel selS selP selDH selC := selectionBundleOfRawSelection h.σ
  have dv := fun {ε : ℝ} (Fm : FamP ε) hc x hx k i =>
    (GlobalTheory.Cp.divRows3G_iff _).1 (h.hDivG Fm hc x hx k i)
  have rows : Closed (D3 3 h.𝒜) fun Fm CH => ∀ hc : D3 3 h.𝒜 Fm,
      RowsAtSelAlt sel (indefiniteRealisationChoiceOfSelection selB)
        (fun Fm hc x hx k i C CH => Formalism.L2.Top4Wire2.DefRowsFAlt
          (indefiniteRealisationChoiceOfSelection selB) Fm hc x hx k i C CH)
        (SingleMapCondition selB) Fm (d3_a hc) CH := h.rRows.imp fun _ _ _ r hc => by
    obtain ⟨C, h0, x0, r⟩ := r hc
    refine ⟨C, h0, x0, fun x hx k hx0 i => ?_⟩
    obtain ⟨a, d⟩ := r x hx k hx0 i
    exact ⟨⟨a.w1, a.covol, a.onto, a.lamLow, a.seeIso, a.miStar, a.fun0, a.pass, a.kap⟩, d⟩
  have rest := GlobalTheory.Top.link_brest_alt h.𝒜 sel selS selP selDH selC selB
    h.hRB h.hPA dv h.hDcPtG rows h.tie
  have hCsz := Formalism.MainNotions.DIV.closed_Csz_ge_fn (D3 3 h.𝒜) fun _ => 0
  have oneMap : Closed (D3 3 h.𝒜) fun Fm _ => ∀ hc : D3 3 h.𝒜 Fm,
      EventuallyAlongSelection sel Fm (d3_a hc) ((SingleMapCondition selB) Fm (d3_a hc)) :=
    Closed.of_class fun Fm _ _ hc => ⟨0, fun x hx k _ i j => (h.hRB Fm (d3_a hc) x hx k i).oneMap j⟩
  have admissible := GlobalTheory.Top.closed_family_admissible_twist_link_alt h.𝒜 sel
    h.aPt0 h.aPtTw h.aPer0 h.aPerTw h.aP10 h.aAtG ((GlobalTheory.Cp.serv_t_iff_formalism_serv_t _ _).1 h.hServ)
  have count := GlobalTheory.Top.selection_closed_of_wu_decay_alt h.𝒜 sel selS selP selDH selC selB
    h.hWu h.hRF h.selJ h.jOn rows
  let rank {ε : ℝ} (Fm : FamP ε) (hc : D3 3 h.𝒜 Fm) :=
    RankOfDivisionKernel sel selS selP selDH selC (kernelChoiceOfSelection selB)
      (indefiniteRealisationChoiceOfSelection selB) h.hPA Fm hc
  have bridge : Closed (D3 3 h.𝒜) fun Fm CH => ∀ hc : D3 3 h.𝒜 Fm, TuSize Fm → DGamSize Fm →
      Formalism.L2.DIV.DivisionKernelConstantBounds Fm (rank Fm hc) 2 CH := by
    apply (rest.and ((Closed.of_class fun Fm _ hc => cut_of_stable (h.hMt Fm (d3_a hc))).and
      (rows.and (oneMap.and (hCsz.and (admissible.and (h.aC2.and count))))))).imp
    intro _ Fm CH _ data hc hTu hDGam
    obtain ⟨r, cut, rr, om, cz, adm, c2, c5⟩ := data
    exact (r hc hTu hDGam).toRows_alt (fun hN => GlobalTheory.Top.wire_sel_alt h.𝒜 sel selS selP selDH selC
      selB h.hTw h.hPA dv h.hDcPtG Fm hc CH cz hDGam (rr hc) (om hc) (r hc hTu hDGam).bu hN)
      cut adm (complement_two_of_items c2) c5
  have divisibility := Formalism.L2.DIV.closed_linkDIVt_of_closed_bridge_kernel (D3 3 h.𝒜) 2 rank bridge
  have irreducible := GlobalTheory.Top.Irr.closed_linkIRR_of_join_count green h.𝒜 sel h.cIc h.hcI h.irrC
  have spectral := GlobalTheory.Top.link_alt_alt_bis h.𝒜 sel selS h.hWu h.hRF h.hTF
    h.c30 h.hc30 h.sTy h.sNG h.sM h.sLp h.sO h.h30 h.hInstR
  have sizes : Closed (D3 3 h.𝒜) fun Fm _ => TuSize Fm ∧ DGamSize Fm :=
    Closed.of_class fun _ _ hc => hc.2.2
  have sub {ε : ℝ} (Fm : FamP ε) (hc : D3 3 (fun Fm => h.𝒜 Fm ∧ (GChi PChar.one).cls (3/2) Fm) Fm) :
      D3 3 h.𝒜 Fm := ⟨⟨⟨⟨hc.1.1.1.1.1, hc.1.1.1.2⟩, hc.1.1.2⟩, hc.1.2⟩, hc.2⟩
  apply rh_of_principal_archived_bundle_choices hs hd 2 (by norm_num)
  exact (Pk.Closed.sub (h.nRest.and (irreducible.and (divisibility.and (spectral.and sizes)))) sub).imp
    fun _ _ _ ⟨hn, hi, hv, hS, hTu, hDGam⟩ _ _ => ⟨hn, hi, hv hTu hDGam, hS hTu⟩

end RiemannGaussian.AlpogeWindow

namespace RiemannGaussian.AlpogeWindow

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk

open Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT

open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc

open Formalism.MainNotions.StandardLattice.HarishChandraReduction

set_option maxHeartbeats 3500000 in

set_option synthInstance.maxHeartbeats 200000 in

theorem principal_archived_row_selection
    {KP : ∀ B : Base, Fr B.toPre → Prop} {Q Q' : V4.Slot}
    {Lk : LkT BundleCondition} {N : FamClass → Prop} {DR : R1.DefiniteSideType} :
    StandardLattice.SiegelMassRatioCM → LitThin → Formalism.L2.SG.Pf.WuDecayOfGap →
    Formalism.L2.SG.RowsDef.RowsFinDim → Formalism.L2.SG.RowsPos.TypeP →
    Formalism.L2.SG.RowsPos.RowNGP → Formalism.L2.SG.RowsPos.RowMainEqP →
    (∀ D, MassRatioUnderVolume D) → (∀ D, GenusMassVolumes.GenusMassAt D 2) →
    (DC.MinkDiv → GroupRetwisting.BaseCond KP ∧ GroupRetwisting.FirstG KP Q ∧
      GroupRetwisting.ExportF KP Q ∧ GroupRetwisting.SecondG KP Q Q') →
    ExBL KP Q Q' Lk → AllRowsAlt KP Q Q' Lk N DR →
    ∃ h : HypsAlt N DR, IsSel Q' Lk (fun _ _ _ _ _ => True) h.𝒜 h.σ ∧
      (DC.MinkDiv → UpperTheory.Top.ExD h.𝒜 (fun _ => cTmin)) := by
  intro hP hLit hWu hRF hTy hNG hM hU hG hc hx hA
  obtain ⟨R30, hR30, c30, cIc, hb30, hpos, r30⟩ := hA.c30
  have rTu := Row.rowL (KP := KP) (Q := Q) largeBaseProperty_true (_root_.GlobalTheory.Fc.row_hTu_cTmin_alt hU hG Q' Lk)
  have hall := RowL.and (hA.hn4 : RowL KP Q Q' Lk fun 𝒜 _ => R0.ClassCountBoundAllPoints 𝒜) <|
    RowL.and (hA.jOn : RowL KP Q Q' Lk fun 𝒜 _ => R0.H_jOn 𝒜) <|
    RowL.and (hA.hInstR : RowL KP Q Q' Lk fun 𝒜 _ => ClassTwoEntries.H_hInstR 𝒜) <|
    RowL.and (hA.aC2 : RowL KP Q Q' Lk fun 𝒜 _ => ClassTwoEntries.DivisionSecondComplementAdmissible 𝒜) <|
    RowL.and (hA.aP10 : RowL KP Q Q' Lk fun 𝒜 _ => AllBundlePointProperties.LevelPrimeColumnValuationsClosed 𝒜) <|
    RowL.and (hA.aAtG : RowL KP Q Q' Lk fun 𝒜 _ => AllBundlePointProperties.H_aAtG 𝒜) <|
    RowL.and (hA.aPt0 : RowL KP Q Q' Lk fun 𝒜 _ => PeriodEntriesOverColumns.ReferenceChainEvaluationAdmissible 𝒜) <|
    RowL.and (hA.aPtTw : RowL KP Q Q' Lk fun 𝒜 _ => PeriodEntriesOverColumns.H_aPtTw 𝒜) <|
    RowL.and (hA.aPer0 : RowL KP Q Q' Lk fun 𝒜 _ => PeriodEntriesOverColumns.H_aPer0 𝒜) <|
    RowL.and (hA.aPerTw : RowL KP Q Q' Lk fun 𝒜 _ => PeriodEntriesOverColumns.H_aPerTw 𝒜) <|
    RowL.and (hA.tie : RowL KP Q Q' Lk fun 𝒜 _ => PeriodEntriesOverColumns.H_tie 𝒜) <|
    RowL.and (hA.hRB : RowL KP Q Q' Lk (AtAll _root_.GlobalTheory.Fc.R1.P_hRB_alt)) <|
    RowL.and (hA.hTw : RowL KP Q Q' Lk (AtAll _root_.GlobalTheory.Fc.R1.TwistBundleCondition)) <|
    RowL.and (hA.hPA : RowL KP Q Q' Lk (AtAll _root_.GlobalTheory.Fc.R1.PrimitivityBundleCondition)) <|
    RowL.and (hA.hLamP : RowL KP Q Q' Lk (AtAll _root_.GlobalTheory.Fc.R1.LambdaPrimeBundleCondition)) <|
    RowL.and (hA.hDivG : RowL KP Q Q' Lk (AtAll _root_.GlobalTheory.Fc.R1.DivisorBundleCondition)) <|
    RowL.and (hA.hDcPtG : RowL KP Q Q' Lk (AtAll _root_.GlobalTheory.Fc.R1.DecompositionPointBundle)) <|
    RowL.and (hA.selJ : RowL KP Q Q' Lk (AtAll _root_.GlobalTheory.Fc.R1.SelectionJumpBundleCondition)) <|
    RowL.and (hA.sLp : RowL KP Q Q' Lk _root_.GlobalTheory.Fc.R1.SelectionLpBound) <|
    RowL.and (hA.sO : RowL KP Q Q' Lk _root_.GlobalTheory.Fc.R1.SelectionOrderBound) <|
    RowL.and (hA.hServ : RowL KP Q Q' Lk _root_.GlobalTheory.Fc.R1.SelectionServesFamily) <|
    RowL.and (hA.zL : RowL KP Q Q' Lk _root_.GlobalTheory.Fc.R1.SelectionZeroLocus) <|
    RowL.and (hA.hTF : RowL KP Q Q' Lk fun 𝒜 _ => R1.H_hTF 𝒜) <|
    RowL.and (hA.rRows : RowL KP Q Q' Lk (_root_.GlobalTheory.Fc.R1.SelectionDefiniteRows DR)) <|
    RowL.and (hA.nRest : RowL KP Q Q' Lk fun 𝒜 _ => N (GlobalTheory.Cp.D3 3 𝒜)) <|
    RowL.and (⟨R30, hR30, r30⟩ : RowL KP Q Q' Lk _) rTu
  obtain ⟨𝒜, σ, hE, hD, hs, hn4, jOn, hInstR, aC2, aP10, aAtG, aPt0, aPtTw, aPer0, aPerTw, tie, hRB, hTw, hPA, hLamP, hDivG,
    hDcPtG, selJ, sLp, sO, hServ, zL, hTF, rRows, nRest, ⟨h30, irrC⟩, hTu⟩ :=
    UpperTheory.Top.classSel hP (fun D => hU D) KP Q Q' _root_.GlobalTheory.Fc.BundleCondition Lk _ (fun _ => cTmin) hc hx hall
  have s3 : ∀ {eps : ℝ} (Fm : FamP eps), GlobalTheory.Cp.D3 3 𝒜 Fm → W3 𝒜 Fm := fun Fm h => ((GlobalTheory.Fc.copies_frozen.1 𝒜 _ Fm).1).1 h
  have s1 : ∀ {eps : ℝ} (Fm : FamP eps), Formalism.MainNotions.WithTw (Formalism.MainNotions.WithSm (GlobalTheory.Cp.WithChN 𝒜)) Fm → W1 𝒜 Fm :=
    fun Fm h => ((GlobalTheory.Fc.copies_frozen.1 𝒜 _ Fm).2).1 h
  let h : HypsAlt N DR := {
    𝒜 := 𝒜
    σ := σ
    cT := fun _ => cTmin
    hEx := fun hM la G hla hH => working_classes_frozen.2 _ _ (fun hM' => hE hM' la G hla hH) hM
    hduty := fun Fm h => GlobalTheory.Fc.copies_frozen.2 _ Fm (hD _ Fm h).1
    hRB := fun Fm hc x hx _ i => hRB Fm hc x hx i
    hTw := fun Fm hc x hx _ i => hTw Fm hc x hx i
    hPA := fun Fm hc x hx _ i => hPA Fm hc x hx i
    hLamP := fun Fm hc x hx _ i => hLamP Fm hc x hx i
    hDivG := fun Fm hc x hx _ i => hDivG Fm hc x hx i
    hDcPtG := fun Fm hc x hx _ i => hDcPtG Fm hc x hx i
    hTu := hTu
    hn4 := Formalism.MainNotions.Pk.Closed.sub hn4 s1
    hLit := hLit
    hWu := hWu
    hRF := hRF
    hTF := hTF
    c30 := c30
    hc30 := hb30
    sTy := hTy
    sNG := hNG
    sM := hM
    sLp := sLp
    sO := sO
    h30 := h30
    hInstR := fun Fm hc x hx _ i => hInstR Fm hc x hx i
    selJ := fun Fm hc x hx _ i => Classical.choice (selJ Fm hc x hx i)
    jOn := Formalism.MainNotions.Pk.Closed.sub jOn s3
    hMt := fun Fm h => (hD _ Fm h).2
    rRows := rRows
    aPt0 := Formalism.MainNotions.Pk.Closed.sub aPt0 s3
    aPtTw := Formalism.MainNotions.Pk.Closed.sub aPtTw s3
    aPer0 := Formalism.MainNotions.Pk.Closed.sub aPer0 s3
    aPerTw := Formalism.MainNotions.Pk.Closed.sub aPerTw s3
    aP10 := Formalism.MainNotions.Pk.Closed.sub aP10 s3
    aAtG := Formalism.MainNotions.Pk.Closed.sub aAtG s3
    aC2 := Formalism.MainNotions.Pk.Closed.sub aC2 s3
    hServ := hServ
    cIc := cIc
    hcI := hpos
    irrC := irrC
    zL := zL
    tie := Formalism.MainNotions.Pk.Closed.sub tie s3
    hU := hU
    hG := hG
    nRest := nRest }
  exact ⟨h, hs, hE⟩

end RiemannGaussian.AlpogeWindow

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

structure OpenLiteratureStatements : Prop where
  caraianiLocalGlobalDual : _root_.UpperTheory.One.M.Row
  localLanglandsExists : _root_.UpperTheory.Zero.LLC.RecTExists
  galoisRepOfPolarizedPairLit : _root_.UpperTheory.One.M.Row

theorem siegel_klingen_deligne_ribet_of_literature (_O : OpenLiteratureStatements) : GlobalTheory.Published.SiegelKlingenDeligneRibet :=
  GlobalTheory.siegelKlingenDeligneRibet_of_both PositivityTheory.Prw.siegelKlingen_holds PositivityTheory.PfDRL.deligneRibet

theorem join_out_of_literature (O : OpenLiteratureStatements) : GlobalTheory.Mem.LiteralAutomorphy.JoinOut :=
  GlobalTheory.JoinFun.joinOut_of_five PositivityTheory.Prw.ellipticMainTheoremCM_holds GlobalTheory.Laid.hcfj_holds (siegel_klingen_deligne_ribet_of_literature O) PositivityTheory.Prw.partialZetaFunctionalEquation_holds GlobalTheory.CompanionTheory.HeckeFE.heckeTateFunctionalEquation

theorem algebraic_character_wd_of_literature (_O : OpenLiteratureStatements) : GlobalTheory.Published.AlgebraicCharacterWD :=
  UpperTheory.Lit.CharWD.algebraicCharacterWD GlobalTheory.globalArtinReciprocity_holds UpperTheory.Lit.heckeLAdicCharacterDeRham GlobalTheory.deRham_potentiallySemistable

theorem ar_calc_of_literature (_O : OpenLiteratureStatements) : GlobalTheory.Published.ArCalc :=
  GlobalTheory.ArithmeticHeightTower.ArakelovDirectHeights.arCalc_direct PositivityTheory.Tls2.Pl.poincareLelong PositivityTheory.ResPlug.FromRes.resK

theorem ar_degree_of_literature (_O : OpenLiteratureStatements) : GlobalTheory.Published.ArDegree :=
  GlobalTheory.Published.arDegree_of_heightProjection (GlobalTheory.Published.CycleHeights.heightProjection (GlobalTheory.ArithmeticHeightTower.ArakelovDirectHeights.cycleHeights_direct PositivityTheory.Tls2.Pl.poincareLelong PositivityTheory.ResPlug.FromRes.resK)) GlobalTheory.ChernDegree.chernDegreeComplex

theorem arith_hilbert_samuel_of_literature (_O : OpenLiteratureStatements) : GlobalTheory.Published.ArithHilbertSamuel :=
  GlobalTheory.arithHilbertSamuel_of_principalisation PositivityTheory.ResPlug.WeightsCompactStabilizer.principalisation_closed

theorem base_change_definite_unitary_group_of_literature (_O : OpenLiteratureStatements) : GlobalTheory.Published.BaseChangeDefiniteUnitaryGroup :=
  UpperTheory.BaseChangeIdentities.definiteN_of UpperTheory.BaseChangeIdentities.baseChangeN

theorem bhatt_scholze_crystalline_lattices_of_literature (_O : OpenLiteratureStatements) : GlobalTheory.Published.BhattScholzeCrystallineLattices :=
  (GlobalTheory.bhattScholze_coeff GlobalTheory.BSP.bhattScholzeIntegral)

theorem ess_square_integrable_segments_of_literature (_O : OpenLiteratureStatements) : GlobalTheory.Published.EssSquareIntegrableSegments :=
  PositivityTheory.Exh.essSquareIntegrableSegments_of_seg (PositivityTheory.RgGu.segmentRepresentation)

theorem pair_u_of_literature (O : OpenLiteratureStatements) : _root_.UpperTheory.GalS.PairUAlt :=
  _root_.UpperTheory.GalS.field_of_starFull_alt O.localLanglandsExists DiscreteGroups.sglob.LConv.localConverseGL (PositivityTheory.Exh.langlandsExhaustionGL_of_seg (PositivityTheory.RgGu.segmentRepresentation)) O.galoisRepOfPolarizedPairLit

theorem gelfand_kazhdan_dual_of_literature (_O : OpenLiteratureStatements) : GlobalTheory.Published.GelfandKazhdanDual :=
  PositivityTheory.JMult1.gelfandKazhdanDual_of_rigidity PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity RfCs.cuspidalSpectrumGL.2.2

theorem generic_unlinked_gl_of_literature (_O : OpenLiteratureStatements) : GlobalTheory.Published.GenericUnlinkedGL :=
  GlobalTheory.RgGu.genericUnlinkedGL_of_segRep2 (PositivityTheory.RgGu.segmentRepresentation)

theorem grothendieck_ring_polynomial_of_literature (_O : OpenLiteratureStatements) : GlobalTheory.Published.GrothendieckRingPolynomial :=
  PositivityTheory.Groth.grothendieckRingPolynomial_of_seg (PositivityTheory.RgGu.segmentRepresentation)

theorem zelevinsky_polynomial_ring_of_literature (O : OpenLiteratureStatements) : GlobalTheory.Published.ZelevinskyPolynomialRing :=
  PositivityTheory.Prw.zelevinskyPolynomialRing_of PositivityTheory.Prw.bernsteinZelevinskyFiniteness_holds PositivityTheory.RgGu.segmentRepresentation (grothendieck_ring_polynomial_of_literature O)

theorem depth_zero_induction_of_literature (O : OpenLiteratureStatements) : GlobalTheory.Published.DepthZeroInduction :=
  (GlobalTheory.DepthZeroPass.depthZeroInduction GlobalTheory.CompanionTheory.GeoLink.geometricLemma PositivityTheory.Prw.bernsteinZelevinskyFiniteness_holds (zelevinsky_polynomial_ring_of_literature O))

theorem langlands_exhaustion_gl_of_literature (_O : OpenLiteratureStatements) : GlobalTheory.Published.LanglandsExhaustionGL :=
  PositivityTheory.Exh.langlandsExhaustionGL_of_seg (PositivityTheory.RgGu.segmentRepresentation)

theorem langlands_multisegments_of_literature (_O : OpenLiteratureStatements) : GlobalTheory.Published.LanglandsMultisegments :=
  PositivityTheory.Exh.langlandsMultisegments_of_seg (PositivityTheory.RgGu.segmentRepresentation)

theorem standard_cosocle_gl_of_literature (_O : OpenLiteratureStatements) : GlobalTheory.Published.StandardCosocleGL :=
  PositivityTheory.Exh.standardCosocleGL_of_seg (PositivityTheory.RgGu.segmentRepresentation)

theorem local_langlands_gl_recT_exists_of_literature (O : OpenLiteratureStatements) : _root_.UpperTheory.Zero.LLC.RecTExists :=
  _root_.UpperTheory.One.M.New.llOf_alt O.localLanglandsExists DiscreteGroups.sglob.LConv.localConverseGL (depth_zero_induction_of_literature O) GlobalTheory.BrauerZero.brauerDegreeZero GlobalTheory.Published.chevalleyUnits' GlobalTheory.globalArtinReciprocity_holds (langlands_exhaustion_gl_of_literature O) (langlands_multisegments_of_literature O) (standard_cosocle_gl_of_literature O) (zelevinsky_polynomial_ring_of_literature O) GlobalTheory.CompanionTheory.GeoLink.geometricLemma PositivityTheory.Prw.bernsteinZelevinskyFiniteness_holds

theorem tempered_product_of_square_integrable_of_literature (O : OpenLiteratureStatements) : GlobalTheory.Published.TemperedProductOfSquareIntegrable :=
  UpperTheory.Lit.Cas.temperedProduct GlobalTheory.CompanionTheory.GeoLink.geometricLemma PositivityTheory.Prw.bernsteinZelevinskyFiniteness_holds PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top PositivityTheory.Tls2.BZGL.standardFunctorsFiniteLength_top (langlands_exhaustion_gl_of_literature O) (standard_cosocle_gl_of_literature O) (langlands_multisegments_of_literature O) (ess_square_integrable_segments_of_literature O)

theorem cusp_trace_class_of_literature (_O : OpenLiteratureStatements) : GlobalTheory.Published.CuspTraceClass :=
  PositivityTheory.Prw.cuspTraceClass_of PositivityTheory.Prw.dixmierMalliavinFactorisation_holds

theorem cycle_heights_of_literature (_O : OpenLiteratureStatements) : GlobalTheory.Published.CycleHeights :=
  GlobalTheory.ArithmeticHeightTower.ArakelovDirectHeights.cycleHeights_direct PositivityTheory.Tls2.Pl.poincareLelong PositivityTheory.ResPlug.FromRes.resK

theorem doubling_method (_O : OpenLiteratureStatements) : GlobalTheory.Published.DoublingMethodLocalZetaIntegrals :=
  ResidueKilled.dm_of_two GlobalTheory.RapidDecay.cuspRapidDecay PositivityTheory.RgEis.Sp.Hd.siegelEisensteinContinuation trivial

theorem flath_factorisation_of_literature (_O : OpenLiteratureStatements) : GlobalTheory.Published.FlathFactorisation :=
  GlobalTheory.flathFactorisation_of_tensorProduct CompanionTheory.Rg.Fl.B.flathTensorProduct CompanionTheory.Rg.Fl.B.unitaryIrreducibleAdmissible

theorem cusp_u_of_literature (O : OpenLiteratureStatements) : _root_.UpperTheory.GalS.CuspUAlt :=
  (_root_.UpperTheory.GalS.bridgeStar_alt (gelfand_kazhdan_dual_of_literature O)).2 (pair_u_of_literature O)

theorem green_series_st_of_literature (_O : OpenLiteratureStatements) : GlobalTheory.Published.GreenSeriesSt :=
  GlobalTheory.GreenSeries.green_series PositivityTheory.GreenCharacters.greenCuspidal

theorem grothendieck_deformation_of_literature (_O : OpenLiteratureStatements) : GlobalTheory.Published.GrothendieckDeformation :=
  GlobalTheory.Published.grothendieckDeformation_of_lifting GlobalTheory.abelianDeRham GlobalTheory.abelianScheme_hom_lifting_nilpotent_dividedPowers

theorem grothendieck_messing_of_literature (O : OpenLiteratureStatements) : GlobalTheory.Published.GrothendieckMessing :=
  GlobalTheory.Published.GrothendieckDeformation.grothendieckMessing (grothendieck_deformation_of_literature O)

theorem harish_chandra_analyticity_of_literature (_O : OpenLiteratureStatements) : GlobalTheory.Published.HarishChandraAnalyticity :=
  GlobalTheory.CompanionTheory.Hypotheses₂.harishChandra_analyticity_density

theorem hecke_l_adic_character_crystalline_of_literature (O : OpenLiteratureStatements) : GlobalTheory.Published.HeckeLAdicCharacterCrystalline :=
  _root_.GlobalTheory.Published.CharCrysModel.of_hypotheses_m_alt UpperTheory.Lit.heckeLAdicCharacterDeRham GlobalTheory.deRham_potentiallySemistable (algebraic_character_wd_of_literature O) (local_langlands_gl_recT_exists_of_literature O)

theorem hecke_l_adic_character_above_of_literature (O : OpenLiteratureStatements) : GlobalTheory.Published.HeckeLAdicCharacterAbove :=
  GlobalTheory.HeckeAboveBridge.heckeLAdicCharacterAbove_of_potSemistable UpperTheory.Lit.heckeLAdicCharacterDeRham (hecke_l_adic_character_crystalline_of_literature O) GlobalTheory.deRham_potentiallySemistable

theorem hecke_l_adic_parameter_above_of_literature (O : OpenLiteratureStatements) : _root_.GlobalTheory.Published.HeckeLAdicParameterAboveAlt :=
  (_root_.GlobalTheory.heckeLAdicParameterAbove_of_algebraicCharacterWD_alt (algebraic_character_wd_of_literature O))

theorem kawamata_viehweg_of_literature (_O : OpenLiteratureStatements) : GlobalTheory.Published.KawamataViehweg :=
  GlobalTheory.KVFromPair.kawamataViehweg_of_nadelVanishingPair (GlobalTheory.nefNumerics_outright) (And.left (NadelVanishingSeparation.NSI.nadelVanishingAndNonKltDivisor))

theorem landherr_st_of_literature (_O : OpenLiteratureStatements) : GlobalTheory.Published.LandherrSt :=
  (GlobalTheory.QNorm.landherr_and_landherrSt).2

theorem carU_local_global_of_literature (O : OpenLiteratureStatements) : _root_.UpperTheory.GalS.CarUAlt :=
  (_root_.UpperTheory.GalS.ofDual_star_alt (PositivityTheory.PRW.GKD.gelfandKazhdanDual_of_multiplicityOne PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity PositivityTheory.jumpWindows.cuspidalMultiplicityOne GlobalTheory.CompanionTheory.CuspFinGL.cuspFormsBoundedGL) O.caraianiLocalGlobalDual)

theorem carU_above_l_of_literature (O : OpenLiteratureStatements) : _root_.UpperTheory.GalS.CarUAlt :=
  (_root_.UpperTheory.GalS.carU_of_finite_gl_recT CuspFormAutomorphicBounds.automorphicFormsFiniteGL (local_langlands_gl_recT_exists_of_literature O) (carU_local_global_of_literature O))

theorem ray_character_artin_of_literature (_O : OpenLiteratureStatements) : GlobalTheory.Published.RayCharacterArtin :=
  GlobalTheory.Published.GlobalArtinReciprocity.rayCharacterArtin GlobalTheory.globalArtinReciprocity_holds

theorem regular_algebraic_purity_of_literature (_O : OpenLiteratureStatements) : GlobalTheory.Published.RegularAlgebraicPurity :=
  (GlobalTheory.regularAlgebraicPurity_of_clozel PositivityTheory.Lit1.ClozelPurity.clozelPurity PositivityTheory.Rg.Cz.clozelCohomological)

theorem square_integrable_segment_of_literature (O : OpenLiteratureStatements) : GlobalTheory.Published.SquareIntegrableSegment :=
  PositivityTheory.Prw.squareIntegrableSegment_of (ess_square_integrable_segments_of_literature O)

theorem totally_disjoint_product_irreducible_of_literature (_O : OpenLiteratureStatements) : GlobalTheory.Published.TotallyDisjointProductIrreducible :=
  PositivityTheory.SlGl.totallyDisjointProductIrreducible_of_parts (GlobalTheory.geometricLemma_of_filtration PositivityTheory.Prw.bernsteinZelevinskyFiniteness_holds PositivityTheory.Geo.geometricLemmaFiltration) (PositivityTheory.RgGu.segmentRepresentation) (PositivityTheory.Groth.grothendieckRingPolynomial_of_seg (PositivityTheory.RgGu.segmentRepresentation))

theorem unlinked_product_irreducible_of_literature (O : OpenLiteratureStatements) : GlobalTheory.Published.UnlinkedProductIrreducible :=
  (GlobalTheory.TotDisjUnlinked.main (totally_disjoint_product_irreducible_of_literature O))

theorem vol_ge_of_literature (O : OpenLiteratureStatements) : GlobalTheory.Published.VolGe :=
  GlobalTheory.VolBr.volGe_of_hilbertSamuel (arith_hilbert_samuel_of_literature O) (ar_calc_of_literature O) GlobalTheory.nefNumerics_outright

theorem vol_nef_of_literature (O : OpenLiteratureStatements) : GlobalTheory.Published.VolNef :=
  GlobalTheory.Published.ArithHilbertSamuel.volNef (arith_hilbert_samuel_of_literature O)

theorem zarhin_statement (_O : OpenLiteratureStatements) : GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement :=
  PositivityTheory.HtPt.Narrow.zarhin GlobalTheory.dualAbelianScheme

theorem greenberg_wiles_of_literature (_O : OpenLiteratureStatements) : ReciprocityTheory.Gal.GreenbergWiles :=
  GlobalTheory.CompanionTheory.GreenbergWiles.Assembly.greenbergWiles_of_poitouTate PositivityTheory.Lit1.PTN.poitouTateNormalised_holds PositivityTheory.Lit1.GEN.globalEulerChar_full GlobalTheory.CompanionTheory.Hypotheses₂.localTateDuality GlobalTheory.CompanionTheory.Hypotheses₂.LocalEuler.localEulerChar_holds GlobalTheory.CompanionTheory.Hypotheses₂.localFiniteness

theorem literature_local (O : OpenLiteratureStatements) : _root_.GlobalTheory.Mem.LiteralAutomorphy.LocalRepresentationTheoryHypothesesAlt where
  bz := PositivityTheory.Prw.bernsteinZelevinskyFiniteness_holds
  bern := PositivityTheory.RgUd.All.bernsteinUnitaryProductIrreducible
  geo := GlobalTheory.CompanionTheory.GeoLink.geometricLemma
  zel := (zelevinsky_polynomial_ring_of_literature O)
  disj := (totally_disjoint_product_irreducible_of_literature O)
  mp := PositivityTheory.Prw.moyPrasadJacquetIso_holds
  temp := (tempered_product_of_square_integrable_of_literature O)
  seg := (ess_square_integrable_segments_of_literature O)
  sq := (square_integrable_segment_of_literature O)
  gen := (generic_unlinked_gl_of_literature O)
  multi := (langlands_multisegments_of_literature O)
  exh := (langlands_exhaustion_gl_of_literature O)
  cos := (standard_cosocle_gl_of_literature O)
  llc := O.localLanglandsExists
  conv := DiscreteGroups.sglob.LConv.localConverseGL
  dzi := (depth_zero_induction_of_literature O)
  brauer := GlobalTheory.BrauerZero.brauerDegreeZero
  chev := GlobalTheory.Published.chevalleyUnits'
  green := PositivityTheory.Stage1.PM.greenRegularCharacters

theorem literature_automorphy (O : OpenLiteratureStatements) : _root_.GlobalTheory.Mem.LiteralAutomorphy.GlobalAutomorphicGaloisHypotheses' where
  decay := GlobalTheory.RapidDecay.cuspRapidDecay
  hc := PositivityTheory.RgHf.harishChandraFinite
  fin := CuspFormAutomorphicBounds.automorphicFormsFiniteGL
  js := PositivityTheory.AdelicQuotientData.jacquetShalika
  cusp := RfCs.cuspidalSpectrumGL
  bc := UpperTheory.BaseChangeIdentities.baseChangeN
  gk := (gelfand_kazhdan_dual_of_literature O)
  gal := (pair_u_of_literature O)
  car := O.caraianiLocalGlobalDual
  pur := PositivityTheory.Lit1.ClozelPurity.clozelPurity
  coh := PositivityTheory.Rg.Cz.clozelCohomological
  art := GlobalTheory.globalArtinReciprocity_holds
  ray := PositivityTheory.Stage1.PM.rayClassFieldSt
  chA := (hecke_l_adic_character_above_of_literature O)
  chW := (algebraic_character_wd_of_literature O)
  berger := GlobalTheory.deRham_potentiallySemistable

theorem literature_cohomology (O : OpenLiteratureStatements) : GlobalTheory.Mem.LiteralAutomorphy.LitCoh where
  pt := PositivityTheory.Lit1.PTN.poitouTateNormalised_holds
  lf := GlobalTheory.CompanionTheory.Hypotheses₂.localFiniteness
  lt := GlobalTheory.CompanionTheory.Hypotheses₂.localTateDuality
  le := GlobalTheory.CompanionTheory.Hypotheses₂.LocalEuler.localEulerChar_holds
  gf := PositivityTheory.Lit1.GF.globalFiniteness
  ge := PositivityTheory.Lit1.GEN.globalEulerChar_full
  uo := GlobalTheory.CompanionTheory.Hypotheses₂.unramifiedOrthogonality
  gw := (greenberg_wiles_of_literature O)
  lfK := CompanionTheory.LocalTateOrthogonality.Gcoh.top_locfin
  ltK := CompanionTheory.LocalTateOrthogonality.Gcoh.top_tate
  leK := CompanionTheory.LocalTateOrthogonality.Gcoh.top_euler
  bk := GlobalTheory.CompanionTheory.Hypotheses₂.BK.blochKatoLocal

theorem literature_nonexistence (O : OpenLiteratureStatements) : _root_.GlobalTheory.Mem.LiteralAutomorphy.NonEndoscopicHypothesesAlt where
  loc := (literature_local O)
  aut := (literature_automorphy O)
  coh := (literature_cohomology O)
  join := (join_out_of_literature O)
  fe := GlobalTheory.CompanionTheory.HeckeFE.heckeTateFunctionalEquation

theorem published_results_analytic (O : OpenLiteratureStatements) : GlobalTheory.NRows.GeometricGaloisRepCompatibility where
  weil := GlobalTheory.weilRepresentationUnitaryPair
  ds := CompanionTheory.RgDs.B.discreteSeriesExists
  ana := (harish_chandra_analyticity_of_literature O)
  dsc := CompanionTheory.RgExh.discreteSeriesClassification
  trc := (cusp_trace_class_of_literature O)
  dm := PositivityTheory.DM.dixmierMalliavinFactorisation_holds
  flath := (flath_factorisation_of_literature O)
  sw := UpperTheory.Lit.Sw47.weilUnitary
  dbl := (doubling_method O)
  udbl := GlobalTheory.UnramDoublingProof.unramifiedDoublingGL
  hl := GlobalTheory.Published.HeckeLPartialContinuation_holds
  ht := GlobalTheory.HtCardProof.htCard

theorem published_results_local (_O : OpenLiteratureStatements) : GlobalTheory.NLink.Hypotheses₂ where
  font := GlobalTheory.MemLoc.fontaineBcris
  artin := GlobalTheory.globalArtinReciprocity_holds
  bk := GlobalTheory.CompanionTheory.Hypotheses₂.BK.blochKatoLocal
  tate := CompanionTheory.LocalTateOrthogonality.Gcoh.top_tate
  euler := CompanionTheory.LocalTateOrthogonality.Gcoh.top_euler
  fin := CompanionTheory.LocalTateOrthogonality.Gcoh.top_locfin
  bs := GlobalTheory.BSP.bhattScholzeIntegral

theorem published_results_eigen (O : OpenLiteratureStatements) : _root_.GlobalTheory.Fc.S0.UnitaryGroupThirdPlaceHypotheses where
  clozelCohomological := PositivityTheory.Rg.Cz.clozelCohomological
  greenCuspidal := PositivityTheory.GreenCharacters.greenCuspidal
  heckeLAdicCharacter := PositivityTheory.Stage1.PM.heckeLAdicCharacter
  chebotarevDegreeOne := GlobalTheory.Published.chebotarevDegreeOne'
  galoisRepOfPolarizedCuspidal := (cusp_u_of_literature O)
  baseChangeDefiniteUnitary := (base_change_definite_unitary_group_of_literature O)
  bhattScholzeCrystallineLattices := (bhatt_scholze_crystalline_lattices_of_literature O)
  heckeLAdicCharacterAbove := (hecke_l_adic_character_above_of_literature O)
  cuspRapidDecay := GlobalTheory.RapidDecay.cuspRapidDecay
  weilSiegelFormulaUnitary := UpperTheory.Lit.Sw47.weilUnitary
  siegelWeilUnitaryConvergent := UpperTheory.Lit.Sw47.convergent
  doublingMethod := (doubling_method O)
  unramifiedDoublingGL := GlobalTheory.UnramDoublingProof.unramifiedDoublingGL
  bernsteinZelevinskyFiniteness := PositivityTheory.Prw.bernsteinZelevinskyFiniteness_holds
  formalDegreeCompactDual := PositivityTheory.RgFd.B.formalDegreeCompactDual
  bernsteinUnitaryProductIrreducible := PositivityTheory.RgUd.All.bernsteinUnitaryProductIrreducible
  geometricLemmaFiltration := GlobalTheory.geometricLemmaFiltration_holds
  unlinkedProductIrreducible := (unlinked_product_irreducible_of_literature O)
  depthZeroJacquetInjective := GlobalTheory.DepthZeroJac.depthZeroJacquetInjective
  jacquetShalika := PositivityTheory.AdelicQuotientData.jacquetShalika
  automorphicFormsFiniteGL := CuspFormAutomorphicBounds.automorphicFormsFiniteGL
  localGlobalAboveL := (carU_above_l_of_literature O)
  regularAlgebraicPurity := (regular_algebraic_purity_of_literature O)
  globalArtinReciprocity := GlobalTheory.globalArtinReciprocity_holds
  heckeLAdicParameterAbove := (hecke_l_adic_parameter_above_of_literature O)
  deRhamPotSemistable := GlobalTheory.deRham_potentiallySemistable
  harishChandraFinite := PositivityTheory.RgHf.harishChandraFinite
  greenRegularCharacters := PositivityTheory.Stage1.PM.greenRegularCharacters
  zelevinskyPolynomialRing := (zelevinsky_polynomial_ring_of_literature O)
  rayClassFieldSt := PositivityTheory.Stage1.PM.rayClassFieldSt
  rayCharacterArtin := (ray_character_artin_of_literature O)
  genericUnitaryDualGL := PositivityTheory.Gud.Fin.genericUnitaryDualGL_holds
  standardCosocleGL := (standard_cosocle_gl_of_literature O)
  cheb := GlobalTheory.Published.cheb_holds
  discreteSeriesCover := CompanionTheory.RgExh.discreteSeriesCover
  harishChandraModules := GlobalTheory.HcPort.print_harishChandraModules
  casselmanWallach := PositivityTheory.CWB.casselmanWallach
  weilRepresentationUnitaryPair := GlobalTheory.weilRepresentationUnitaryPair
  discreteSeriesExists := CompanionTheory.RgDs.B.discreteSeriesExists
  discreteSeriesClassification := CompanionTheory.RgExh.discreteSeriesClassification
  strongApproxSU := GlobalTheory.StrongApproxSUProof.strongApproxSU
  siegelWeilUnitaryConvergent2 := GlobalTheory.CompanionTheory.SW.siegelWeilUnitaryConvergent
  harishChandraAnalyticity := (harish_chandra_analyticity_of_literature O)
  cuspTraceClass := (cusp_trace_class_of_literature O)
  dixmierMalliavinFactorisation := PositivityTheory.DM.dixmierMalliavinFactorisation_holds
  flathFactorisation := (flath_factorisation_of_literature O)
  cMCurveGoodOutsidePrimeSt := GlobalTheory.Published.cmCurveGoodOutsidePrime
  weberRayFieldSt := PositivityTheory.Prw.weberRayFieldSt_holds
  discreteSeriesCoverExists := CompanionTheory.RgDs.B.discreteSeriesCoverExists
  siegelWeilUnitarySchrodinger := PositivityTheory.SiegelWeilCoefficients.field
  siegelEisensteinContinuation := PositivityTheory.RgEis.Sp.Hd.siegelEisensteinContinuation
  siegelEisensteinSimplePole := trivial
  schurOrthogonalitySquareIntegrable := GlobalTheory.Published.schurOrthogonalitySquareIntegrable'
  litN := (literature_nonexistence O)
  toHypothesesX := (published_results_analytic O)
  nLink := (published_results_local O)
  depthZeroSupport' := GlobalTheory.SmGL.depthZeroSupport
  localFiniteness := GlobalTheory.CompanionTheory.Hypotheses₂.localFiniteness
  localTateDuality := GlobalTheory.CompanionTheory.Hypotheses₂.localTateDuality
  localEulerChar := GlobalTheory.CompanionTheory.Hypotheses₂.LocalEuler.localEulerChar_holds

theorem published_results_arithmetic (O : OpenLiteratureStatements) : GlobalTheory.CovTop.PublishedHodgeBundleTheorems where
  p1 := GlobalTheory.toroidalCompactification_holds
  p2 := (vol_ge_of_literature O)
  p3 := (vol_nef_of_literature O)
  p4 := (ar_calc_of_literature O)
  p5 := GlobalTheory.abelianDeRham
  p8 := PositivityTheory.Stage1.PM.rayClassFieldSt
  p12 := GlobalTheory.SS.semistableReductionSt
  p13 := GlobalTheory.StrongApproxSUProof.strongApproxSU
  p14 := (green_series_st_of_literature O)
  p16 := GlobalTheory.GoodMetric.goodChernWeil
  p19 := (landherr_st_of_literature O)
  p20 := GlobalTheory.QNorm.hasseNormSt
  p22 := GlobalTheory.semiAbelianHomExtension_holds
  p23 := GlobalTheory.Alc.inducedSimpleLowestAlcove
  p25 := GlobalTheory.AbLaw.principalPolarisation_unique_section
  p26 := GlobalTheory.abMulN_holds
  q1 := (grothendieck_messing_of_literature O)
  q4 := UpperTheory.Lit.prismaticDieudonneHodge
  q6 := (kawamata_viehweg_of_literature O)
  q7 := GlobalTheory.nefNumerics_outright
  q8 := GlobalTheory.l2ExtensionLogCanonical'
  q9 := (arith_hilbert_samuel_of_literature O)
  q10 := GlobalTheory.Published.chowFormExists_holds
  q11 := (cycle_heights_of_literature O)
  q13 := GlobalTheory.Published.serreHolomorphicSections_holds
  q15 := NadelVanishingSeparation.NSI.nadelVanishingAndNonKltDivisor
  q16 := PositivityTheory.ResPlug.WeightsCompactStabilizer.principalisation_closed
  q18 := GlobalTheory.formalAlgebraisation

theorem principal_archived_covolume (O : OpenLiteratureStatements) : GlobalTheory.CovTop.CovolumeBoundOfX := by
  exact SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt
    PositivityTheory.Resplug.ResolutionBlowup.resolutionCharZero PositivityTheory.ResPlug.WeightsCompactStabilizer.principalisationCharZero_closed
    PositivityTheory.Tls2.Pl.poincareLelongInv PositivityTheory.Pf1.HilbertSamuelMoriwaki.hsUse_outright
    PositivityTheory.Pf1.HilbertSamuelMoriwaki.moriwakiBig_outright UpperTheory.Lit.farguesExact
    (zarhin_statement O) PositivityTheory.Tls2.Nef.nefRR GlobalTheory.siegelToroidalIntegral_holds
    GlobalTheory.TorKSField.toroidalForFanKS GlobalTheory.Nef.semiAbelianLieSeminegative
    NadelVanishingSeparation.NSI.pointSeparationPair (ar_degree_of_literature O) (published_results_arithmetic O)
    (grothendieck_deformation_of_literature O)

end RiemannGaussian.AlpogeWindow.ArchivedInputs

namespace RiemannGaussian.AlpogeWindow

open Formalism.BasicNotions Formalism.MainNotions Formalism.HC

open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc

open GlobalTheory.Mem.LiteralAutomorphy UpperTheory.Top

set_option maxHeartbeats 3500000 in

set_option synthInstance.maxHeartbeats 200000 in

theorem rh_of_principal_archived_open_rows
    (P : S0.UnitaryGroupThirdPlaceHypotheses) (hR : S0.RowRat)
    (hL : UpperTheory.Zero.LLC.RecTExists) (cDep : ℝ) (A : GroupRetwisting.AtP)
    (hA : EvLgG A)
    (hN : RL.LinkedAt (parametersOfDependence hL cDep) (fun Q L =>
      R1.SlotNormCondition Q L fun 𝒞 => Formalism.MainNotions.Closed 𝒞 fun Fm _ => GlobalTheory.NLink.BoundAtTwoThreeFamilyFonAlt Fm))
    (hF : RL.LinkedAt (parametersOfExtension (extensionWithAtProperty hL
      (GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) A) SExt.none (geoCl anyGeometry)) S0.FunctionalCondition)
    (hL3 : RL.LinkedAt (parametersOfExtension (extensionWithAtProperty hL
      (GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) A) SExt.none (geoCl anyGeometry)) S0.CovolumeBoundThirdPlaceSeries)
    (hhost : HostExW (3/2) (GChi PChar.one).req) : RiemannHypothesis := by
  obtain ⟨hP, hMem, hEx⟩ := GlobalTheory.T.large_unramified_exponent_bundles_exist_alt P hR hL cDep A hA
  obtain ⟨_, prN, serN, _⟩ := GlobalTheory.T.hyps_e_third_layer_ser_n_of_geometric_galois P.litN P.toHypothesesX
  have hOL := GlobalTheory.Fc.S0.ontoX_and_lamLow_of_unitaryGroupHypotheses' P
  have hO := GlobalTheory.T.open0_of_unitary_group_hypotheses P hL cDep
  have hNrow := UpperTheory.GalC.final_alt_alt P.nLink prN P.toHypothesesX serN P.depthZeroSupport'
    P.localFiniteness P.localTateDuality P.localEulerChar hL cDep hN
  have hmono := GlobalTheory.Glob.open_and_linked_of_stronger_extension_alt hL (GlobalTheory.HeightCounting.Up.extensionWithList hL cDep) (GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL (GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) A) SExt.none (geoCl anyGeometry)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ x => ⟨x.1.1⟩)
  have hO' := hmono.2 hO
  have hN' : GlobalTheory.Fc.RL.LinkedAt (GlobalTheory.Mem.Top.Bl.parametersOfExtension (GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL (GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) A) SExt.none (geoCl anyGeometry)) (fun Q L => GlobalTheory.Fc.R1.SlotNormCondition Q L S0.NL) :=
    hmono.1 (fun 𝒜 _ => S0.NL (GlobalTheory.Cp.D3 3 𝒜)) hNrow
  have hAll := GlobalTheory.Fc.AllAtMemberStage0.allRows_of_open0_alt P.globalArtinReciprocity P.siegelWeilUnitaryConvergent2 P.discreteSeriesCover
    P.harishChandraModules P.cuspRapidDecay P.casselmanWallach P.discreteSeriesClassification hOL.1 hOL.2
    hL _ _ _ S0.NL hO' hL3 hF hN'
  obtain ⟨h, hs, designs⟩ := principal_archived_row_selection hP GlobalTheory.ThinScaleLiterature.litThin GlobalTheory.wuDecayOfGap GlobalTheory.rowsFinDim_link
    GlobalTheory.rowsPos_typeP (GlobalTheory.rowNGP_of_siegelWeil P.siegelWeilUnitaryConvergent2)
    (GlobalTheory.rowMainEqP_of_siegelWeil P.siegelWeilUnitaryConvergent2)
    (GlobalTheory.VolRatioFromSiegelWeil.volumeRatio P.siegelWeilUnitaryConvergent2) GlobalTheory.genusMassAt_two
    (fun _ => hMem) hEx hAll
  let p := parametersOfExtension (extensionWithAtProperty hL
    (GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) A) SExt.none (geoCl anyGeometry)
  exact rh_of_principal_archived_bundle_rows (Q := IsGoodE p.s) (p := p)
    (E := fun _ _ _ _ _ => True) h (fun Fm hc => hs Fm hc)
    (designs minkowski_bound_rat (3/2) (GChi PChar.one) (by norm_num) hhost)
    (GlobalTheory.GreenBridge.green_of_regular P.greenRegularCharacters)

set_option maxHeartbeats 3500000 in

set_option synthInstance.maxHeartbeats 200000 in

theorem rh_of_principal_archived_grid
    (P : S0.UnitaryGroupThirdPlaceHypotheses) (hX : GlobalTheory.CovTop.CovolumeBoundOfX)
    (hL : UpperTheory.Zero.LLC.RecTExists) (hhost : HostExW (3/2) (GChi PChar.one).req) :
    RiemannHypothesis := by
  let F := archive_local_theta_inputs
  obtain ⟨hA, hM⟩ := PositivityTheory.ThKR.theoremK_head2 PositivityTheory.RgEis.Hd.eisBL
    PositivityTheory.SiegelWeilFormula.Fin.siegelWeilStd
  have C := P.litN
  have hS : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate :=
    UpperTheory.Lit.functionalsSeparate_of_howeUnram_of_siegelWeil F GlobalTheory.Hk3.howeUnram_holds P.siegelWeilUnitaryConvergent
  have hRat : S0.RowRat := GlobalTheory.Mem.LiteralAutomorphy.rowRatW_of_rowTest (GlobalTheory.T.test_vector_assembly_holds F.siegelSetUnitary F.howeDualityReal
    P.greenCuspidal F C.join C.fe hA hM hS)
  have hFit : GlobalTheory.BigTop.Fun.ConstantFunctionFits @GlobalTheory.BigTop.Fun.Fld := GlobalTheory.BigTop.Fun.Close.fourier_coefficient_fit_of_join_alt F C.join C.fe hA hM hS (GlobalTheory.Fc.S0.ontoX_and_lamLow_of_unitaryGroupHypotheses' P).2
  obtain ⟨CF1, hCF1⟩ := GlobalTheory.Mem.LiteralAutomorphy.evaluation_grid_of_join F.howeDualityReal hM F C.join C.fe hA
    (GlobalTheory.WeilConv.twisted_weil_representation_convergence F.siegelSetUnitary F) (GlobalTheory.T.twisted_local_factors_match F.howeDualityReal F hA hM)
    (GlobalTheory.T.twisted_square_theta_integrals_eq F hA hM) hS
  obtain ⟨CF0, hCF0⟩ := GlobalTheory.Fc.StageOne.rowFun_at_gridA_alt P.discreteSeriesCover P.harishChandraModules P.cuspRapidDecay P.casselmanWallach
    P.rayClassFieldSt hFit
  have hEv : EvLgG (GridA (max CF0 CF1)) := hCF1 _ (le_max_right _ _)
  have hOpen1 : GlobalTheory.Fc.S0.OpenParameterStatements (GlobalTheory.Mem.Top.Bl.parametersOfDependence hL (max CF0 CF1)) := GlobalTheory.T.open0_of_unitary_group_hypotheses P hL (max CF0 CF1)
  have hMono := GlobalTheory.Glob.open_and_linked_of_stronger_extension_alt hL (GlobalTheory.HeightCounting.Up.extensionWithList hL (max CF0 CF1))
    (GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL (GlobalTheory.HeightCounting.Up.extensionWithOrigin hL (max CF0 CF1)) (GridA (max CF0 CF1))) SExt.none (geoCl anyGeometry)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ x => ⟨x.1.1⟩)
  have hOpenA := hMono.2 hOpen1
  have hFun := hCF0 (max CF0 CF1) (le_max_left _ _) hL (GlobalTheory.HeightCounting.Up.extensionWithOrigin hL (max CF0 CF1)) SExt.none (geoCl anyGeometry)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ x => ⟨x.1⟩) hOpenA
  have hL3 := GlobalTheory.Glob.CovolRow.linked_bundles_l3_of_open_alt P.discreteSeriesCover P.harishChandraModules P.cuspRapidDecay
    P.casselmanWallach P.rayClassFieldSt hX hL (GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL (GlobalTheory.HeightCounting.Up.extensionWithOrigin hL (max CF0 CF1)) (GridA (max CF0 CF1)))
    SExt.none (geoCl anyGeometry) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ x => ⟨x.1.1.1⟩) hOpenA
  exact rh_of_principal_archived_open_rows P hRat hL (max CF0 CF1) (GridA (max CF0 CF1)) hEv
    (UpperTheory.N.boundAtTwoThree_linked_of_recT P.nLink (parametersOfDependence hL (max CF0 CF1)))
    hFun hL3 hhost

open Formalism.HC UpperTheory.Top

open GlobalTheory.Mem.LiteralAutomorphy

theorem principal_archived_window (O : ArchivedInputs.OpenLiteratureStatements)
    (gal : UpperTheory.V.Z.Win.RowT) : VWinAt PChar.one 401 := by
  let L := ArchivedInputs.literature_local O
  let A := ArchivedInputs.literature_automorphy O
  let loc : LitLocAlt :=
    ⟨L.bz, L.bern, L.geo, L.zel, L.disj, L.mp, L.temp, L.seg, L.sq, L.gen,
      L.multi, L.exh, L.cos, L.conv, L.dzi, L.brauer, L.chev, L.green⟩
  let aut : LiteratureAutomorphyHypothesis := {
    decay := A.decay
    hc := A.hc
    fin := A.fin
    js := A.js
    cusp := A.cusp
    bc := UpperTheory.BaseChangeIdentities.baseChangeN
    gk := A.gk
    gal := gal
    pur := A.pur
    coh := A.coh
    art := A.art
    ray := A.ray
    chA := A.chA
    chW := A.chW
    berger := A.berger }
  let cm : LiteratureCMHypothesis := {
    gm := ArchivedInputs.grothendieck_deformation_of_literature O
    dr := GlobalTheory.abelianDeRham
    dual := GlobalTheory.abelianDualCrystal_of_dual_of_smoothLift GlobalTheory.dualAbelianScheme
      GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations
    per := GlobalTheory.PeriodFamily.periodComparison_holds
    gmp := GlobalTheory.PeriodFamily.gaussManinPeriods_holds
    st := UpperTheory.Lit.serreTateGoodReduction
    cm := PositivityTheory.Prw.ellipticMainTheoremCM_holds
    hj := GlobalTheory.Laid.hcfj_holds
    dri := ArchivedInputs.siegel_klingen_deligne_ribet_of_literature O
    pz := PositivityTheory.Prw.partialZetaFunctionalEquation_holds
    fe := GlobalTheory.CompanionTheory.HeckeFE.heckeTateFunctionalEquation }
  exact UpperTheory.V.v_window_of_literal_automorphy_n
    ⟨loc, aut, ArchivedInputs.literature_cohomology O, cm⟩ PChar.one

theorem rh_of_principal_archived_geometry : RiemannHypothesis := by
  let hG := UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter
  let hL := UpperTheory.Zero.LLC.recTExists
  let O : ArchivedInputs.OpenLiteratureStatements := ⟨hG, hL, hG⟩
  exact rh_of_principal_archived_grid (ArchivedInputs.published_results_eigen O)
    (ArchivedInputs.principal_archived_covolume O) hL
    (UpperTheory.Top.supplyChi Formalism.HC.PChar.one (principal_archived_window O hG))

end RiemannGaussian.AlpogeWindow

example : _root_.RiemannHypothesis := RiemannGaussian.AlpogeWindow.rh_of_principal_archived_geometry

open Lean Elab Command in
run_cmd do
  let target := ``RiemannGaussian.AlpogeWindow.rh_of_principal_archived_geometry
  let actual ← collectAxioms target
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  unless actual.size == expected.size && expected.all actual.contains do
    throwError "Unexpected axiom set for {target}: {actual}"
  logInfo m!"{target} : RiemannHypothesis; axioms {actual}"
