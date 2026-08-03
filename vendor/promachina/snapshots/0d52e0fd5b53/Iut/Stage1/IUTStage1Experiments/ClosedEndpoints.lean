/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Stage1.IUTStage1Experiments.Diagnostics

/-!
Closed local-to-global CTheta endpoint families extracted from the Stage 1 experiment surface.
-/

namespace Iut
namespace Stage1
namespace Experiments

open RealLineCopy
open IUTStage1SourcePackage.PlaceAuditedMultiradialThetaHullEndpoint
open IUTStage1SourcePackage.PlaceAuditedMultiradialThetaHullEndpoint.LogVolumeChartAudit
open FLZModCuspLabelThetaHodgeDescentPacketTransportAudit
open FLZModCuspLabelThetaCuspClassContainerAudit
open IUTStage1ZModCuspFullLabel
open IUTStage1ProcessionNormalizedIndeterminacyCorridor
open IUTStage1ZModSquareWeightProfile
open IUTStage1ZModSquareWeightProfile.GaussianMonoidDegreeEvaluation
open IUTStage1ZModSquareWeightProfile.LGPSplittingMonoidTensorPacketAction
open IUTStage1StructuredSHEFactoredSquareFullLabelObligations
open IUTStage1HullDetPilotUpperRayLogVolume
open IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor
open IUTStage1Theorem311OneSidedMultiradialConstructionSource
open scoped BigOperators
open scoped NormedField
open scoped Valued

universe u v w x y z ac ag ic ig ec eg kc kg b gc gg
namespace ConstructedTheorem311IndeterminacyLocalGlobalCThetaSource

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {record : IUTStage1Theorem311MultiradialSourceRecord package}
variable {β : Type v} [Fintype β]
variable {sourceData :
  IUTStage1SourcePackage.IUTStage1Remark395ConstructedHolomorphicHullDeterminantSource
    (β := β) record}
variable {estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow}
variable {choice : Type w}

set_option linter.style.longLine false in
/--
Named ordered-real chain converting the paper-side arithmetic gap into the
actual \(C_\Theta\) comparison.

The local-to-global source proves
`C_{Theta,can} + 1 <= arithmeticUpperTerm - mainLogTerm`; the IUT IV estimate
identifies the right hand side with `C_Theta + 1`.  This audit exposes the
intermediate `+ 1` inequality before cancelling the normalized unit.
-/
structure ArithmeticGapCThetaChainAudit
    (source :
      ConstructedTheorem311IndeterminacyLocalGlobalCThetaSource
        sourceData estimate choice) : Prop where
  arithmeticGap_dominates_canonicalCThetaScale :
    sourceData.canonicalCThetaScale + 1 <=
      estimate.arithmeticUpperTerm - estimate.mainLogTerm
  iutIV_cTheta_plus_one_eq_arithmeticGap :
    estimate.cTheta + 1 =
      estimate.arithmeticUpperTerm - estimate.mainLogTerm
  canonicalCThetaScale_plus_one_le_iutIVCTheta_plus_one :
    sourceData.canonicalCThetaScale + 1 <= estimate.cTheta + 1
  canonicalCThetaScale_le_iutIVCTheta :
    sourceData.canonicalCThetaScale <= estimate.cTheta

set_option linter.style.longLine false in
theorem arithmeticGapCThetaChainAudit
    (source :
      ConstructedTheorem311IndeterminacyLocalGlobalCThetaSource
        sourceData estimate choice) :
    ArithmeticGapCThetaChainAudit source := by
  have hplus :
      estimate.cTheta + 1 =
        estimate.arithmeticUpperTerm - estimate.mainLogTerm :=
    estimate.corollary312_handoff_endpoint.2.1
  have hgap := source.arithmeticGap_dominates_canonicalCThetaScale
  have hcanonPlus :
      sourceData.canonicalCThetaScale + 1 <= estimate.cTheta + 1 := by
    linarith
  have hcanon :
      sourceData.canonicalCThetaScale <= estimate.cTheta := by
    linarith
  exact
    { arithmeticGap_dominates_canonicalCThetaScale := hgap,
      iutIV_cTheta_plus_one_eq_arithmeticGap := hplus,
      canonicalCThetaScale_plus_one_le_iutIVCTheta_plus_one := hcanonPlus,
      canonicalCThetaScale_le_iutIVCTheta := hcanon }

theorem canonicalCThetaScale_le_iutIVCTheta
    (source :
      ConstructedTheorem311IndeterminacyLocalGlobalCThetaSource
        sourceData estimate choice) :
    sourceData.canonicalCThetaScale <= estimate.cTheta :=
  source.arithmeticGapCThetaChainAudit.canonicalCThetaScale_le_iutIVCTheta

theorem localGlobalHandoffAudit
    (source :
      ConstructedTheorem311IndeterminacyLocalGlobalCThetaSource
        sourceData estimate choice) :
    Remark395ConstructedIUTIVCThetaHandoffAudit sourceData estimate :=
  remark395ConstructedHolomorphicHullDeterminantSource_iutIVCThetaHandoffAudit
    sourceData estimate source.canonicalCThetaScale_le_iutIVCTheta

set_option linter.style.longLine false in
set_option linter.style.longLine false in
def Endpoint
    (source :
      ConstructedTheorem311IndeterminacyLocalGlobalCThetaSource
        sourceData estimate choice) :
    Prop :=
  source.localPlaceLogVolumeAssembly ∧
    source.finiteDivisorValuationBallHaarNormalization ∧
    source.productSumLocalToGlobalAssembly ∧
    source.theorem311IndeterminacyToStepXICompatibility ∧
    sourceData.canonicalCThetaScale <= estimate.cTheta ∧
    estimate.cTheta =
      estimate.arithmeticUpperTerm - estimate.mainLogTerm - 1 ∧
    package.preLedger.thetaSigned <=
      estimate.cTheta * (-package.preLedger.qSigned) ∧
    ((package.preLedger.qSigned = package.preLedger.thetaSigned ∧
        package.preLedger.thetaSigned < 0) ∨
      (-1 : Real) < estimate.cTheta)

set_option linter.style.longLine false in
set_option linter.style.longLine false in
theorem endpoint
    (source :
      ConstructedTheorem311IndeterminacyLocalGlobalCThetaSource
        sourceData estimate choice) :
    Endpoint source :=
  let audit := source.localGlobalHandoffAudit
  ⟨source.localPlaceLogVolumeAssembly_holds,
    source.finiteDivisorValuationBallHaarNormalization_holds,
    source.productSumLocalToGlobalAssembly_holds,
    source.theorem311IndeterminacyToStepXICompatibility_holds,
    source.canonicalCThetaScale_le_iutIVCTheta,
    audit.iutIVCThetaExpression,
    audit.thetaSigned_le_iutIVCTheta_absLogQ,
    audit.dichotomy⟩

set_option linter.style.longLine false in
/--
Raw-comparison-free closed endpoint for the local-to-global \(C_\Theta\)
source.

Unlike `Endpoint`, this proposition does not expose either the derived
`C_{Theta,can} <= C_Theta` comparison or the derived signed numeric bound as
conjuncts.  It records only the constructed source obligations, the IUT IV
paper expression for \(C_\Theta\), and the final Corollary 3.12 dichotomy.
-/
def ClosedDichotomyEndpoint
    (source :
      ConstructedTheorem311IndeterminacyLocalGlobalCThetaSource
        sourceData estimate choice) :
    Prop :=
  source.localPlaceLogVolumeAssembly ∧
    source.finiteDivisorValuationBallHaarNormalization ∧
    source.productSumLocalToGlobalAssembly ∧
    source.theorem311IndeterminacyToStepXICompatibility ∧
    estimate.cTheta =
      estimate.arithmeticUpperTerm - estimate.mainLogTerm - 1 ∧
    ((package.preLedger.qSigned = package.preLedger.thetaSigned ∧
        package.preLedger.thetaSigned < 0) ∨
      (-1 : Real) < estimate.cTheta)

set_option linter.style.longLine false in
theorem closedDichotomyEndpoint
    (source :
      ConstructedTheorem311IndeterminacyLocalGlobalCThetaSource
        sourceData estimate choice) :
    ClosedDichotomyEndpoint source :=
  let audit := source.localGlobalHandoffAudit
  ⟨source.localPlaceLogVolumeAssembly_holds,
    source.finiteDivisorValuationBallHaarNormalization_holds,
    source.productSumLocalToGlobalAssembly_holds,
    source.theorem311IndeterminacyToStepXICompatibility_holds,
    audit.iutIVCThetaExpression,
    audit.dichotomy⟩

set_option linter.style.longLine false in
/--
Closed-endpoint audit showing that the raw comparison inputs are derived inside
the local-to-global source.

The source exposes only the paper-shaped arithmetic-gap proof
`C_{Theta,can} + 1 <= A - M`; this audit records the ordered-real cancellation,
the resulting `C_{Theta,can} <= C_Theta`, the signed
`thetaSigned <= C_Theta * (-qSigned)` bound, and the final dichotomy as
projections of the constructed handoff rather than as endpoint hypotheses.
-/
structure ClosedNoRawComparisonAudit
    (source :
      ConstructedTheorem311IndeterminacyLocalGlobalCThetaSource
        sourceData estimate choice) : Prop where
  closedDichotomyEndpoint : ClosedDichotomyEndpoint source
  endpoint : Endpoint source
  arithmeticGapCThetaChainAudit :
    ArithmeticGapCThetaChainAudit source
  localGlobalHandoffAudit :
    Remark395ConstructedIUTIVCThetaHandoffAudit sourceData estimate
  sourceDerivedCanonicalCThetaScale_le_iutIVCTheta :
    sourceData.canonicalCThetaScale <= estimate.cTheta
  sourceDerivedThetaSigned_le_iutIVCTheta_absLogQ :
    package.preLedger.thetaSigned <=
      estimate.cTheta * (-package.preLedger.qSigned)
  dichotomy :
    (package.preLedger.qSigned = package.preLedger.thetaSigned ∧
        package.preLedger.thetaSigned < 0) ∨
      (-1 : Real) < estimate.cTheta

set_option linter.style.longLine false in
theorem closedNoRawComparisonAudit
    (source :
      ConstructedTheorem311IndeterminacyLocalGlobalCThetaSource
        sourceData estimate choice) :
    ClosedNoRawComparisonAudit source :=
  let handoff := source.localGlobalHandoffAudit
  { endpoint := source.endpoint,
    closedDichotomyEndpoint := source.closedDichotomyEndpoint,
    arithmeticGapCThetaChainAudit := source.arithmeticGapCThetaChainAudit,
    localGlobalHandoffAudit := handoff,
    sourceDerivedCanonicalCThetaScale_le_iutIVCTheta :=
      source.canonicalCThetaScale_le_iutIVCTheta,
    sourceDerivedThetaSigned_le_iutIVCTheta_absLogQ :=
      handoff.thetaSigned_le_iutIVCTheta_absLogQ,
    dichotomy := handoff.dichotomy }

end ConstructedTheorem311IndeterminacyLocalGlobalCThetaSource

set_option linter.style.longLine false in
/--
Finite local-place source for the local-to-global `C_Theta` comparison.

This refines the coarse arithmetic-gap field of
`ConstructedTheorem311IndeterminacyLocalGlobalCThetaSource`.  Each local place
contributes a canonical Step (xi) scale, an IUT IV arithmetic upper term, a main
log term, and a Haar-normalization defect.  The local Step (xi)/Haar inequality
is summed over the finite place set; the total Haar defect supplies the final
`+ 1` needed to compare the canonical local scale with the IUT IV
`arithmeticUpperTerm - mainLogTerm`.
-/
structure ConstructedTheorem311FinitePlaceLocalGlobalCThetaSource
    {source target : Copy} {index : Type u}
    {package : IUTStage1SourcePackage source target index}
    {record : IUTStage1Theorem311MultiradialSourceRecord package}
    {β : Type v} [Fintype β]
    (sourceData :
      IUTStage1SourcePackage.IUTStage1Remark395ConstructedHolomorphicHullDeterminantSource
        (β := β) record)
    (estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow)
    (choice : Type w) (place : Type x) [Fintype place] where
  typedIndeterminacyCore :
    IUTStage1Theorem311TypedIndeterminacyCore choice
  localCanonicalScale : place -> Real
  localArithmeticUpperContribution : place -> Real
  localMainLogContribution : place -> Real
  localHaarNormalizationDefect : place -> Real
  canonicalCThetaScale_eq_sum :
    sourceData.canonicalCThetaScale =
      ∑ place, localCanonicalScale place
  arithmeticUpperTerm_eq_sum :
    estimate.arithmeticUpperTerm =
      ∑ place, localArithmeticUpperContribution place
  mainLogTerm_eq_sum :
    estimate.mainLogTerm =
      ∑ place, localMainLogContribution place
  local_stepXI_haar_bound :
    ∀ place,
      localCanonicalScale place + localHaarNormalizationDefect place <=
        localArithmeticUpperContribution place - localMainLogContribution place
  total_haar_defect_ge_one :
    (1 : Real) <= ∑ place, localHaarNormalizationDefect place

namespace ConstructedTheorem311FinitePlaceLocalGlobalCThetaSource

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {record : IUTStage1Theorem311MultiradialSourceRecord package}
variable {β : Type v} [Fintype β]
variable {sourceData :
  IUTStage1SourcePackage.IUTStage1Remark395ConstructedHolomorphicHullDeterminantSource
    (β := β) record}
variable {estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow}
variable {choice : Type w} {place : Type x} [Fintype place]

theorem summed_stepXI_haar_bound
    (source :
      ConstructedTheorem311FinitePlaceLocalGlobalCThetaSource
        sourceData estimate choice place) :
    (∑ place, source.localCanonicalScale place) +
        ∑ place, source.localHaarNormalizationDefect place <=
      (∑ place, source.localArithmeticUpperContribution place) -
        ∑ place, source.localMainLogContribution place := by
  calc
    (∑ place, source.localCanonicalScale place) +
        ∑ place, source.localHaarNormalizationDefect place
        = ∑ place,
            (source.localCanonicalScale place +
              source.localHaarNormalizationDefect place) := by
          rw [Finset.sum_add_distrib]
    _ <= ∑ place,
            (source.localArithmeticUpperContribution place -
              source.localMainLogContribution place) := by
          exact Finset.sum_le_sum (fun place _hplace =>
            source.local_stepXI_haar_bound place)
    _ =
      (∑ place, source.localArithmeticUpperContribution place) -
        ∑ place, source.localMainLogContribution place := by
          rw [Finset.sum_sub_distrib]

theorem arithmeticGap_dominates_canonicalCThetaScale
    (source :
      ConstructedTheorem311FinitePlaceLocalGlobalCThetaSource
        sourceData estimate choice place) :
    sourceData.canonicalCThetaScale + 1 <=
      estimate.arithmeticUpperTerm - estimate.mainLogTerm := by
  have hsum := source.summed_stepXI_haar_bound
  linarith [source.canonicalCThetaScale_eq_sum,
    source.arithmeticUpperTerm_eq_sum, source.mainLogTerm_eq_sum,
    source.total_haar_defect_ge_one, hsum]

set_option linter.style.longLine false in
def toConstructedTheorem311IndeterminacyLocalGlobalCThetaSource
    (source :
      ConstructedTheorem311FinitePlaceLocalGlobalCThetaSource
        sourceData estimate choice place) :
    ConstructedTheorem311IndeterminacyLocalGlobalCThetaSource
      sourceData estimate choice :=
  { typedIndeterminacyCore := source.typedIndeterminacyCore,
    localPlaceLogVolumeAssembly :=
      sourceData.canonicalCThetaScale =
          ∑ place, source.localCanonicalScale place,
    localPlaceLogVolumeAssembly_holds :=
      source.canonicalCThetaScale_eq_sum,
    finiteDivisorValuationBallHaarNormalization :=
      (1 : Real) <= ∑ place, source.localHaarNormalizationDefect place,
    finiteDivisorValuationBallHaarNormalization_holds :=
      source.total_haar_defect_ge_one,
    productSumLocalToGlobalAssembly :=
      estimate.arithmeticUpperTerm =
          ∑ place, source.localArithmeticUpperContribution place ∧
        estimate.mainLogTerm =
          ∑ place, source.localMainLogContribution place,
    productSumLocalToGlobalAssembly_holds :=
      ⟨source.arithmeticUpperTerm_eq_sum, source.mainLogTerm_eq_sum⟩,
    theorem311IndeterminacyToStepXICompatibility :=
      ∀ place,
        source.localCanonicalScale place +
            source.localHaarNormalizationDefect place <=
          source.localArithmeticUpperContribution place -
            source.localMainLogContribution place,
    theorem311IndeterminacyToStepXICompatibility_holds :=
      source.local_stepXI_haar_bound,
    arithmeticGap_dominates_canonicalCThetaScale :=
      source.arithmeticGap_dominates_canonicalCThetaScale }

theorem canonicalCThetaScale_le_iutIVCTheta
    (source :
      ConstructedTheorem311FinitePlaceLocalGlobalCThetaSource
        sourceData estimate choice place) :
    sourceData.canonicalCThetaScale <= estimate.cTheta :=
  source.toConstructedTheorem311IndeterminacyLocalGlobalCThetaSource
    |>.canonicalCThetaScale_le_iutIVCTheta

theorem endpoint
    (source :
      ConstructedTheorem311FinitePlaceLocalGlobalCThetaSource
        sourceData estimate choice place) :
    ConstructedTheorem311IndeterminacyLocalGlobalCThetaSource.Endpoint
      source.toConstructedTheorem311IndeterminacyLocalGlobalCThetaSource :=
  source.toConstructedTheorem311IndeterminacyLocalGlobalCThetaSource.endpoint

end ConstructedTheorem311FinitePlaceLocalGlobalCThetaSource

set_option linter.style.longLine false in
/--
Preferred one-sided Theorem 3.11 local-to-global `C_Theta` source.

This wrapper replaces the older bare `typedIndeterminacyCore` handoff by the
source-faithful multiradial construction from Step (xi): possible-image
identifications are read through the `(Ind1)/(Ind2)` equality quotient, while
`(Ind3)` remains a one-sided upper-semi log-volume assertion.  The q-pilot
region of the constructed Remark 3.9.5 source is tied to the selected
Theorem 3.11 possible image before the local-to-global arithmetic gap is used.
-/
structure ConstructedTheorem311OneSidedLocalGlobalCThetaSource
    {source target : Copy} {index : Type u}
    {package : IUTStage1SourcePackage source target index}
    {record : IUTStage1Theorem311MultiradialSourceRecord package}
    {β : Type v} [Fintype β]
    (sourceData :
      IUTStage1SourcePackage.IUTStage1Remark395ConstructedHolomorphicHullDeterminantSource
        (β := β) record)
    (estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow)
    (l : PrimeGeFive) where
  oneSidedMultiradialSource :
    IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource
      (package := package) record l
  qPilotRegion_eq_selectedQRegion :
    sourceData.qPilotRegion =
      oneSidedMultiradialSource.selectedQRegion.toSet
  localPlaceLogVolumeAssembly : Prop
  localPlaceLogVolumeAssembly_holds : localPlaceLogVolumeAssembly
  finiteDivisorValuationBallHaarNormalization : Prop
  finiteDivisorValuationBallHaarNormalization_holds :
    finiteDivisorValuationBallHaarNormalization
  productSumLocalToGlobalAssembly : Prop
  productSumLocalToGlobalAssembly_holds : productSumLocalToGlobalAssembly
  theorem311IndeterminacyToStepXICompatibility : Prop
  theorem311IndeterminacyToStepXICompatibility_holds :
    theorem311IndeterminacyToStepXICompatibility
  arithmeticGap_dominates_canonicalCThetaScale :
    sourceData.canonicalCThetaScale + 1 <=
      estimate.arithmeticUpperTerm - estimate.mainLogTerm

namespace ConstructedTheorem311OneSidedLocalGlobalCThetaSource

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {record : IUTStage1Theorem311MultiradialSourceRecord package}
variable {β : Type v} [Fintype β]
variable {sourceData :
  IUTStage1SourcePackage.IUTStage1Remark395ConstructedHolomorphicHullDeterminantSource
    (β := β) record}
variable {estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow}
variable {l : PrimeGeFive}

def toConstructedTheorem311IndeterminacyLocalGlobalCThetaSource
    (source :
      ConstructedTheorem311OneSidedLocalGlobalCThetaSource
        sourceData estimate l) :
    ConstructedTheorem311IndeterminacyLocalGlobalCThetaSource
      sourceData estimate index :=
  { typedIndeterminacyCore :=
      source.oneSidedMultiradialSource.typedIndeterminacyCore,
    localPlaceLogVolumeAssembly := source.localPlaceLogVolumeAssembly,
    localPlaceLogVolumeAssembly_holds :=
      source.localPlaceLogVolumeAssembly_holds,
    finiteDivisorValuationBallHaarNormalization :=
      source.finiteDivisorValuationBallHaarNormalization,
    finiteDivisorValuationBallHaarNormalization_holds :=
      source.finiteDivisorValuationBallHaarNormalization_holds,
    productSumLocalToGlobalAssembly :=
      source.productSumLocalToGlobalAssembly,
    productSumLocalToGlobalAssembly_holds :=
      source.productSumLocalToGlobalAssembly_holds,
    theorem311IndeterminacyToStepXICompatibility :=
      source.theorem311IndeterminacyToStepXICompatibility,
    theorem311IndeterminacyToStepXICompatibility_holds :=
      source.theorem311IndeterminacyToStepXICompatibility_holds,
    arithmeticGap_dominates_canonicalCThetaScale :=
      source.arithmeticGap_dominates_canonicalCThetaScale }

set_option linter.style.longLine false in
theorem selectedQRegion_endpoint
    (source :
      ConstructedTheorem311OneSidedLocalGlobalCThetaSource
        sourceData estimate l) :
    sourceData.qPilotRegion =
        IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImage
          record source.oneSidedMultiradialSource.selectedQChoice ∧
      sourceData.qPilotRegion ⊆
        IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImageUnion
          record ∧
      source.oneSidedMultiradialSource.multiradialImages.possibleImages =
        record.thetaPossibleImages :=
  source.oneSidedMultiradialSource.remark395SelectedQRegion_endpoint
    sourceData source.qPilotRegion_eq_selectedQRegion

theorem ind3_logVolume_upper
    (source :
      ConstructedTheorem311OneSidedLocalGlobalCThetaSource
        sourceData estimate l)
    {choice₁ choice₂ : index}
    (hstep :
      source.oneSidedMultiradialSource.typedIndeterminacyCore.ind3.step
        choice₁ choice₂) :
    source.oneSidedMultiradialSource.typedIndeterminacyCore.logVolume choice₁ <=
      source.oneSidedMultiradialSource.typedIndeterminacyCore.logVolume choice₂ :=
  source.oneSidedMultiradialSource.ind3_logVolume_upper hstep

theorem quotientPossibleImages_pullback
    (source :
      ConstructedTheorem311OneSidedLocalGlobalCThetaSource
        sourceData estimate l)
    (choice : index) :
    source.oneSidedMultiradialSource.equalityQuotientPossibleImages.quotientImages.region
        (source.oneSidedMultiradialSource.typedIndeterminacyCore.equalityQuotientMap
          choice) =
      record.thetaPossibleImages.images.region choice :=
  source.oneSidedMultiradialSource.equalityQuotientPossibleImages_pullback choice

theorem selectedQRegion_eq_quotientPossibleImage
    (source :
      ConstructedTheorem311OneSidedLocalGlobalCThetaSource
        sourceData estimate l) :
    source.oneSidedMultiradialSource.selectedQRegion =
      source.oneSidedMultiradialSource.equalityQuotientPossibleImages.quotientImages.region
        (source.oneSidedMultiradialSource.typedIndeterminacyCore.equalityQuotientMap
          source.oneSidedMultiradialSource.selectedQChoice) :=
  source.oneSidedMultiradialSource.selectedQRegion_eq_quotientPossibleImage

set_option linter.style.longLine false in
theorem oneSidedQuotientAudit
    (source :
      ConstructedTheorem311OneSidedLocalGlobalCThetaSource
        sourceData estimate l) :
    IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.OneSidedQuotientAudit
      source.oneSidedMultiradialSource :=
  source.oneSidedMultiradialSource.oneSidedQuotientAudit

theorem canonicalCThetaScale_le_iutIVCTheta
    (source :
      ConstructedTheorem311OneSidedLocalGlobalCThetaSource
        sourceData estimate l) :
    sourceData.canonicalCThetaScale <= estimate.cTheta :=
  source.toConstructedTheorem311IndeterminacyLocalGlobalCThetaSource
    |>.canonicalCThetaScale_le_iutIVCTheta

set_option linter.style.longLine false in
def OneSidedMultiradialEndpoint
    (source :
      ConstructedTheorem311OneSidedLocalGlobalCThetaSource
        sourceData estimate l) :
    Prop :=
  source.oneSidedMultiradialSource.multiradialImages.quotient =
        source.oneSidedMultiradialSource.typedIndeterminacyCore.equalityQuotient ∧
    source.oneSidedMultiradialSource.multiradialImages.possibleImages =
        record.thetaPossibleImages ∧
      Fintype.card (ZMod l.value) = l.value ∧
        (∀ t choice,
          source.oneSidedMultiradialSource.typedIndeterminacyCore.equalityQuotientMap choice =
            source.oneSidedMultiradialSource.typedIndeterminacyCore.equalityQuotientMap
              (source.oneSidedMultiradialSource.flProcessionAction.transition t choice)) ∧
        (∀ {choice₁ choice₂ : index},
          source.oneSidedMultiradialSource.typedIndeterminacyCore.ind3.step choice₁ choice₂ ->
            source.oneSidedMultiradialSource.typedIndeterminacyCore.logVolume choice₁ <=
              source.oneSidedMultiradialSource.typedIndeterminacyCore.logVolume choice₂) ∧
        (∀ choice,
          source.oneSidedMultiradialSource.equalityQuotientPossibleImages.quotientImages.region
              (source.oneSidedMultiradialSource.typedIndeterminacyCore.equalityQuotientMap
                choice) =
            record.thetaPossibleImages.images.region choice) ∧
        source.oneSidedMultiradialSource.selectedQRegion =
          source.oneSidedMultiradialSource.equalityQuotientPossibleImages.quotientImages.region
            (source.oneSidedMultiradialSource.typedIndeterminacyCore.equalityQuotientMap
              source.oneSidedMultiradialSource.selectedQChoice) ∧
        source.oneSidedMultiradialSource.selectedQRegion.toSet =
          IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImage
            record source.oneSidedMultiradialSource.selectedQChoice ∧
        source.oneSidedMultiradialSource.selectedQRegion.toSet ⊆
          IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImageUnion
            record

set_option linter.style.longLine false in
def Endpoint
    (source :
      ConstructedTheorem311OneSidedLocalGlobalCThetaSource
        sourceData estimate l) :
    Prop :=
  OneSidedMultiradialEndpoint source ∧
    sourceData.qPilotRegion =
      IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImage
        record source.oneSidedMultiradialSource.selectedQChoice ∧
    sourceData.qPilotRegion ⊆
      IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImageUnion
        record ∧
    ConstructedTheorem311IndeterminacyLocalGlobalCThetaSource.Endpoint
      source.toConstructedTheorem311IndeterminacyLocalGlobalCThetaSource

set_option linter.style.longLine false in
theorem endpoint
    (source :
      ConstructedTheorem311OneSidedLocalGlobalCThetaSource
        sourceData estimate l) :
    Endpoint source :=
  let hselected := source.selectedQRegion_endpoint
  ⟨source.oneSidedMultiradialSource.endpoint,
    hselected.1,
    hselected.2.1,
    source.toConstructedTheorem311IndeterminacyLocalGlobalCThetaSource.endpoint⟩

end ConstructedTheorem311OneSidedLocalGlobalCThetaSource

set_option linter.style.longLine false in
/--
Finite-place version of the preferred one-sided Theorem 3.11 local-to-global
`C_Theta` source.

The local place summation derives the arithmetic gap exactly as in
`ConstructedTheorem311FinitePlaceLocalGlobalCThetaSource`, but the Theorem 3.11
payload is now the one-sided multiradial source rather than a bare typed core.
-/
structure ConstructedTheorem311OneSidedFinitePlaceLocalGlobalCThetaSource
    {source target : Copy} {index : Type u}
    {package : IUTStage1SourcePackage source target index}
    {record : IUTStage1Theorem311MultiradialSourceRecord package}
    {β : Type v} [Fintype β]
    (sourceData :
      IUTStage1SourcePackage.IUTStage1Remark395ConstructedHolomorphicHullDeterminantSource
        (β := β) record)
    (estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow)
    (l : PrimeGeFive) (place : Type x) [Fintype place] where
  oneSidedMultiradialSource :
    IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource
      (package := package) record l
  qPilotRegion_eq_selectedQRegion :
    sourceData.qPilotRegion =
      oneSidedMultiradialSource.selectedQRegion.toSet
  localCanonicalScale : place -> Real
  localArithmeticUpperContribution : place -> Real
  localMainLogContribution : place -> Real
  localHaarNormalizationDefect : place -> Real
  canonicalCThetaScale_eq_sum :
    sourceData.canonicalCThetaScale =
      ∑ place, localCanonicalScale place
  arithmeticUpperTerm_eq_sum :
    estimate.arithmeticUpperTerm =
      ∑ place, localArithmeticUpperContribution place
  mainLogTerm_eq_sum :
    estimate.mainLogTerm =
      ∑ place, localMainLogContribution place
  local_stepXI_haar_bound :
    ∀ place,
      localCanonicalScale place + localHaarNormalizationDefect place <=
        localArithmeticUpperContribution place - localMainLogContribution place
  total_haar_defect_ge_one :
    (1 : Real) <= ∑ place, localHaarNormalizationDefect place

namespace ConstructedTheorem311OneSidedFinitePlaceLocalGlobalCThetaSource

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {record : IUTStage1Theorem311MultiradialSourceRecord package}
variable {β : Type v} [Fintype β]
variable {sourceData :
  IUTStage1SourcePackage.IUTStage1Remark395ConstructedHolomorphicHullDeterminantSource
    (β := β) record}
variable {estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow}
variable {l : PrimeGeFive} {place : Type x} [Fintype place]

theorem summed_stepXI_haar_bound
    (source :
      ConstructedTheorem311OneSidedFinitePlaceLocalGlobalCThetaSource
        sourceData estimate l place) :
    (∑ place, source.localCanonicalScale place) +
        ∑ place, source.localHaarNormalizationDefect place <=
      (∑ place, source.localArithmeticUpperContribution place) -
        ∑ place, source.localMainLogContribution place := by
  calc
    (∑ place, source.localCanonicalScale place) +
        ∑ place, source.localHaarNormalizationDefect place
        = ∑ place,
            (source.localCanonicalScale place +
              source.localHaarNormalizationDefect place) := by
          rw [Finset.sum_add_distrib]
    _ <= ∑ place,
            (source.localArithmeticUpperContribution place -
              source.localMainLogContribution place) := by
          exact Finset.sum_le_sum (fun place _hplace =>
            source.local_stepXI_haar_bound place)
    _ =
      (∑ place, source.localArithmeticUpperContribution place) -
        ∑ place, source.localMainLogContribution place := by
          rw [Finset.sum_sub_distrib]

theorem arithmeticGap_dominates_canonicalCThetaScale
    (source :
      ConstructedTheorem311OneSidedFinitePlaceLocalGlobalCThetaSource
        sourceData estimate l place) :
    sourceData.canonicalCThetaScale + 1 <=
      estimate.arithmeticUpperTerm - estimate.mainLogTerm := by
  have hsum := source.summed_stepXI_haar_bound
  linarith [source.canonicalCThetaScale_eq_sum,
    source.arithmeticUpperTerm_eq_sum, source.mainLogTerm_eq_sum,
    source.total_haar_defect_ge_one, hsum]

set_option linter.style.longLine false in
def toConstructedTheorem311OneSidedLocalGlobalCThetaSource
    (source :
      ConstructedTheorem311OneSidedFinitePlaceLocalGlobalCThetaSource
        sourceData estimate l place) :
    ConstructedTheorem311OneSidedLocalGlobalCThetaSource
      sourceData estimate l :=
  { oneSidedMultiradialSource := source.oneSidedMultiradialSource,
    qPilotRegion_eq_selectedQRegion :=
      source.qPilotRegion_eq_selectedQRegion,
    localPlaceLogVolumeAssembly :=
      sourceData.canonicalCThetaScale =
          ∑ place, source.localCanonicalScale place,
    localPlaceLogVolumeAssembly_holds :=
      source.canonicalCThetaScale_eq_sum,
    finiteDivisorValuationBallHaarNormalization :=
      (1 : Real) <= ∑ place, source.localHaarNormalizationDefect place,
    finiteDivisorValuationBallHaarNormalization_holds :=
      source.total_haar_defect_ge_one,
    productSumLocalToGlobalAssembly :=
      estimate.arithmeticUpperTerm =
          ∑ place, source.localArithmeticUpperContribution place ∧
        estimate.mainLogTerm =
          ∑ place, source.localMainLogContribution place,
    productSumLocalToGlobalAssembly_holds :=
      ⟨source.arithmeticUpperTerm_eq_sum, source.mainLogTerm_eq_sum⟩,
    theorem311IndeterminacyToStepXICompatibility :=
      ∀ place,
        source.localCanonicalScale place +
            source.localHaarNormalizationDefect place <=
          source.localArithmeticUpperContribution place -
            source.localMainLogContribution place,
    theorem311IndeterminacyToStepXICompatibility_holds :=
      source.local_stepXI_haar_bound,
    arithmeticGap_dominates_canonicalCThetaScale :=
      source.arithmeticGap_dominates_canonicalCThetaScale }

theorem endpoint
    (source :
      ConstructedTheorem311OneSidedFinitePlaceLocalGlobalCThetaSource
        sourceData estimate l place) :
    ConstructedTheorem311OneSidedLocalGlobalCThetaSource.Endpoint
      source.toConstructedTheorem311OneSidedLocalGlobalCThetaSource :=
  source.toConstructedTheorem311OneSidedLocalGlobalCThetaSource.endpoint

theorem canonicalCThetaScale_le_iutIVCTheta
    (source :
      ConstructedTheorem311OneSidedFinitePlaceLocalGlobalCThetaSource
        sourceData estimate l place) :
    sourceData.canonicalCThetaScale <= estimate.cTheta :=
  source.toConstructedTheorem311OneSidedLocalGlobalCThetaSource
    |>.canonicalCThetaScale_le_iutIVCTheta

set_option linter.style.longLine false in
theorem oneSidedQuotientAudit
    (source :
      ConstructedTheorem311OneSidedFinitePlaceLocalGlobalCThetaSource
        sourceData estimate l place) :
    IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.OneSidedQuotientAudit
      source.oneSidedMultiradialSource :=
  source.toConstructedTheorem311OneSidedLocalGlobalCThetaSource.oneSidedQuotientAudit

set_option linter.style.longLine false in
/--
Paper-facing derivation audit for the one-sided finite-place
local-to-global \(C_\Theta\) source.

This is the actual arithmetic bridge used by the closed endpoint: local
Step~(xi) Haar bounds are summed, the normalized Haar defect contributes the
global `+ 1`, the IUT~IV identity rewrites
`C_Theta = arithmeticUpperTerm - mainLogTerm - 1`, and the constructed
Remark~3.9.5 source supplies the final signed \(C_\Theta\) dichotomy.
-/
structure LocalGlobalCThetaDerivationAudit
    (source :
      ConstructedTheorem311OneSidedFinitePlaceLocalGlobalCThetaSource
        sourceData estimate l place) : Prop where
  summed_stepXI_haar_bound :
    (∑ place, source.localCanonicalScale place) +
        ∑ place, source.localHaarNormalizationDefect place <=
      (∑ place, source.localArithmeticUpperContribution place) -
        ∑ place, source.localMainLogContribution place
  arithmeticGap_dominates_canonicalCThetaScale :
    sourceData.canonicalCThetaScale + 1 <=
      estimate.arithmeticUpperTerm - estimate.mainLogTerm
  arithmeticGapCThetaChainAudit :
    ConstructedTheorem311IndeterminacyLocalGlobalCThetaSource.ArithmeticGapCThetaChainAudit
      source.toConstructedTheorem311OneSidedLocalGlobalCThetaSource.toConstructedTheorem311IndeterminacyLocalGlobalCThetaSource
  iutIVCThetaExpression :
    estimate.cTheta =
      estimate.arithmeticUpperTerm - estimate.mainLogTerm - 1
  canonicalCThetaScale_le_iutIVCTheta :
    sourceData.canonicalCThetaScale <= estimate.cTheta
  handoffAudit :
    Remark395ConstructedIUTIVCThetaHandoffAudit sourceData estimate
  globalScaleComparisonAudit :
    IUTStage1SourcePackage.IUTStage1Remark395ConstructedHolomorphicHullDeterminantSource.ConstructedGlobalCThetaScaleComparisonAudit
      sourceData estimate.cTheta
  endpoint :
    ConstructedTheorem311OneSidedLocalGlobalCThetaSource.Endpoint
      source.toConstructedTheorem311OneSidedLocalGlobalCThetaSource
  thetaSigned_le_iutIVCTheta_absLogQ :
    package.preLedger.thetaSigned <=
      estimate.cTheta * (-package.preLedger.qSigned)
  dichotomy :
    (package.preLedger.qSigned = package.preLedger.thetaSigned ∧
        package.preLedger.thetaSigned < 0) ∨
      (-1 : Real) < estimate.cTheta

set_option linter.style.longLine false in
theorem localGlobalCThetaDerivationAudit
    (source :
      ConstructedTheorem311OneSidedFinitePlaceLocalGlobalCThetaSource
        sourceData estimate l place) :
    LocalGlobalCThetaDerivationAudit source := by
  let coarseSource :=
    source.toConstructedTheorem311OneSidedLocalGlobalCThetaSource
      |>.toConstructedTheorem311IndeterminacyLocalGlobalCThetaSource
  let handoff := coarseSource.localGlobalHandoffAudit
  exact
    { summed_stepXI_haar_bound := source.summed_stepXI_haar_bound,
      arithmeticGap_dominates_canonicalCThetaScale :=
        source.arithmeticGap_dominates_canonicalCThetaScale,
      arithmeticGapCThetaChainAudit :=
        coarseSource.arithmeticGapCThetaChainAudit,
      iutIVCThetaExpression := handoff.iutIVCThetaExpression,
      canonicalCThetaScale_le_iutIVCTheta :=
        source.canonicalCThetaScale_le_iutIVCTheta,
      handoffAudit := handoff,
      globalScaleComparisonAudit := handoff.globalScaleComparisonAudit,
      endpoint := source.endpoint,
      thetaSigned_le_iutIVCTheta_absLogQ :=
        handoff.thetaSigned_le_iutIVCTheta_absLogQ,
      dichotomy := handoff.dichotomy }

set_option linter.style.longLine false in
/--
Explicit IUT IV arithmetic-gap handoff for the one-sided finite-place source.

This audit keeps the whole ordered-real calculation visible in one declaration:
the canonical scale and IUT IV upper/main terms are identified with finite
sums, the summed Step~(xi)/Haar bound and total Haar defect produce
`C_{Theta,can} + 1 <= A - M`, and the IUT IV identity
`C_Theta + 1 = A - M` gives the final
`C_{Theta,can} <= C_Theta` comparison by cancelling the common unit.
-/
structure IUTIVArithmeticGapHandoffAudit
    (source :
      ConstructedTheorem311OneSidedFinitePlaceLocalGlobalCThetaSource
        sourceData estimate l place) : Prop where
  canonicalCThetaScale_eq_sum :
    sourceData.canonicalCThetaScale =
      ∑ place, source.localCanonicalScale place
  arithmeticUpperTerm_eq_sum :
    estimate.arithmeticUpperTerm =
      ∑ place, source.localArithmeticUpperContribution place
  mainLogTerm_eq_sum :
    estimate.mainLogTerm =
      ∑ place, source.localMainLogContribution place
  summed_stepXI_haar_bound :
    (∑ place, source.localCanonicalScale place) +
        ∑ place, source.localHaarNormalizationDefect place <=
      (∑ place, source.localArithmeticUpperContribution place) -
        ∑ place, source.localMainLogContribution place
  total_haar_defect_ge_one :
    (1 : Real) <= ∑ place, source.localHaarNormalizationDefect place
  arithmeticGap_dominates_canonicalCThetaScale :
    sourceData.canonicalCThetaScale + 1 <=
      estimate.arithmeticUpperTerm - estimate.mainLogTerm
  iutIV_cTheta_plus_one_eq_arithmeticGap :
    estimate.cTheta + 1 =
      estimate.arithmeticUpperTerm - estimate.mainLogTerm
  canonicalCThetaScale_plus_one_le_iutIVCTheta_plus_one :
    sourceData.canonicalCThetaScale + 1 <= estimate.cTheta + 1
  canonicalCThetaScale_le_iutIVCTheta :
    sourceData.canonicalCThetaScale <= estimate.cTheta
  localGlobalCThetaDerivationAudit :
    LocalGlobalCThetaDerivationAudit source

set_option linter.style.longLine false in
theorem iutIVArithmeticGapHandoffAudit
    (source :
      ConstructedTheorem311OneSidedFinitePlaceLocalGlobalCThetaSource
        sourceData estimate l place) :
    IUTIVArithmeticGapHandoffAudit source :=
  let derivationAudit := source.localGlobalCThetaDerivationAudit
  let arithmeticGapAudit :=
    derivationAudit.arithmeticGapCThetaChainAudit
  { canonicalCThetaScale_eq_sum :=
      source.canonicalCThetaScale_eq_sum,
    arithmeticUpperTerm_eq_sum :=
      source.arithmeticUpperTerm_eq_sum,
    mainLogTerm_eq_sum :=
      source.mainLogTerm_eq_sum,
    summed_stepXI_haar_bound :=
      derivationAudit.summed_stepXI_haar_bound,
    total_haar_defect_ge_one :=
      source.total_haar_defect_ge_one,
    arithmeticGap_dominates_canonicalCThetaScale :=
      derivationAudit.arithmeticGap_dominates_canonicalCThetaScale,
    iutIV_cTheta_plus_one_eq_arithmeticGap :=
      arithmeticGapAudit.iutIV_cTheta_plus_one_eq_arithmeticGap,
    canonicalCThetaScale_plus_one_le_iutIVCTheta_plus_one :=
      arithmeticGapAudit.canonicalCThetaScale_plus_one_le_iutIVCTheta_plus_one,
    canonicalCThetaScale_le_iutIVCTheta :=
      arithmeticGapAudit.canonicalCThetaScale_le_iutIVCTheta,
    localGlobalCThetaDerivationAudit :=
      derivationAudit }

set_option linter.style.longLine false in
/--
Concrete audit for the four assembly slots of the coarse local-global source.

The closed endpoint still consumes
`ConstructedTheorem311IndeterminacyLocalGlobalCThetaSource`, whose assembly
surface has four generic `Prop` fields.  For a one-sided finite-place source
these four fields are not opaque: they are definitionally the canonical-scale
finite-sum identity, the total Haar-defect bound, the IUT IV upper/main finite
sum identities, and the local Step (xi)/Haar inequality family.
-/
structure CoarseAssemblyConcreteAudit
    (source :
      ConstructedTheorem311OneSidedFinitePlaceLocalGlobalCThetaSource
        sourceData estimate l place) : Prop where
  coarseEndpoint :
    ConstructedTheorem311IndeterminacyLocalGlobalCThetaSource.Endpoint
      source.toConstructedTheorem311OneSidedLocalGlobalCThetaSource.toConstructedTheorem311IndeterminacyLocalGlobalCThetaSource
  localPlaceLogVolumeAssembly_eq_finiteSum :
    source.toConstructedTheorem311OneSidedLocalGlobalCThetaSource.toConstructedTheorem311IndeterminacyLocalGlobalCThetaSource.localPlaceLogVolumeAssembly =
      (sourceData.canonicalCThetaScale =
        ∑ place, source.localCanonicalScale place)
  finiteDivisorValuationBallHaarNormalization_eq_totalDefect :
    source.toConstructedTheorem311OneSidedLocalGlobalCThetaSource.toConstructedTheorem311IndeterminacyLocalGlobalCThetaSource.finiteDivisorValuationBallHaarNormalization =
      ((1 : Real) <= ∑ place, source.localHaarNormalizationDefect place)
  productSumLocalToGlobalAssembly_eq_finiteSums :
    source.toConstructedTheorem311OneSidedLocalGlobalCThetaSource.toConstructedTheorem311IndeterminacyLocalGlobalCThetaSource.productSumLocalToGlobalAssembly =
      (estimate.arithmeticUpperTerm =
          ∑ place, source.localArithmeticUpperContribution place ∧
        estimate.mainLogTerm =
          ∑ place, source.localMainLogContribution place)
  theorem311IndeterminacyToStepXICompatibility_eq_localBounds :
    source.toConstructedTheorem311OneSidedLocalGlobalCThetaSource.toConstructedTheorem311IndeterminacyLocalGlobalCThetaSource.theorem311IndeterminacyToStepXICompatibility =
      (∀ place,
        source.localCanonicalScale place +
            source.localHaarNormalizationDefect place <=
          source.localArithmeticUpperContribution place -
            source.localMainLogContribution place)
  localPlaceLogVolumeAssembly_holds :
    sourceData.canonicalCThetaScale =
      ∑ place, source.localCanonicalScale place
  finiteDivisorValuationBallHaarNormalization_holds :
    (1 : Real) <= ∑ place, source.localHaarNormalizationDefect place
  productSumLocalToGlobalAssembly_holds :
    estimate.arithmeticUpperTerm =
        ∑ place, source.localArithmeticUpperContribution place ∧
      estimate.mainLogTerm =
        ∑ place, source.localMainLogContribution place
  theorem311IndeterminacyToStepXICompatibility_holds :
    ∀ place,
      source.localCanonicalScale place +
          source.localHaarNormalizationDefect place <=
        source.localArithmeticUpperContribution place -
          source.localMainLogContribution place

set_option linter.style.longLine false in
theorem coarseAssemblyConcreteAudit
    (source :
      ConstructedTheorem311OneSidedFinitePlaceLocalGlobalCThetaSource
        sourceData estimate l place) :
    CoarseAssemblyConcreteAudit source :=
  { coarseEndpoint :=
      source.toConstructedTheorem311OneSidedLocalGlobalCThetaSource
        |>.toConstructedTheorem311IndeterminacyLocalGlobalCThetaSource
        |>.endpoint,
    localPlaceLogVolumeAssembly_eq_finiteSum := rfl,
    finiteDivisorValuationBallHaarNormalization_eq_totalDefect := rfl,
    productSumLocalToGlobalAssembly_eq_finiteSums := rfl,
    theorem311IndeterminacyToStepXICompatibility_eq_localBounds := rfl,
    localPlaceLogVolumeAssembly_holds :=
      source.canonicalCThetaScale_eq_sum,
    finiteDivisorValuationBallHaarNormalization_holds :=
      source.total_haar_defect_ge_one,
    productSumLocalToGlobalAssembly_holds :=
      ⟨source.arithmeticUpperTerm_eq_sum, source.mainLogTerm_eq_sum⟩,
    theorem311IndeterminacyToStepXICompatibility_holds :=
      source.local_stepXI_haar_bound }

end ConstructedTheorem311OneSidedFinitePlaceLocalGlobalCThetaSource

set_option linter.style.longLine false in
/--
Concrete Hodge-theater/log-theta finite-place local-to-global `C_Theta` source.

This is the concrete-source version of the one-sided finite-place handoff:
the Remark 3.9.5 hull/determinant source is constructed internally from the
quotient theta-pilot source, and the global `C_Theta` comparison is then
derived from finite local scale/upper/main/Haar-defect data.  Thus the concrete
Theorem 3.11 quotient layer no longer stops at a raw
`canonicalCThetaScale <= C_Theta` hypothesis.
-/
noncomputable def concreteHodgeTheaterLogThetaQuotientThetaPilotSource_toOneSidedFinitePlaceLocalGlobalCThetaSource
    {source target : Copy} {coric : Type u}
    {l : PrimeGeFive}
    {package :
      IUTStage1SourcePackage source target
        (IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l)}
    {record : IUTStage1Theorem311MultiradialSourceRecord package}
    {indData :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice.IndeterminacyData coric l}
    (sourceData :
      ConcreteHodgeTheaterLogThetaQuotientThetaPilotSource record indData)
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (hullOperator :
      IUTStage1Remark395HolomorphicHullOperator (Point target))
    {β : Type v} [Fintype β]
    {γ : Type w} [Fintype γ]
    (ob3ob4Source :
      IUTStage1Remark395Ob3Ob4AdjustedDeterminantSource β γ)
    (compatibility :
      IUTStage1HullApproximantWeightedDeterminantCompatibility
        (IUTStage1HullLogVolumeApproximant.canonical
          (IUTStage1HolomorphicHullLogVolumeShadow.ofRemark395Operator
            hullOperator)
          (recordThetaPossibleImageUnion record))
        ob3ob4Source.toWeightedDeterminantSource)
    (measure_eq_hullLogVolume :
      package.preLedger.measure =
        (IUTStage1HolomorphicHullLogVolumeShadow.ofRemark395Operator
          hullOperator).toRegionMeasure)
    (tensorPower_bound :
      (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
          ob3ob4Source.toWeightedDeterminantSource).normalizedLogVolume <=
        package.preLedger.thetaSigned)
    (hullDetBridge_eq :
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        recordCanonicalHullTensorPowerHullDetDataOfQSubsetUnion
          (record := record)
          operation hullOperation determinantOperation
          (IUTStage1HolomorphicHullLogVolumeShadow.ofRemark395Operator
            hullOperator)
          sourceData.toConstruction.selectedQRegion.toSet
          sourceData.toConstruction.selectedQRegion_subset_recordUnion
          ob3ob4Source.toWeightedDeterminantSource compatibility
          measure_eq_hullLogVolume tensorPower_bound)
    (q_pilot_positive : 0 < -package.preLedger.qSigned)
    (normalization : package.preLedger.normalization)
    (estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow)
    (place : Type x) [Fintype place]
    (localCanonicalScale : place -> Real)
    (localArithmeticUpperContribution : place -> Real)
    (localMainLogContribution : place -> Real)
    (localHaarNormalizationDefect : place -> Real)
    (canonicalCThetaScale_eq_sum :
      (sourceData.toRemark395ConstructedHolomorphicHullDeterminantSource
        operation hullOperation determinantOperation hullOperator
        ob3ob4Source compatibility measure_eq_hullLogVolume
        tensorPower_bound hullDetBridge_eq q_pilot_positive
        normalization).canonicalCThetaScale =
          ∑ place, localCanonicalScale place)
    (arithmeticUpperTerm_eq_sum :
      estimate.arithmeticUpperTerm =
        ∑ place, localArithmeticUpperContribution place)
    (mainLogTerm_eq_sum :
      estimate.mainLogTerm = ∑ place, localMainLogContribution place)
    (local_stepXI_haar_bound :
      ∀ place,
        localCanonicalScale place + localHaarNormalizationDefect place <=
          localArithmeticUpperContribution place -
            localMainLogContribution place)
    (total_haar_defect_ge_one :
      (1 : Real) <= ∑ place, localHaarNormalizationDefect place) :
    ConstructedTheorem311OneSidedFinitePlaceLocalGlobalCThetaSource
      (sourceData.toRemark395ConstructedHolomorphicHullDeterminantSource
        operation hullOperation determinantOperation hullOperator
        ob3ob4Source compatibility measure_eq_hullLogVolume
        tensorPower_bound hullDetBridge_eq q_pilot_positive normalization)
      estimate l place :=
  { oneSidedMultiradialSource := sourceData.toConstruction,
    qPilotRegion_eq_selectedQRegion := rfl,
    localCanonicalScale := localCanonicalScale,
    localArithmeticUpperContribution := localArithmeticUpperContribution,
    localMainLogContribution := localMainLogContribution,
    localHaarNormalizationDefect := localHaarNormalizationDefect,
    canonicalCThetaScale_eq_sum := canonicalCThetaScale_eq_sum,
    arithmeticUpperTerm_eq_sum := arithmeticUpperTerm_eq_sum,
    mainLogTerm_eq_sum := mainLogTerm_eq_sum,
    local_stepXI_haar_bound := local_stepXI_haar_bound,
    total_haar_defect_ge_one := total_haar_defect_ge_one }

set_option linter.style.longLine false in
/--
Endpoint audit for the concrete Hodge-theater/log-theta finite-place
local-to-global source.

The returned certificate keeps the concrete quotient selected-q facts next to
the finite-place `C_Theta` derivation: selected q-region, quotient-image
identity, local summed Step (xi)/Haar bound, the derived
`C_{Theta,can} <= C_Theta` comparison, the global signed bound, and the final
Corollary 3.12 dichotomy.
-/
theorem concreteHodgeTheaterLogThetaQuotientThetaPilotSource_toOneSidedFinitePlaceLocalGlobalCThetaSource_endpoint
    {source target : Copy} {coric : Type u}
    {l : PrimeGeFive}
    {package :
      IUTStage1SourcePackage source target
        (IUTStage1ConcreteHodgeTheaterLogThetaChoice coric l)}
    {record : IUTStage1Theorem311MultiradialSourceRecord package}
    {indData :
      IUTStage1ConcreteHodgeTheaterLogThetaChoice.IndeterminacyData coric l}
    (sourceData :
      ConcreteHodgeTheaterLogThetaQuotientThetaPilotSource record indData)
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (hullOperator :
      IUTStage1Remark395HolomorphicHullOperator (Point target))
    {β : Type v} [Fintype β]
    {γ : Type w} [Fintype γ]
    (ob3ob4Source :
      IUTStage1Remark395Ob3Ob4AdjustedDeterminantSource β γ)
    (compatibility :
      IUTStage1HullApproximantWeightedDeterminantCompatibility
        (IUTStage1HullLogVolumeApproximant.canonical
          (IUTStage1HolomorphicHullLogVolumeShadow.ofRemark395Operator
            hullOperator)
          (recordThetaPossibleImageUnion record))
        ob3ob4Source.toWeightedDeterminantSource)
    (measure_eq_hullLogVolume :
      package.preLedger.measure =
        (IUTStage1HolomorphicHullLogVolumeShadow.ofRemark395Operator
          hullOperator).toRegionMeasure)
    (tensorPower_bound :
      (IUTStage1NaiveFrobeniusTensorPowerLogVolume.ofWeightedDeterminant
          ob3ob4Source.toWeightedDeterminantSource).normalizedLogVolume <=
        package.preLedger.thetaSigned)
    (hullDetBridge_eq :
      package.preLedger.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        recordCanonicalHullTensorPowerHullDetDataOfQSubsetUnion
          (record := record)
          operation hullOperation determinantOperation
          (IUTStage1HolomorphicHullLogVolumeShadow.ofRemark395Operator
            hullOperator)
          sourceData.toConstruction.selectedQRegion.toSet
          sourceData.toConstruction.selectedQRegion_subset_recordUnion
          ob3ob4Source.toWeightedDeterminantSource compatibility
          measure_eq_hullLogVolume tensorPower_bound)
    (q_pilot_positive : 0 < -package.preLedger.qSigned)
    (normalization : package.preLedger.normalization)
    (estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow)
    (place : Type x) [Fintype place]
    (localCanonicalScale : place -> Real)
    (localArithmeticUpperContribution : place -> Real)
    (localMainLogContribution : place -> Real)
    (localHaarNormalizationDefect : place -> Real)
    (canonicalCThetaScale_eq_sum :
      (sourceData.toRemark395ConstructedHolomorphicHullDeterminantSource
        operation hullOperation determinantOperation hullOperator
        ob3ob4Source compatibility measure_eq_hullLogVolume
        tensorPower_bound hullDetBridge_eq q_pilot_positive
        normalization).canonicalCThetaScale =
          ∑ place, localCanonicalScale place)
    (arithmeticUpperTerm_eq_sum :
      estimate.arithmeticUpperTerm =
        ∑ place, localArithmeticUpperContribution place)
    (mainLogTerm_eq_sum :
      estimate.mainLogTerm = ∑ place, localMainLogContribution place)
    (local_stepXI_haar_bound :
      ∀ place,
        localCanonicalScale place + localHaarNormalizationDefect place <=
          localArithmeticUpperContribution place -
            localMainLogContribution place)
    (total_haar_defect_ge_one :
      (1 : Real) <= ∑ place, localHaarNormalizationDefect place) :
    let constructedSource :=
      sourceData.toRemark395ConstructedHolomorphicHullDeterminantSource
        operation hullOperation determinantOperation hullOperator
        ob3ob4Source compatibility measure_eq_hullLogVolume
        tensorPower_bound hullDetBridge_eq q_pilot_positive normalization;
    let localGlobalSource :=
      concreteHodgeTheaterLogThetaQuotientThetaPilotSource_toOneSidedFinitePlaceLocalGlobalCThetaSource
        sourceData operation hullOperation determinantOperation hullOperator
        ob3ob4Source compatibility measure_eq_hullLogVolume
        tensorPower_bound hullDetBridge_eq q_pilot_positive normalization
        estimate place localCanonicalScale localArithmeticUpperContribution
        localMainLogContribution localHaarNormalizationDefect
        canonicalCThetaScale_eq_sum arithmeticUpperTerm_eq_sum
        mainLogTerm_eq_sum local_stepXI_haar_bound total_haar_defect_ge_one;
    constructedSource.qPilotRegion =
        sourceData.toConstruction.selectedQRegion.toSet ∧
      constructedSource.qPilotRegion =
        (sourceData.quotientImages.region
          ((IUTStage1Theorem311TypedIndeterminacyCore.ConcreteHodgeTheaterLogTheta.typedCore
              indData).equalityQuotientMap sourceData.selectedQChoice)).toSet ∧
      ConstructedTheorem311OneSidedFinitePlaceLocalGlobalCThetaSource.LocalGlobalCThetaDerivationAudit
        localGlobalSource ∧
      constructedSource.canonicalCThetaScale <= estimate.cTheta ∧
      package.preLedger.thetaSigned <=
        estimate.cTheta * (-package.preLedger.qSigned) ∧
      constructedSource.hullOperator.logVolume constructedSource.qPilotRegion <=
        estimate.cTheta * (-package.preLedger.qSigned) ∧
      ((package.preLedger.qSigned = package.preLedger.thetaSigned ∧
          package.preLedger.thetaSigned < 0) ∨
        (-1 : Real) < estimate.cTheta) := by
  intro constructedSource localGlobalSource
  let sourceEndpoint :=
    sourceData.toRemark395ConstructedHolomorphicHullDeterminantSource_endpoint
      operation hullOperation determinantOperation hullOperator
      ob3ob4Source compatibility measure_eq_hullLogVolume
      tensorPower_bound hullDetBridge_eq q_pilot_positive normalization
  let derivationAudit :=
    localGlobalSource.localGlobalCThetaDerivationAudit
  exact
    ⟨sourceEndpoint.1,
      sourceEndpoint.2.1,
      derivationAudit,
      derivationAudit.canonicalCThetaScale_le_iutIVCTheta,
      derivationAudit.thetaSigned_le_iutIVCTheta_absLogQ,
      derivationAudit.handoffAudit.sourceBridge_to_iutIVCTheta_chain,
      derivationAudit.dichotomy⟩

set_option linter.style.longLine false in
/--
Strict finite-toy constructor for the one-sided finite-place local-to-global
`C_Theta` source.

This bridges the two-point typed `(Ind1)/(Ind2)/(Ind3)` model into the actual
finite-place summation object used by the closed `C_Theta` corridor.  The local
Step~(xi)/Haar data are still supplied as source data, but the Theorem 3.11
multiradial quotient layer is the strict finite construction, so the resulting
source carries the non-equality of the `(Ind3)` step through the local-to-global
comparison.
-/
def strictFiniteToyOneSidedFinitePlaceLocalGlobalCThetaSource
    {source target : Copy}
    {package : IUTStage1SourcePackage source target (Fin 2)}
    {record : IUTStage1Theorem311MultiradialSourceRecord package}
    {β : Type v} [Fintype β]
    (sourceData :
      IUTStage1SourcePackage.IUTStage1Remark395ConstructedHolomorphicHullDeterminantSource
        (β := β) record)
    (estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow)
    (l : PrimeGeFive)
    (gluingTorsor : IUTStage1ThetaNFBridgeGluingTorsor l)
    (images_eq_strict :
      record.thetaPossibleImages.images =
        IUTStage1Theorem311TypedIndeterminacyCore.strictFiniteToyPossibleImageFamily
          target)
    (selectedQChoice : Fin 2)
    (qPilotRegion_eq_selected :
      sourceData.qPilotRegion =
        IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImage
          record selectedQChoice)
    (place : Type x) [Fintype place]
    (localCanonicalScale : place -> Real)
    (localArithmeticUpperContribution : place -> Real)
    (localMainLogContribution : place -> Real)
    (localHaarNormalizationDefect : place -> Real)
    (canonicalCThetaScale_eq_sum :
      sourceData.canonicalCThetaScale = ∑ place, localCanonicalScale place)
    (arithmeticUpperTerm_eq_sum :
      estimate.arithmeticUpperTerm =
        ∑ place, localArithmeticUpperContribution place)
    (mainLogTerm_eq_sum :
      estimate.mainLogTerm = ∑ place, localMainLogContribution place)
    (local_stepXI_haar_bound :
      ∀ place,
        localCanonicalScale place + localHaarNormalizationDefect place <=
          localArithmeticUpperContribution place -
            localMainLogContribution place)
    (total_haar_defect_ge_one :
      (1 : Real) <= ∑ place, localHaarNormalizationDefect place) :
    ConstructedTheorem311OneSidedFinitePlaceLocalGlobalCThetaSource
      sourceData estimate l place :=
  { oneSidedMultiradialSource :=
      IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.strictFiniteToyOneSidedMultiradialConstructionSource
        record l gluingTorsor images_eq_strict selectedQChoice,
    qPilotRegion_eq_selectedQRegion := by
      simpa [
        IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.strictFiniteToyOneSidedMultiradialConstructionSource,
        IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.IUTStage1Theorem311OneSidedMultiradialConstructionSource.selectedQRegion_eq_recordThetaPossibleImage
      ] using qPilotRegion_eq_selected,
    localCanonicalScale := localCanonicalScale,
    localArithmeticUpperContribution := localArithmeticUpperContribution,
    localMainLogContribution := localMainLogContribution,
    localHaarNormalizationDefect := localHaarNormalizationDefect,
    canonicalCThetaScale_eq_sum := canonicalCThetaScale_eq_sum,
    arithmeticUpperTerm_eq_sum := arithmeticUpperTerm_eq_sum,
    mainLogTerm_eq_sum := mainLogTerm_eq_sum,
    local_stepXI_haar_bound := local_stepXI_haar_bound,
    total_haar_defect_ge_one := total_haar_defect_ge_one }

set_option linter.style.longLine false in
/--
Audit for the strict finite-toy local-to-global `C_Theta` source.

The audit keeps three facts adjacent: the finite-place `C_Theta` derivation, the
closed one-sided local-global endpoint, and the strict `(Ind3)` non-collapse
inside the same source object.
-/
structure StrictFiniteToyOneSidedFinitePlaceLocalGlobalCThetaAudit
    {source target : Copy}
    {package : IUTStage1SourcePackage source target (Fin 2)}
    {record : IUTStage1Theorem311MultiradialSourceRecord package}
    {β : Type v} [Fintype β]
    {sourceData :
      IUTStage1SourcePackage.IUTStage1Remark395ConstructedHolomorphicHullDeterminantSource
        (β := β) record}
    {estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow}
    {l : PrimeGeFive}
    {place : Type x} [Fintype place]
    (localGlobalSource :
      ConstructedTheorem311OneSidedFinitePlaceLocalGlobalCThetaSource
        sourceData estimate l place) :
    Prop where
  endpoint :
    ConstructedTheorem311OneSidedLocalGlobalCThetaSource.Endpoint
      localGlobalSource.toConstructedTheorem311OneSidedLocalGlobalCThetaSource
  localGlobalCThetaDerivationAudit :
    ConstructedTheorem311OneSidedFinitePlaceLocalGlobalCThetaSource.LocalGlobalCThetaDerivationAudit
      localGlobalSource
  arithmeticGap_dominates_canonicalCThetaScale :
    sourceData.canonicalCThetaScale + 1 <=
      estimate.arithmeticUpperTerm - estimate.mainLogTerm
  canonicalCThetaScale_le_iutIVCTheta :
    sourceData.canonicalCThetaScale <= estimate.cTheta
  thetaSigned_le_iutIVCTheta_absLogQ :
    package.preLedger.thetaSigned <=
      estimate.cTheta * (-package.preLedger.qSigned)
  ind3_step_strict_not_equalized :
    localGlobalSource.oneSidedMultiradialSource.typedIndeterminacyCore.ind3.step
        (0 : Fin 2) (1 : Fin 2) ∧
      localGlobalSource.oneSidedMultiradialSource.typedIndeterminacyCore.logVolume
          (0 : Fin 2) <
        localGlobalSource.oneSidedMultiradialSource.typedIndeterminacyCore.logVolume
          (1 : Fin 2) ∧
      (1 : Fin 2) ∉
        localGlobalSource.oneSidedMultiradialSource.typedIndeterminacyCore.equalityOrbit
          (0 : Fin 2) ∧
      localGlobalSource.oneSidedMultiradialSource.typedIndeterminacyCore.equalityQuotientMap
          (0 : Fin 2) ≠
        localGlobalSource.oneSidedMultiradialSource.typedIndeterminacyCore.equalityQuotientMap
          (1 : Fin 2) ∧
      (∀ {choice₁ choice₂ : Fin 2},
        localGlobalSource.oneSidedMultiradialSource.typedIndeterminacyCore.equalityGenerators.ind3_step
          choice₁ choice₂ -> False)

set_option linter.style.longLine false in
theorem strictFiniteToyOneSidedFinitePlaceLocalGlobalCThetaSource_audit
    {source target : Copy}
    {package : IUTStage1SourcePackage source target (Fin 2)}
    {record : IUTStage1Theorem311MultiradialSourceRecord package}
    {β : Type v} [Fintype β]
    (sourceData :
      IUTStage1SourcePackage.IUTStage1Remark395ConstructedHolomorphicHullDeterminantSource
        (β := β) record)
    (estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow)
    (l : PrimeGeFive)
    (gluingTorsor : IUTStage1ThetaNFBridgeGluingTorsor l)
    (images_eq_strict :
      record.thetaPossibleImages.images =
        IUTStage1Theorem311TypedIndeterminacyCore.strictFiniteToyPossibleImageFamily
          target)
    (selectedQChoice : Fin 2)
    (qPilotRegion_eq_selected :
      sourceData.qPilotRegion =
        IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImage
          record selectedQChoice)
    (place : Type x) [Fintype place]
    (localCanonicalScale : place -> Real)
    (localArithmeticUpperContribution : place -> Real)
    (localMainLogContribution : place -> Real)
    (localHaarNormalizationDefect : place -> Real)
    (canonicalCThetaScale_eq_sum :
      sourceData.canonicalCThetaScale = ∑ place, localCanonicalScale place)
    (arithmeticUpperTerm_eq_sum :
      estimate.arithmeticUpperTerm =
        ∑ place, localArithmeticUpperContribution place)
    (mainLogTerm_eq_sum :
      estimate.mainLogTerm = ∑ place, localMainLogContribution place)
    (local_stepXI_haar_bound :
      ∀ place,
        localCanonicalScale place + localHaarNormalizationDefect place <=
          localArithmeticUpperContribution place -
            localMainLogContribution place)
    (total_haar_defect_ge_one :
      (1 : Real) <= ∑ place, localHaarNormalizationDefect place) :
    let localGlobalSource :=
      strictFiniteToyOneSidedFinitePlaceLocalGlobalCThetaSource
        sourceData estimate l gluingTorsor images_eq_strict selectedQChoice
        qPilotRegion_eq_selected place localCanonicalScale
        localArithmeticUpperContribution localMainLogContribution
        localHaarNormalizationDefect canonicalCThetaScale_eq_sum
        arithmeticUpperTerm_eq_sum mainLogTerm_eq_sum local_stepXI_haar_bound
        total_haar_defect_ge_one;
    StrictFiniteToyOneSidedFinitePlaceLocalGlobalCThetaAudit localGlobalSource := by
  intro localGlobalSource
  have hstrict :=
    IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.strictFiniteToyOneSidedMultiradialConstructionSource_ind3_not_equalized
      record l gluingTorsor images_eq_strict selectedQChoice
  exact
    { endpoint := localGlobalSource.endpoint,
      localGlobalCThetaDerivationAudit :=
        localGlobalSource.localGlobalCThetaDerivationAudit,
      arithmeticGap_dominates_canonicalCThetaScale :=
        localGlobalSource.arithmeticGap_dominates_canonicalCThetaScale,
      canonicalCThetaScale_le_iutIVCTheta :=
        localGlobalSource.canonicalCThetaScale_le_iutIVCTheta,
      thetaSigned_le_iutIVCTheta_absLogQ :=
        localGlobalSource.localGlobalCThetaDerivationAudit.thetaSigned_le_iutIVCTheta_absLogQ,
      ind3_step_strict_not_equalized := by
        simpa [
          strictFiniteToyOneSidedFinitePlaceLocalGlobalCThetaSource
        ] using hstrict }

set_option linter.style.longLine false in
/--
Strict finite-toy audit for the explicit IUT IV arithmetic-gap handoff.

This is the nonvacuity check for the local-to-global handoff certificate:
the same two-point typed `(Ind1)/(Ind2)/(Ind3)` source that keeps the strict
`(Ind3)` step outside the equality quotient also carries the finite-sum
identifications, summed Step~(xi)/Haar bound, IUT IV `C_Theta + 1 = A - M`
identity, and final `C_{Theta,can} <= C_Theta` cancellation.
-/
structure StrictFiniteToyOneSidedIUTIVArithmeticGapHandoffAudit
    {source target : Copy}
    {package : IUTStage1SourcePackage source target (Fin 2)}
    {record : IUTStage1Theorem311MultiradialSourceRecord package}
    {β : Type v} [Fintype β]
    {sourceData :
      IUTStage1SourcePackage.IUTStage1Remark395ConstructedHolomorphicHullDeterminantSource
        (β := β) record}
    {estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow}
    {l : PrimeGeFive}
    {place : Type x} [Fintype place]
    (localGlobalSource :
      ConstructedTheorem311OneSidedFinitePlaceLocalGlobalCThetaSource
        sourceData estimate l place) :
    Prop where
  strictFinitePlaceAudit :
    StrictFiniteToyOneSidedFinitePlaceLocalGlobalCThetaAudit localGlobalSource
  iutIVArithmeticGapHandoffAudit :
    ConstructedTheorem311OneSidedFinitePlaceLocalGlobalCThetaSource.IUTIVArithmeticGapHandoffAudit
      localGlobalSource
  canonicalCThetaScale_eq_sum :
    sourceData.canonicalCThetaScale =
      ∑ place, localGlobalSource.localCanonicalScale place
  summed_stepXI_haar_bound :
    (∑ place, localGlobalSource.localCanonicalScale place) +
        ∑ place, localGlobalSource.localHaarNormalizationDefect place <=
      (∑ place, localGlobalSource.localArithmeticUpperContribution place) -
        ∑ place, localGlobalSource.localMainLogContribution place
  iutIV_cTheta_plus_one_eq_arithmeticGap :
    estimate.cTheta + 1 =
      estimate.arithmeticUpperTerm - estimate.mainLogTerm
  canonicalCThetaScale_le_iutIVCTheta :
    sourceData.canonicalCThetaScale <= estimate.cTheta
  ind3_step_strict_not_equalized :
    localGlobalSource.oneSidedMultiradialSource.typedIndeterminacyCore.ind3.step
        (0 : Fin 2) (1 : Fin 2) ∧
      localGlobalSource.oneSidedMultiradialSource.typedIndeterminacyCore.logVolume
          (0 : Fin 2) <
        localGlobalSource.oneSidedMultiradialSource.typedIndeterminacyCore.logVolume
          (1 : Fin 2) ∧
      (1 : Fin 2) ∉
        localGlobalSource.oneSidedMultiradialSource.typedIndeterminacyCore.equalityOrbit
          (0 : Fin 2) ∧
      localGlobalSource.oneSidedMultiradialSource.typedIndeterminacyCore.equalityQuotientMap
          (0 : Fin 2) ≠
        localGlobalSource.oneSidedMultiradialSource.typedIndeterminacyCore.equalityQuotientMap
          (1 : Fin 2) ∧
      (∀ {choice₁ choice₂ : Fin 2},
        localGlobalSource.oneSidedMultiradialSource.typedIndeterminacyCore.equalityGenerators.ind3_step
          choice₁ choice₂ -> False)

set_option linter.style.longLine false in
theorem strictFiniteToyOneSidedIUTIVArithmeticGapHandoffAudit
    {source target : Copy}
    {package : IUTStage1SourcePackage source target (Fin 2)}
    {record : IUTStage1Theorem311MultiradialSourceRecord package}
    {β : Type v} [Fintype β]
    (sourceData :
      IUTStage1SourcePackage.IUTStage1Remark395ConstructedHolomorphicHullDeterminantSource
        (β := β) record)
    (estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow)
    (l : PrimeGeFive)
    (gluingTorsor : IUTStage1ThetaNFBridgeGluingTorsor l)
    (images_eq_strict :
      record.thetaPossibleImages.images =
        IUTStage1Theorem311TypedIndeterminacyCore.strictFiniteToyPossibleImageFamily
          target)
    (selectedQChoice : Fin 2)
    (qPilotRegion_eq_selected :
      sourceData.qPilotRegion =
        IUTStage1SourcePackage.IUTStage1Theorem311HullDetSourceConstructor.recordThetaPossibleImage
          record selectedQChoice)
    (place : Type x) [Fintype place]
    (localCanonicalScale : place -> Real)
    (localArithmeticUpperContribution : place -> Real)
    (localMainLogContribution : place -> Real)
    (localHaarNormalizationDefect : place -> Real)
    (canonicalCThetaScale_eq_sum :
      sourceData.canonicalCThetaScale = ∑ place, localCanonicalScale place)
    (arithmeticUpperTerm_eq_sum :
      estimate.arithmeticUpperTerm =
        ∑ place, localArithmeticUpperContribution place)
    (mainLogTerm_eq_sum :
      estimate.mainLogTerm = ∑ place, localMainLogContribution place)
    (local_stepXI_haar_bound :
      ∀ place,
        localCanonicalScale place + localHaarNormalizationDefect place <=
          localArithmeticUpperContribution place -
            localMainLogContribution place)
    (total_haar_defect_ge_one :
      (1 : Real) <= ∑ place, localHaarNormalizationDefect place) :
    let localGlobalSource :=
      strictFiniteToyOneSidedFinitePlaceLocalGlobalCThetaSource
        sourceData estimate l gluingTorsor images_eq_strict selectedQChoice
        qPilotRegion_eq_selected place localCanonicalScale
        localArithmeticUpperContribution localMainLogContribution
        localHaarNormalizationDefect canonicalCThetaScale_eq_sum
        arithmeticUpperTerm_eq_sum mainLogTerm_eq_sum local_stepXI_haar_bound
        total_haar_defect_ge_one;
    StrictFiniteToyOneSidedIUTIVArithmeticGapHandoffAudit localGlobalSource := by
  intro localGlobalSource
  let strictAudit :=
    strictFiniteToyOneSidedFinitePlaceLocalGlobalCThetaSource_audit
      sourceData estimate l gluingTorsor images_eq_strict selectedQChoice
      qPilotRegion_eq_selected place localCanonicalScale
      localArithmeticUpperContribution localMainLogContribution
      localHaarNormalizationDefect canonicalCThetaScale_eq_sum
      arithmeticUpperTerm_eq_sum mainLogTerm_eq_sum local_stepXI_haar_bound
      total_haar_defect_ge_one
  let handoffAudit := localGlobalSource.iutIVArithmeticGapHandoffAudit
  exact
    { strictFinitePlaceAudit := strictAudit,
      iutIVArithmeticGapHandoffAudit := handoffAudit,
      canonicalCThetaScale_eq_sum :=
        handoffAudit.canonicalCThetaScale_eq_sum,
      summed_stepXI_haar_bound :=
        handoffAudit.summed_stepXI_haar_bound,
      iutIV_cTheta_plus_one_eq_arithmeticGap :=
        handoffAudit.iutIV_cTheta_plus_one_eq_arithmeticGap,
      canonicalCThetaScale_le_iutIVCTheta :=
        handoffAudit.canonicalCThetaScale_le_iutIVCTheta,
      ind3_step_strict_not_equalized :=
        strictAudit.ind3_step_strict_not_equalized }


end Experiments
end Stage1
end Iut
