/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Stage1.CorollarySchema

/-!
Ledger of source obligations for the Stage 1 final comparison.

This file packages the hypotheses that future IUT-specific work must supply
before the signed Corollary 3.12 schema can be applied.
-/

namespace Iut
namespace Stage1

open RealLineCopy

/-- A named three-term real comparison `q <= target <= theta`. -/
structure ThreeTermComparison (qSigned targetSigned thetaSigned : Real) where
  q_le_target : qSigned <= targetSigned
  target_le_theta : targetSigned <= thetaSigned

namespace ThreeTermComparison

variable {qSigned targetSigned thetaSigned : Real}

theorem q_le_theta
    (chain : ThreeTermComparison qSigned targetSigned thetaSigned) :
    qSigned <= thetaSigned :=
  le_trans chain.q_le_target chain.target_le_theta

end ThreeTermComparison

/--
Completed source obligations for a structured Stage 1 comparison.

The `normalization` field is intentionally an arbitrary proposition: different
future source-specific constructions may have different normalization statements.
The final inequality does not use this field directly, but the ledger records
that the normalization/comparability obligation has been discharged.
-/
structure SourceObligationLedger
    {source target : Copy} {index : Type u}
    (output : AlgorithmicOutput source target index)
    (measure : RegionMeasure target) (thetaSigned qSigned : Real)
    (normalization : Prop) where
  certified : output.Certified
  certificate : QualitativeData.StructuredCertificate output.family
  chartedContainer : output.ChartedCommonContainerData measure thetaSigned
  she_matches_certificate :
    chartedContainer.commonContainer.hddShe.sheArrow.datum = certificate.she
  qValue : output.ChartedQValueData measure chartedContainer.chart qSigned
  thetaBound :
    output.ChartedThetaBoundData measure chartedContainer.chart thetaSigned
  theta_commonBound :
    output.CommonTargetBound measure thetaSigned
  theta_commonBound_eq_charted :
    theta_commonBound = chartedContainer.apply certificate
  chosenOutput : output.ChosenOutputData
  targetVolume :
    output.ChartedTargetVolumeData measure chartedContainer.chart chosenOutput.choice
  membership :
    output.ChartedMembershipData measure chartedContainer.chart
      qValue chosenOutput targetVolume
  q_positive : 0 < -qSigned
  normalization_proof : normalization

namespace SourceObligationLedger

variable {source target : Copy} {index : Type u}
variable {output : AlgorithmicOutput source target index}
variable {measure : RegionMeasure target}
variable {thetaSigned qSigned : Real}
variable {normalization : Prop}

theorem algorithmCertified (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    output.Certified :=
  ledger.certified

def threeTermComparison (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    ThreeTermComparison qSigned ledger.targetVolume.targetSigned thetaSigned :=
  { q_le_target := ledger.membership.q_le_target,
    target_le_theta := by
      rw [ledger.targetVolume.targetSigned_eq]
      exact TransportedRegionFamily.choice_targetVolume_le_of_commonBound
        ledger.theta_commonBound ledger.chosenOutput.choice }

theorem threeTerm_q_le_target_eq_membership (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    ledger.threeTermComparison.q_le_target =
      ledger.membership.q_le_target :=
  rfl

theorem threeTerm_target_le_theta_eq_commonBound (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    ledger.threeTermComparison.target_le_theta =
      (by
        rw [ledger.targetVolume.targetSigned_eq]
        exact TransportedRegionFamily.choice_targetVolume_le_of_commonBound
          ledger.theta_commonBound ledger.chosenOutput.choice) :=
  rfl

theorem chosenComparisonHoldsQ (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    ledger.chosenOutput.comparison.Holds ledger.qValue.qPoint :=
  ledger.membership.holds

theorem chosenComparisonHoldsQ_eq_membership (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    ledger.chosenComparisonHoldsQ = ledger.membership.holds :=
  rfl

theorem qSigned_le_targetSigned (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    qSigned <= ledger.targetVolume.targetSigned :=
  ledger.membership.q_le_target

theorem qSigned_le_targetSigned_eq_membership (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    ledger.qSigned_le_targetSigned = ledger.membership.q_le_target :=
  rfl

theorem targetSigned_eq_choiceTargetVolume (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    ledger.targetVolume.targetSigned =
      RegionMeasure.targetVolume measure
        (output.comparison ledger.chosenOutput.choice) :=
  ledger.targetVolume.targetSigned_eq

theorem targetSigned_eq_choiceTargetVolume_eq_field (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    ledger.targetSigned_eq_choiceTargetVolume =
      ledger.targetVolume.targetSigned_eq :=
  rfl

theorem choiceTargetVolume_eq_targetSigned (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    RegionMeasure.targetVolume measure
        (output.comparison ledger.chosenOutput.choice) =
      ledger.targetVolume.targetSigned :=
  ledger.targetVolume.targetSigned_eq.symm

theorem targetSigned_le_thetaSigned (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    ledger.targetVolume.targetSigned <= thetaSigned := by
  exact ledger.threeTermComparison.target_le_theta

theorem targetSigned_le_thetaSigned_eq_threeTerm (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    ledger.targetSigned_le_thetaSigned =
      ledger.threeTermComparison.target_le_theta :=
  rfl

theorem targetSigned_le_thetaSigned_eq_commonBound (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    ledger.targetSigned_le_thetaSigned =
      (by
        rw [ledger.targetVolume.targetSigned_eq]
        exact TransportedRegionFamily.choice_targetVolume_le_of_commonBound
          ledger.theta_commonBound ledger.chosenOutput.choice) :=
  rfl

theorem chosenComparison_eq_outputComparison (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    ledger.chosenOutput.comparison =
      output.comparison ledger.chosenOutput.choice :=
  ledger.chosenOutput.comparison_eq

theorem chosenComparison_eq_outputComparison_eq_field (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    ledger.chosenComparison_eq_outputComparison =
      ledger.chosenOutput.comparison_eq :=
  rfl

theorem outputComparison_eq_chosenComparison (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    output.comparison ledger.chosenOutput.choice =
      ledger.chosenOutput.comparison :=
  ledger.chosenOutput.comparison_eq.symm

theorem targetSigned_eq_chosenComparisonVolume (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    ledger.targetVolume.targetSigned =
      RegionMeasure.targetVolume measure ledger.chosenOutput.comparison := by
  rw [ledger.chosenOutput.comparison_eq]
  exact ledger.targetVolume.targetSigned_eq

theorem chosenComparisonVolume_eq_targetSigned (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    RegionMeasure.targetVolume measure ledger.chosenOutput.comparison =
      ledger.targetVolume.targetSigned := by
  rw [ledger.chosenOutput.comparison_eq]
  exact ledger.targetVolume.targetSigned_eq.symm

theorem qSigned_le_thetaSigned (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    qSigned <= thetaSigned :=
  ledger.threeTermComparison.q_le_theta

theorem qSigned_le_thetaSigned_eq_threeTerm (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    ledger.qSigned_le_thetaSigned =
      ledger.threeTermComparison.q_le_theta :=
  rfl

theorem qSigned_le_thetaSigned_eq_membership_commonBound (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    ledger.qSigned_le_thetaSigned =
      le_trans ledger.membership.q_le_target
        (by
          rw [ledger.targetVolume.targetSigned_eq]
          exact TransportedRegionFamily.choice_targetVolume_le_of_commonBound
            ledger.theta_commonBound ledger.chosenOutput.choice) :=
  rfl

theorem corollary312 (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    Corollary312Inequality
      (signedPilotLogVolume PilotSide.theta thetaSigned)
      (signedPilotLogVolume PilotSide.q qSigned) :=
  corollary312_of_signed_le ledger.qSigned_le_thetaSigned

theorem corollary312_eq_threeTermComparison (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    ledger.corollary312 =
      corollary312_of_signed_le ledger.threeTermComparison.q_le_theta :=
  rfl

theorem corollary312_eq_membership_commonBound (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    ledger.corollary312 =
      corollary312_of_signed_le
        (le_trans ledger.membership.q_le_target
          (by
            rw [ledger.targetVolume.targetSigned_eq]
            exact TransportedRegionFamily.choice_targetVolume_le_of_commonBound
              ledger.theta_commonBound ledger.chosenOutput.choice)) :=
  rfl

def comparisonData (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    Corollary312ComparisonData :=
  { thetaSigned := thetaSigned,
    qSigned := qSigned,
    q_positive := ledger.q_positive,
    qSigned_le_thetaSigned := ledger.qSigned_le_thetaSigned }

theorem comparisonData_thetaSigned (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    ledger.comparisonData.thetaSigned = thetaSigned :=
  rfl

theorem comparisonData_qSigned (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    ledger.comparisonData.qSigned = qSigned :=
  rfl

theorem comparisonData_corollary312_eq (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    ledger.comparisonData.corollary312 = ledger.corollary312 :=
  rfl

def stage1Comparison (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    Stage1Comparison :=
  ledger.comparisonData.stage1Comparison

theorem comparisonData_stage1Comparison_eq (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    ledger.comparisonData.stage1Comparison = ledger.stage1Comparison :=
  rfl

theorem comparisonData_publicAudit_eq (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    ledger.comparisonData.publicAudit =
      (⟨ledger.qSigned_le_thetaSigned,
          ledger.corollary312,
          (rfl :
            corollary312_from_stage1_comparison ledger.stage1Comparison =
              corollary312_of_signed_le ledger.qSigned_le_thetaSigned)⟩ :
        qSigned <= thetaSigned ∧
          Corollary312Inequality
            (signedPilotLogVolume PilotSide.theta thetaSigned)
            (signedPilotLogVolume PilotSide.q qSigned) ∧
          corollary312_from_stage1_comparison ledger.stage1Comparison =
            corollary312_of_signed_le ledger.qSigned_le_thetaSigned) :=
  rfl

theorem stage1Comparison_theta_eq_signed (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    ledger.stage1Comparison.theta =
      signedPilotLogVolume PilotSide.theta thetaSigned :=
  rfl

theorem stage1Comparison_q_eq_signed (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    ledger.stage1Comparison.q =
      signedPilotLogVolume PilotSide.q qSigned :=
  rfl

theorem stage1Comparison_theta_value_eq_neg (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    ledger.stage1Comparison.theta.value = -thetaSigned :=
  rfl

theorem stage1Comparison_q_value_eq_neg (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    ledger.stage1Comparison.q.value = -qSigned :=
  rfl

theorem stage1Comparison_theta_side_eq_ledger (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    ledger.stage1Comparison.theta_side = rfl :=
  rfl

theorem stage1Comparison_q_side_eq_ledger (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    ledger.stage1Comparison.q_side = rfl :=
  rfl

theorem stage1Comparison_theta_side_value (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    ledger.stage1Comparison.theta.side = PilotSide.theta :=
  rfl

theorem stage1Comparison_q_side_value (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    ledger.stage1Comparison.q.side = PilotSide.q :=
  rfl

theorem stage1Comparison_q_positive_eq_ledger (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    ledger.stage1Comparison.q_positive = ledger.q_positive :=
  rfl

theorem stage1Comparison_q_positive_from_signed (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    0 < ledger.stage1Comparison.q.value := by
  rw [ledger.stage1Comparison_q_value_eq_neg]
  exact ledger.q_positive

theorem q_positive_from_stage1Comparison (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    0 < -qSigned := by
  rw [← ledger.stage1Comparison_q_value_eq_neg]
  exact ledger.stage1Comparison.q_positive

theorem stage1Comparison_comparison_eq_corollary312 (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    ledger.stage1Comparison.comparison = ledger.corollary312 :=
  rfl

theorem stage1Comparison_comparison_eq_threeTermComparison (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    ledger.stage1Comparison.comparison =
      corollary312_of_signed_le ledger.threeTermComparison.q_le_theta :=
  rfl

theorem stage1Comparison_comparison_eq_membership_commonBound (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    ledger.stage1Comparison.comparison =
      corollary312_of_signed_le
        (le_trans ledger.membership.q_le_target
          (by
            rw [ledger.targetVolume.targetSigned_eq]
            exact TransportedRegionFamily.choice_targetVolume_le_of_commonBound
              ledger.theta_commonBound ledger.chosenOutput.choice)) :=
  rfl

theorem stage1Comparison_recovers_corollary312 (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    corollary312_from_stage1_comparison ledger.stage1Comparison =
      ledger.corollary312 :=
  rfl

theorem stage1Comparison_recovers_threeTermComparison (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    corollary312_from_stage1_comparison ledger.stage1Comparison =
      corollary312_of_signed_le ledger.threeTermComparison.q_le_theta :=
  rfl

theorem sheMatchesCertificate (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    ledger.chartedContainer.commonContainer.hddShe.sheArrow.datum =
      ledger.certificate.she :=
  ledger.she_matches_certificate

theorem sheMatchesCertificate_eq_field (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    ledger.sheMatchesCertificate = ledger.she_matches_certificate :=
  rfl

theorem certificateShe_eq_commonContainerSheDatum (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    ledger.certificate.she =
      ledger.chartedContainer.commonContainer.hddShe.sheArrow.datum :=
  ledger.she_matches_certificate.symm

theorem commonContextMatchesCertificate (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    ledger.chartedContainer.commonContainer.context =
      ledger.certificate.she.sharedContext := by
  rw [← ledger.chartedContainer.commonContainer.she_context_matches]
  rw [ledger.she_matches_certificate]

theorem commonContextMatchesCertificate_eq_sheAlignment (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    ledger.commonContextMatchesCertificate =
      (by
        rw [← ledger.chartedContainer.commonContainer.she_context_matches]
        rw [ledger.she_matches_certificate]) :=
  rfl

theorem certificateContext_eq_commonContext (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    ledger.certificate.she.sharedContext =
      ledger.chartedContainer.commonContainer.context :=
  ledger.commonContextMatchesCertificate.symm

theorem thetaChartTrivial (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    Transport.TrivialMonodromy
      ledger.chartedContainer.chart.thetaToTarget :=
  ledger.chartedContainer.thetaTrivial

theorem thetaChartTrivial_eq_chartedContainer (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    ledger.thetaChartTrivial = ledger.chartedContainer.thetaTrivial :=
  rfl

theorem thetaChartTrivial_eq_chartField (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    ledger.thetaChartTrivial =
      ledger.chartedContainer.chart.theta_trivial :=
  rfl

theorem qSigned_eq_chartedQ (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    (Transport.map ledger.chartedContainer.chart.qToTarget
      ledger.qValue.qPoint).coord = qSigned :=
  ledger.qValue.qSigned_eq

theorem qSigned_eq_chartedQ_eq_field (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    ledger.qSigned_eq_chartedQ = ledger.qValue.qSigned_eq :=
  rfl

theorem qSigned_eq_chartedQCoord (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    qSigned =
      (Transport.map ledger.chartedContainer.chart.qToTarget
        ledger.qValue.qPoint).coord :=
  ledger.qValue.qSigned_eq.symm

theorem thetaSigned_eq_chartedTheta (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    (Transport.map ledger.chartedContainer.chart.thetaToTarget
      ledger.thetaBound.thetaPoint).coord = thetaSigned :=
  ledger.thetaBound.thetaSigned_eq

theorem thetaSigned_eq_chartedTheta_eq_field (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    ledger.thetaSigned_eq_chartedTheta = ledger.thetaBound.thetaSigned_eq :=
  rfl

theorem thetaSigned_eq_chartedThetaCoord (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    thetaSigned =
      (Transport.map ledger.chartedContainer.chart.thetaToTarget
        ledger.thetaBound.thetaPoint).coord :=
  ledger.thetaBound.thetaSigned_eq.symm

def thetaCommonBound (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    output.CommonTargetBound measure thetaSigned :=
  ledger.theta_commonBound

theorem thetaCommonBound_eq_field (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    ledger.thetaCommonBound = ledger.theta_commonBound :=
  rfl

theorem thetaCommonBound_eq_chartedContainer_apply (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    ledger.thetaCommonBound =
      ledger.chartedContainer.apply ledger.certificate :=
  ledger.theta_commonBound_eq_charted

/-- Source-agnostic audit summary for a completed source-obligation ledger. -/
structure Audit (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) : Prop where
  certified :
    output.Certified
  she_matches_certificate :
    ledger.chartedContainer.commonContainer.hddShe.sheArrow.datum =
      ledger.certificate.she
  theta_commonBound_matches_charted :
    ledger.thetaCommonBound =
      ledger.chartedContainer.apply ledger.certificate
  common_context_matches :
    ledger.chartedContainer.commonContainer.context =
      ledger.certificate.she.sharedContext
  theta_chart_trivial :
    Transport.TrivialMonodromy ledger.chartedContainer.chart.thetaToTarget
  q_charted :
    (Transport.map ledger.chartedContainer.chart.qToTarget
      ledger.qValue.qPoint).coord = qSigned
  theta_charted :
    (Transport.map ledger.chartedContainer.chart.thetaToTarget
      ledger.thetaBound.thetaPoint).coord = thetaSigned
  chosen_holds :
    ledger.chosenOutput.comparison.Holds ledger.qValue.qPoint
  q_le_target :
    qSigned <= ledger.targetVolume.targetSigned
  target_le_theta :
    ledger.targetVolume.targetSigned <= thetaSigned
  q_le_theta :
    qSigned <= thetaSigned
  corollary_packaging :
    ledger.corollary312 =
      corollary312_of_signed_le ledger.qSigned_le_thetaSigned
  stage_comparison_packaging :
    ledger.stage1Comparison.comparison = ledger.corollary312
  stage_recovers_corollary :
    corollary312_from_stage1_comparison ledger.stage1Comparison =
      ledger.corollary312
  normalization_witness :
    normalization

theorem audit (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    Audit ledger :=
  { certified := ledger.algorithmCertified,
    she_matches_certificate := ledger.sheMatchesCertificate,
    theta_commonBound_matches_charted :=
      ledger.thetaCommonBound_eq_chartedContainer_apply,
    common_context_matches := ledger.commonContextMatchesCertificate,
    theta_chart_trivial := ledger.thetaChartTrivial,
    q_charted := ledger.qSigned_eq_chartedQ,
    theta_charted := ledger.thetaSigned_eq_chartedTheta,
    chosen_holds := ledger.chosenComparisonHoldsQ,
    q_le_target := ledger.qSigned_le_targetSigned,
    target_le_theta := ledger.targetSigned_le_thetaSigned,
    q_le_theta := ledger.qSigned_le_thetaSigned,
    corollary_packaging := rfl,
    stage_comparison_packaging :=
      ledger.stage1Comparison_comparison_eq_corollary312,
    stage_recovers_corollary := ledger.stage1Comparison_recovers_corollary312,
    normalization_witness := ledger.normalization_proof }

theorem publicAudit (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    qSigned <= thetaSigned ∧
      Corollary312Inequality
        (signedPilotLogVolume PilotSide.theta thetaSigned)
        (signedPilotLogVolume PilotSide.q qSigned) ∧
      corollary312_from_stage1_comparison ledger.stage1Comparison =
        corollary312_of_signed_le ledger.qSigned_le_thetaSigned := by
  let audit := ledger.audit
  exact ⟨audit.q_le_theta,
    ledger.corollary312,
    rfl⟩

theorem hasNormalization (ledger :
    SourceObligationLedger output measure thetaSigned qSigned normalization) :
    normalization :=
  ledger.normalization_proof

end SourceObligationLedger

end Stage1
end Iut
